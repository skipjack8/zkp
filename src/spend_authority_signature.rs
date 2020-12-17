// For benchmarking
use std::time::{Duration, Instant};

// We'll use these interfaces to construct our circuit.
use hi_crypto::bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError,
};
// We're going to use the Groth16 proving system.
use hi_crypto::bellman::groth16::{
    create_random_proof,
    generate_random_parameters,
    prepare_verifying_key,
    Proof,
    verify_proof,
};
// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use hi_crypto::bellman::pairing::bls12_381::{Bls12, Fr};
use hi_crypto::bellman::pairing::ff::{Field, from_hex, to_hex};
use hi_crypto::circuit::blake2b::blake2b;
use hi_crypto::circuit::boolean::{Boolean, field_into_boolean_vec_le, u8_vec_into_boolean_vec_le};
use hi_crypto::circuit::ecc::EdwardsPoint;
use hi_crypto::circuit::multipack::pack_into_inputs;
use hi_crypto::jubjub::{edwards, JubjubEngine, Unknown, JubjubParams};
use hi_crypto::jubjub::{JubjubBls12, fs::Fs};
use hi_crypto::redjubjub::{
    PrivateKey, PublicKey
};
// For randomness (during paramgen and proof generation)
use rand::{Rng, thread_rng};
use hi_crypto::jubjub::edwards::Point;

#[derive(Clone)]
struct SpendAuthoritySignature<E: JubjubEngine> {
    r: Option<edwards::Point<E, Unknown>>,
    s: Option<E::Fs>,
}


#[derive(Clone)]
struct VerifySpendAuthoritySignatureDemo<'a, E: JubjubEngine> {
    msg_hash: Option<Vec<u8>>,
    signature: SpendAuthoritySignature<E>,
    public_key: Option<edwards::Point<E, Unknown>>,
    generator: Option<edwards::Point<E, Unknown>>,
    params: &'a E::Params,
}

impl<'a, E: JubjubEngine> Circuit<E> for VerifySpendAuthoritySignatureDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    {
        let vk = EdwardsPoint::witness(cs.namespace(||"vk"), self.public_key, self.params)?;
        vk.assert_not_small_order(cs.namespace(||"vk not small order"), &self.params)?;

        let r = EdwardsPoint::witness(cs.namespace(||"r"), self.signature.r, self.params)?;
        r.inputize(cs.namespace(||"inputize signature.r"))?;

        let mut input_bits: Vec<Boolean> = vec![];
        //add r_bar to hash
        let r_bar_bit = r.repr(cs.namespace(||"r unpack to bits"))?;
        input_bits.extend(r_bar_bit.into_iter());
        input_bits.resize(256, Boolean::Constant(false));

        // //add vk to hash
        let vk_bits = vk.repr(cs.namespace(||"vk unpack to bits"))?;
        input_bits.extend(vk_bits.into_iter());
        input_bits.resize(512, Boolean::Constant(false));

        //add msg hash to hash
        let msg_hash_bits = u8_vec_into_boolean_vec_le(cs.namespace(||"message unpack into bits"), self.msg_hash)?;
        input_bits.extend(msg_hash_bits.into_iter());
        input_bits.resize(768, Boolean::Constant(false));

        let h_star = blake2b(cs.namespace(||"blake2b hash"), &input_bits, b"Zcash_RedJubjubH").unwrap();
        assert_eq!(h_star.len(), 512);

        let s_bit = field_into_boolean_vec_le(cs.namespace(||"scalar into bits"), self.signature.s)?;
        pack_into_inputs(cs.namespace(||"signature.s inputize"), &s_bit)?;

        let generator = EdwardsPoint::witness(cs.namespace(||"generator witness"), self.generator, self.params)?;
        let generator = generator.negate(cs.namespace(||"generator negate"), self.params)?;

        let mut sig = vk.mul(cs.namespace(||"hstar * vk"), &h_star, self.params)?;
        let tmp = generator.mul(cs.namespace(||"-s * generator"), &s_bit, self.params)?;
        sig = sig.add(cs.namespace(||"signature add1"), &tmp, self.params)?;
        sig = sig.add(cs.namespace(||"signature add2"), &r, self.params)?;

        let mut zero = sig.double(cs.namespace(||"sig double"), self.params)?;
        zero = zero.double(cs.namespace(||"sig times 4"), self.params)?;
        zero = zero.double(cs.namespace(||"sig times 8"), self.params)?;

        cs.enforce(
            ||"result to zero point x",
            |lc| lc + zero.get_x().get_variable(),
            |lc| lc + CS::one(),
            |lc| lc
        );

        cs.enforce(
            ||"result to zero point y",
            |lc| lc + zero.get_y().get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + CS::one()
        );

        Ok(())
    }
}

#[test]
fn test_spend_auth_sig_bls12() {
    use hi_crypto::jubjub::FixedGenerators;

    let jubjubbls12_params = &JubjubBls12::new();
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let rng = &mut thread_rng();
    let p_g = FixedGenerators::SpendingKeyGenerator;
    let gen = Point::<Bls12, Unknown>::from(jubjubbls12_params.generator(p_g).clone());

    let sk = PrivateKey::<Bls12>(rng.gen());
    let vk = PublicKey::from_private(&sk, p_g, jubjubbls12_params);
    let msg = b"This is a test message for sign.";
    let mut data_to_be_signed = [0u8; 64];
    vk.write(&mut data_to_be_signed[0..32]).unwrap();
    (&mut data_to_be_signed[32..64]).copy_from_slice(&({ &*msg })[..]);

    println!("Creating parameters...");
    let signature = SpendAuthoritySignature::<Bls12>{
        r: None,
        s: None
    };
    // Create parameters for our circuit
    let params = {
        let c = VerifySpendAuthoritySignatureDemo::<Bls12> {
            msg_hash: None,
            signature: signature,
            public_key: None,
            generator: None,
            params: jubjubbls12_params
        };

        generate_random_parameters(c, rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    // Let's benchmark stuff!
    const SAMPLES: u32 = 10;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];

    for cnt in 0..SAMPLES {
        proof_vec.truncate(0);

        //generate signature
        let sig = sk.sign(&data_to_be_signed, rng, p_g, jubjubbls12_params);
        assert!(vk.verify(&data_to_be_signed, &sig, p_g, jubjubbls12_params));

        let mut sig_bytes = [0u8; 64];
        sig.write(&mut sig_bytes[..]).unwrap();
        let r_point  = PublicKey::<Bls12>::read(&sig_bytes[..32], &jubjubbls12_params).unwrap().0;
        let s_fs = PrivateKey::<Bls12>::read(&sig_bytes[32..]).unwrap().0;

        println!("Creating proofs {:?}...", cnt);
        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = VerifySpendAuthoritySignatureDemo::<Bls12> {
                msg_hash: Some(msg.iter().cloned().collect()),
                signature: SpendAuthoritySignature::<Bls12> {
                    r: Some(r_point.clone()),
                    s: Some(s_fs),
                },
                public_key: Some(vk.clone().0),
                generator: Some(gen.clone()),
                params: jubjubbls12_params
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();

        //generate public inputs
        let mut image = vec![];
        let r_point_x_y = r_point.into_xy();
        image.push(r_point_x_y.0);
        image.push(r_point_x_y.1);

        let s_hex = to_hex::<Fs>(&s_fs);
        let s_fr = from_hex::<Fr>(&s_hex).unwrap();
        image.push(s_fr);

        println!("Verifying proofs {:?}...", cnt);
        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(
            &pvk,
            &proof,
            &image
        ).unwrap());
        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg = proving_avg.subsec_nanos() as f64 / 1_000_000_000f64
        + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg = verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64
        + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}

