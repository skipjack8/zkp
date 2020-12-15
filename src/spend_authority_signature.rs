// For benchmarking
use std::time::{Duration, Instant};

// We'll use these interfaces to construct our circuit.
use franklin_crypto::bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError,
};
// We're going to use the Groth16 proving system.
use franklin_crypto::bellman::groth16::{
    create_random_proof,
    generate_random_parameters,
    prepare_verifying_key,
    Proof,
    verify_proof,
};
// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use franklin_crypto::bellman::pairing::bls12_381::Bls12;
use franklin_crypto::jubjub::JubjubBls12;
use franklin_crypto::bellman::pairing::ff::Field;
use franklin_crypto::circuit::boolean::{AllocatedBit, Boolean, u8_vec_into_boolean_vec_le, field_into_boolean_vec_le};
use franklin_crypto::circuit::blake2b::blake2b;
use franklin_crypto::circuit::ecc;
use franklin_crypto::jubjub::{JubjubEngine, ToUniform, Unknown, edwards, PrimeOrder};
use franklin_crypto::redjubjub::{
    PublicKey, Signature, PrivateKey
};
// For randomness (during paramgen and proof generation)
use rand::{Rng, thread_rng};
use franklin_crypto::circuit::ecc::EdwardsPoint;
use franklin_crypto::circuit::num::AllocatedNum;

#[derive(Clone)]
struct SpendAuthoritySignature<E: JubjubEngine> {
    r: Option<edwards::Point<E, PrimeOrder>>,
    s: Option<E::Fs>,
}


#[derive(Clone)]
struct VerifySpendAuthoritySignatureDemo<'a, E: JubjubEngine> {
    msg_hash: Option<Vec<u8>>,
    signature: SpendAuthoritySignature<E>,
    public_key: Option<edwards::Point<E, PrimeOrder>>,
    generator: Option<edwards::Point<E, PrimeOrder>>,
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

        let mut input_bits: Vec<Boolean> = vec![];
        //add r_bar to hash
        let r_bar_bit = r.repr(cs.namespace(||"r unpack to bits"))?;
        input_bits.extend(r_bar_bit.into_iter());
        input_bits.resize(256, Boolean::Constant(false));

        //add vk to hash
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

pub fn pack_bits_into_bytes(bits: Vec<Boolean>) -> Vec<u8> {
    let mut message_bytes: Vec<u8> = Vec::with_capacity(bits.len() / 8);
    let byte_chunks = bits.chunks(8);
    for byte_chunk in byte_chunks {
        let mut byte = 0u8;
        for (i, bit) in byte_chunk.iter().enumerate() {
            let bit_bool = bit.get_value().expect("shoule be succeed.");
            if bit_bool {
                byte |= 1 << i;
            }
        }
        message_bytes.push(byte);
    }
    message_bytes
}

// #[test]
// fn test_spend_auth_sig_bls12() {
//     let jubjubbls12_params = &JubjubBls12::new();
//     // This may not be cryptographically safe, use
//     // `OsRng` (for example) in production software.
//     let rng = &mut thread_rng();
//
//     println!("Creating parameters...");
//     let sig = SpendAuthoritySignature::<Bls12>{
//         r: None,
//         s: None
//     };
//     // Create parameters for our circuit
//     let params = {
//         let c = VerifySpendAuthoritySignatureDemo::<Bls12> {
//             msg_hash: None,
//             signature: sig,
//             public_key: None,
//             generator: None,
//             params: jubjubbls12_params
//         };
//
//         generate_random_parameters(c, rng).unwrap()
//     };
//
//     // Prepare the verification key (for proof verification)
//     let pvk = prepare_verifying_key(&params.vk);
//
//     println!("Creating proofs...");
//
//     // Let's benchmark stuff!
//     const SAMPLES: u32 = 1;
//     let mut total_proving = Duration::new(0, 0);
//     let mut total_verifying = Duration::new(0, 0);
//
//     // Just a place to put the proof data, so we can
//     // benchmark deserialization.
//     let mut proof_vec = vec![];
//
//     for _ in 0..SAMPLES {
//         // Generate a random preimage and compute the image
//         let xl = rng.gen();
//         let xr = rng.gen();
//         let image = mimc::<Bls12>(xl, xr, &constants);
//
//         proof_vec.truncate(0);
//
//         let start = Instant::now();
//         {
//             // Create an instance of our circuit (with the
//             // witness)
//             let c = MiMCDemo {
//                 xl: Some(xl),
//                 xr: Some(xr),
//                 constants: &constants
//             };
//
//             // Create a groth16 proof with our parameters.
//             let proof = create_random_proof(c, &params, rng).unwrap();
//
//             proof.write(&mut proof_vec).unwrap();
//         }
//
//         total_proving += start.elapsed();
//
//         let start = Instant::now();
//         let proof = Proof::read(&proof_vec[..]).unwrap();
//         // Check the proof
//         assert!(verify_proof(
//             &pvk,
//             &proof,
//             &[image]
//         ).unwrap());
//         total_verifying += start.elapsed();
//     }
    // let proving_avg = total_proving / SAMPLES;
    // let proving_avg = proving_avg.subsec_nanos() as f64 / 1_000_000_000f64
    //     + (proving_avg.as_secs() as f64);
    //
    // let verifying_avg = total_verifying / SAMPLES;
    // let verifying_avg = verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64
    //     + (verifying_avg.as_secs() as f64);
    //
    // println!("Average proving time: {:?} seconds", proving_avg);
    // println!("Average verifying time: {:?} seconds", verifying_avg);
// }

