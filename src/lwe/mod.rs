use std::ops::{Add, Mul, Rem};

use rand::Rng;
use rand_distr::{num_traits::Float, Distribution, Normal};
use crate::treepp::{pushable, script, Script};

pub fn polymul(x: &[i64], y: &[i64], modulus: i64, poly_mod: &[i64]) -> Vec<i64> {
    let mut result = vec![0; x.len() + y.len() - 1];
    for (i, &xi) in x.iter().enumerate() {
        for (j, &yj) in y.iter().enumerate() {
            result[i + j] = (result[i + j] + xi * yj) % modulus;
        }
    }
    polydiv(&result, poly_mod, modulus)
}

pub fn polyadd(x: &[i64], y: &[i64], modulus: i64, poly_mod: &[i64]) -> Vec<i64> {
    let len = std::cmp::max(x.len(), y.len());
    let mut result = vec![0; len];
    for i in 0..len {
        result[i] = ((if i < x.len() { x[i] } else { 0 }) + (if i < y.len() { y[i] } else { 0 })) % modulus;
    }
    polydiv(&result, poly_mod, modulus)
}

pub fn polydiv(x: &[i64], poly_mod: &[i64], modulus: i64) -> Vec<i64> {
    let mut result = x.to_vec();
    while result.len() >= poly_mod.len() {
        let lead_coeff = result[result.len() - 1];
        let degree_diff = result.len() - poly_mod.len();
        for (i, &coeff) in poly_mod.iter().enumerate() {
            let index = degree_diff + i;
            result[index] = (result[index] - lead_coeff * coeff) % modulus;
            if result[index] < 0 {
                result[index] += modulus;
            }
        }
        while result.last() == Some(&0) {
            result.pop();
        }
    }
    result
}

pub fn gen_binary_poly(size: usize) -> Vec<i64> {
    let mut rng = rand::thread_rng();
    (0..size).map(|_| rng.gen_range(0..2)).collect()
}

pub fn gen_uniform_poly(size: usize, modulus: i64) -> Vec<i64> {
    let mut rng = rand::thread_rng();
    (0..size).map(|_| rng.gen_range(0..modulus)).collect()
}

pub fn gen_normal_poly(size: usize) -> Vec<i64> {
    let normal = Normal::new(0.0, 2.0).unwrap();
    let mut rng = rand::thread_rng();
    (0..size).map(|_| normal.sample(&mut rng).round() as i64).collect()
}

pub fn keygen(size: usize, modulus: i64, poly_mod: &[i64]) -> ((Vec<i64>, Vec<i64>), Vec<i64>) {
    let sk = gen_binary_poly(size);
    let a = gen_uniform_poly(size, modulus);
    let e = gen_normal_poly(size);

    let minus_a = a.iter().map(|&ai| -ai).collect::<Vec<i64>>();
    let minus_e = e.iter().map(|&ei| -ei).collect::<Vec<i64>>();

    let b = polyadd(
        &polymul(&minus_a, &sk, modulus, poly_mod),
        &minus_e,
        modulus,
        poly_mod,
    );

    ((b, a), sk)
}

pub fn encrypt(
    pk: (Vec<i64>, Vec<i64>),
    size: usize,
    q: i64,
    t: i64,
    poly_mod: &[i64],
    pt: i64,
) -> (Vec<i64>, Vec<i64>) {
    let mut m = vec![0; size];
    m[0] = pt % t;
    let delta = q / t;
    let scaled_m: Vec<i64> = m.iter().map(|&mi| (delta * mi) % q).collect();

    let e1 = gen_normal_poly(size);
    let e2 = gen_normal_poly(size);
    let u = gen_binary_poly(size);

    let ct0 = polyadd(
        &polyadd(
            &polymul(&pk.0, &u, q, poly_mod),
            &e1,
            q,
            poly_mod,
        ),
        &scaled_m,
        q,
        poly_mod,
    );
    let ct1 = polyadd(
        &polymul(&pk.1, &u, q, poly_mod),
        &e2,
        q,
        poly_mod,
    );

    (ct0, ct1)
}

pub fn decrypt(
    sk: &[i64],
    size: usize,
    q: i64,
    t: i64,
    poly_mod: &[i64],
    ct: (Vec<i64>, Vec<i64>),
) -> i64 {
    let scaled_pt = polyadd(
        &polymul(&ct.1, sk, q, poly_mod),
        &ct.0,
        q,
        poly_mod,
    );

    let decrypted_poly: Vec<i64> = scaled_pt
        .iter()
        .map(|&coef| ((coef as f64 * t as f64 / q as f64).round() as i64) % t)
        .collect();

    decrypted_poly[0]
}

pub fn add_plain(
    ct: (Vec<i64>, Vec<i64>),
    pt: i64,
    q: i64,
    t: i64,
    poly_mod: &[i64],
) -> (Vec<i64>, Vec<i64>) {
    let size = poly_mod.len() - 1;

    let mut m = vec![0; size];
    m[0] = pt % t;
    let delta = q / t;
    let scaled_m: Vec<i64> = m.iter().map(|&mi| (delta * mi) % q).collect();

    let new_ct0 = polyadd(&ct.0, &scaled_m, q, poly_mod);
    (new_ct0, ct.1.clone())
}

pub fn add_cipher(
    ct1: (Vec<i64>, Vec<i64>),
    ct2: (Vec<i64>, Vec<i64>),
    q: i64,
    poly_mod: &[i64],
) -> (Vec<i64>, Vec<i64>) {
    let new_ct0 = polyadd(&ct1.0, &ct2.0, q, poly_mod);
    let new_ct1 = polyadd(&ct1.1, &ct2.1, q, poly_mod);
    (new_ct0, new_ct1)
}

#[cfg(test)]
mod tests {
    use bitcoin::opcodes::all::{OP_ADD, OP_EQUAL};

    use crate::execute_script;

    use super::*;

    #[test]
    fn test_add_plain() {
        let n = 16;
        let q = 2i64.pow(15);
        let t = 2i64.pow(8);
        let mut poly_mod = vec![0; n + 1];
        poly_mod[0] = 1;
        poly_mod[n] = 1;

        let (pk, sk) = keygen(n, q, &poly_mod);
        let pt = 73;
        let ct = encrypt(pk.clone(), n, q, t, &poly_mod, pt);
        let cst = 7;
        let ct_new = add_plain(ct, cst, q, t, &poly_mod);
        let decrypted_ct_new = decrypt(&sk, n, q, t, &poly_mod, ct_new);

        let exec_script = script!{
            73
            7
            OP_ADD
            {decrypted_ct_new}
            OP_EQUAL
        };

        let exec_result = execute_script(exec_script);
        assert!(exec_result.success)
    }

    #[test]
    fn test_add_cipher() {
        let n = 16;
        let q = 2i64.pow(15);
        let t = 2i64.pow(8);
        let mut poly_mod = vec![0; n + 1];
        poly_mod[0] = 1;
        poly_mod[n] = 1;

        let (pk, sk) = keygen(n, q, &poly_mod);
        let pt1 = 73;
        let pt2 = 20;
        let ct1 = encrypt(pk.clone(), n, q, t, &poly_mod, pt1);
        let ct2 = encrypt(pk, n, q, t, &poly_mod, pt2);
        let ct_new = add_cipher(ct1, ct2, q, &poly_mod);
        let decrypted_ct_new = decrypt(&sk, n, q, t, &poly_mod, ct_new);

        let exec_script = script!{
            73
            20
            OP_ADD
            {decrypted_ct_new}
            OP_EQUAL
        };


        let exec_result = execute_script(exec_script);
        assert!(exec_result.success)
    }
}
