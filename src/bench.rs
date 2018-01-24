// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::BitVec;
use rand::{Rng, weak_rng, XorShiftRng};
use std::collections::BTreeSet;

use test::{Bencher, black_box};

const BENCH_BITS : usize = 1 << 16;
const U32_BITS: usize = 32;

fn rng() -> XorShiftRng {
    weak_rng()
}

#[bench]
fn bench_usize_small(b: &mut Bencher) {
    let mut r = rng();
    let mut bit_vec = 0 as usize;
    b.iter(|| {
        for _ in 0..100 {
            bit_vec |= 1 << ((r.next_u32() as usize) % U32_BITS);
        }
        black_box(&bit_vec);
    });
}

#[bench]
fn bench_bit_set_big_fixed(b: &mut Bencher) {
    let mut r = rng();
    let mut bit_vec = BitVec::<u32>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        for _ in 0..100 {
            bit_vec.set((r.next_u32() as usize) % BENCH_BITS, true);
        }
        black_box(&bit_vec);
    });
}

#[bench]
fn bench_bit_set_big_variable(b: &mut Bencher) {
    let mut r = rng();
    let mut bit_vec = BitVec::<u32>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        for _ in 0..100 {
            bit_vec.set((r.next_u32() as usize) % BENCH_BITS, r.gen());
        }
        black_box(&bit_vec);
    });
}

#[bench]
fn bench_bit_set_rng_overhead(b: &mut Bencher) {
    let mut r = rng();
    let mut bit_vec = BitVec::<u32>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        let mut sum = 0;
        let mut x = false;
        for _ in 0..100 {
            sum += r.next_u32() as usize;
            x = x && r.gen();
        }
        (sum, x)
    });
}

#[bench]
fn bench_bit_set_small(b: &mut Bencher) {
    let mut r = rng();
    let mut bit_vec = BitVec::<u32>::from_elem(U32_BITS, false);
    b.iter(|| {
        for _ in 0..100 {
            bit_vec.set((r.next_u32() as usize) % U32_BITS, true);
        }
        black_box(&bit_vec);
    });
}

#[bench]
fn bench_bit_vec_big_union(b: &mut Bencher) {
    let mut b1 = BitVec::<u32>::from_elem(BENCH_BITS, false);
    let b2 = BitVec::<u32>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        b1.union(&b2)
    })
}

#[bench]
fn bench_bit_vec_big_union_u64_storage(b: &mut Bencher) {
    let mut b1 = BitVec::<u64>::from_elem(BENCH_BITS, false);
    let b2 = BitVec::<u64>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        b1.union(&b2)
    });
}

#[bench]
fn bench_bit_vec_big_cloned_union(b: &mut Bencher) {
    let mut b1 = BitVec::<u32>::from_elem(BENCH_BITS, false);
    let b2 = BitVec::<u32>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        let mut b3 = b1.clone();
        b3.union(&b2);
        b3
    })
}

#[bench]
fn bench_bit_vec_big_cloned_union_u64_storage(b: &mut Bencher) {
    let mut b1 = BitVec::<u64>::from_elem(BENCH_BITS, false);
    let b2 = BitVec::<u64>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        let mut b3 = b1.clone();
        b3.union(&b2);
        b3
    })
}

#[bench]
fn bench_bit_vec_big_cloned_union_u8_storage(b: &mut Bencher) {
    let mut b1 = BitVec::<u8>::from_elem(BENCH_BITS, false);
    let b2 = BitVec::<u8>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        let mut b3 = b1.clone();
        b3.union(&b2);
        b3
    })
}

#[bench]
fn bench_clone_big(b: &mut Bencher) {
    let xs = BitVec::<u32>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        xs.clone()
    });
}

#[bench]
fn bench_btreeset_big_union(b: &mut Bencher) {
    let mut r = rng();
    let mut xs = BTreeSet::new();
    let mut ys = BTreeSet::new();
    for _ in 0..(BENCH_BITS / 4) {
        xs.insert(r.gen::<usize>());
        ys.insert(r.gen::<usize>());
    }

    b.iter(|| {
        xs.union(&ys).cloned().collect::<BTreeSet<usize>>()
    });
}

#[bench]
fn bench_btreeset_big_union_collect_vec(b: &mut Bencher) {
    let mut r = rng();
    let mut xs = BTreeSet::new();
    let mut ys = BTreeSet::new();
    for _ in 0..(BENCH_BITS / 4) {
        xs.insert(r.gen::<usize>());
        ys.insert(r.gen::<usize>());
    }

    b.iter(|| {
        xs.union(&ys).cloned().collect::<Vec<usize>>()
    });
}

#[bench]
fn bench_bit_vec_small_iter(b: &mut Bencher) {
    let bit_vec = BitVec::<u32>::from_elem(U32_BITS, false);
    b.iter(|| {
        let mut sum = 0;
        for _ in 0..10 {
            for pres in &bit_vec {
                sum += pres as usize;
            }
        }
        sum
    })
}

#[bench]
fn bench_u32_vec_big_iter(b: &mut Bencher) {
    let xs: Vec<u32> = vec![0; BENCH_BITS];
    b.iter(|| {
        let mut sum = 0usize;
        for pres in &xs {
            sum += *pres as usize;
        }
        sum
    });
}

#[bench]
fn bench_bit_vec_big_iter(b: &mut Bencher) {
    let bit_vec = BitVec::<u32>::from_elem(BENCH_BITS, false);
    b.iter(|| {
        let mut sum = 0;
        for pres in &bit_vec {
            sum += pres as usize;
        }
        sum
    })
}

#[bench]
fn bench_from_elem(b: &mut Bencher) {
    let cap = black_box(BENCH_BITS);
    let bit = black_box(true);
    b.iter(|| {
        // create a BitVec and popcount it
        BitVec::<u32>::from_elem(cap, bit).blocks()
                                   .fold(0, |acc, b| acc + b.count_ones())
    });
    b.bytes = cap as u64 / 8;
}
