//
// Copyright 2024 Christopher Atherton <the8lack8ox@pm.me>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the “Software”), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.
//

use std::env;
use std::fs::File;
use std::io::{Read, Result};
use std::ops::Shr;

struct Sha256Hasher {
    hash: [u32; 8],
    buffer: Vec<u8>,
    length: usize,
    finished: bool,
}

impl Sha256Hasher {
    pub fn new() -> Self {
        Self {
            hash: [
                0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F,
                0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
            ],
            buffer: Vec::new(),
            length: 0,
            finished: false,
        }
    }

    fn slow_update(&mut self, buf: &[u8]) {
        const K: [u32; 64] = [
            0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B,
            0x59F111F1, 0x923F82A4, 0xAB1C5ED5, 0xD807AA98, 0x12835B01,
            0x243185BE, 0x550C7DC3, 0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7,
            0xC19BF174, 0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC,
            0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA, 0x983E5152,
            0xA831C66D, 0xB00327C8, 0xBF597FC7, 0xC6E00BF3, 0xD5A79147,
            0x06CA6351, 0x14292967, 0x27B70A85, 0x2E1B2138, 0x4D2C6DFC,
            0x53380D13, 0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85,
            0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3, 0xD192E819,
            0xD6990624, 0xF40E3585, 0x106AA070, 0x19A4C116, 0x1E376C08,
            0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F,
            0x682E6FF3, 0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208,
            0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2,
        ];

        self.length += buf.len();
        self.buffer.extend_from_slice(buf);

        let chunks = self.buffer.chunks_exact(64);
        let remainder_tmp = chunks.remainder();
        for chunk in chunks {
            let mut w = Vec::with_capacity(64);
            for i in 0..16 {
                w.push(u32::from_be_bytes(
                    chunk[i * 4..i * 4 + 4].try_into().unwrap(),
                ));
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7)
                    ^ w[i - 15].rotate_right(18)
                    ^ w[i - 15].shr(3);
                let s1 = w[i - 2].rotate_right(17)
                    ^ w[i - 2].rotate_right(19)
                    ^ w[i - 2].shr(10);
                w.push(
                    w[i - 16]
                        .wrapping_add(s0)
                        .wrapping_add(w[i - 7])
                        .wrapping_add(s1),
                );
            }

            let mut a = self.hash[0];
            let mut b = self.hash[1];
            let mut c = self.hash[2];
            let mut d = self.hash[3];
            let mut e = self.hash[4];
            let mut f = self.hash[5];
            let mut g = self.hash[6];
            let mut h = self.hash[7];

            for i in 0..64 {
                let s1 =
                    e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
                let ch = (e & f) ^ ((!e) & g);
                let tmp1 = h
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]);
                let s0 =
                    a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
                let maj = (a & b) ^ (a & c) ^ (b & c);
                let tmp2 = s0.wrapping_add(maj);

                h = g;
                g = f;
                f = e;
                e = d.wrapping_add(tmp1);
                d = c;
                c = b;
                b = a;
                a = tmp1.wrapping_add(tmp2);
            }

            self.hash[0] = self.hash[0].wrapping_add(a);
            self.hash[1] = self.hash[1].wrapping_add(b);
            self.hash[2] = self.hash[2].wrapping_add(c);
            self.hash[3] = self.hash[3].wrapping_add(d);
            self.hash[4] = self.hash[4].wrapping_add(e);
            self.hash[5] = self.hash[5].wrapping_add(f);
            self.hash[6] = self.hash[6].wrapping_add(g);
            self.hash[7] = self.hash[7].wrapping_add(h);
        }

        self.buffer = Vec::from(remainder_tmp);
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "sha")]
    #[allow(overflowing_literals)]
    unsafe fn intrinsic_update(&mut self, buf: &[u8]) {
        use std::arch::x86_64::*;

        self.length += buf.len();
        self.buffer.extend_from_slice(buf);

        let mask = _mm_set_epi64x(0x0C0D0E0F08090A0B, 0x0405060700010203);
        let mut tmp = _mm_loadu_si128(self.hash[0..4].as_ptr() as *const _);
        let mut state1 = _mm_loadu_si128(self.hash[4..8].as_ptr() as *const _);

        tmp = _mm_shuffle_epi32(tmp, 0xB1);
        state1 = _mm_shuffle_epi32(state1, 0x1B);
        let mut state0 = _mm_alignr_epi8(tmp, state1, 8);
        state1 = _mm_blend_epi16(state1, tmp, 0xF0);

        let chunks = self.buffer.chunks_exact(64);
        let remainder_tmp = chunks.remainder();
        for chunk in chunks {
            // Save current state
            let abef_save = state0;
            let cdgh_save = state1;

            // Rounds 0 ~ 3
            let mut msg = _mm_loadu_si128(chunk[0..16].as_ptr() as *const _);
            let mut msg0 = _mm_shuffle_epi8(msg, mask);
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0xE9B5DBA5B5C0FBCF, 0x71374491428A2F98),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Rounds 4 ~ 7
            let mut msg1 = _mm_loadu_si128(chunk[16..32].as_ptr() as *const _);
            msg1 = _mm_shuffle_epi8(msg1, mask);
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0xAB1C5ED5923F82A4, 0x59F111F13956C25B),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg0 = _mm_sha256msg1_epu32(msg0, msg1);

            // Rounds 8 ~ 11
            let mut msg2 = _mm_loadu_si128(chunk[32..48].as_ptr() as *const _);
            msg2 = _mm_shuffle_epi8(msg2, mask);
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0x550C7DC3243185BE, 0x12835B01D807AA98),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg1 = _mm_sha256msg1_epu32(msg1, msg2);

            // Rounds 12 ~ 15
            let mut msg3 = _mm_loadu_si128(chunk[48..64].as_ptr() as *const _);
            msg3 = _mm_shuffle_epi8(msg3, mask);
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0xC19BF1749BDC06A7, 0x80DEB1FE72BE5D74),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg3, msg2, 4);
            msg0 = _mm_add_epi32(msg0, tmp);
            msg0 = _mm_sha256msg2_epu32(msg0, msg3);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg2 = _mm_sha256msg1_epu32(msg2, msg3);

            // Rounds 16 ~ 19
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0x240CA1CC0FC19DC6, 0xEFBE4786E49B69C1),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg0, msg3, 4);
            msg1 = _mm_add_epi32(msg1, tmp);
            msg1 = _mm_sha256msg2_epu32(msg1, msg0);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg3 = _mm_sha256msg1_epu32(msg3, msg0);

            // Rounds 20 ~ 23
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0x76F988DA5CB0A9DC, 0x4A7484AA2DE92C6F),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg1, msg0, 4);
            msg2 = _mm_add_epi32(msg2, tmp);
            msg2 = _mm_sha256msg2_epu32(msg2, msg1);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg0 = _mm_sha256msg1_epu32(msg0, msg1);

            // Rounds 24 ~ 27
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0xBF597FC7B00327C8, 0xA831C66D983E5152),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg2, msg1, 4);
            msg3 = _mm_add_epi32(msg3, tmp);
            msg3 = _mm_sha256msg2_epu32(msg3, msg2);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg1 = _mm_sha256msg1_epu32(msg1, msg2);

            // Rounds 28 ~ 31
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0x1429296706CA6351, 0xD5A79147C6E00BF3),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg3, msg2, 4);
            msg0 = _mm_add_epi32(msg0, tmp);
            msg0 = _mm_sha256msg2_epu32(msg0, msg3);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg2 = _mm_sha256msg1_epu32(msg2, msg3);

            // Rounds 32 ~ 35
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0x53380D134D2C6DFC, 0x2E1B213827B70A85),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg0, msg3, 4);
            msg1 = _mm_add_epi32(msg1, tmp);
            msg1 = _mm_sha256msg2_epu32(msg1, msg0);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg3 = _mm_sha256msg1_epu32(msg3, msg0);

            // Rounds 36 ~ 39
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0x92722C8581C2C92E, 0x766A0ABB650A7354),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg1, msg0, 4);
            msg2 = _mm_add_epi32(msg2, tmp);
            msg2 = _mm_sha256msg2_epu32(msg2, msg1);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg0 = _mm_sha256msg1_epu32(msg0, msg1);

            // Rounds 40 ~ 43
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0xC76C51A3C24B8B70, 0xA81A664BA2BFE8A1),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg2, msg1, 4);
            msg3 = _mm_add_epi32(msg3, tmp);
            msg3 = _mm_sha256msg2_epu32(msg3, msg2);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg1 = _mm_sha256msg1_epu32(msg1, msg2);

            // Rounds 44 ~ 47
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0x106AA070F40E3585, 0xD6990624D192E819),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg3, msg2, 4);
            msg0 = _mm_add_epi32(msg0, tmp);
            msg0 = _mm_sha256msg2_epu32(msg0, msg3);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg2 = _mm_sha256msg1_epu32(msg2, msg3);

            // Rounds 48 ~ 51
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0x34B0BCB52748774C, 0x1E376C0819A4C116),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg0, msg3, 4);
            msg1 = _mm_add_epi32(msg1, tmp);
            msg1 = _mm_sha256msg2_epu32(msg1, msg0);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg3 = _mm_sha256msg1_epu32(msg3, msg0);

            // Rounds 52 ~ 55
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0x682E6FF35B9CCA4F, 0x4ED8AA4A391C0CB3),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg1, msg0, 4);
            msg2 = _mm_add_epi32(msg2, tmp);
            msg2 = _mm_sha256msg2_epu32(msg2, msg1);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Rounds 56 ~ 59
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0x8CC7020884C87814, 0x78A5636F748F82EE),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg2, msg1, 4);
            msg3 = _mm_add_epi32(msg3, tmp);
            msg3 = _mm_sha256msg2_epu32(msg3, msg2);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Rounds 60 ~ 63
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0xC67178F2BEF9A3F7, 0xA4506CEB90BEFFFA),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Combine state
            state0 = _mm_add_epi32(state0, abef_save);
            state1 = _mm_add_epi32(state1, cdgh_save);
        }

        tmp = _mm_shuffle_epi32(state0, 0x1B); // FEBA
        state1 = _mm_shuffle_epi32(state1, 0xB1); // DCHG
        state0 = _mm_blend_epi16(tmp, state1, 0xF0); // DCBA
        state1 = _mm_alignr_epi8(state1, tmp, 8); // ABEF

        _mm_storeu_si128(self.hash[0..4].as_ptr() as *mut _, state0);
        _mm_storeu_si128(self.hash[4..8].as_ptr() as *mut _, state1);

        self.buffer = Vec::from(remainder_tmp);
    }

    pub fn update(&mut self, buf: &[u8]) {
        assert!(!self.finished);

        #[cfg(target_arch = "x86_64")]
        {
            if is_x86_feature_detected!("sha") {
                unsafe {
                    self.intrinsic_update(buf);
                }
                return;
            }
        }

        self.slow_update(buf);
    }

    pub fn finish(&mut self) {
        assert!(!self.finished);

        const ZEROS: [u8; 64] = [0; 64];
        let mut end = Vec::with_capacity(64);
        end.push(0x80);
        end.extend_from_slice(&ZEROS[..(120 - ((self.length + 1) % 64)) % 64]);
        end.extend_from_slice(&(self.length as u64 * 8).to_be_bytes());

        self.update(&end);
        self.finished = true;
    }

    // pub fn hash(&self) -> [u32; 8] {
    //     assert!(self.finished);
    //     self.hash
    // }

    pub fn hash_as_string(&self) -> String {
        assert!(self.finished);
        format!(
            "{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}",
            self.hash[0],
            self.hash[1],
            self.hash[2],
            self.hash[3],
            self.hash[4],
            self.hash[5],
            self.hash[6],
            self.hash[7]
        )
    }
}

fn run() -> Result<()> {
    let inputs: Vec<_> = env::args().skip(1).collect();

    if inputs.is_empty() {
        let mut hasher = Sha256Hasher::new();
        let mut buffer = [0; 8192];
        let mut count = std::io::stdin().read(&mut buffer)?;
        while count > 0 {
            hasher.update(&buffer[..count]);
            count = std::io::stdin().read(&mut buffer)?;
        }
        hasher.finish();
        println!("{} -", hasher.hash_as_string());
    } else {
        for input in &inputs {
            let mut hasher = Sha256Hasher::new();
            let mut buffer = [0; 8192];
            let mut file = File::open(input)?;
            let mut count = file.read(&mut buffer)?;
            while count > 0 {
                hasher.update(&buffer[..count]);
                count = file.read(&mut buffer)?;
            }
            hasher.finish();
            println!("{} {input}", hasher.hash_as_string());
        }
    }

    Ok(())
}

fn main() {
    match run() {
        Ok(()) => (),
        Err(err) => {
            eprintln!("{err}");
            std::process::exit(1);
        }
    }
}
