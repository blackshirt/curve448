// Copyright © 2026 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Internal helper functions used across the curve448 module.
module curve448

import math.bits
import math.unsigned

// mask_64bits returns an all-ones mask if cond is nonzero, all-zeros if
// cond == 0.
//
// Robust to any nonzero encoding of "true" (1, -1, 2, ...). Uses the
// branchless trick: (x | -x) has its MSB set iff x != 0.
//
// This is the fundamental building block for constant-time selection.
@[inline]
fn mask_64bits(cond int) u64 {
	c := u64(cond)
	normalized := (c | (0 - c)) >> 63
	return u64(0) - normalized
}

// mult_64 computes the full 128-bit product of two 64-bit values.
//
// Returns a Uint128 where: value = a · b
@[inline]
fn mult_64(a u64, b u64) unsigned.Uint128 {
	// Use the built-in 64-bit multiplication to get the full 128-bit result.
	// activated with `-d use_128hw` flag
	$if use_128hw ? {
		// Use the C backend implementation of 128-bit multiplication.
		// See util.h for the C implementation of mul_64_hw.
		mut hi := u64(0)
		lo := C.mul_64_hw(a, b, &hi)
		return unsigned.uint128_new(lo, hi)
	}
	// Fallback to builtin math.bits implementation.
	hi, lo := bits.mul_64(a, b)
	return unsigned.uint128_new(lo, hi)
}

// mult_56 performs a 64×32 → 128-bit multiply and splits the result into
// 56-bit limbs.
//
// Given:
//   a  — 64-bit multiplicand (up to 64 bits).
//   b  — 32-bit multiplier    (up to 32 bits).
//
// The full 128-bit product P = a * b is decomposed as:
//
//     P = hi·2^56 + lo   where   0 ≤ lo < 2^56
//
// Returns:
//   lo — Lower 56 bits of the product (masked).
//   hi — Upper bits of the product, right-shifted by 56 places.
//
// This is useful in multi-limb big-integer arithmetic where each limb
// carries 56 bits (e.g. base-2^56 representation).
@[inline]
fn mult_56(a u64, b u32) (u64, u64) {
	$if use_128hw ? {
		// Use the C backend implementation of 128-bit multiplication
		// See util.h for the C implementation of mul_64_hw.
		mut prod_hi := u64(0)
		prod_lo := C.mul_64_hw(a, u64(b), &prod_hi)

		// Extract the low 56-bit limb.
		lo := prod_lo & mask_56bits

		// The remaining bits above bit 55 come from:
		//   • the upper 8 bits of prod_lo  (prod_lo >> 56)
		//   • all 64 bits of prod_hi, shifted left by 8 to align with bit 56
		hi := (prod_hi << 8) | (prod_lo >> limb_bits_size)

		return lo, hi
	}
	// Otherwise, use the fallback implementation with math.bits.mul_64
	hh, ll := bits.mul_64(a, u64(b))
	lo := ll & mask_56bits
	hi := (hh << 8) | (ll >> limb_bits_size)
	return lo, hi
}

// add_128 adds two 128-bit unsigned integers.
@[inline]
fn add_128(a unsigned.Uint128, b unsigned.Uint128) unsigned.Uint128 {
	// Use the C implementation of 128-bit addition.
	$if use_128hw ? {
		// Use the C backend implementation of 128-bit addition
		// See util.h for the C implementation of add_128_hw.
		mut hi := u64(0)
		lo := C.add_128_hw(a.lo, a.hi, b.lo, b.hi, &hi)
		return unsigned.uint128_new(lo, hi)
	}
	// Fallback to manual addition with carry.
	lo := a.lo + b.lo
	carry := u64(lo < a.lo) // same idiom sub_128 already uses
	hi := a.hi + b.hi + carry
	return unsigned.uint128_new(lo, hi)
}

// sub_128 subtracts b from a, both 128-bit unsigned integers.
//
// PRECONDITION: a >= b. The caller must ensure this; behavior is
// undefined otherwise (wrap-around in unsigned arithmetic).
@[inline]
fn sub_128(a unsigned.Uint128, b unsigned.Uint128) unsigned.Uint128 {
	// Use the C implementation of 128-bit subtraction.
	$if use_128hw ? {
		mut hi := u64(0)
		lo := C.sub_128_hw(a.lo, a.hi, b.lo, b.hi, &hi)
		return unsigned.uint128_new(lo, hi)
	}
	// Fallback to manual subtraction with borrow.
	lo := a.lo - b.lo
	borrow := u64(a.lo < b.lo) // same idiom add_u64_to_128 already uses
	hi := a.hi - b.hi - borrow
	return unsigned.uint128_new(lo, hi)
}

// lsh_128 left-shifts a 128-bit value by 1 bit.
//
// Computes: result = a << 1
@[inline]
fn lsh_128(a unsigned.Uint128) unsigned.Uint128 {
	return unsigned.uint128_new(a.lo << 1, (a.hi << 1) | (a.lo >> 63))
}

// add_u64_to_128 adds a u64 carry to a 128-bit value.
//
// Returns (lo, hi) where the result is hi·2⁶⁴ + lo.
@[inline]
fn add_u64_to_128(t unsigned.Uint128, c u64) (u64, u64) {
	lo := t.lo + c
	// Equivalent to: t.hi + if lo < c { u64(1) } else { u64(0) }
	hi := t.hi + u64(lo < c) // branchless, compiles to ADC/CMOV
	return lo, hi
}

// Helpers for wiping sensitive data securely
//

// crypto_wipe_8xu64 zeroes a 8-element u64 array.
@[direct_array_access; inline]
fn crypto_wipe_8xu64(mut values [8]u64) {
	secure_zero_ptr(voidptr(&values[0]), 8 * 8)
}

// secure_zero_ptr zeroises ptr data of length len using volatile byte pointer access.
@[inline]
fn secure_zero_ptr(ptr voidptr, len int) {
	if isnil(ptr) || len == 0 {
		return
	}
	unsafe {
		// Cast the void pointer to a volatile byte pointer.
		// The `volatile` qualifier informs the backend compiler that writes
		// to this memory location produce observable side-effects and must NOT
		// be elided or optimized away (preventing Dead Store Elimination).
		mut volatile vp := &u8(ptr)

		for i in 0 .. len {
			vp[i] = 0
		}
	}
}

// secure_zero_buf zeroises buf data securely.
@[direct_array_access; inline]
fn secure_zero_buf(mut buf []u8) {
	secure_zero_ptr(buf.data, buf.len)
}
