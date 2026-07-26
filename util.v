// Copyright © 2026 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Some helpers used accross the module
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

// add_128 adds two 128-bit unsigned integers.
@[inline]
fn add_128(a unsigned.Uint128, b unsigned.Uint128) unsigned.Uint128 {
	return a.add(b)
}

// lsh_128 left-shifts a 128-bit value by 1 bit.
//
// Computes: result = a << 1
@[inline]
fn lsh_128(a unsigned.Uint128) unsigned.Uint128 {
	return unsigned.uint128_new(a.lo << 1, (a.hi << 1) | (a.lo >> 63))
}

// mult_64 computes the full 128-bit product of two 64-bit values.
//
// Returns a Uint128 where: value = a · b
@[inline]
fn mult_64(a u64, b u64) unsigned.Uint128 {
	hi, lo := bits.mul_64(a, b)
	return unsigned.uint128_new(lo, hi)
}

// mult_56 multiplies a 56-bit limb by a 32-bit scalar.
//
// Returns (lo, hi) such that: lo + hi · 2⁵⁶ = a · b
// The low 56 bits are masked; the high bits are shifted appropriately.
@[inline]
fn mult_56(a u64, b u32) (u64, u64) {
	hh, ll := bits.mul_64(a, u64(b))
	lo := ll & mask_56bits
	hi := (hh << 8) | (ll >> limb_bits_size)
	return lo, hi
}

// add_u64_to_128 adds a u64 carry to a 128-bit value.
//
// Returns (lo, hi) where the result is hi·2⁶⁴ + lo.
@[inline]
fn add_u64_to_128(t unsigned.Uint128, c u64) (u64, u64) {
	lo := t.lo + c
	// Thisa basically same with t.hi + if lo < c { u64(1) } else { u64(0) }
	hi := t.hi + u64(lo < c) // branchless, compiles to ADC/CMOV
	return lo, hi
}

// sub_128 subtracts b from a, using a manual branch for the borrow
// (same style as add_u64_to_128) instead of bits.sub_64.
//
// PRECONDITION: a >= b. The caller must ensure this; behavior is
// undefined otherwise (wrap-around in unsigned arithmetic).
@[inline]
fn sub_128(a unsigned.Uint128, b unsigned.Uint128) unsigned.Uint128 {
	lo := a.lo - b.lo
	// This is intended to use branch for perf reason.
	// For constant time, use bits trick instead.
	// borrow := if a.lo < b.lo { u64(1) } else { u64(0) }
	borrow := u64(a.lo < b.lo) // compiles to SETB or CMOV, zero cycles on modern uarch
	hi := a.hi - b.hi - borrow
	return unsigned.uint128_new(lo, hi)
}

// Helpers for wiping sensitive data securely
//

// clear_7xuint128 reset out the data into 0.
@[direct_array_access; inline]
fn clear_7xuint128(mut data [7]unsigned.Uint128) {
	unsafe {
		vmemset(voidptr(&data[0]), 0, 7 * 2 * 8)
	}
}

// crypto_wipe_4xu64 zeroes a 4-element u64 array.
@[direct_array_access; inline]
fn crypto_wipe_4xu64(mut values [4]u64) {
	secure_zero_ptr(voidptr(&values[0]), 4 * 8)
}

// crypto_wipe_8xu64 zeroes a 8-element u64 array.
@[direct_array_access; inline]
fn crypto_wipe_8xu64(mut values [8]u64) {
	secure_zero_ptr(voidptr(&values[0]), 8 * 8)
}

// crypto_wipe_7xuint128 securely zeroises a 7-element Uint128 array.
//
// Uint128 field accumulators can contain secret-dependent products during X448.
// Route through secure_zero_ptr so the wipe uses vmemset plus the same volatile
// read barrier as byte-slice scalar clearing.
@[direct_array_access; inline]
fn crypto_wipe_7xuint128(mut values [7]unsigned.Uint128) {
	secure_zero_ptr(voidptr(&values[0]), 7 * 16)
}

// crypto_wipe_15xuint128 zeroes a 15-element Uint128 array.
@[direct_array_access; inline]
fn crypto_wipe_15xuint128(mut values [15]unsigned.Uint128) {
	secure_zero_ptr(voidptr(&values[0]), 15 * 16)
}

// secure_zero_ptr zeroises ptr data with length len.
//
// NOTE: This code was working, but not guarantees.
// Its depends on the backend generated output.
// TODO: correct way to do this in v.
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
