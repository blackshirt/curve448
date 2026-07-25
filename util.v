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

// sub_128 subtracts b from a.
//
// PRECONDITION: a >= b. The caller must ensure this; behavior is undefined
// otherwise (wrap-around in unsigned arithmetic).
@[inline]
fn sub_128(a unsigned.Uint128, b unsigned.Uint128) unsigned.Uint128 {
	lo, borrow := bits.sub_64(a.lo, b.lo, 0)
	hi, _ := bits.sub_64(a.hi, b.hi, borrow)
	return unsigned.uint128_new(lo, hi)
}

// Helpers for wiping sensitive data securely
//

// clear_7xuint128 reset out the data into 0.
@[direct_array_access; inline]
fn clear_7xuint128(mut data [7]unsigned.Uint128) {
	unsafe {
		vmemset(voidptr(&data[0]), 0, 7 * sizeof(unsigned.Uint128))
	}
}

// crypto_wipe_4xu64 zeroes a 4-element u64 array.
@[direct_array_access; inline]
fn crypto_wipe_4xu64(mut values [4]u64) {
	secure_zero_ptr(voidptr(&values[0]), isize(4 * sizeof(u64)))
}

// crypto_wipe_8xu64 zeroes a 8-element u64 array.
@[direct_array_access; inline]
fn crypto_wipe_8xu64(mut values [8]u64) {
	secure_zero_ptr(voidptr(&values[0]), isize(8 * sizeof(u64)))
}

// crypto_wipe_7xuint128 securely zeroises a 7-element Uint128 array.
//
// Uint128 field accumulators can contain secret-dependent products during X448.
// Route through secure_zero_ptr so the wipe uses vmemset plus the same volatile
// read barrier as byte-slice scalar clearing.
@[direct_array_access; inline]
fn crypto_wipe_7xuint128(mut values [7]unsigned.Uint128) {
	secure_zero_ptr(voidptr(&values[0]), isize(7 * sizeof(unsigned.Uint128)))
}

// crypto_wipe_15xuint128 zeroes a 15-element Uint128 array.
@[direct_array_access; inline]
fn crypto_wipe_15xuint128(mut values [15]unsigned.Uint128) {
	secure_zero_ptr(voidptr(&values[0]), isize(15 * sizeof(unsigned.Uint128)))
}

// secure_zero_ptr zeroises ptr data with length len.
//
// Its internally used vmemset for writing (zeroing) data,
// and use volatile read dependency to tell the compiler to commit
// all prior memory stores before executing the read.
// NOTE: This code was working, but not guarantees. Its depends on
// the backend generated output.
// TODO: correct way to do this in v.
@[inline]
fn secure_zero_ptr(ptr voidptr, len isize) {
	if isnil(ptr) || len == 0 {
		return
	}
	unsafe {
		// 1. Fast zeroing via built-in vmemset
		vmemset(ptr, 0, len)

		// 2. Pure V Volatile Read Dependency
		//
		// Reading a byte via a volatile pointer forces the compiler to commit
		// all prior memory stores before executing the read.
		mut volatile vptr := &u8(ptr)
		_ = vptr[0]
	}
}

// secure_zero_buf zeroises buf data securely.
@[inline]
fn secure_zero_buf(mut buf []u8) {
	if buf.len == 0 {
		return
	}

	unsafe {
		// 1. Fast zeroing
		vmemset(buf.data, 0, buf.len)

		// 2. Pure V Compiler Barrier
		//
		// Force a volatile read on the first byte.
		// The compiler cannot elide the `vmemset` store above because
		// it must satisfy this subsequent volatile read access.
		mut volatile vp := &u8(buf.data)
		_ = vp[0]
	}
}
