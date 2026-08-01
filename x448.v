// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// This module implements the core low-level building blocks for Elliptic-Curve Diffie-Hellman
// key exchange (ECDH) using Curve448 (Curve448-Goldilocks), offering ~224 bits of security.
module curve448

// scalar_size is the byte length of scalars and point coordinates in X448 (56 bytes / 448 bits).
const scalar_size = 56

// base_point is the standard generator point u-coordinate for Curve448 in 56-byte little-endian format (u = 5).
const base_point = [u8(5), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0]

// X448 Diffie-Hellman key-exchange (ECDH) algorithm.
//
// Implements the raw (low level) `x448` function as defined in [RFC 7748 (Section 5)].
// The function takes a 56-byte secret scalar and a 56-byte u-coordinate point representation.
// The scalar is internally cloned and clamped (bits 0, 1 cleared; bit 447 set) before
// scalar multiplication to prevent small-subgroup and timing attacks.
//
// Non-canonical input point bytes (u >= p) are automatically reduced modulo p per RFC 7748.
//
// See [RFC 7748]: https://datatracker.ietf.org/doc/html/rfc7748
// Note: The scalar buffer is cloned internally and zeroed upon completion to prevent key exposure.
// For (recommended) higher level API, use type-based (PrivateKey and PublicKey) instead.
@[direct_array_access]
pub fn x448(scalar []u8, point []u8) ![]u8 {
	if scalar.len != scalar_size {
		return error('x448: bad scalar length')
	}

	// Clamping the key
	//
	// As per RFC 7748 requirements, the clamping process ensures that the integer
	// used for the multiplication is a multiple of 4, at least 2⁴⁴⁷, and lower than
	// 2⁴⁴⁸; the two least significant bits of the first byte, and the
	// most significant bit of the last byte, are ignored.
	mut s := scalar.clone()
	defer {
		// zeroise the cloned scalar after use
		secure_zero_buf(mut s)
	}
	s[0] &= 252
	s[55] |= 128

	mut u := Field{}
	u.set_bytes_loosely(point)!
	defer {
		fe_clear(mut u)
	}

	// setup vars
	mut x1 := u
	mut x2 := fe_one
	mut z2 := Field{}
	mut x3 := u
	mut z3 := fe_one
	defer {
		fe_clear(mut x1)
		fe_clear(mut x2)
		fe_clear(mut z2)
		fe_clear(mut x3)
		fe_clear(mut z3)
	}
	mut swap := 0

	// temporary vars
	mut a, mut aa := Field{}, Field{}
	mut b, mut bb := Field{}, Field{}
	mut e, mut c, mut d := Field{}, Field{}, Field{}
	mut da, mut cb := Field{}, Field{}
	defer {
		fe_clear(mut a)
		fe_clear(mut aa)
		fe_clear(mut b)
		fe_clear(mut bb)
		fe_clear(mut e)
		fe_clear(mut c)
		fe_clear(mut d)
		fe_clear(mut da)
		fe_clear(mut cb)
	}
	// Step 4: The Montgomery ladder loop.
	// We iterate bit-by-bit through the 448-bit scalar from the MSB (bit 447) to the LSB (bit 0).
	// This loop has a fixed trip count and fixed scalar-byte indexes for every
	// iteration. The scalar bit only controls the mask passed into fe_cswap; it
	// must not control branches or memory addresses.
	for t := 447; t >= 0; t-- {
		// Extract the t-th bit of the scalar s. The index is derived only from the
		// public loop counter, not from secret scalar data.
		kt := int(s[t / 8] >> (t % 8)) & 1

		// Determine whether the coordinate pairs need to be swapped. The value is
		// consumed only by fe_cswap, which implements the swap with a word mask.
		swap ^= kt

		// Perform a constant-time swap of the projective coordinate pairs (x2, x3) and (z2, z3)
		// if swap is 1. This implements the CSWAP step of the ladder.
		fe_cswap(mut x2, mut x3, swap)
		fe_cswap(mut z2, mut z3, swap)

		// Update swap flag for the next iteration.
		swap = kt

		// Step 4.1: Compute intermediate values for differential addition and doubling.
		fe_add(mut a, x2, z2) // A = x_2 + z_2
		fe_sqr(mut aa, a) // AA = A^2
		fe_sub(mut b, x2, z2) // B = x_2 - z_2
		fe_sqr(mut bb, b) // BB = B^2
		fe_sub(mut e, aa, bb) // E = AA - BB (this represents the difference)

		fe_add(mut c, x3, z3) // C = x_3 + z_3
		fe_sub(mut d, x3, z3) // D = x_3 - z_3
		fe_mult(mut da, d, a) // DA = D * A
		fe_mult(mut cb, c, b) // CB = C * B

		// Step 4.2: Perform Point Addition to update (x3, z3)
		fe_add(mut x3, da, cb) // x_3 = (DA + CB)^2
		fe_sqr(mut x3, x3)

		fe_sub(mut z3, da, cb) // z_3 = x_1 * (DA - CB)^2
		fe_sqr(mut z3, z3)
		fe_mult(mut z3, z3, x1)

		// Step 4.3: Perform Point Doubling to update (x2, z2)
		fe_mult(mut x2, aa, bb) // x_2 = AA * BB

		// z_2 = E * (AA + a24 * E) where a24 = 39081 for Curve448
		fe_mult_32(mut z2, e, 39081)
		fe_add(mut z2, z2, aa)
		fe_mult(mut z2, z2, e)
	}
	// (x₂, x₃) = cswap(swap, x₂, x₃)
	// (z₂, z₃) = cswap(swap, z₂, z₃)
	fe_cswap(mut x2, mut x3, swap)
	fe_cswap(mut z2, mut z3, swap)

	// Return x₂ * z₂ᵖ ⁻ ²
	mut ret := Field{}
	defer { fe_clear(mut ret) }
	fe_inverse(mut ret, z2)
	fe_mult(mut ret, x2, ret)

	ret_is_zero := fe_cmp(ret, fe_zero)
	// Keep the low-order/all-zero API branch after wiping scalar and field
	// temporaries. The ladder itself remains branch-free with respect to scalar
	// bits; this branch only decides whether to return the already-computed output.
	if ret_is_zero == 1 {
		return error('x448 bad input point: low order point')
	}
	// wiring ret into out
	mut out := []u8{len: 56}
	ret.bytes(mut out)!
	return out
}

// Helpers for validating point.
//
// validate_point validates that `point` is a valid 56-byte canonical, non-low-order point for X448.
// Returns an error if the point length is invalid (!= 56), if it encodes a non-canonical field element (u >= p),
// or if it encodes a known low-order curve point (u = 0, 1, or p - 1).
// Note: For standard RFC 7748 ECDH where non-canonical inputs are reduced modulo p, `x448()` can be called directly.
@[direct_array_access]
pub fn validate_point(point []u8) ! {
	if point.len != scalar_size {
		return error('x448: bad point length')
	}
	mut u := Field{}
	u.set_bytes(point) or { return error('x448: non-canonical point') }
	if fe_cmp(u, fe_zero) == 1 || fe_cmp(u, fe_one) == 1 || fe_cmp(u, fe_minus_one) == 1 {
		return error('x448: low order point')
	}
}
