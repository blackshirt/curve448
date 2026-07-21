// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// This module implements building block for elliptic-curve diffie-helman
// key exchange (ECDH) mechanism through curve448 curve, offering 224 bits of security.
module curve448

import internal.fp448

// X448 diffie-helman key-exchange (ECDH) algorithm.
//
// This module implements the X448 primitive, as defined by [RFC 7748].
// The primitive takes an input of two 56-byte values, the first was the scalar.
// The scalar is internally "clamped" (some bits are set to specific values)
// before used. The second being the representation of a point on Curve448
// and the output point is encoded into little-endian of 56 bytes.
// The `x448()` function implements the process described in RFC 7748 (section 5).
// The `x448()` function does NOT filter out any value from its input;
// any input sequence of 56 bytes is accepted, even if it encodes a
// low-order curve point.
//
// See [RFC 7748]: https://datatracker.ietf.org/doc/html/rfc7748
// Notes: scalar is cloned internally to avoid side-effects (mutating key in memory)
pub fn x448(scalar []u8, point []u8) ![]u8 {
	if scalar.len != 56 {
		return error('x448: bad scalar length')
	}
	// TODO: point validation
	if point.len != 56 {
		return error('x448: bad point length')
	}

	// Clamping the key
	//
	// As per RFC 7748 requirements, the clamping process ensures that the integer
	// used for the multiplication is a multiple of 4, at least 2⁴⁴⁷, and lower than
	// 2⁴⁴⁸; the two least significant bits of the first byte, and the
	// most significant bit of the last byte, are ignored.
	mut s := scalar.clone()
	s[0] &= 252
	s[55] |= 128

	mut u := fp448.new_field()
	u.set_bytes(point)

	// setup vars
	mut x1 := u
	mut x2 := fp448.fe_one
	mut z2 := fp448.new_field()
	mut x3 := u
	mut z3 := fp448.fe_one

	mut swap := 0

	// temporary vars
	mut a, mut aa := fp448.new_field(), fp448.new_field()
	mut b, mut bb := fp448.new_field(), fp448.new_field()
	mut e, mut c, mut d := fp448.new_field(), fp448.new_field(), fp448.new_field()
	mut da, mut cb := fp448.new_field(), fp448.new_field()

	// Step 4: The Montgomery ladder loop.
	// We iterate bit-by-bit through the 448-bit scalar from the MSB (bit 447) to the LSB (bit 0).
	for t := 447; t >= 0; t-- {
		// Extract the t-th bit of the scalar s.
		kt := int(s[t / 8] >> (t % 8)) & 1
		
		// Determine if we need to swap the coordinate pairs based on the scalar bit.
		swap ^= kt
		
		// Perform a constant-time swap of the projective coordinate pairs (x2, x3) and (z2, z3)
		// if swap is 1. This implements the CSWAP step of the ladder.
		fp448.fe_cswap(mut x2, mut x3, swap)
		fp448.fe_cswap(mut z2, mut z3, swap)
		
		// Update swap flag for the next iteration.
		swap = kt

		// Step 4.1: Compute intermediate values for differential addition and doubling.
		fp448.fe_add(mut a, x2, z2)        // A = x_2 + z_2
		fp448.fe_sqr(mut aa, a)            // AA = A^2
		fp448.fe_sub(mut b, x2, z2)        // B = x_2 - z_2
		fp448.fe_sqr(mut bb, b)            // BB = B^2
		fp448.fe_sub(mut e, aa, bb)        // E = AA - BB (this represents the difference)
		
		fp448.fe_add(mut c, x3, z3)        // C = x_3 + z_3
		fp448.fe_sub(mut d, x3, z3)        // D = x_3 - z_3
		fp448.fe_mult(mut da, d, a)        // DA = D * A
		fp448.fe_mult(mut cb, c, b)        // CB = C * B

		// Step 4.2: Perform Point Addition to update (x3, z3)
		fp448.fe_add(mut x3, da, cb)       // x_3 = (DA + CB)^2
		fp448.fe_sqr(mut x3, x3)

		fp448.fe_sub(mut z3, da, cb)       // z_3 = x_1 * (DA - CB)^2
		fp448.fe_sqr(mut z3, z3)
		fp448.fe_mult(mut z3, z3, x1)

		// Step 4.3: Perform Point Doubling to update (x2, z2)
		fp448.fe_mult(mut x2, aa, bb)      // x_2 = AA * BB

		// z_2 = E * (AA + a24 * E) where a24 = 39081 for Curve448
		fp448.fe_mult_32(mut z2, e, 39081) 
		fp448.fe_add(mut z2, z2, aa)
		fp448.fe_mult(mut z2, z2, e)
	}
	// (x₂, x₃) = cswap(swap, x₂, x₃)
	// (z₂, z₃) = cswap(swap, z₂, z₃)
	fp448.fe_cswap(mut x2, mut x3, swap)
	fp448.fe_cswap(mut z2, mut z3, swap)

	// Return x₂ * z₂ᵖ ⁻ ²
	mut ret := fp448.new_field()
	fp448.fe_inverse(mut ret, z2)
	fp448.fe_mult(mut ret, x2, ret)
	if fp448.fe_cmp(ret, fp448.fe_zero) == 1 {
		return error('x448 bad input point: low order point')
	}
	return ret.bytes()
}
