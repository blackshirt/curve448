// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// This module implements the core low-level building blocks for Elliptic-Curve Diffie-Hellman
// key exchange (ECDH) using Curve448 (Curve448-Goldilocks), offering ~224 bits of security.
//
// Curve448 is defined over the Galois field GF(p) where p = 2⁴⁴⁸ - 2²²⁴ - 1.
// In Montgomery form, the curve equation is:
//     v² = u³ + A·u² + u  (mod p)   where A = 156324.
//
// The scalar multiplication routine uses the Montgomery ladder algorithm operating on
// projective coordinates (X : Z) to achieve timing side-channel resistance and avoid
// costly modular division during intermediate ladder steps.
module curve448

// scalar_size is the byte length of scalars and point coordinates in X448 (56 bytes / 448 bits).
pub const scalar_size = 56

// base_point is the standard generator point u-coordinate for Curve448 in 56-byte little-endian format (u = 5).
pub const base_point = [u8(5), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0]

// x448 performs X448 Diffie-Hellman scalar multiplication as defined in RFC 7748 (Section 5).
//
// Parameters:
//   scalar - 56-byte secret scalar buffer (cloned and clamped internally).
//   point  - 56-byte little-endian u-coordinate representation of the input curve point.
//
// Returns:
//   56-byte byte slice containing the little-endian u-coordinate of the resulting point `[scalar] point`.
//
// Errors:
//   - Returns error if `scalar.len != 56`.
//   - Returns error if `scalar` multiplication results in a low-order point (all-zero output u-coordinate).
//
// Security guarantees:
//   1. Scalar clamping: Bits 0 and 1 of `scalar[0]` are cleared (forcing scalar to be a multiple of 4),
//      and bit 7 of `scalar[55]` is set (forcing bit 447 to 1), preventing small-subgroup attacks.
//   2. Zeroization: The cloned scalar buffer `s` and all field temporaries are explicitly zeroed
//      upon completion via `defer` handlers.
//   3. Non-canonical point handling: Input bytes encoding `u >= p` are loosely decoded modulo `p` per RFC 7748.
//   4. Constant-time execution: The Montgomery ladder loop executes a fixed 448 iterations without
//      secret-dependent branches or memory access patterns.
//
// See [RFC 7748 §5]: https://datatracker.ietf.org/doc/html/rfc7748#section-5
// Note: For a type-safe higher-level API with distinct key types, see `PrivateKey` and `PublicKey` in `keys.v`.
@[direct_array_access]
pub fn x448(scalar []u8, point []u8) ![]u8 {
	if scalar.len != scalar_size {
		return error('x448: bad scalar length')
	}

	// Clamping the secret key per RFC 7748 §5:
	//   s[0]  &= 252 (bits 0, 1 cleared: clears cofactor 4)
	//   s[55] |= 128 (bit 447 set: enforces fixed bit-length)
	mut s := scalar.clone()
	defer {
		// Zeroise the cloned scalar buffer immediately after ladder completion.
		secure_zero_buf(mut s)
	}
	s[0] &= 252
	s[55] |= 128

	// Parse input point u-coordinate. Loose parsing handles non-canonical inputs (u >= p) modulo p.
	mut u := Field{}
	u.set_bytes_loosely(point)!
	defer {
		fe_clear(mut u)
	}

	// Initialize projective coordinates (X2:Z2) for R0 and (X3:Z3) for R1:
	//   R0 = (1 : 0)  [point at infinity]
	//   R1 = (u : 1)  [the base point input u]
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

	// Temporary field accumulators used inside the ladder loop steps.
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
	// We iterate bit-by-bit through the 448-bit clamped scalar from MSB (bit 447) down to LSB (bit 0).
	// Fixed trip count (448 iterations) and deterministic memory access ensure constant-time execution.
	for t := 447; t >= 0; t-- {
		// Extract the t-th bit of the clamped scalar s.
		// The bit index is computed strictly from public loop index t.
		kt := int(s[t / 8] >> (t % 8)) & 1

		// Determine whether the coordinate pairs need to be swapped for this iteration.
		swap ^= kt

		// Constant-time conditional swap of coordinate pairs (x2, x3) and (z2, z3).
		// Swaps operands if swap == 1 without secret-dependent branching.
		fe_cswap(mut x2, mut x3, swap)
		fe_cswap(mut z2, mut z3, swap)

		// Record the current scalar bit for the next iteration's CSWAP step.
		swap = kt

		// Step 4.1: Compute intermediate values for differential point addition and doubling.
		fe_add(mut a, x2, z2) // A  = X₂ + Z₂
		fe_sqr(mut aa, a) // AA = A² = (X₂ + Z₂)²
		fe_sub(mut b, x2, z2) // B  = X₂ - Z₂
		fe_sqr(mut bb, b) // BB = B² = (X₂ - Z₂)²
		fe_sub(mut e, aa, bb) // E  = AA - BB = 4 · X₂ · Z₂

		fe_add(mut c, x3, z3) // C  = X₃ + Z₃
		fe_sub(mut d, x3, z3) // D  = X₃ - Z₃
		fe_mult(mut da, d, a) // DA = D · A = (X₃ - Z₃)(X₂ + Z₂)
		fe_mult(mut cb, c, b) // CB = C · B = (X₃ + Z₃)(X₂ - Z₂)

		// Step 4.2: Differential Point Addition: update (X₃, Z₃)
		//   X₃' = (DA + CB)²
		//   Z₃' = X₁ · (DA - CB)²
		fe_add(mut x3, da, cb)
		fe_sqr(mut x3, x3)

		fe_sub(mut z3, da, cb)
		fe_sqr(mut z3, z3)
		fe_mult(mut z3, z3, x1)

		// Step 4.3: Point Doubling: update (X₂, Z₂)
		//   X₂' = AA · BB
		//   Z₂' = E · (AA + a24 · E)  where a24 = (A + 2) / 4 = (156324 + 2) / 4 = 39081
		fe_mult(mut x2, aa, bb)

		fe_mult_32(mut z2, e, 39081)
		fe_add(mut z2, z2, aa)
		fe_mult(mut z2, z2, e)
	}

	// Final conditional swap to undo any remaining unswapped state.
	fe_cswap(mut x2, mut x3, swap)
	fe_cswap(mut z2, mut z3, swap)

	// Convert projective coordinate (X₂ : Z₂) back to affine u-coordinate: u = X₂ · Z₂⁻¹ (mod p).
	mut ret := Field{}
	defer {
		fe_clear(mut ret)
	}
	fe_inverse(mut ret, z2)
	fe_mult(mut ret, x2, ret)

	// Reduce output element to unique canonical representation in [0, p-1].
	fe_reduce(mut ret)
	ret_is_zero := fe_cmp_canonical(ret, fe_zero)

	// Reject all-zero output (indicates low-order input point / small-subgroup attack).
	if ret_is_zero == 1 {
		return error('x448 bad input point: low order point')
	}

	// Serialize canonical field element to 56-byte little-endian output slice.
	mut out := []u8{len: 56}
	ret.bytes(mut out)!
	return out
}

// validate_point validates that `point` is a valid 56-byte canonical, non-low-order X448 public point.
//
// Parameters:
//   point - 56-byte little-endian point representation.
//
// Errors:
//   - Returns error if `point.len != 56`.
//   - Returns error if `point` encodes a non-canonical field element (u >= p).
//   - Returns error if `point` encodes a known low-order curve point (u = 0, 1, or p - 1).
//
// Note: For standard RFC 7748 ECDH key exchange, `x448()` automatically handles loose parsing
// and non-canonical input reduction mod p. `validate_point` is intended for protocols that
// demand strict RFC 7748 input validation prior to processing.
@[direct_array_access]
pub fn validate_point(point []u8) ! {
	if point.len != scalar_size {
		return error('x448: bad point length')
	}
	mut u := Field{}
	u.set_bytes(point) or { return error('x448: non-canonical point') }
	// set_bytes guarantees u is canonical (rejects non-canonical input u >= p above).
	// fe_zero, fe_one, fe_minus_one are module constants in canonical form.
	// Combine comparison flags branchlessly with bitwise OR.
	is_low_order := fe_cmp_canonical(u, fe_zero) | fe_cmp_canonical(u, fe_one) | fe_cmp_canonical(u,
		fe_minus_one)
	if is_low_order == 1 {
		return error('x448: low order point')
	}
}
