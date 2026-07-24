// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// This file contains low-level primitive field arithmetic for Curve448,
// operating on elements of the Galois field GF(p) where:
//     p = 2⁴⁴⁸ - 2²²⁴ - 1
//
// The field uses an unsaturated (redundant) limb representation: 8 limbs
// of 56 bits each, stored in little-endian order. This representation
// allows lazy carry handling and defers full reduction until needed.
//
// SECURITY NOTE: All comparison, selection, and swap operations are
// implemented to run in constant-time to mitigate timing side-channels.
// However, full constant-time guarantees also depend on the compiler not
// optimizing away the branchless patterns used here.
module curve448

import math.bits
import math.unsigned

// Module Constants

// limbsize is the width of each field limb in bits.
// Eight limbs × 56 bits = 448 bits total.
const limbsize = 56

// mask_56bits masks the lower 56 bits of a u64 value.
// Used to clamp each limb to its valid bit-width.
const mask_56bits = u64(0x00ff_ffff_ffff_ffff)

// fe_zero is the additive identity of the field.
const fe_zero = Field{
	el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
}

// fe_one is the multiplicative identity of the field.
const fe_one = Field{
	el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
}

// fe_prime is the prime modulus of the field:
//     p = 2⁴⁴⁸ - 2²²⁴ - 1
//
// In 56-bit limb form (little-endian):
//   limbs 0-3: 0x00FF_FFFF_FFFF_FFFF
//   limb  4:   0x00FF_FFFF_FFFF_FFFE  (one less than max)
//   limbs 5-7: 0x00FF_FFFF_FFFF_FFFF
const fe_prime = Field{
	el: [
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFE),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
	]!
}

// fe_4p_limbs holds 4 × p in limb form, pre-computed to prevent
// underflow during subtraction (fe_sub, fe_negate).
//
// Rationale: Using 2×p as the subtrahend base leaves only a 1–3 unit
// margin against the documented < 2⁵⁷ per-limb bound, which is too
// thin. 4×p provides a comfortable safety margin.
const fe_4p_limbs = [
	u64(0x03FF_FFFF_FFFF_FFFC),
	u64(0x03FF_FFFF_FFFF_FFFC),
	u64(0x03FF_FFFF_FFFF_FFFC),
	u64(0x03FF_FFFF_FFFF_FFFC),
	u64(0x03FF_FFFF_FFFF_FFF8),
	u64(0x03FF_FFFF_FFFF_FFFC),
	u64(0x03FF_FFFF_FFFF_FFFC),
	u64(0x03FF_FFFF_FFFF_FFFC),
]!

// Field represents an element of GF(p) where p = 2⁴⁴⁸ - 2²²⁴ - 1.
//
// The 448-bit integer is stored in unsaturated (redundant) 56-bit limbs
// in little-endian order:
//
//     value = el[0]·2⁰    + el[1]·2⁵⁶  + el[2]·2¹¹² + el[3]·2¹⁶⁸
//           + el[4]·2²²⁴ + el[5]·2²⁸⁰ + el[6]·2³³⁶ + el[7]·2³⁹²
//
// Between operations, each limb is expected to fit in 56 bits
// (i.e., el[i] < 2⁵⁶), though temporary values may exceed this
// before reduction is applied.
//
// The struct is marked @[noinit] to prevent accidental construction
// without proper initialization or reduction.
@[noinit]
struct Field {
mut:
	// el stores the 8 limbs of the 448-bit field element.
	// Each limb is a 56-bit value stored in a u64.
	el [8]u64
}

// Basic Field Operations
//

// fe_clear overwrites a field element with zeros in-place.
//
// This is a best-effort source-level wipe of temporary values that may
// contain secret-dependent data. For strict secure-zeroization guarantees,
// audit the generated C/assembly or replace this with a compiler-resistant
// wipe primitive (e.g., explicit_bzero, memset_s, or volatile writes).
@[direct_array_access; inline]
fn fe_clear(mut z Field) {
	for i := 0; i < 8; i++ {
		z.el[i] = 0
	}
}

// fe_clone copies all limbs from x into z.
//
// Equivalent to: z = x
@[direct_array_access; inline]
fn fe_clone(mut z Field, x Field) {
	for i := 0; i < 8; i++ {
		z.el[i] = x.el[i]
	}
}

// fe_add computes modular field addition: z = a + b (mod p).
//
// Algorithm:
//   1. Perform limb-wise addition of a and b.
//   2. Propagate carries and reduce via fe_weak_reduce.
//
// The addition may temporarily overflow 56 bits per limb; the subsequent
// weak reduction normalizes the result.
@[direct_array_access; inline]
fn fe_add(mut z Field, a Field, b Field) {
	// Step 1: Limb-wise addition (may overflow 56 bits).
	z.el[0] = a.el[0] + b.el[0]
	z.el[1] = a.el[1] + b.el[1]
	z.el[2] = a.el[2] + b.el[2]
	z.el[3] = a.el[3] + b.el[3]
	z.el[4] = a.el[4] + b.el[4]
	z.el[5] = a.el[5] + b.el[5]
	z.el[6] = a.el[6] + b.el[6]
	z.el[7] = a.el[7] + b.el[7]

	// Step 2: Propagate carries and apply Solinas reduction.
	fe_weak_reduce(mut z)
}

// fe_sub computes modular field subtraction: z = a - b (mod p).
//
// Algorithm:
//   1. Add 4×p to a to guarantee no underflow during subtraction.
//   2. Subtract b limb-wise.
//   3. Extract carries and propagate them.
//   4. Apply final weak reduction.
//
// The 4×p offset ensures all intermediate limb values remain non-negative.
@[direct_array_access; inline]
fn fe_sub(mut z Field, a Field, b Field) {
	// Step 1: Compute (a + 4p) - b per limb, extracting carries.
	z0 := (a.el[0] + fe_4p_limbs[0]) - b.el[0]
	c0 := z0 >> limbsize
	z.el[0] = z0 & mask_56bits

	z1 := (a.el[1] + fe_4p_limbs[1]) - b.el[1]
	c1 := z1 >> limbsize
	z.el[1] = z1 & mask_56bits

	z2 := (a.el[2] + fe_4p_limbs[2]) - b.el[2]
	c2 := z2 >> limbsize
	z.el[2] = z2 & mask_56bits

	z3 := (a.el[3] + fe_4p_limbs[3]) - b.el[3]
	c3 := z3 >> limbsize
	z.el[3] = z3 & mask_56bits

	z4 := (a.el[4] + fe_4p_limbs[4]) - b.el[4]
	c4 := z4 >> limbsize
	z.el[4] = z4 & mask_56bits

	z5 := (a.el[5] + fe_4p_limbs[5]) - b.el[5]
	c5 := z5 >> limbsize
	z.el[5] = z5 & mask_56bits

	z6 := (a.el[6] + fe_4p_limbs[6]) - b.el[6]
	c6 := z6 >> limbsize
	z.el[6] = z6 & mask_56bits

	z7 := (a.el[7] + fe_4p_limbs[7]) - b.el[7]
	c7 := z7 >> limbsize
	z.el[7] = z7 & mask_56bits

	// Step 2: Propagate carries. The carry out of limb 7 is folded
	// back into limbs 0 and 4 per the Solinas identity 2⁴⁴⁸ = 2²²⁴ + 1.
	z.el[0] += c7
	z.el[4] += c7

	z.el[1] += c0
	z.el[2] += c1
	z.el[3] += c2
	z.el[4] += c3
	z.el[5] += c4
	z.el[6] += c5
	z.el[7] += c6

	// Step 3: Normalize any new overflows from carry propagation.
	fe_weak_reduce(mut z)
}

// fe_negate computes the additive inverse: z = -a (mod p).
//
// Algorithm:
//   1. Subtract each limb of a from 4×p (same base as fe_sub).
//   2. Propagate carries and reduce.
//
// Using 4×p instead of 2×p provides the same safety margin as fe_sub.
@[direct_array_access; inline]
fn fe_negate(mut z Field, a Field) {
	// Step 1: Compute 4p - a per limb.
	z0 := fe_4p_limbs[0] - a.el[0]
	c0 := z0 >> limbsize
	z.el[0] = z0 & mask_56bits

	z1 := fe_4p_limbs[1] - a.el[1]
	c1 := z1 >> limbsize
	z.el[1] = z1 & mask_56bits

	z2 := fe_4p_limbs[2] - a.el[2]
	c2 := z2 >> limbsize
	z.el[2] = z2 & mask_56bits

	z3 := fe_4p_limbs[3] - a.el[3]
	c3 := z3 >> limbsize
	z.el[3] = z3 & mask_56bits

	z4 := fe_4p_limbs[4] - a.el[4]
	c4 := z4 >> limbsize
	z.el[4] = z4 & mask_56bits

	z5 := fe_4p_limbs[5] - a.el[5]
	c5 := z5 >> limbsize
	z.el[5] = z5 & mask_56bits

	z6 := fe_4p_limbs[6] - a.el[6]
	c6 := z6 >> limbsize
	z.el[6] = z6 & mask_56bits

	z7 := fe_4p_limbs[7] - a.el[7]
	c7 := z7 >> limbsize
	z.el[7] = z7 & mask_56bits

	// Step 2: Propagate carries with Solinas fold-back.
	z.el[0] += c7
	z.el[4] += c7

	z.el[1] += c0
	z.el[2] += c1
	z.el[3] += c2
	z.el[4] += c3
	z.el[5] += c4
	z.el[6] += c5
	z.el[7] += c6

	// Step 3: Normalize.
	fe_weak_reduce(mut z)
}

// Comparison and Constant-Time Selection
//

// fe_equal returns true iff a == b (mod p).
//
// Both inputs are fully reduced to canonical form before comparison.
// This function is constant-time.
@[direct_array_access; inline]
fn fe_equal(a Field, b Field) bool {
	return fe_cmp(a, b) == 1
}

// fe_cmp compares two field elements modulo p in constant-time.
//
// Returns:
//   1  if a == b (mod p)
//   0  otherwise
//
// Algorithm:
//   1. Reduce both a and b to canonical form.
//   2. XOR corresponding limbs; any difference sets bits in accumulator c.
//   3. Return 1 if c == 0, else 0, computed branchlessly.
@[direct_array_access; inline]
fn fe_cmp(a Field, b Field) int {
	// Step 1: Reduce to canonical representation.
	mut x := a
	mut y := b
	fe_reduce(mut x)
	fe_reduce(mut y)

	// Step 2: Constant-time limb comparison via XOR accumulation.
	// Any differing bit in any limb will set a bit in c.
	mut c := u64(0)
	c |= x.el[0] ^ y.el[0]
	c |= x.el[1] ^ y.el[1]
	c |= x.el[2] ^ y.el[2]
	c |= x.el[3] ^ y.el[3]
	c |= x.el[4] ^ y.el[4]
	c |= x.el[5] ^ y.el[5]
	c |= x.el[6] ^ y.el[6]
	c |= x.el[7] ^ y.el[7]

	// Step 3: Branchless result: 1 if c == 0, else 0.
	// Trick: (c | -c) has MSB set iff c != 0.
	return int(1 - ((c | (0 - c)) >> 63))
}

// fe_cselect performs a constant-time conditional selection.
//
// Sets z to a if c == 1, or to b if c == 0.
// The condition c may be any nonzero value for "true".
//
// Uses a bitmask derived from c to blend limbs branchlessly.
@[direct_array_access; inline]
fn fe_cselect(mut z Field, a Field, b Field, c int) {
	m := mask_64bits(c)
	z.el[0] = (a.el[0] & m) | (b.el[0] & ~m)
	z.el[1] = (a.el[1] & m) | (b.el[1] & ~m)
	z.el[2] = (a.el[2] & m) | (b.el[2] & ~m)
	z.el[3] = (a.el[3] & m) | (b.el[3] & ~m)
	z.el[4] = (a.el[4] & m) | (b.el[4] & ~m)
	z.el[5] = (a.el[5] & m) | (b.el[5] & ~m)
	z.el[6] = (a.el[6] & m) | (b.el[6] & ~m)
	z.el[7] = (a.el[7] & m) | (b.el[7] & ~m)
}

// fe_cswap performs a constant-time conditional swap.
//
// Swaps a and b in-place if c == 1; leaves them unchanged if c == 0.
// Uses XOR-swap with a bitmask to avoid branches.
@[direct_array_access; inline]
fn fe_cswap(mut a Field, mut b Field, c int) {
	m := mask_64bits(c)

	// XOR-swap each limb branchlessly.
	d0 := m & (a.el[0] ^ b.el[0])
	a.el[0] ^= d0
	b.el[0] ^= d0

	d1 := m & (a.el[1] ^ b.el[1])
	a.el[1] ^= d1
	b.el[1] ^= d1

	d2 := m & (a.el[2] ^ b.el[2])
	a.el[2] ^= d2
	b.el[2] ^= d2

	d3 := m & (a.el[3] ^ b.el[3])
	a.el[3] ^= d3
	b.el[3] ^= d3

	d4 := m & (a.el[4] ^ b.el[4])
	a.el[4] ^= d4
	b.el[4] ^= d4

	d5 := m & (a.el[5] ^ b.el[5])
	a.el[5] ^= d5
	b.el[5] ^= d5

	d6 := m & (a.el[6] ^ b.el[6])
	a.el[6] ^= d6
	b.el[6] ^= d6

	d7 := m & (a.el[7] ^ b.el[7])
	a.el[7] ^= d7
	b.el[7] ^= d7
}

// Modular Inverse and Exponentiation
//
// fe_inverse computes the modular multiplicative inverse: z = x⁻¹ (mod p).
//
// Algorithm: Fermat's little theorem.
//   x⁻¹ ≡ x^(p-2)  (mod p)
//
// Since p = 2⁴⁴⁸ - 2²²⁴ - 1, we have:
//   p - 2 = 2⁴⁴⁸ - 2²²⁴ - 3
//
// This is computed as:
//   t = x^((p-3)/4) = x^(2⁴⁴⁶ - 2²²² - 1)   [via fe_power446]
//   t = t²                                        [2⁴⁴⁷ - 2²²³ - 2]
//   t = t²                                        [2⁴⁴⁸ - 2²²⁴ - 4]
//   z = t · x                                     [2⁴⁴⁸ - 2²²⁴ - 3]
@[direct_array_access; inline]
fn fe_inverse(mut z Field, x Field) {
	mut t := Field{}
	fe_power446(mut t, x)
	fe_sqr(mut t, t)
	fe_sqr(mut t, t) // t = x^(2⁴⁴⁸ - 2²²⁴ - 4)

	fe_mult(mut z, t, x) // z = x^(2⁴⁴⁸ - 2²²⁴ - 3) = x⁻¹
}

// fe_power446 computes v = z^((p-3)/4) (mod p), where:
//     (p-3)/4 = 2⁴⁴⁶ - 2²²² - 1
//
// This is the core exponentiation used by both fe_inverse and
// fe_sqrtratio. It uses an addition-chain approach with pre-computed
// powers to minimize the number of squarings.
//
// The exponent is built from the binary pattern:
//   2⁴⁴⁶ - 2²²² - 1 = (2²²² - 1) · 2²²⁴ + (2²²² - 1)
//
// Intermediate powers:
//   t3   = z^(2³   - 1)
//   t6   = z^(2⁶   - 1)
//   t9   = z^(2⁹   - 1)
//   t18  = z^(2¹⁸  - 1)
//   t37  = z^(2³⁷  - 1)
//   t111 = z^(2¹¹¹ - 1)
//   t222 = z^(2²²² - 1)
//   t223 = z^(2²²³ - 1)
//   v    = z^(2⁴⁴⁶ - 2²²² - 1)
@[direct_array_access; inline]
fn fe_power446(mut v Field, z Field) {
	mut t1 := Field{}
	mut t2 := Field{}
	mut t3 := Field{}

	// t3 = z^(2³ - 1) = z³
	fe_sqr(mut t1, z) // t1 = z²
	fe_sqr(mut t2, t1) // t2 = z⁴
	fe_mult(mut t3, z, t1) // t3 = z³
	fe_mult(mut t3, t3, t2) // t3 = z⁷ = z^(2³-1)

	// t6 = z^(2⁶ - 1)
	mut t6 := Field{}
	fe_sqr(mut t6, t3)
	fe_sqr(mut t6, t6)
	fe_sqr(mut t6, t6)
	fe_mult(mut t6, t6, t3) // t6 = z⁶³ = z^(2⁶-1)

	// t9 = z^(2⁹ - 1)
	mut t9 := Field{}
	fe_sqr(mut t9, t6)
	fe_sqr(mut t9, t9)
	fe_sqr(mut t9, t9)
	fe_mult(mut t9, t9, t3) // t9 = z⁵¹¹ = z^(2⁹-1)

	// t18 = z^(2¹⁸ - 1)
	mut t18 := Field{}
	fe_sqr(mut t18, t9)
	for i := 1; i < 9; i++ {
		fe_sqr(mut t18, t18)
	}
	fe_mult(mut t18, t18, t9) // t18 = z^(2¹⁸-1)

	// t37 = z^(2³⁷ - 1)
	mut t37 := Field{}
	fe_sqr(mut t37, t18)
	for i := 1; i < 18; i++ {
		fe_sqr(mut t37, t37)
	}
	fe_mult(mut t37, t37, t18)
	fe_sqr(mut t37, t37)
	fe_mult(mut t37, t37, z) // t37 = z^(2³⁷-1)

	// t111 = z^(2¹¹¹ - 1)
	mut t111 := Field{}
	fe_sqr(mut t111, t37)
	for i := 1; i < 37; i++ {
		fe_sqr(mut t111, t111)
	}
	fe_mult(mut t111, t111, t37)
	for i := 0; i < 37; i++ {
		fe_sqr(mut t111, t111)
	}
	fe_mult(mut t111, t111, t37) // t111 = z^(2¹¹¹-1)

	// t222 = z^(2²²² - 1)
	mut t222 := Field{}
	fe_sqr(mut t222, t111)
	for i := 1; i < 111; i++ {
		fe_sqr(mut t222, t222)
	}
	fe_mult(mut t222, t222, t111) // t222 = z^(2²²²-1)

	// t223 = z^(2²²³ - 1)
	mut t223 := Field{}
	fe_sqr(mut t223, t222)
	fe_mult(mut t223, t223, z) // t223 = z^(2²²³-1)

	// v = z^(2⁴⁴⁶ - 2²²² - 1)
	mut x := Field{}
	fe_sqr(mut x, t223)
	for i := 1; i < 223; i++ {
		fe_sqr(mut x, x)
	}
	fe_mult(mut v, x, t222) // v = z^(2⁴⁴⁶ - 2²²² - 1)
}

// fe_sqrtratio computes the square root of the ratio u/v (mod p).
//
// If u/v is a quadratic residue (square), returns (r, 1) where r²·v ≡ u (mod p).
// If u/v is not a square, returns (r, 0) where r is still defined as
//     r = u · (u·v)^((p-3)/4)  (mod p)
//
// This is the standard "sqrt ratio" primitive used in Edwards-curve
// point decompression (e.g., Decaf/Ristretto-style encoding).
@[direct_array_access; inline]
fn fe_sqrtratio(mut r Field, u Field, v Field) (Field, int) {
	mut uv := Field{}
	fe_mult(mut uv, u, v)
	fe_power446(mut uv, uv) // uv = (u·v)^((p-3)/4)
	fe_mult(mut r, u, uv) // r = u · (u·v)^((p-3)/4)

	// Verify: v · r² == u  (mod p)
	mut ck := Field{}
	fe_sqr(mut ck, r)
	fe_mult(mut ck, v, ck)

	is_square := fe_cmp(ck, u)

	return r, is_square
}

// fe_abs computes the absolute value: z = |u| (mod p).
//
// In the field context, "absolute value" means: if u is "negative"
// (its least significant bit is 1 after canonical reduction), return -u;
// otherwise return u.
@[direct_array_access; inline]
fn fe_abs(mut z Field, u Field) {
	mut x := Field{}
	fe_negate(mut x, u)
	fe_cselect(mut z, x, u, u.is_negative())
}

// is_negative reports whether this field element is "negative".
//
// A field element is considered negative if its canonical (reduced)
// least significant bit is 1. This is the standard convention for
// Edwards-curve sign checks.
@[direct_array_access; inline]
fn (v Field) is_negative() int {
	mut x := Field{}
	fe_clone(mut x, v)
	fe_reduce(mut x)
	return int(x.el[0] & 1)
}

// Multiplication

// fe_mult multiplies two field elements: z = x · y (mod p).
//
// Currently routes through Karatsuba multiplication (fe_mult_karatsuba).
// TODO: Evaluate further optimizations (e.g., Toom-Cook, FFT-based).
@[direct_array_access]
fn fe_mult(mut z Field, x Field, y Field) {
	fe_mult_karatsuba(mut z, x, y)
}

// fe_mult_karatsuba multiplies two field elements using 2-way Karatsuba.
//
// Split each 448-bit input into low and high 224-bit halves (4 limbs each):
//     x = x0 + x1·B⁴,   y = y0 + y1·B⁴,   where B = 2⁵⁶
//
// Karatsuba computes the product with three 4-limb multiplications
// instead of four:
//     z0 = x0 · y0
//     z2 = x1 · y1
//     z1 = (x0+x1)·(y0+y1) - z0 - z2
//     x·y = z0 + z1·B⁴ + z2·B⁸
//
// The 15 resulting polynomial limbs are then folded modulo p using the
// Solinas identity B⁸ = B⁴ + 1 (i.e., 2⁴⁴⁸ = 2²²⁴ + 1).
//
// All intermediate arithmetic stays below 128 bits.
@[direct_array_access; inline]
fn fe_mult_karatsuba(mut z Field, x Field, y Field) {
	mut z0 := [7]unsigned.Uint128{}
	mut z1 := [7]unsigned.Uint128{}
	mut z2 := [7]unsigned.Uint128{}

	// 1. Compute lower product: z0 = x0 · y0
	mul_4limb_schoolbook(mut z0, x.el[0], x.el[1], x.el[2], x.el[3], y.el[0], y.el[1], y.el[2],
		y.el[3])

	// 2. Compute upper product: z2 = x1 · y1
	mul_4limb_schoolbook(mut z2, x.el[4], x.el[5], x.el[6], x.el[7], y.el[4], y.el[5], y.el[6],
		y.el[7])

	// 3. Compute middle product: z1 = (x0+x1)·(y0+y1) - z0 - z2
	//    First, compute the sums x0+x1 and y0+y1.
	x01_0 := x.el[0] + x.el[4]
	x01_1 := x.el[1] + x.el[5]
	x01_2 := x.el[2] + x.el[6]
	x01_3 := x.el[3] + x.el[7]

	y01_0 := y.el[0] + y.el[4]
	y01_1 := y.el[1] + y.el[5]
	y01_2 := y.el[2] + y.el[6]
	y01_3 := y.el[3] + y.el[7]

	mul_4limb_schoolbook(mut z1, x01_0, x01_1, x01_2, x01_3, y01_0, y01_1, y01_2, y01_3)

	// Apply a bias of 2¹²⁰ to each z1 limb before subtraction to ensure
	// non-negative intermediate values (since Uint128 has no signed mode).
	bias := unsigned.uint128_new(0, u64(1) << 56)

	for i := 0; i < 7; i++ {
		z1_biased := add_128(z1[i], bias)
		z1[i] = sub_128(sub_128(z1_biased, z0[i]), z2[i])
	}

	// 4. Assemble the full 15-limb product polynomial r[0..14].
	mut r := [15]unsigned.Uint128{}
	for i := 0; i < 7; i++ {
		r[i] = add_128(r[i], z0[i])
		r[i + 4] = add_128(r[i + 4], z1[i])
		r[i + 8] = add_128(r[i + 8], z2[i])
	}

	// Subtract the bias back out from limbs 4..10 (where it was added).
	for i := 0; i < 7; i++ {
		r[i + 4] = sub_128(r[i + 4], bias)
	}

	// 5. Reduce modulo p = 2⁴⁴⁸ - 2²²⁴ - 1.
	fold_and_reduce_15limb(mut z, r)

	// NOTE: Stack clearing of z0/z1/z2/r is commented out below.
	// For strict side-channel resistance, these should be wiped if the
	// inputs are secret. V zero-initializes fresh arrays, but does not
	// guarantee clearing of intermediate stack values.
	//
	// clear_uint128x7(mut z0)
	// clear_uint128x7(mut z1)
	// clear_uint128x7(mut z2)
	// clear_uint128x15(mut r)
}

// Squaring
//
// fe_sqr squares a field element: z = x² (mod p).
//
// Routes through a dedicated squaring path (fe_sqr_karatsuba) which is
// ~37% faster than generic multiplication for this operation.
@[direct_array_access; inline]
fn fe_sqr(mut z Field, a Field) {
	fe_sqr_karatsuba(mut z, a)
}

// fe_sqr_karatsuba squares a field element using optimized Karatsuba.
//
// Structurally identical to fe_mult_karatsuba, but since both operands
// are the same (x = x0 + x1·B⁴), all three sub-products are squarings:
//     z0 = x0²,   z2 = x1²,   z1 = (x0+x1)² - z0 - z2
//
// Each sub-product uses mul_4limb_schoolbook_square (10 multiplications)
// instead of mul_4limb_schoolbook (16 multiplications): 30 total vs 48,
// a ~37% reduction. This is the highest-leverage optimization in the
// entire field layer because fe_power446 (the core of inverse and sqrt)
// consists almost entirely of repeated squarings (>400 per call).
@[direct_array_access; inline]
fn fe_sqr_karatsuba(mut z Field, x Field) {
	mut z0 := [7]unsigned.Uint128{}
	mut z1 := [7]unsigned.Uint128{}
	mut z2 := [7]unsigned.Uint128{}

	// 1. Lower square: z0 = x0²
	mul_4limb_schoolbook_square(mut z0, x.el[0], x.el[1], x.el[2], x.el[3])

	// 2. Upper square: z2 = x1²
	mul_4limb_schoolbook_square(mut z2, x.el[4], x.el[5], x.el[6], x.el[7])

	// 3. Middle square: z1 = (x0+x1)² - z0 - z2
	x01_0 := x.el[0] + x.el[4]
	x01_1 := x.el[1] + x.el[5]
	x01_2 := x.el[2] + x.el[6]
	x01_3 := x.el[3] + x.el[7]

	mul_4limb_schoolbook_square(mut z1, x01_0, x01_1, x01_2, x01_3)

	// Bias to ensure non-negative subtraction.
	bias := unsigned.uint128_new(0, u64(1) << 56)

	for i := 0; i < 7; i++ {
		z1_biased := add_128(z1[i], bias)
		z1[i] = sub_128(sub_128(z1_biased, z0[i]), z2[i])
	}

	// 4. Assemble 15-limb polynomial.
	mut r := [15]unsigned.Uint128{}
	for i := 0; i < 7; i++ {
		r[i] = add_128(r[i], z0[i])
		r[i + 4] = add_128(r[i + 4], z1[i])
		r[i + 8] = add_128(r[i + 8], z2[i])
	}

	// Remove bias from limbs 4..10.
	for i := 0; i < 7; i++ {
		r[i + 4] = sub_128(r[i + 4], bias)
	}

	// 5. Solinas reduction.
	fold_and_reduce_15limb(mut z, r)
}

// Low-Level Limb Multiplication Primitives
//
// mul_4limb_schoolbook_square performs 4-limb schoolbook squaring into a
// 7-element Uint128 array.
//
// Diagonal terms x[i]² contribute once. Cross terms x[i]·x[j] (i < j) are
// computed once and doubled via a 1-bit left shift (lsh_128).
//
// Cost: 10 word multiplications (4 diagonal + 6 cross) vs 16 for a generic
// 4×4 multiplication — a 37.5% saving.
//
// PRECONDITION: `out` must be zero-initialized. All call sites pass a
// fresh `[7]unsigned.Uint128{}` literal, which V zero-initializes.
@[direct_array_access; inline]
fn mul_4limb_schoolbook_square(mut out [7]unsigned.Uint128, x0 u64, x1 u64, x2 u64, x3 u64) {
	// Diagonal terms: x_i · x_i
	out[0] = add_128(out[0], mult_64(x0, x0))
	out[2] = add_128(out[2], mult_64(x1, x1))
	out[4] = add_128(out[4], mult_64(x2, x2))
	out[6] = add_128(out[6], mult_64(x3, x3))

	// Cross terms: 2 · (x_i · x_j) for i < j, computed as left-shift.
	out[1] = add_128(out[1], lsh_128(mult_64(x0, x1)))
	out[2] = add_128(out[2], lsh_128(mult_64(x0, x2)))
	out[3] = add_128(out[3], lsh_128(mult_64(x0, x3)))
	out[3] = add_128(out[3], lsh_128(mult_64(x1, x2)))
	out[4] = add_128(out[4], lsh_128(mult_64(x1, x3)))
	out[5] = add_128(out[5], lsh_128(mult_64(x2, x3)))
}

// mul_4limb_schoolbook performs 4×4 limb schoolbook multiplication into
// a 7-element Uint128 array.
//
// Computes the product of two 224-bit numbers (4 limbs × 56 bits):
//     out = X · Y
// where X = [x0, x1, x2, x3] and Y = [y0, y1, y2, y3].
//
// The result is a 448-bit value stored in 7 limbs of 128 bits each.
@[direct_array_access; inline]
fn mul_4limb_schoolbook(mut out [7]unsigned.Uint128, x0 u64, x1 u64, x2 u64, x3 u64, y0 u64, y1 u64, y2 u64, y3 u64) {
	clear_uint128x7(mut out)

	// Row 0: x0 · [y0, y1, y2, y3]
	out[0] = add_128(out[0], mult_64(x0, y0))
	out[1] = add_128(out[1], mult_64(x0, y1))
	out[2] = add_128(out[2], mult_64(x0, y2))
	out[3] = add_128(out[3], mult_64(x0, y3))

	// Row 1: x1 · [y0, y1, y2, y3]
	out[1] = add_128(out[1], mult_64(x1, y0))
	out[2] = add_128(out[2], mult_64(x1, y1))
	out[3] = add_128(out[3], mult_64(x1, y2))
	out[4] = add_128(out[4], mult_64(x1, y3))

	// Row 2: x2 · [y0, y1, y2, y3]
	out[2] = add_128(out[2], mult_64(x2, y0))
	out[3] = add_128(out[3], mult_64(x2, y1))
	out[4] = add_128(out[4], mult_64(x2, y2))
	out[5] = add_128(out[5], mult_64(x2, y3))

	// Row 3: x3 · [y0, y1, y2, y3]
	out[3] = add_128(out[3], mult_64(x3, y0))
	out[4] = add_128(out[4], mult_64(x3, y1))
	out[5] = add_128(out[5], mult_64(x3, y2))
	out[6] = add_128(out[6], mult_64(x3, y3))
}

// Reduction Helpers
//
// reduce_8limb_product reduces eight 128-bit accumulators into an 8-limb
// 56-bit field element.
//
// Algorithm:
//   1. Sequentially extract 56-bit limbs and propagate carries.
//   2. The carry out of the final limb is folded back into limbs 0 and 4
//      using the Solinas identity 2⁴⁴⁸ = 2²²⁴ + 1.
//   3. Apply fe_weak_reduce to normalize any remaining overflows.
@[direct_array_access; inline]
fn reduce_8limb_product(mut z Field, t0 unsigned.Uint128, t1 unsigned.Uint128, t2 unsigned.Uint128, t3 unsigned.Uint128, t4 unsigned.Uint128, t5 unsigned.Uint128, t6 unsigned.Uint128, t7 unsigned.Uint128) {
	mut c := u64(0)

	// Extract 56-bit limbs from each 128-bit accumulator, propagating carries.
	z.el[0] = t0.lo & mask_56bits
	c = (t0.hi << 8) | (t0.lo >> 56)

	lo1, hi1 := add_u64_to_128(t1, c)
	z.el[1] = lo1 & mask_56bits
	c = (hi1 << 8) | (lo1 >> 56)

	lo2, hi2 := add_u64_to_128(t2, c)
	z.el[2] = lo2 & mask_56bits
	c = (hi2 << 8) | (lo2 >> 56)

	lo3, hi3 := add_u64_to_128(t3, c)
	z.el[3] = lo3 & mask_56bits
	c = (hi3 << 8) | (lo3 >> 56)

	lo4, hi4 := add_u64_to_128(t4, c)
	z.el[4] = lo4 & mask_56bits
	c = (hi4 << 8) | (lo4 >> 56)

	lo5, hi5 := add_u64_to_128(t5, c)
	z.el[5] = lo5 & mask_56bits
	c = (hi5 << 8) | (lo5 >> 56)

	lo6, hi6 := add_u64_to_128(t6, c)
	z.el[6] = lo6 & mask_56bits
	c = (hi6 << 8) | (lo6 >> 56)

	lo7, hi7 := add_u64_to_128(t7, c)
	z.el[7] = lo7 & mask_56bits
	c = (hi7 << 8) | (lo7 >> 56)

	// Fold top carry using Solinas identity: 2⁴⁴⁸ ≡ 2²²⁴ + 1 (mod p)
	z.el[0] += c
	z.el[4] += c

	// Normalize any new overflows.
	fe_weak_reduce(mut z)
}

// add_u64_to_128 adds a u64 carry to a 128-bit value.
//
// Returns (lo, hi) where the result is hi·2⁶⁴ + lo.
@[inline]
fn add_u64_to_128(t unsigned.Uint128, c u64) (u64, u64) {
	lo, carry := bits.add_64(t.lo, c, 0)
	hi, _ := bits.add_64(t.hi, 0, carry)
	return lo, hi
}

// Scalar Multiplication (by u32)
//
// fe_mult_32 multiplies a field element by a 32-bit scalar: z = x · y (mod p).
//
// Uses 56-bit limb multiplication (mult_56) which returns a (lo, hi) pair
// where lo + hi·2⁵⁶ = a · b. Carries are propagated across limbs and the
// final result is reduced.
@[direct_array_access; inline]
fn fe_mult_32(mut z Field, x Field, y u32) {
	// Multiply each limb by the scalar.
	x0lo, x0hi := mult_56(x.el[0], y)
	x1lo, x1hi := mult_56(x.el[1], y)
	x2lo, x2hi := mult_56(x.el[2], y)
	x3lo, x3hi := mult_56(x.el[3], y)
	x4lo, x4hi := mult_56(x.el[4], y)
	x5lo, x5hi := mult_56(x.el[5], y)
	x6lo, x6hi := mult_56(x.el[6], y)
	x7lo, x7hi := mult_56(x.el[7], y)

	// Propagate carries. The hi term of limb 7 folds into limb 0 and 4
	// (Solinas identity: overflow at 2⁴⁴⁸ maps to 2²²⁴ + 1).
	z.el[0] = x0lo + x7hi
	z.el[1] = x1lo + x0hi
	z.el[2] = x2lo + x1hi
	z.el[3] = x3lo + x2hi
	z.el[4] = x4lo + x3hi + x7hi
	z.el[5] = x5lo + x4hi
	z.el[6] = x6lo + x5hi
	z.el[7] = x7lo + x6hi

	fe_weak_reduce(mut z)
}

// Serialization / Deserialization
//
// set_bytes parses a 56-byte little-endian array into a field element.
//
// Returns an error if:
//   - b.len != 56
//   - The decoded value is not canonical (i.e., value >= p)
//
// This is the STRICT variant: non-canonical inputs are rejected.
// For RFC 7748 compliant behavior (reduce non-canonical inputs mod p),
// use set_bytes_little_endian instead.
@[direct_array_access; inline]
fn (mut z Field) set_bytes(b []u8) ! {
	if b.len != 56 {
		return error('set_bytes: expected 56 bytes, got ${b.len}')
	}

	// Parse little-endian limbs: each limb is 7 bytes (56 bits).
	for i := 0; i < 8; i++ {
		mut limb := u64(0)
		for j := 0; j < 7; j++ {
			limb |= u64(b[i * 7 + j]) << (j * 8)
		}
		z.el[i] = limb
	}

	// Verify canonicality: x must be in [0, p-1].
	if !z.is_canonical() {
		return error('set_bytes: non-canonical field element (x >= p)')
	}
}

// set_bytes_little_endian parses a 56-byte little-endian array and reduces
// the result modulo p.
//
// Per RFC 7748, X448 implementations must accept non-canonical input bytes
// (x >= p) and reduce them modulo p. This function implements that behavior.
@[direct_array_access; inline]
fn (mut z Field) set_bytes_little_endian(b []u8) ! {
	if b.len != 56 {
		return error('set_bytes_little_endian: expected 56 bytes, got ${b.len}')
	}

	// Parse little-endian limbs.
	for i := 0; i < 8; i++ {
		mut limb := u64(0)
		for j := 0; j < 7; j++ {
			limb |= u64(b[i * 7 + j]) << (j * 8)
		}
		z.el[i] = limb
	}

	// Reduce non-canonical values modulo p.
	fe_reduce(mut z)
}

// is_canonical reports whether the field element is in canonical form [0, p-1].
//
// Algorithm:
//   1. Check that all limbs fit in 56 bits.
//   2. Test if z >= p by computing the carry of z + (2²²⁴ + 1).
//      If the carry is 1, then z + 2²²⁴ + 1 >= 2⁴⁴⁸, so z >= p.
//
// NOTE: This function assumes limbs may have unpropagated carries.
// If called on a partially-reduced value, it may return false even
// though the true value is < p. For reliable results, call fe_reduce first.
fn (z Field) is_canonical() bool {
	// Quick reject: any limb exceeding 56 bits is definitely non-canonical
	// (or at least not fully reduced).
	for i := 0; i < 8; i++ {
		if z.el[i] > mask_56bits {
			return false
		}
	}

	// Constant-time test: compute z + 2²²⁴ + 1 and check for overflow.
	// 2²²⁴ + 1 in limb form is: [1, 0, 0, 0, 1, 0, 0, 0].
	mut c := u64(1) // +1 at bit 0
	for i := 0; i < 8; i++ {
		// Branchless: add = 1 when i == 4, else 0.
		add := u64(1) - ((u64(i ^ 4) | (0 - u64(i ^ 4))) >> 63)
		sum := z.el[i] + add + c
		c = sum >> 56
	}

	// c == 1 means z + 2²²⁴ + 1 >= 2⁴⁴⁸, therefore z >= p.
	return c == 0
}

// bytes serializes a field element into a 56-byte little-endian array.
//
// The element is first fully reduced to canonical form before serialization.
// Panics if internal serialization fails (should never happen with correct
// buffer sizing).
@[direct_array_access; inline]
fn (mut x Field) bytes() []u8 {
	mut dst := []u8{len: 56}
	x.to_bytes(mut dst) or { panic('bytes: internal serialization error') }
	return dst
}

// to_bytes serializes a field element into a pre-allocated 56-byte buffer
// in little-endian form.
//
// The element is fully reduced before serialization. Returns an error if
// dst.len != 56.
@[direct_array_access; inline]
fn (mut x Field) to_bytes(mut dst []u8) ! {
	if dst.len != 56 {
		return error('to_bytes: destination must be exactly 56 bytes')
	}

	// Ensure canonical representation before serialization.
	fe_reduce(mut x)

	// Serialize each 56-bit limb into 7 little-endian bytes.
	for i := 0; i < 7; i++ {
		dst[i + 0] = u8(x.el[0] >> u64(i * 8))
		dst[i + 7] = u8(x.el[1] >> u64(i * 8))
		dst[i + 14] = u8(x.el[2] >> u64(i * 8))
		dst[i + 21] = u8(x.el[3] >> u64(i * 8))
		dst[i + 28] = u8(x.el[4] >> u64(i * 8))
		dst[i + 35] = u8(x.el[5] >> u64(i * 8))
		dst[i + 42] = u8(x.el[6] >> u64(i * 8))
		dst[i + 49] = u8(x.el[7] >> u64(i * 8))
	}
}

// Field Reduction
//
// fe_reduce fully reduces a field element to its canonical representation
// modulo p.
//
// Algorithm:
//   1. Apply fe_weak_reduce to normalize limb overflows.
//   2. Test if x >= p by computing x + 2²²⁴ + 1 and checking for carry.
//   3. If x >= p, subtract p by adding the carry c to limbs 0 and 4
//      (using the Solinas identity).
//   4. Propagate any new carries and weak-reduce again.
@[direct_array_access; inline]
fn fe_reduce(mut x Field) {
	// Step 1: Normalize limb overflows.
	fe_weak_reduce(mut x)

	// Step 2: Test if x >= p.
	// Compute x + 2²²⁴ + 1. If this overflows 448 bits (carry out = 1),
	// then x >= p and we must subtract p.
	mut c := u64(1) // +1 at bit 0
	for i := 0; i < 8; i++ {
		// Branchless: add = 1 when i == 4 (the 2²²⁴ term), else 0.
		add := u64(1) - ((u64(i ^ 4) | (0 - u64(i ^ 4))) >> 63)
		s := x.el[i] + add + c
		c = s >> limbsize
	}

	// Step 3: Subtract p by adding c·(2²²⁴ + 1) to x.
	// When c == 1, this effectively subtracts p (since 2⁴⁴⁸ ≡ 2²²⁴ + 1).
	x.el[0] += c
	x.el[4] += c

	// Step 4: Propagate new carries and normalize.
	c = 0
	for i := 0; i < 8; i++ {
		s := x.el[i] + c
		x.el[i] = s & mask_56bits
		c = s >> limbsize
	}

	// Final safety pass: absorb any remaining carry from the subtraction.
	fe_weak_reduce(mut x)
}

// fe_weak_reduce performs carry propagation across all limbs.
//
// Algorithm:
//   1. Two full passes extract 56-bit limbs and propagate carries.
//   2. The carry out of limb 7 is folded back into limbs 0 and 4
//      (Solinas: 2⁴⁴⁸ = 2²²⁴ + 1).
//   3. A final ripple handles any overflow in limbs 0 or 4 caused by
//      the fold-back.
//
// Two passes are mathematically sufficient to absorb all Solinas carries.
@[direct_array_access; inline]
fn fe_weak_reduce(mut x Field) {
	mut c := u64(0)

	// Pass 1 & 2: Extract 56-bit limbs and propagate carries.
	for _ in 0 .. 2 {
		for i := 0; i < 8; i++ {
			s := x.el[i] + c
			x.el[i] = s & mask_56bits
			c = s >> limbsize
		}
		// Fold overflow carry back into limbs 0 and 4.
		x.el[0] += c
		x.el[4] += c
		// Reset carry for the next pass, which will sweep any new
		// overflows created by the additions to el[0] and el[4].
		c = 0
	}

	// Final ripple: handle any single-bit overflow in el[0] or el[4]
	// that remains after the two passes.
	x.el[1] += x.el[0] >> limbsize
	x.el[0] &= mask_56bits
	x.el[5] += x.el[4] >> limbsize
	x.el[4] &= mask_56bits
}

// Utility / Helper Functions
//
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
	hi := (hh << 8) | (ll >> limbsize)
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

// clear_u64x4 zeroes a 4-element u64 array.
@[direct_array_access; inline]
fn clear_u64x4(mut values [4]u64) {
	for i := 0; i < 4; i++ {
		values[i] = 0
	}
}

// clear_uint128x7 zeroes a 7-element Uint128 array.
@[direct_array_access; inline]
fn clear_uint128x7(mut values [7]unsigned.Uint128) {
	zero := unsigned.uint128_new(0, 0)
	for i := 0; i < 7; i++ {
		values[i] = zero
	}
}

// clear_uint128x15 zeroes a 15-element Uint128 array.
@[direct_array_access; inline]
fn clear_uint128x15(mut values [15]unsigned.Uint128) {
	zero := unsigned.uint128_new(0, 0)
	for i := 0; i < 15; i++ {
		values[i] = zero
	}
}

// Solinas Reduction: 15-limb folding
//
// fold_and_reduce_15limb folds a 15-limb unreduced product r[0..14] modulo
// p = 2⁴⁴⁸ - 2²²⁴ - 1 using the Solinas identity B⁸ = B⁴ + 1.
//
// Given a polynomial:
//     R = r₀ + r₁·B + ... + r₁₄·B¹⁴
//
// We fold the high limbs (B⁸ and above) back down using:
//     B⁸ = B⁴ + 1
//     B⁹ = B⁵ + B
//     ...
//     B¹⁴ = B¹⁰ + B⁶
//
// Terms that land at B⁸..B¹⁰ from the first fold are folded once more.
// The final 8 accumulators are passed to reduce_8limb_product.
@[direct_array_access; inline]
fn fold_and_reduce_15limb(mut z Field, r [15]unsigned.Uint128) {
	// Pre-compute 2 × r[12..14] for the second fold pass.
	r12_x2 := lsh_128(r[12])
	r13_x2 := lsh_128(r[13])
	r14_x2 := lsh_128(r[14])

	// First fold: distribute r[8..14] according to B⁸ = B⁴ + 1.
	// r[8]  → t0 (×1) and t4 (×1)
	// r[9]  → t1 (×1) and t5 (×1)
	// r[10] → t2 (×1) and t6 (×1)
	// r[11] → t3 (×1) and t7 (×1)
	// r[12] → t0 (×1) and t4 (×2)  [because B¹² = B⁸·B⁴ = (B⁴+1)·B⁴ = B⁸+B⁴]
	// r[13] → t1 (×1) and t5 (×2)
	// r[14] → t2 (×1) and t6 (×2)
	mut t0 := add_128(r[0], add_128(r[8], r[12]))
	mut t1 := add_128(r[1], add_128(r[9], r[13]))
	mut t2 := add_128(r[2], add_128(r[10], r[14]))
	mut t3 := add_128(r[3], r[11])

	mut t4 := add_128(r[4], add_128(r[8], r12_x2))
	mut t5 := add_128(r[5], add_128(r[9], r13_x2))
	mut t6 := add_128(r[6], add_128(r[10], r14_x2))
	mut t7 := add_128(r[7], r[11])

	// Pass the 8 accumulators to the 128-bit → 56-bit carry sweep.
	reduce_8limb_product(mut z, t0, t1, t2, t3, t4, t5, t6, t7)
}
