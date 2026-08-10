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
// Solinas Reduction
//
// For Curve448, the prime p = 2⁴⁴⁸ - 2²²⁴ - 1 admits a fast reduction rule:
//
//   2⁴⁴⁸ ≡ 2²²⁴ + 1  (mod p)
//
// This means any overflow at the top limb (limb 7) can be folded back by
// adding its carry to limbs 0 and 4. In effect, it replaces an expensive
// full modular reduction with cheap additions to two limbs.
//
// SECURITY NOTE: All comparison, selection, and swap operations are
// implemented to run in constant-time to mitigate timing side-channels.
// However, full constant-time guarantees also depend on the compiler not
// optimizing away the branchless patterns used here.
module curve448

// Module Constants

// limb_bits_size is the width of each field limb in bits.
// Eight limbs × 56 bits = 448 bits total.
const limb_bits_size = 56

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

// fe_minus_one is the canonical representative of -1 mod p (p - 1).
// It is a known low-order Montgomery u-coordinate and must be rejected by
// strict point validation.
const fe_minus_one = Field{
	el: [
		u64(0x00FF_FFFF_FFFF_FFFE),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFE),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF),
	]!
}

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
	crypto_wipe_8xu64(mut z.el)
}

// fe_clone copies all limbs from x into z.
//
// Equivalent to: z = x
@[direct_array_access; inline]
fn fe_clone(mut z Field, x Field) {
	z.el[0] = x.el[0]
	z.el[1] = x.el[1]
	z.el[2] = x.el[2]
	z.el[3] = x.el[3]
	z.el[4] = x.el[4]
	z.el[5] = x.el[5]
	z.el[6] = x.el[6]
	z.el[7] = x.el[7]
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
	// Step 1: Perform unreduced limb-wise addition.
	// Each limb sum can temporarily reach up to (2⁵⁶ - 1) + (2⁵⁶ - 1) = 2⁵⁷ - 2 (< 2⁶⁴),
	// fitting comfortably inside a u64 without integer overflow.
	z.el[0] = a.el[0] + b.el[0]
	z.el[1] = a.el[1] + b.el[1]
	z.el[2] = a.el[2] + b.el[2]
	z.el[3] = a.el[3] + b.el[3]
	z.el[4] = a.el[4] + b.el[4]
	z.el[5] = a.el[5] + b.el[5]
	z.el[6] = a.el[6] + b.el[6]
	z.el[7] = a.el[7] + b.el[7]

	// Step 2: Propagate carries and apply Solinas reduction (2⁴⁴⁸ ≡ 2²²⁴ + 1 mod p)
	// to bring all limbs back into normalized bound [0, 2⁵⁶).
	fe_weak_reduce(mut z)
}

// fe_sub computes modular field subtraction: z = a - b (mod p).
//
// The key challenge: direct subtraction risks underflow since b might be
// "redundant" (limbs up to 2⁵⁷). Solution: use 4×p as an offset.
//
// Why 4×p (not 2×p)?
// - Each limb b[i] can reach ~2⁵⁷ before reduction.
// - Using 2×p leaves only a 1–3 unit safety margin.
// - 4×p provides comfortable headroom and is still fast to precompute.
//
// Algorithm:
//   1. Compute (a + 4p) - b per limb. The 4p offset prevents underflow.
//   2. Extract 56-bit portion and carry for each result.
//   3. Propagate carries left-to-right (limbs 0..6 to their next).
//   4. Fold the top carry (c7) back via Solinas: c7 → limbs 0 and 4.
//   5. Apply single-pass weak reduction (all limbs back to <2⁵⁶).
@[direct_array_access; inline]
fn fe_sub(mut z Field, a Field, b Field) {
	// Step 1: Compute (a + 4p) - b per limb, extracting 56-bit carries.
	// Adding fe_4p_limbs guarantees that (a.el[i] + fe_4p_limbs[i]) >= b.el[i]
	// even if b is at its maximum redundant bound (< 2⁵⁷), preventing u64 underflow.
	z0 := (a.el[0] + fe_4p_limbs[0]) - b.el[0]
	c0 := z0 >> limb_bits_size
	z.el[0] = z0 & mask_56bits

	z1 := (a.el[1] + fe_4p_limbs[1]) - b.el[1]
	c1 := z1 >> limb_bits_size
	z.el[1] = z1 & mask_56bits

	z2 := (a.el[2] + fe_4p_limbs[2]) - b.el[2]
	c2 := z2 >> limb_bits_size
	z.el[2] = z2 & mask_56bits

	z3 := (a.el[3] + fe_4p_limbs[3]) - b.el[3]
	c3 := z3 >> limb_bits_size
	z.el[3] = z3 & mask_56bits

	z4 := (a.el[4] + fe_4p_limbs[4]) - b.el[4]
	c4 := z4 >> limb_bits_size
	z.el[4] = z4 & mask_56bits

	z5 := (a.el[5] + fe_4p_limbs[5]) - b.el[5]
	c5 := z5 >> limb_bits_size
	z.el[5] = z5 & mask_56bits

	z6 := (a.el[6] + fe_4p_limbs[6]) - b.el[6]
	c6 := z6 >> limb_bits_size
	z.el[6] = z6 & mask_56bits

	z7 := (a.el[7] + fe_4p_limbs[7]) - b.el[7]
	c7 := z7 >> limb_bits_size
	z.el[7] = z7 & mask_56bits

	// Step 2: Propagate carries. The top carry c7 out of limb 7 represents
	// overflow at 2⁴⁴⁸, which folds back into limbs 0 and 4 per Solinas identity:
	// 2⁴⁴⁸ ≡ 2²²⁴ + 1 (mod p).
	z.el[0] += c7
	z.el[4] += c7

	// Ripple lower carries c0..c6 forward into adjacent higher limbs.
	z.el[1] += c0
	z.el[2] += c1
	z.el[3] += c2
	z.el[4] += c3
	z.el[5] += c4
	z.el[6] += c5
	z.el[7] += c6

	// Step 3: Single-pass weak reduction to absorb ripple overflows into [0, 2⁵⁶).
	fe_weak_reduce_1pass(mut z)
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
	// Step 1: Compute (4p - a) per limb, extracting 56-bit carries.
	z0 := fe_4p_limbs[0] - a.el[0]
	c0 := z0 >> limb_bits_size
	z.el[0] = z0 & mask_56bits

	z1 := fe_4p_limbs[1] - a.el[1]
	c1 := z1 >> limb_bits_size
	z.el[1] = z1 & mask_56bits

	z2 := fe_4p_limbs[2] - a.el[2]
	c2 := z2 >> limb_bits_size
	z.el[2] = z2 & mask_56bits

	z3 := fe_4p_limbs[3] - a.el[3]
	c3 := z3 >> limb_bits_size
	z.el[3] = z3 & mask_56bits

	z4 := fe_4p_limbs[4] - a.el[4]
	c4 := z4 >> limb_bits_size
	z.el[4] = z4 & mask_56bits

	z5 := fe_4p_limbs[5] - a.el[5]
	c5 := z5 >> limb_bits_size
	z.el[5] = z5 & mask_56bits

	z6 := fe_4p_limbs[6] - a.el[6]
	c6 := z6 >> limb_bits_size
	z.el[6] = z6 & mask_56bits

	z7 := fe_4p_limbs[7] - a.el[7]
	c7 := z7 >> limb_bits_size
	z.el[7] = z7 & mask_56bits

	// Step 2: Propagate carries with Solinas fold-back (c7 into limbs 0 and 4).
	z.el[0] += c7
	z.el[4] += c7

	z.el[1] += c0
	z.el[2] += c1
	z.el[3] += c2
	z.el[4] += c3
	z.el[5] += c4
	z.el[6] += c5
	z.el[7] += c6

	// Step 3: Single-pass weak reduction.
	fe_weak_reduce_1pass(mut z)
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

// fe_cmp compares two field elements in constant-time.
//
// Returns: 1 if a ≡ b (mod p), 0 otherwise.
//
// Constant-time design (no branches on secret data):
//   - Both inputs reduced to canonical form [0, p-1].
//   - Compare all 8 limbs via XOR (bitwise, not conditional).
//   - Any differing bit sets accumulator → result is 0.
//   - No early exit if a mismatch is found.
@[direct_array_access; inline]
fn fe_cmp(a Field, b Field) int {
	// Step 1: Reduce both inputs to canonical representation in [0, p-1].
	mut x := a
	mut y := b
	fe_reduce(mut x)
	fe_reduce(mut y)

	// Step 2: Constant-time limb comparison via bitwise XOR accumulation.
	// Any differing bit in any limb will set one or more bits in accumulator c.
	mut c := u64(0)
	c |= x.el[0] ^ y.el[0]
	c |= x.el[1] ^ y.el[1]
	c |= x.el[2] ^ y.el[2]
	c |= x.el[3] ^ y.el[3]
	c |= x.el[4] ^ y.el[4]
	c |= x.el[5] ^ y.el[5]
	c |= x.el[6] ^ y.el[6]
	c |= x.el[7] ^ y.el[7]

	// Step 3: Branchless normalization: returns 1 if c == 0 (equal), else 0.
	// Bitwise trick: (c | -c) has bit 63 set iff c != 0. Shifting right by 63 yields 1 for c != 0, 0 for c == 0.
	return int(1 - ((c | (0 - c)) >> 63))
}

// fe_cmp_canonical compares two field elements that are already in
// canonical form (all limbs < 2^56, value < p).
// No reduction is performed. Use only when both inputs are known canonical.
@[direct_array_access; inline]
fn fe_cmp_canonical(a Field, b Field) int {
	// Accumulate limb differences via XOR without reducing first.
	mut c := u64(0)
	c |= a.el[0] ^ b.el[0]
	c |= a.el[1] ^ b.el[1]
	c |= a.el[2] ^ b.el[2]
	c |= a.el[3] ^ b.el[3]
	c |= a.el[4] ^ b.el[4]
	c |= a.el[5] ^ b.el[5]
	c |= a.el[6] ^ b.el[6]
	c |= a.el[7] ^ b.el[7]
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
	// m = 0xFFFF_FFFF_FFFF_FFFF if c != 0, else 0x0000_0000_0000_0000.
	m := mask_64bits(c)
	// Blend each limb branchlessly: (a & m) selects a when m is all-ones, (b & ~m) selects b when m is all-zeros.
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
	// Derive all-ones bitmask for true, all-zeros for false.
	m := mask_64bits(c)

	// Constant-time XOR-swap for each limb:
	//   d = m & (a ^ b)  -> d = a ^ b if c != 0, else 0
	//   a = a ^ d        -> a = b if c != 0, else a
	//   b = b ^ d        -> b = a if c != 0, else b
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
// Algorithm: Fermat's Little Theorem.
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
	fe_power446(mut z, x)
	fe_sqr_n(mut z, z, 2) // t = x^(2⁴⁴⁸ - 2²²⁴ - 4)
	fe_mult(mut z, z, x) // z = x^(2⁴⁴⁸ - 2²²⁴ - 3) = x⁻¹
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
	fe_sqr_n(mut t6, t3, 3) // t6 = z^(7·2³) = z^(2⁶-2³)
	fe_mult(mut t6, t6, t3) // t6 = z⁶³ = z^(2⁶-1)

	// t9 = z^(2⁹ - 1)
	mut t9 := Field{}
	fe_sqr_n(mut t9, t6, 3) // t9 = z^((2⁶-1)·2³) = z^(2⁹-2³)
	fe_mult(mut t9, t9, t3) // t9 = z⁵¹¹ = z^(2⁹-1)

	// t18 = z^(2¹⁸ - 1)
	mut t18 := Field{}
	fe_sqr_n(mut t18, t9, 9) // t18 = z^((2⁹-1)·2⁹) = z^(2¹⁸-2⁹)
	fe_mult(mut t18, t18, t9) // t18 = z^(2¹⁸-1)

	// t37 = z^(2³⁷ - 1)
	mut t37 := Field{}
	fe_sqr_n(mut t37, t18, 18) // t37 = z^((2¹⁸-1)·2¹⁸) = z^(2³⁶-2¹⁸)
	fe_mult(mut t37, t37, t18)
	fe_sqr(mut t37, t37)
	fe_mult(mut t37, t37, z) // t37 = z^(2³⁷-1)

	// t111 = z^(2¹¹¹ - 1)
	mut t111 := Field{}
	fe_sqr_n(mut t111, t37, 37) // t111 = z^((2³⁷-1)·2³⁷) = z^(2⁷⁴-2³⁷)
	fe_mult(mut t111, t111, t37)
	fe_sqr_n(mut t111, t111, 37) // t111 = z^((2⁷⁴-1)·2³⁷) = z^(2¹¹¹-2³⁷)
	fe_mult(mut t111, t111, t37) // t111 = z^(2¹¹¹-1)

	// t222 = z^(2²²² - 1)
	mut t222 := Field{}
	fe_sqr_n(mut t222, t111, 111) // t222 = z^((2¹¹¹-1)·2¹¹¹) = z^(2²²²-2¹¹¹)
	fe_mult(mut t222, t222, t111) // t222 = z^(2²²²-1)

	// t223 = z^(2²²³ - 1)
	mut t223 := Field{}
	fe_sqr(mut t223, t222)
	fe_mult(mut t223, t223, z) // t223 = z^(2²²³-1)

	// v = z^(2⁴⁴⁶ - 2²²² - 1)
	fe_sqr_n(mut v, t223, 223) // x = z^((2²²³-1)·2²²³) = z^(2⁴⁴⁶-2²²³)
	fe_mult(mut v, v, t222) // v = z^(2⁴⁴⁶ - 2²²² - 1)
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
	fe_negate(mut z, u)
	fe_cselect(mut z, z, u, u.is_negative())
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

	is_negative := int(x.el[0] & 1)

	return is_negative
}

// fe_is_zero returns 1 if x == 0 (mod p), otherwise 0.
//
// The input is reduced in place before inspection so callers that already plan
// to clear the field element do not create an extra stack copy of secret data.
@[direct_array_access; inline]
fn fe_is_zero(mut x Field) int {
	fe_reduce(mut x)

	mut c := u64(0)
	c |= x.el[0]
	c |= x.el[1]
	c |= x.el[2]
	c |= x.el[3]
	c |= x.el[4]
	c |= x.el[5]
	c |= x.el[6]
	c |= x.el[7]

	return int(1 - ((c | (0 - c)) >> 63))
}

// Multiplication

// fe_mult multiplies two field elements: z = x · y (mod p).
//
// Routes through Karatsuba multiplication (fe_mult_karatsuba).
@[direct_array_access; inline]
fn fe_mult(mut z Field, x Field, y Field) {
	// See fe_mult_karatsuba implementation in field_mult.v
	fe_mult_karatsuba(mut z, x, y)
}

// Squaring
//
// fe_sqr squares a field element: z = x² (mod p).
//
// Routes through a dedicated squaring path (fe_sqr_karatsuba) which is
// ~37% faster than generic multiplication for this operation.
@[direct_array_access; inline]
fn fe_sqr(mut z Field, a Field) {
	// See fe_sqr_karatsuba implementation in field_mult.v
	fe_sqr_karatsuba(mut z, a)
}

// fe_sqr_n squares x, n times: z = x^(2^n) (mod p).
//
// Derived from the OpenSSL gf_sqrn() routine approach.
// Unrolls squarings in pairs for small n to reduce function-call overhead and
// improve register allocation in hot exponentiation loops.
//
// Preconditions: n > 0.
@[direct_array_access; inline]
fn fe_sqr_n(mut z Field, x Field, n int) {
	if n <= 0 {
		return
	}
	// For small n (1, 2, 3, 9) used in fe_power446, unroll squarings directly.
	if n == 1 {
		fe_sqr_karatsuba(mut z, x)
	} else if n == 2 {
		fe_sqr_karatsuba(mut z, x)
		fe_sqr_karatsuba(mut z, z)
	} else if n == 3 {
		fe_sqr_karatsuba(mut z, x)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
	} else if n == 9 {
		fe_sqr_karatsuba(mut z, x)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
		fe_sqr_karatsuba(mut z, z)
	} else {
		fe_sqr_karatsuba(mut z, x)
		for _ in 1 .. n {
			fe_sqr_karatsuba(mut z, z)
		}
	}
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
// use set_bytes_loosely instead.
@[direct_array_access; inline]
fn (mut z Field) set_bytes(b []u8) ! {
	if b.len != 56 {
		return error('set_bytes: expected 56 bytes, got ${b.len}')
	}

	// All byte offsets and shift amounts are compile-time constants.
	// The compiler can schedule all 56 loads in parallel.
	z.el[0] = u64(b[0]) | u64(b[1]) << 8 | u64(b[2]) << 16 | u64(b[3]) << 24 | u64(b[4]) << 32 | u64(b[5]) << 40 | u64(b[6]) << 48
	z.el[1] = u64(b[7]) | u64(b[8]) << 8 | u64(b[9]) << 16 | u64(b[10]) << 24 | u64(b[11]) << 32 | u64(b[12]) << 40 | u64(b[13]) << 48
	z.el[2] = u64(b[14]) | u64(b[15]) << 8 | u64(b[16]) << 16 | u64(b[17]) << 24 | u64(b[18]) << 32 | u64(b[19]) << 40 | u64(b[20]) << 48
	z.el[3] = u64(b[21]) | u64(b[22]) << 8 | u64(b[23]) << 16 | u64(b[24]) << 24 | u64(b[25]) << 32 | u64(b[26]) << 40 | u64(b[27]) << 48
	z.el[4] = u64(b[28]) | u64(b[29]) << 8 | u64(b[30]) << 16 | u64(b[31]) << 24 | u64(b[32]) << 32 | u64(b[33]) << 40 | u64(b[34]) << 48
	z.el[5] = u64(b[35]) | u64(b[36]) << 8 | u64(b[37]) << 16 | u64(b[38]) << 24 | u64(b[39]) << 32 | u64(b[40]) << 40 | u64(b[41]) << 48
	z.el[6] = u64(b[42]) | u64(b[43]) << 8 | u64(b[44]) << 16 | u64(b[45]) << 24 | u64(b[46]) << 32 | u64(b[47]) << 40 | u64(b[48]) << 48
	z.el[7] = u64(b[49]) | u64(b[50]) << 8 | u64(b[51]) << 16 | u64(b[52]) << 24 | u64(b[53]) << 32 | u64(b[54]) << 40 | u64(b[55]) << 48

	// Verify canonicality: x must be in [0, p-1].
	if !z.is_canonical() {
		return error('set_bytes: non-canonical field element (x >= p)')
	}
}

// set_bytes_loosely parses a 56-byte little-endian array and reduces
// the result modulo p.
//
// Per RFC 7748, X448 implementations must accept non-canonical input bytes
// (x >= p) and reduce them modulo p. This function implements that behavior.
@[direct_array_access; inline]
fn (mut z Field) set_bytes_loosely(b []u8) ! {
	if b.len != 56 {
		return error('set_bytes_loosely: expected 56 bytes, got ${b.len}')
	}

	// Parse little-endian limbs, with loop-unrolling
	z.el[0] = u64(b[0]) | u64(b[1]) << 8 | u64(b[2]) << 16 | u64(b[3]) << 24 | u64(b[4]) << 32 | u64(b[5]) << 40 | u64(b[6]) << 48
	z.el[1] = u64(b[7]) | u64(b[8]) << 8 | u64(b[9]) << 16 | u64(b[10]) << 24 | u64(b[11]) << 32 | u64(b[12]) << 40 | u64(b[13]) << 48
	z.el[2] = u64(b[14]) | u64(b[15]) << 8 | u64(b[16]) << 16 | u64(b[17]) << 24 | u64(b[18]) << 32 | u64(b[19]) << 40 | u64(b[20]) << 48
	z.el[3] = u64(b[21]) | u64(b[22]) << 8 | u64(b[23]) << 16 | u64(b[24]) << 24 | u64(b[25]) << 32 | u64(b[26]) << 40 | u64(b[27]) << 48
	z.el[4] = u64(b[28]) | u64(b[29]) << 8 | u64(b[30]) << 16 | u64(b[31]) << 24 | u64(b[32]) << 32 | u64(b[33]) << 40 | u64(b[34]) << 48
	z.el[5] = u64(b[35]) | u64(b[36]) << 8 | u64(b[37]) << 16 | u64(b[38]) << 24 | u64(b[39]) << 32 | u64(b[40]) << 40 | u64(b[41]) << 48
	z.el[6] = u64(b[42]) | u64(b[43]) << 8 | u64(b[44]) << 16 | u64(b[45]) << 24 | u64(b[46]) << 32 | u64(b[47]) << 40 | u64(b[48]) << 48
	z.el[7] = u64(b[49]) | u64(b[50]) << 8 | u64(b[51]) << 16 | u64(b[52]) << 24 | u64(b[53]) << 32 | u64(b[54]) << 40 | u64(b[55]) << 48

	// Reduce non-canonical values modulo p.
	fe_reduce(mut z)
}

// fe_is_canonical returns 1 if z is in [0, p-1], and 0 otherwise.
//
// Adding 2²²⁴ + 1 and checking the final carry tests both canonicality
// requirements: every limb fits in 56 bits and the represented integer is
// less than p. The carry chain is branchless and has no early exit.
//
// This is the same carry test used by fe_reduce. The int result is kept
// consistent with fe_cmp, fe_is_zero, and mask_64bits.
@[direct_array_access; inline]
fn fe_is_canonical(z Field) int {
	// Add 2²²⁴ + 1 = [1, 0, 0, 0, 1, 0, 0, 0] to z, propagating carries.
	// If the final carry c == 1, then z + (2²²⁴ + 1) >= 2⁴⁴⁸, so z >= p.
	// If any limb exceeds 56 bits, the carry propagates forward and
	// likewise produces c == 1 at the end.
	//
	// Each line: s = limb + constant_add + carry_in; carry_out = s >> 56
	// The constant adds are: limb 0 gets +1, limb 4 gets +1, rest get +0.
	s0 := z.el[0] + u64(1) // + low word of (2²²⁴ + 1)
	c0 := s0 >> 56

	s1 := z.el[1] + c0
	c1 := s1 >> 56

	s2 := z.el[2] + c1
	c2 := s2 >> 56

	s3 := z.el[3] + c2
	c3 := s3 >> 56

	s4 := z.el[4] + u64(1) + c3 // + high word of (2²²⁴ + 1)
	c4 := s4 >> 56

	s5 := z.el[5] + c4
	c5 := s5 >> 56

	s6 := z.el[6] + c5
	c6 := s6 >> 56

	s7 := z.el[7] + c6
	c7 := s7 >> 56

	// c7 == 1  ↔  z >= p  (NOT canonical)
	// c7 == 0  ↔  z <  p  (canonical)
	// Return 1 for canonical, 0 for non-canonical — branchless.
	return int(1 - c7)
}

// is_canonical reports whether the field element is in canonical form [0, p-1].
//
// This is a thin bool wrapper around fe_is_canonical for call sites that
// need a bool (set_bytes, property tests).  The actual test is performed
// entirely by fe_is_canonical.
@[direct_array_access; inline]
fn (z Field) is_canonical() bool {
	return fe_is_canonical(z) == 1
}

// bytes serializes a field element into a 56-byte little-endian array.
//
// The element is first fully reduced to canonical form before serialization.
// Panics if internal serialization fails (should never happen with correct
// buffer sizing).
@[direct_array_access; inline]
fn (mut x Field) bytes(mut dst []u8) ! {
	if dst.len != 56 {
		return error('bytes: output buffer should be 56-bytes length')
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
// fe_reduce fully reduces a field element to its unique canonical
// representative in [0, p-1].
//
// PRECONDITION: all limbs must satisfy el[i] < 2⁵⁶, i.e. the input
// must already be in the normalized (but possibly non-canonical) form
// produced by fe_weak_reduce.  Calling fe_reduce on limbs that exceed
// 2⁵⁶ is incorrect.
//
// Algorithm:
//
// Step 1 — normalize limb overflows (precondition enforcement).
//
// Step 2 — test x >= p.
//   Compute c = floor((x + 2²²⁴ + 1) / 2⁴⁴⁸).
//   Because x < 2⁴⁴⁸ (all limbs < 2⁵⁶), the maximum of x + 2²²⁴ + 1
//   is 2⁴⁴⁸ + 2²²⁴, so c is exactly 0 or 1.
//   c = 1  <=>  x + 2²²⁴ + 1 >= 2⁴⁴⁸  <=>  x >= 2⁴⁴⁸ - 2²²⁴ - 1 = p.
//
// Step 3 — conditionally add (2²²⁴ + 1) to the limbs.
//   Adding c * (2²²⁴ + 1) raises the integer value to:
//     c=0: x unchanged, already in [0, p-1].
//     c=1: x + (2²²⁴ + 1) in [p + 2²²⁴ + 1, 2⁴⁴⁸ + 2²²⁴]
//                         = [2⁴⁴⁸,            2⁴⁴⁸ + 2²²⁴].
//
// Step 4 — propagate carries.
//   Normalizing the limbs of x + (2²²⁴ + 1) produces:
//     limbs:     (x + 2²²⁴ + 1) mod 2⁴⁴⁸  =  x - p   (when c=1)
//     carry_out: floor(...)  / 2⁴⁴⁸         =  1       (when c=1)
//   The carry_out (= c) is intentionally discarded.  It represents the
//   2⁴⁴⁸ term that was deliberately introduced in step 3; dropping it
//   is the Solinas subtraction: x - p ≡ x - (2⁴⁴⁸ - 2²²⁴ - 1).
//   The remaining value x - p is in [0, 2²²⁴] ⊂ [0, p), already
//   canonical.  No further reduction is required.
@[direct_array_access; inline]
fn fe_reduce(mut x Field) {
	// Step 1: Normalize limb overflows.
	fe_weak_reduce(mut x)

	// Step 2: Test x >= p via overflow of x + (2²²⁴ + 1).
	// 2²²⁴ + 1 in limb form: +1 at el[0] (the 1) and +1 at el[4] (the 2²²⁴).
	mut c := u64(1)
	c = (x.el[0] + c) >> 56
	c = (x.el[1] + c) >> 56
	c = (x.el[2] + c) >> 56
	c = (x.el[3] + c) >> 56
	c = (x.el[4] + 1 + c) >> 56
	c = (x.el[5] + c) >> 56
	c = (x.el[6] + c) >> 56
	c = (x.el[7] + c) >> 56

	// c == 1 iff x >= p.
	// Step 3: Conditionally add (2²²⁴ + 1) = Solinas constant.
	x.el[0] += c
	x.el[4] += c

	// Step 4: Propagate carries.
	// carry_out intentionally discarded — see algorithm comment above.
	mut s := x.el[0]
	// vfmt off
	x.el[0] = s & mask_56bits; c = s >> 56; s = x.el[1] + c
	x.el[1] = s & mask_56bits; c = s >> 56; s = x.el[2] + c
	x.el[2] = s & mask_56bits; c = s >> 56; s = x.el[3] + c
	x.el[3] = s & mask_56bits; c = s >> 56; s = x.el[4] + c
	x.el[4] = s & mask_56bits; c = s >> 56; s = x.el[5] + c
	x.el[5] = s & mask_56bits; c = s >> 56; s = x.el[6] + c
	x.el[6] = s & mask_56bits; c = s >> 56; s = x.el[7] + c
	x.el[7] = s & mask_56bits
	// vfmt on
	// c (== original step-2 carry) is discarded here — deliberate.
	// The result is in [0, 2²²⁴] ⊂ [0, p) and is already canonical.
	// No trailing fe_weak_reduce is needed.
}

// fe_weak_reduce normalizes limbs to [0, 2⁵⁶) without necessarily producing
// the canonical representative modulo p.
//
// Each of two carry-propagation passes folds the carry from limb 7 into limbs
// 0 and 4 using 2⁴⁴⁸ ≡ 2²²⁴ + 1 (mod p). A final ripple absorbs any overflow
// introduced by the second fold. Two passes suffice for the bounds produced
// by the field arithmetic routines.
@[direct_array_access; inline]
fn fe_weak_reduce(mut x Field) {
	mut c := u64(0)
	// The passes are fully unrolled so carry propagation stays straight-line
	// code in this hot primitive.
	// Pass 1: extract 56-bit limbs and propagate carries.
	// vfmt off
	mut s := x.el[0] + c;
	x.el[0] = s & mask_56bits; c = s >> 56;	s = x.el[1] + c
	x.el[1] = s & mask_56bits; c = s >> 56; s = x.el[2] + c
	x.el[2] = s & mask_56bits; c = s >> 56; s = x.el[3] + c
	x.el[3] = s & mask_56bits; c = s >> 56; s = x.el[4] + c
	x.el[4] = s & mask_56bits; c = s >> 56; s = x.el[5] + c
	x.el[5] = s & mask_56bits; c = s >> 56; s = x.el[6] + c
	x.el[6] = s & mask_56bits; c = s >> 56; s = x.el[7] + c
	x.el[7] = s & mask_56bits; c = s >> 56
	// Fold overflow at 2⁴⁴⁸ back into limbs 0 and 4.
	x.el[0] += c
	x.el[4] += c

	// Pass 2: absorb carries introduced by the first fold.
	c = x.el[0] >> 56;
	x.el[0] &= mask_56bits; s = x.el[1] + c
	x.el[1] = s & mask_56bits; c = s >> 56; s = x.el[2] + c
	x.el[2] = s & mask_56bits; c = s >> 56; s = x.el[3] + c
	x.el[3] = s & mask_56bits; c = s >> 56; s = x.el[4] + c
	x.el[4] = s & mask_56bits; c = s >> 56; s = x.el[5] + c
	x.el[5] = s & mask_56bits; c = s >> 56; s = x.el[6] + c
	x.el[6] = s & mask_56bits; c = s >> 56; s = x.el[7] + c
	x.el[7] = s & mask_56bits; c = s >> 56
	// Fold any second-pass overflow as well.
	x.el[0] += c
	x.el[4] += c
	// vfmt on

	// Final ripple: handle any single-bit overflow in el[0] or el[4]
	// that remains after the two passes.
	x.el[1] += x.el[0] >> limb_bits_size
	x.el[0] &= mask_56bits
	x.el[5] += x.el[4] >> limb_bits_size
	x.el[4] &= mask_56bits
}

// fe_weak_reduce_1pass performs a single-pass weak reduction.
//
// Specialized for operations such as `fe_sub` and `fe_negate` where input limb
// bounds are tightly controlled by the 4×p subtrahend offset, allowing a single
// carry pass and Solinas fold to normalize all limbs into [0, 2⁵⁶).
@[direct_array_access; inline]
fn fe_weak_reduce_1pass(mut x Field) {
	mut c := u64(0)
	mut s := x.el[0] + c
	// vfmt off
  	x.el[0] = s & mask_56bits; c = s >> 56; s = x.el[1] + c;
  	x.el[1] = s & mask_56bits; c = s >> 56; s = x.el[2] + c;
  	x.el[2] = s & mask_56bits; c = s >> 56; s = x.el[3] + c;
  	x.el[3] = s & mask_56bits; c = s >> 56; s = x.el[4] + c;
  	x.el[4] = s & mask_56bits; c = s >> 56; s = x.el[5] + c;
  	x.el[5] = s & mask_56bits; c = s >> 56; s = x.el[6] + c;
  	x.el[6] = s & mask_56bits; c = s >> 56; s = x.el[7] + c;
  	x.el[7] = s & mask_56bits; c = s >> 56
	// vfmt on

	// Solinas reduction: 2⁴⁴⁸ ≡ 2²²⁴ + 1 (mod p)
	x.el[0] += c
	x.el[4] += c

	// Final ripple: absorb remaining single-bit carries into adjacent limbs.
	x.el[1] += x.el[0] >> 56
	x.el[0] &= mask_56bits
	x.el[5] += x.el[4] >> 56
	x.el[4] &= mask_56bits
}
