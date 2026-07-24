// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// This file contains low-level primitive in the mean of Galois-Field
// element over 448-bits for curve448 operations.
module curve448

import math.bits
import math.unsigned

// Field is an an opaque represents the field of 448-bits integer of GF modulo p = 2⁴⁴⁸ - 2²²⁴ - 1.
// Its represented as unsaturated (redundant) limb in the form of 8 of 56-bits limbs, ie:
//     t.e0*2⁰ + t.e1*2⁵⁶ + t.e2*2¹¹² + t.e3*2¹⁶⁸ + t.e4*2²²⁴ + t.e5*2²⁸⁰ + t.e6*2³³⁶ + t.e7*2³⁹²
//
@[noinit]
struct Field {
mut:
	// Between operations, all limbs are expected to be lower than 2⁵⁷ (ie, fits in 56-bits)
	el [8]u64
}

// The size of field limb, in bits
const limbsize = 56
// Masking value for field's limb value, ie, 0x00ff_ffff_ffff_ffff
const mask_56bits = u64(0x00ff_ffff_ffff_ffff)

// zero field element
const fe_zero = Field{
	el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
}

// one field element
const fe_one = Field{
	el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
}

// fe_prime is a prime modulus of the field, ie, p = 2⁴⁴⁸ - 2²²⁴ - 1
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

// 4 * fe_p limbs pre-computed to prevent bit-overflow during shift
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

// fe_clear overwrites a field element in-place. It is intended for best-effort
// source-level wiping of temporary values that may contain secret-dependent data
// after use. Strict secure-zeroization guarantees require auditing generated
// C/assembly or replacing this with a compiler-resistant wipe primitive.
@[direct_array_access; inline]
fn fe_clear(mut z Field) {
	for i := 0; i < 8; i++ {
		z.el[i] = 0
	}
}

// fe_add performs modular field addition: z = a + b (mod p).
// Direct limb-wise accumulation followed by carry propagation.
// Safe for in-place operations like fe_add(mut a, a, b).
@[direct_array_access; inline]
fn fe_add(mut z Field, a Field, b Field) {
	// z = a + b
	z.el[0] = a.el[0] + b.el[0]
	z.el[1] = a.el[1] + b.el[1]
	z.el[2] = a.el[2] + b.el[2]
	z.el[3] = a.el[3] + b.el[3]
	z.el[4] = a.el[4] + b.el[4]
	z.el[5] = a.el[5] + b.el[5]
	z.el[6] = a.el[6] + b.el[6]
	z.el[7] = a.el[7] + b.el[7]

	// light reduce
	fe_weak_reduce(mut z)
}

// fe_sub performs modular field subtraction: z = a - b (mod p).
// To prevent underflow, it first adds 2 * p (a multiple of the modulus) to a,
// subtracts b, extracts the carries, and applies a reduction step.
@[direct_array_access; inline]
fn fe_sub(mut z Field, a Field, b Field) {
	// c holds the carry/borrow bits extracted from each limb subtraction.
	mut c := [8]u64{}

	// Step 1: Perform subtraction with biased limbs.
	// Since a.el[i] could be smaller than b.el[i], a direct subtraction could underflow
	// and wrap around. To guarantee that the result remains positive and fits in u64,
	// we add 2 * p.el[i] (which is at least 2^57 - 4) to a.el[i] before subtracting b.el[i].
	// We then extract the carry (which acts as a borrow flag) and mask the limb.
	// UPDATED: use 4*p instead of 2*p
	for i := 0; i < 8; i++ {
		// add by 4 * p.el[i]
		z.el[i] = (a.el[i] + fe_4p_limbs[i]) - b.el[i]
		c[i] = z.el[i] >> limbsize
		z.el[i] = z.el[i] & mask_56bits
	}

	// Step 2: Apply the modular reduction.
	// Just like in addition, any carry from the highest limb (c[7]) represents
	// 2^448. We reduce it by adding c[7] to limb 0 (representing 2^0) and limb 4
	// (representing 2^224).
	z.el[0] += c[7]
	z.el[4] += c[7]

	// Step 3: Propagate the carries.
	// Add the carry bit from the previous limb to the current limb.
	for i := 1; i < 8; i++ {
		z.el[i] += c[i - 1]
	}

	fe_weak_reduce(mut z)
}

// fe_negate negates a field element: z = -a (mod p).
// Uses 4*p (rather than 2*p) as the subtrahend base for the same reason as
// fe_sub: 2*p left only a 1-3 unit margin against the documented < 2^57
// per-limb bound, which is too thin.
@[direct_array_access; inline]
fn fe_negate(mut z Field, a Field) {
	// Step 1: Subtract each limb of a from 4 * p.
	for i := 0; i < 8; i++ {
		z.el[i] = fe_4p_limbs[i] - a.el[i]
	}

	// Step 2: Extract and propagate the carries.
	mut c := [8]u64{}
	for i := 0; i < 8; i++ {
		c[i] = z.el[i] >> limbsize
		z.el[i] = (z.el[i] & mask_56bits)
	}
	// Step 3: Apply modular reduction using the Solinas prime identity:
	//     2^448 = 2^224 + 1 (mod p)
	z.el[0] += c[7]
	z.el[4] += c[7]
	// Step 4: Propagate the carries to higher limbs.
	for i := 1; i < 8; i++ {
		z.el[i] += c[i - 1]
	}
	// final carry
	fe_weak_reduce(mut z)
}

// fe_clone clones x into z
@[direct_array_access; inline]
fn fe_clone(mut z Field, x Field) {
	for i := 0; i < 8; i++ {
		z.el[i] = x.el[i]
	}
}

// fe_mult multiplies a with b and stores into z, ie, z = a * b (mod p)
//
// This is the most intensive routines.
// TODO: optimize it with some well-known algorithm
@[direct_array_access]
fn fe_mult(mut z Field, x Field, y Field) {
	// fe_mult_generic(mut z, x, y)
	fe_mult_karatsuba(mut z, x, y)
}

// fe_mult_karatsuba multiplies two field elements using a two-way Karatsuba split.
//
// The input is split into low and high 224-bit halves, each containing four
// 56-bit limbs:
//
//     x = x0 + x1*B⁴,  y = y0 + y1*B⁴,  B = 2⁵⁶
//
// Karatsuba computes the unreduced product with three 4-limb products instead
// of four:
//
//     z0 = x0*y0
//     z2 = x1*y1
//     z1 = (x0+x1)*(y0+y1) - z0 - z2
//     x*y = z0 + z1*B⁴ + z2*B⁸
//
// The resulting 15 polynomial limbs are then folded modulo
// p = 2⁴⁴⁸ - 2²²⁴ - 1 by B⁸ = B⁴ + 1. Terms at B⁸..B¹⁴ are first folded to
// positions i-8 and i-4; terms that land at B⁸..B¹⁰ from the first fold are
// folded once more. All arithmetic stays below 128 bits: the largest product
// term is a sum of a handful of 57-bit-by-57-bit products.
// fe_mult_karatsuba multiplies two field elements using a 2-way Karatsuba split.
@[direct_array_access; inline]
fn fe_mult_karatsuba(mut z Field, x Field, y Field) {
	mut z0 := [7]unsigned.Uint128{}
	mut z1 := [7]unsigned.Uint128{}
	mut z2 := [7]unsigned.Uint128{}

	// 1. Compute lower product z0 = x0 * y0
	mul_4limb_schoolbook(mut z0, x.el[0], x.el[1], x.el[2], x.el[3], y.el[0], y.el[1], y.el[2],
		y.el[3])

	// 2. Compute upper product z2 = x1 * y1
	mul_4limb_schoolbook(mut z2, x.el[4], x.el[5], x.el[6], x.el[7], y.el[4], y.el[5], y.el[6],
		y.el[7])

	// 3. Compute middle product z1 = (x0 + x1) * (y0 + y1) - z0 - z2
	x01_0 := x.el[0] + x.el[4]
	x01_1 := x.el[1] + x.el[5]
	x01_2 := x.el[2] + x.el[6]
	x01_3 := x.el[3] + x.el[7]

	y01_0 := y.el[0] + y.el[4]
	y01_1 := y.el[1] + y.el[5]
	y01_2 := y.el[2] + y.el[6]
	y01_3 := y.el[3] + y.el[7]

	mul_4limb_schoolbook(mut z1, x01_0, x01_1, x01_2, x01_3, y01_0, y01_1, y01_2, y01_3)

	// Apply bias (2^120) to ensure (z1[i] + bias) >= (z0[i] + z2[i])
	bias := unsigned.uint128_new(0, u64(1) << 56)

	for i := 0; i < 7; i++ {
		z1_biased := add_128(z1[i], bias)
		z1[i] = sub_128(sub_128(z1_biased, z0[i]), z2[i])
	}

	// 4. Assemble full 15-limb product polynomial r[0..14]
	mut r := [15]unsigned.Uint128{}
	for i := 0; i < 7; i++ {
		r[i] = add_128(r[i], z0[i])
		r[i + 4] = add_128(r[i + 4], z1[i])
		r[i + 8] = add_128(r[i + 8], z2[i])
	}

	// Subtract the bias back out from limbs 4..10
	for i := 0; i < 7; i++ {
		r[i + 4] = sub_128(r[i + 4], bias)
	}

	// 5. Solinas reduction mod p = 2^448 - 2^224 - 1
	fold_and_reduce_15limb(mut z, r)

	// Best-effort source-level clearing of reusable stack slots. For strict
	// zeroization guarantees, verify the generated C/assembly does not elide it.
	//
	// clear_uint128x7(mut z0)
	// clear_uint128x7(mut z1)
	// clear_uint128x7(mut z2)
	// clear_uint128x15(mut r)
}

// fe_sqr_karatsuba squares a field element using a dedicated squaring path,
// rather than routing through the general fe_mult_karatsuba(z, a, a).
//
// Structurally this is the same 2-way Karatsuba split as fe_mult_karatsuba
// (x = x0 + x1*B^4), but since the second operand is also x, all three
// sub-products are themselves squarings:
//     z0 = x0^2,  z2 = x1^2,  z1 = (x0+x1)^2 - z0 - z2
// Each uses mul_4limb_schoolbook_square (10 multiplications) instead of
// mul_4limb_schoolbook (16 multiplications): 30 total multiplications versus
// 48 for a generic fe_mult_karatsuba(x, x) call, a ~37% reduction in the
// dominant cost. This matters in practice because fe_power446 -- the
// (p-3)/4 exponentiation behind both fe_inverse and fe_sqrtratio -- is
// almost entirely a long chain of repeated squarings (over 400 of them for
// a single fe_power446 call), so this is the highest-leverage optimization
// in the whole field layer.
// fe_sqr_karatsuba computes z = x^2 (mod p) using optimized Karatsuba squaring.
@[direct_array_access; inline]
fn fe_sqr_karatsuba(mut z Field, x Field) {
	mut z0 := [7]unsigned.Uint128{}
	mut z1 := [7]unsigned.Uint128{}
	mut z2 := [7]unsigned.Uint128{}

	// 1. Compute lower square z0 = x0^2
	mul_4limb_schoolbook_square(mut z0, x.el[0], x.el[1], x.el[2], x.el[3])

	// 2. Compute upper square z2 = x1^2
	mul_4limb_schoolbook_square(mut z2, x.el[4], x.el[5], x.el[6], x.el[7])

	// 3. Compute middle square z1 = (x0 + x1)^2 - z0 - z2
	x01_0 := x.el[0] + x.el[4]
	x01_1 := x.el[1] + x.el[5]
	x01_2 := x.el[2] + x.el[6]
	x01_3 := x.el[3] + x.el[7]

	mul_4limb_schoolbook_square(mut z1, x01_0, x01_1, x01_2, x01_3)

	// Apply bias (2^120) to ensure (z1[i] + bias) >= (z0[i] + z2[i])
	bias := unsigned.uint128_new(0, u64(1) << 56)

	for i := 0; i < 7; i++ {
		z1_biased := add_128(z1[i], bias)
		z1[i] = sub_128(sub_128(z1_biased, z0[i]), z2[i])
	}

	// 4. Assemble full 15-limb product polynomial r[0..14]
	mut r := [15]unsigned.Uint128{}
	for i := 0; i < 7; i++ {
		r[i] = add_128(r[i], z0[i])
		r[i + 4] = add_128(r[i + 4], z1[i])
		r[i + 8] = add_128(r[i + 8], z2[i])
	}

	// Subtract the bias back out from limbs 4..10
	for i := 0; i < 7; i++ {
		r[i + 4] = sub_128(r[i + 4], bias)
	}

	// 5. Solinas reduction mod p = 2^448 - 2^224 - 1
	fold_and_reduce_15limb(mut z, r)

	// Should be clearing out on the hot path?
	//
	// clear_uint128x7(mut z0)
	// clear_uint128x7(mut z1)
	// clear_uint128x7(mut z2)
}

// mul_4limb_schoolbook_square performs 4-limb schoolbook squaring into a
// 7-element Uint128 array. Diagonal terms x[i]*x[i] contribute once; cross
// terms x[i]*x[j] (i != j) are equal for (i,j) and (j,i) in a general
// product, so here they are computed once (i<j) and doubled via a 1-bit
// left shift instead of a second multiplication.
// Note: 10 word multiplications (4 diagonal + 6 cross) instead of the 16 that
// mul_4limb_schoolbook(x, x) would perform.
//
// PRECONDITION: `out` must already be zero-initialized (true for every call
// site here, which always passes a fresh `[7]unsigned.Uint128{}` literal --
// V zero-initializes that on declaration, so no redundant clear is done here).
@[direct_array_access; inline]
fn mul_4limb_schoolbook_square(mut out [7]unsigned.Uint128, x0 u64, x1 u64, x2 u64, x3 u64) {
	mut x := [x0, x1, x2, x3]!
	for i := 0; i < 4; i++ {
		out[2 * i] = add_128(out[2 * i], mult_64(x[i], x[i]))
	}
	for i := 0; i < 4; i++ {
		for j := i + 1; j < 4; j++ {
			out[i + j] = add_128(out[i + j], lsh_128(mult_64(x[i], x[j])))
		}
	}
	// clear_u64x4(mut x)
}

// square squares a field, ie, z = a*a (mod p)
@[direct_array_access; inline]
fn fe_sqr(mut z Field, a Field) {
	fe_sqr_karatsuba(mut z, a)
}

// fe_mult_32 multiplies x with u32 (mod p)
@[direct_array_access; inline]
fn fe_mult_32(mut z Field, x Field, y u32) {
	// 56-bits multiplication, returns u64 (lo, hi) pair
	x0lo, x0hi := mult_56(x.el[0], y)
	x1lo, x1hi := mult_56(x.el[1], y)
	x2lo, x2hi := mult_56(x.el[2], y)
	x3lo, x3hi := mult_56(x.el[3], y)
	x4lo, x4hi := mult_56(x.el[4], y)
	x5lo, x5hi := mult_56(x.el[5], y)
	x6lo, x6hi := mult_56(x.el[6], y)
	x7lo, x7hi := mult_56(x.el[7], y)

	// reduction
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

// set_bytes sets the field values from bytes array
@[direct_array_access; inline]
fn (mut z Field) set_bytes(b []u8) ! {
	if b.len != 56 {
		return error('bad set_bytes input')
	}

	// Parse little-endian limbs
	for i := 0; i < 8; i++ {
		mut limb := u64(0)
		for j := 0; j < 7; j++ {
			limb |= u64(b[i * 7 + j]) << (j * 8)
		}
		z.el[i] = limb
	}
	// Verify canonicality: x must be strictly less than p
	if !z.is_canonical() {
		return error('non-canonical field element (x >= p)')
	}
}

// Check if field element is in canonical form [0, p-1]
fn (x Field) is_canonical() bool {
	// We directly checks individual limbs with z.el[i] > mask_56bits.
	// However, if a field element has unpropagated carries (e.g., el[0] = 2^56
	// while the total value is still modulo $< p$),
	// it will incorrectly return false, so we reduce it firts
	mut z := x

	// when we use fe_reduce() performs full modular reduction —
	// by definition its output is always in [0, p-1].
	// The function then checks whether that already-reduced value is >= p.
	// That can never be true. is_canonical() always returns true, for every input, no matter what.
	// Return false if any limb exceeds 56 bits. so, we use fe_weak_reduce() instead.
	fe_weak_reduce(mut z) // normalize limb form only — do NOT reduce mod p

	for i := 0; i < 8; i++ {
		if z.el[i] > mask_56bits { return false }
	}

	// Test if z >= p by computing carry of z + (2^224 + 1)
	mut c := u64(1) // +1 bit 0
	for i := 0; i < 8; i++ {
		// branchless constant-time check: add is 1 when i == 4, else 0
		add := u64(1) - ((u64(i ^ 4) | (0 - u64(i ^ 4))) >> 63)
		sum := z.el[i] + add + c
		c = sum >> 56
	}
	// If c == 1, then z + 2^224 + 1 >= 2^448 => z >= p
	return c == 0
}

// bytes serializes reduced x field into bytes
@[direct_array_access; inline]
fn (mut x Field) bytes() []u8 {
	mut dst := []u8{len: 56}
	x.to_bytes(mut dst) or { panic('error on bytes call') }
	return dst
}

// to_bytes serializes reduced x Field into bytes in little-endian form.
@[direct_array_access; inline]
fn (mut x Field) to_bytes(mut dst []u8) ! {
	if dst.len != 56 {
		return error('bad destination size')
	}
	// reduces the field first
	fe_reduce(mut x)

	// serialized x field in little-endian form
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

// fe_reduce reduces x field (mod p)
@[direct_array_access; inline]
fn fe_reduce(mut x Field) {
	// by the light reduction, we have a field element representation
	// x < 2⁴⁴⁸ + 2²³² + 2⁸, but we need x < 2⁴⁴⁸ - 2²²⁴ - 1 (p).

	fe_weak_reduce(mut x)

	// Test if x + 2^224 + 1 >= 2^448 (equivalent to x >= p)
	mut c := u64(1)
	for i := 0; i < 8; i++ {
		// Branchless: add is 1 when i == 4, else 0
		add := u64(1) - ((u64(i ^ 4) | (0 - u64(i ^ 4))) >> 63)
		s := x.el[i] + add + c
		c = s >> limbsize
	}

	// Reduce by adding c*(2^224 + 1)
	x.el[0] += c
	x.el[4] += c

	c = 0
	for i := 0; i < 8; i++ {
		s := x.el[i] + c
		x.el[i] = s & mask_56bits
		c = s >> limbsize
	}
	// Ensure any remaining carry is folded (guarantee fully reduced result)
	fe_weak_reduce(mut x)
}

// fe_weak_reduce performs a single pass of carry propagation across the field.
// It extracts the carry from each limb and adds it to the next higher limb,
// while applying the Solinas prime reduction on the overflow carry from limb 7.
@[direct_array_access; inline]
fn fe_weak_reduce(mut x Field) {
	// In rare edge cases where upper limbs are near their maximum value
	// (e.g., right after c[7] reduction addition to el[0] and el[4]),
	// two carry passes might still leave a single bit overflow in el[0] or el[4].
	// Exactly 2 passes are mathematically proven to absorb all Solinas carries (2^448 = 2^224 + 1)
	mut c := u64(0)
	for _ in 0 .. 2 {
		for i := 0; i < 8; i++ {
			s := x.el[i] + c
			x.el[i] = s & mask_56bits
			c = s >> limbsize
		}
		// Fold carry modulo p = 2^448 - 2^224 - 1
		x.el[0] += c
		x.el[4] += c
		// Reset c to 0 because its value was consumed above.
		// Pass 2 will now sweep x.el[0..7] and extract any new
		// limb overflows created by x.el[0] += c and x.el[4] += c.
		c = 0
	}
	// Final ripple for any bit overflowing el[0] or el[4] after pass 2.
	// The issue: c was just added to x.el[0] and x.el[4], but no subsequent
	// sweep occurs to handle the case where x.el[0] or x.el[4]
	// overflow 56 bits as a result of that addition!
	x.el[1] += x.el[0] >> limbsize
	x.el[0] &= mask_56bits
	x.el[5] += x.el[4] >> limbsize
	x.el[4] &= mask_56bits
}

// fe_equal checks whether a == b, return 1 if it true, 0 otherwise
@[direct_array_access; inline]
fn fe_equal(a Field, b Field) bool {
	return fe_cmp(a, b) == 1
}

// fe_cmp compares the fields between a and b modulo p (fully reduces both first).
// Returns 1 if a == b (mod p), and 0 otherwise.
// This function is implemented to run in constant-time.
@[direct_array_access; inline]
fn fe_cmp(a Field, b Field) int {
	// First, reduce both elements to their canonical representation.
	mut x := a
	mut y := b
	fe_reduce(mut x)
	fe_reduce(mut y)

	// Compare the limbs in constant-time.
	// Any difference in any limb will set the bits in `c`.
	mut c := u64(0)
	// Compare x and y
	for i := 0; i < 8; i++ {
		// Constant time implementation
		c |= x.el[i] ^ y.el[i]
	}

	// Return 1 if equal (diff == 0), else 0 in constant-time
	return int(1 - ((c | (0 - c)) >> 63))
}

// fe_cselect set z to a if c == 1, and to b if c == 0
@[direct_array_access; inline]
fn fe_cselect(mut z Field, a Field, b Field, c int) {
	m := mask_64bits(c)
	// Select between a and b
	for i := 0; i < 8; i++ {
		// Constant time implementation
		z.el[i] = (a.el[i] & m) | (b.el[i] & ~m)
	}
}

// fe_cswap perform constant-time conditional swap, ie, swaps a and b if c == 1 or leaves them unchanged if c == 0.
@[direct_array_access; inline]
fn fe_cswap(mut a Field, mut b Field, c int) {
	// The mask is the all-1 or all-0 word
	m := mask_64bits(c)
	mut dummy := u64(0)

	// Conditional swap with constant time implementation
	for i := 0; i < 8; i++ {
		dummy = m & (a.el[i] ^ b.el[i])
		a.el[i] ^= dummy
		b.el[i] ^= dummy
	}
}

// fe_inverse performs modular multiplicative inverse, ie, z = 1/x
@[direct_array_access; inline]
fn fe_inverse(mut z Field, x Field) {
	mut t := Field{}
	fe_power446(mut t, x)
	fe_sqr(mut t, t)
	fe_sqr(mut t, t) // 2^448 - 2^224 - 4

	fe_mult(mut z, t, x) // 2^448 - 2^224 - 3
}

// fe_power446 sets v = v ⁽ᵖ⁻³⁾/⁴ (mod p), and returns v.
// where (p-3)/4 is 2⁴⁴⁶ - 2²²² - 1.
@[direct_array_access; inline]
fn fe_power446(mut v Field, z Field) {
	mut t1 := Field{}
	mut t2 := Field{}
	mut t3 := Field{}

	fe_sqr(mut t1, z) // 2^1
	fe_sqr(mut t2, t1) // 2^2
	fe_mult(mut t3, z, t1) //
	fe_mult(mut t3, t3, t2) // 2^3 - 1

	mut t6 := Field{} //
	fe_sqr(mut t6, t3)
	fe_sqr(mut t6, t6)
	fe_sqr(mut t6, t6)
	fe_mult(mut t6, t6, t3) // 2^6 - 1

	mut t9 := Field{}
	fe_sqr(mut t9, t6)
	fe_sqr(mut t9, t9)
	fe_sqr(mut t9, t9)
	fe_mult(mut t9, t9, t3) // 2^9 - 1

	mut t18 := Field{}
	fe_sqr(mut t18, t9)
	for i := 1; i < 9; i++ {
		fe_sqr(mut t18, t18)
	}
	fe_mult(mut t18, t18, t9) // 2^18 - 1

	mut t37 := Field{}
	fe_sqr(mut t37, t18)
	for i := 1; i < 18; i++ {
		fe_sqr(mut t37, t37)
	}
	fe_mult(mut t37, t37, t18)
	fe_sqr(mut t37, t37)
	fe_mult(mut t37, t37, z) // 2^37 - 1

	mut t111 := Field{}
	fe_sqr(mut t111, t37)
	for i := 1; i < 37; i++ {
		fe_sqr(mut t111, t111)
	}
	fe_mult(mut t111, t111, t37)
	for i := 0; i < 37; i++ {
		fe_sqr(mut t111, t111)
	}
	fe_mult(mut t111, t111, t37) // 2^111 - 1

	mut t222 := Field{}
	fe_sqr(mut t222, t111)
	for i := 1; i < 111; i++ {
		fe_sqr(mut t222, t222)
	}
	fe_mult(mut t222, t222, t111) // 2^222 - 1

	mut t223 := Field{}
	fe_sqr(mut t223, t222)
	fe_mult(mut t223, t223, z) // 2^223 - 1

	mut x := Field{}
	fe_sqr(mut x, t223)
	for i := 1; i < 223; i++ {
		fe_sqr(mut x, x)
	}
	fe_mult(mut v, x, t222) // 2^446 - 2^222 - 1
}

// If u/v is square, fe_sqrtratio computes the square root r and returns (r, 1).
// If u/v is not a square, it returns (r, 0).
// In both cases, r is set to u * (u*v)^((p-3)/4) (mod p).
@[direct_array_access; inline]
fn fe_sqrtratio(mut r Field, u Field, v Field) (Field, int) {
	mut uv := Field{}
	fe_mult(mut uv, u, v)
	fe_power446(mut uv, uv)
	fe_mult(mut r, u, uv)

	// Check if v * r^2 == u
	mut ck := Field{}
	fe_sqr(mut ck, r)
	fe_mult(mut ck, v, ck)

	is_square := fe_cmp(ck, u)

	return r, is_square
}

// fe_abs return absolute value of u, ie, |u| (mod p)
@[direct_array_access; inline]
fn fe_abs(mut z Field, u Field) {
	mut x := Field{}
	fe_negate(mut x, u)
	fe_cselect(mut z, x, u, u.is_negative())
}

@[direct_array_access; inline]
fn (v Field) is_negative() int {
	mut x := Field{}
	fe_clone(mut x, v)
	fe_reduce(mut x)
	return int(x.el[0] & 1)
}

// Helpers
//

// mask_64bits returns all-ones if cond is nonzero, all-zeros if cond == 0 --
// robust to any nonzero encoding of "true" (1, -1, 2, ...), not just exactly
// 1. Branchless: reuses the same "x | (-x) has its MSB set iff x != 0" trick
// already used in fe_cmp, so this stays constant-time.
@[inline]
fn mask_64bits(cond int) u64 {
	c := u64(cond)
	normalized := (c | (0 - c)) >> 63
	return u64(0) - normalized
}

// add_128 adds a + b
@[inline]
fn add_128(a unsigned.Uint128, b unsigned.Uint128) unsigned.Uint128 {
	return a.add(b)
}

// lsh_128 does a << 1
@[inline]
fn lsh_128(a unsigned.Uint128) unsigned.Uint128 {
	return unsigned.uint128_new(a.lo << 1, (a.hi << 1) | (a.lo >> 63))
}

// mult_64 creates Uint128 from two's 64-bit product of a*b
@[inline]
fn mult_64(a u64, b u64) unsigned.Uint128 {
	hi, lo := bits.mul_64(a, b)
	return unsigned.uint128_new(lo, hi)
}

// mult_56 returns (lo, hi) where lo + hi * 2^56 = a * b
@[inline]
fn mult_56(a u64, b u32) (u64, u64) {
	hh, ll := bits.mul_64(a, u64(b))
	lo := ll & mask_56bits
	hi := (hh << 8) | (ll >> limbsize)
	return lo, hi
}

// sub_128 subtracts b from a. Callers only use it when a >= b.
@[inline]
fn sub_128(a unsigned.Uint128, b unsigned.Uint128) unsigned.Uint128 {
	lo, borrow := bits.sub_64(a.lo, b.lo, 0)
	hi, _ := bits.sub_64(a.hi, b.hi, borrow)
	return unsigned.uint128_new(lo, hi)
}

// mul_4limb_schoolbook performs 4x4 limb schoolbook multiplication into a 7-element Uint128 array.
@[direct_array_access; inline]
fn mul_4limb_schoolbook(mut out [7]unsigned.Uint128, x0 u64, x1 u64, x2 u64, x3 u64, y0 u64, y1 u64, y2 u64, y3 u64) {
	// This routine accepts mut out [7]unsigned.Uint128, but it accumulates (add_128)
	// into out[i + j] without zeroing out first.
	// If out contains uninitialized memory or previous stack junk,
	// the products will be corrupted. so we initialize out to zero
	clear_uint128x7(mut out)
	mut x := [x0, x1, x2, x3]!
	mut y := [y0, y1, y2, y3]!
	for i := 0; i < 4; i++ {
		for j := 0; j < 4; j++ {
			out[i + j] = add_128(out[i + j], mult_64(x[i], y[j]))
		}
	}
	// clear_u64x4(mut x)
	// clear_u64x4(mut y)
}

// reduce_8limb_product reduces 8 128-bit accumulators down to an 8-limb 56-bit field element.
//
// Sequentially extracts full 128-bit carries (`(hi << 8) | (lo >> 56)`) to ensure zero
// upper-bit truncation before applying final Solinas reduction.
@[direct_array_access; inline]
fn reduce_8limb_product(mut z Field, mut t0 unsigned.Uint128, mut t1 unsigned.Uint128, mut t2 unsigned.Uint128, mut t3 unsigned.Uint128, mut t4 unsigned.Uint128, mut t5 unsigned.Uint128, mut t6 unsigned.Uint128, mut t7 unsigned.Uint128) {
	mut res := Field{}
	mut c := u64(0)

	// Step-by-step carry extraction across 128-bit limb accumulators
	t0 = t0.add(unsigned.uint128_new(c, 0))
	res.el[0] = t0.lo & mask_56bits
	c = (t0.hi << 8) | (t0.lo >> 56)

	t1 = t1.add(unsigned.uint128_new(c, 0))
	res.el[1] = t1.lo & mask_56bits
	c = (t1.hi << 8) | (t1.lo >> 56)

	t2 = t2.add(unsigned.uint128_new(c, 0))
	res.el[2] = t2.lo & mask_56bits
	c = (t2.hi << 8) | (t2.lo >> 56)

	t3 = t3.add(unsigned.uint128_new(c, 0))
	res.el[3] = t3.lo & mask_56bits
	c = (t3.hi << 8) | (t3.lo >> 56)

	t4 = t4.add(unsigned.uint128_new(c, 0))
	res.el[4] = t4.lo & mask_56bits
	c = (t4.hi << 8) | (t4.lo >> 56)

	t5 = t5.add(unsigned.uint128_new(c, 0))
	res.el[5] = t5.lo & mask_56bits
	c = (t5.hi << 8) | (t5.lo >> 56)

	t6 = t6.add(unsigned.uint128_new(c, 0))
	res.el[6] = t6.lo & mask_56bits
	c = (t6.hi << 8) | (t6.lo >> 56)

	t7 = t7.add(unsigned.uint128_new(c, 0))
	res.el[7] = t7.lo & mask_56bits
	c = (t7.hi << 8) | (t7.lo >> 56)

	// Reduce top carry using Solinas identity 2^448 = 2^224 + 1
	res.el[0] += c
	res.el[4] += c

	fe_weak_reduce(mut res)
	fe_clone(mut z, res)
}

@[direct_array_access; inline]
fn clear_u64x4(mut values [4]u64) {
	for i := 0; i < 4; i++ {
		values[i] = 0
	}
}

// clear_uint128x7 zeroes out a 7-element array of Uint128 values.
@[direct_array_access; inline]
fn clear_uint128x7(mut values [7]unsigned.Uint128) {
	zero := unsigned.uint128_new(0, 0)
	for i := 0; i < 7; i++ {
		values[i] = zero
	}
}

@[direct_array_access; inline]
fn clear_uint128x15(mut values [15]unsigned.Uint128) {
	zero := unsigned.uint128_new(0, 0)
	for i := 0; i < 15; i++ {
		values[i] = zero
	}
}

// fold_and_reduce_15limb folds a 15-limb unreduced product r[0..14] mod p = 2^448 - 2^224 - 1
// using the Solinas identity B^8 = B^4 + 1, then reduces it into z.
@[direct_array_access; inline]
fn fold_and_reduce_15limb(mut z Field, r [15]unsigned.Uint128) {
	// Pre-compute 2 * r[12..14]
	r12_x2 := lsh_128(r[12])
	r13_x2 := lsh_128(r[13])
	r14_x2 := lsh_128(r[14])

	// Fold polynomial limbs according to Solinas identity
	mut t0 := add_128(r[0], add_128(r[8], r[12]))
	mut t1 := add_128(r[1], add_128(r[9], r[13]))
	mut t2 := add_128(r[2], add_128(r[10], r[14]))
	mut t3 := add_128(r[3], r[11])

	mut t4 := add_128(r[4], add_128(r[8], r12_x2))
	mut t5 := add_128(r[5], add_128(r[9], r13_x2))
	mut t6 := add_128(r[6], add_128(r[10], r14_x2))
	mut t7 := add_128(r[7], r[11])

	// Pass accumulators to the 128-bit -> 56-bit carry sweep and reduction
	reduce_8limb_product(mut z, mut t0, mut t1, mut t2, mut t3, mut t4, mut t5, mut t6, mut t7)
}
