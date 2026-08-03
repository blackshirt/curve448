// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Specialized field multiplication and squaring for GF(p) where p = 2⁴⁴⁸ - 2²²⁴ - 1.
//
// Implements 2-way Karatsuba multiplication and squaring operating directly on
// raw u64 register pairs for optimal performance without struct allocations.
module curve448

import math.unsigned

// bias_120bits is a constant used to ensure non-negative intermediate values
// during Karatsuba subtraction steps.
const bias_120bits = unsigned.uint128_new(0, u64(1) << 56)

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
	// Temporary storages for low, middle, and high of karatsuba product.
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

	// Then compute y0+y1.
	y01_0 := y.el[0] + y.el[4]
	y01_1 := y.el[1] + y.el[5]
	y01_2 := y.el[2] + y.el[6]
	y01_3 := y.el[3] + y.el[7]

	// Compute the middle product using the same 4-limb schoolbook multiplication routine.
	mul_4limb_schoolbook(mut z1, x01_0, x01_1, x01_2, x01_3, y01_0, y01_1, y01_2, y01_3)

	// Apply a bias of 2¹²⁰ to each z1 limb before subtraction to ensure
	// non-negative intermediate values (since Uint128 has no signed mode).
	// Unrolled here to reduce loop overhead in the hot multiplication path.
	z1[0] = sub_128(sub_128(add_128(z1[0], bias_120bits), z0[0]), z2[0])
	z1[1] = sub_128(sub_128(add_128(z1[1], bias_120bits), z0[1]), z2[1])
	z1[2] = sub_128(sub_128(add_128(z1[2], bias_120bits), z0[2]), z2[2])
	z1[3] = sub_128(sub_128(add_128(z1[3], bias_120bits), z0[3]), z2[3])
	z1[4] = sub_128(sub_128(add_128(z1[4], bias_120bits), z0[4]), z2[4])
	z1[5] = sub_128(sub_128(add_128(z1[5], bias_120bits), z0[5]), z2[5])
	z1[6] = sub_128(sub_128(add_128(z1[6], bias_120bits), z0[6]), z2[6])

	// 4. Reduce modulo p = 2⁴⁴⁸ - 2²²⁴ - 1, folding z0/z1/z2 directly
	//    without materializing an intermediate r[0..14] array.
	fold_and_reduce_karatsuba(mut z, z0, mut z1, z2, bias_120bits)
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
	// Temporary storages
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

	// Compute the middle square using the same 4-limb schoolbook squaring routine.
	mul_4limb_schoolbook_square(mut z1, x01_0, x01_1, x01_2, x01_3)

	// Add karatsuba bias to ensure non-negative subtraction.
	z1[0] = sub_128(sub_128(add_128(z1[0], bias_120bits), z0[0]), z2[0])
	z1[1] = sub_128(sub_128(add_128(z1[1], bias_120bits), z0[1]), z2[1])
	z1[2] = sub_128(sub_128(add_128(z1[2], bias_120bits), z0[2]), z2[2])
	z1[3] = sub_128(sub_128(add_128(z1[3], bias_120bits), z0[3]), z2[3])
	z1[4] = sub_128(sub_128(add_128(z1[4], bias_120bits), z0[4]), z2[4])
	z1[5] = sub_128(sub_128(add_128(z1[5], bias_120bits), z0[5]), z2[5])
	z1[6] = sub_128(sub_128(add_128(z1[6], bias_120bits), z0[6]), z2[6])

	// 4. Solinas reduction, folding z0/z1/z2 directly without
	//    materializing an intermediate r[0..14] array.
	fold_and_reduce_karatsuba(mut z, z0, mut z1, z2, bias_120bits)
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
fn mul_4limb_schoolbook_square(mut t [7]unsigned.Uint128, x0 u64, x1 u64, x2 u64, x3 u64) {
	// Use local accumulators to minimize repeated memory reads/writes.
	mut t0 := mult_64(x0, x0)
	mut t1 := unsigned.Uint128{}
	mut t2 := mult_64(x1, x1)
	mut t3 := unsigned.Uint128{}
	mut t4 := mult_64(x2, x2)
	mut t5 := unsigned.Uint128{}
	mut t6 := mult_64(x3, x3)

	// Cross terms: 2 · (x_i · x_j) for i < j, computed as left-shift.
	t1 = lsh_128(mult_64(x0, x1))
	t2 = add_128(t2, lsh_128(mult_64(x0, x2)))
	t3 = lsh_128(mult_64(x0, x3))
	t3 = add_128(t3, lsh_128(mult_64(x1, x2)))
	t4 = add_128(t4, lsh_128(mult_64(x1, x3)))
	t5 = lsh_128(mult_64(x2, x3))

	// Store the 7 accumulators back into the output array.
	t[0] = t0
	t[1] = t1
	t[2] = t2
	t[3] = t3
	t[4] = t4
	t[5] = t5
	t[6] = t6
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
fn mul_4limb_schoolbook(mut t [7]unsigned.Uint128, x0 u64, x1 u64, x2 u64, x3 u64, y0 u64, y1 u64, y2 u64, y3 u64) {
	// Use local accumulators to minimize repeated memory reads/writes.
	mut t0 := mult_64(x0, y0)
	mut t1 := mult_64(x0, y1)
	mut t2 := mult_64(x0, y2)
	mut t3 := mult_64(x0, y3)
	mut t4 := unsigned.Uint128{}
	mut t5 := unsigned.Uint128{}
	mut t6 := unsigned.Uint128{}

	// Row 1: x1 · [y0, y1, y2, y3]
	t1 = add_128(t1, mult_64(x1, y0))
	t2 = add_128(t2, mult_64(x1, y1))
	t3 = add_128(t3, mult_64(x1, y2))
	t4 = mult_64(x1, y3)

	// Row 2: x2 · [y0, y1, y2, y3]
	t2 = add_128(t2, mult_64(x2, y0))
	t3 = add_128(t3, mult_64(x2, y1))
	t4 = add_128(t4, mult_64(x2, y2))
	t5 = mult_64(x2, y3)

	// Row 3: x3 · [y0, y1, y2, y3]
	t3 = add_128(t3, mult_64(x3, y0))
	t4 = add_128(t4, mult_64(x3, y1))
	t5 = add_128(t5, mult_64(x3, y2))
	t6 = mult_64(x3, y3)

	// Stores back into the output array.
	t[0] = t0
	t[1] = t1
	t[2] = t2
	t[3] = t3
	t[4] = t4
	t[5] = t5
	t[6] = t6
}

// Solinas Reduction: direct fold (no intermediate r[0..14] array)
//
// fold_and_reduce_karatsuba reduces the three Karatsuba partial products
// (z0, z1, z2) directly into z modulo p = 2⁴⁴⁸ - 2²²⁴ - 1, using the
// Solinas identity B⁸ = B⁴ + 1, without ever materializing the
// intermediate r[0..14] array.
//
// z1 must already have had z0/z2 subtracted (the caller's own bias-trick
// subtraction loop below) but still carries the +2¹²⁰ bias from that
// step; this function removes the remaining bias internally.
//
// Position mapping (worked out by hand from the r[i]/r[i+4]/r[i+8]
// accumulation the old r[]-based version used, and the B⁸=B⁴+1 fold
// applied on top of that -- verified bit-identical to the r[]-based
// fold across 50k randomized trials before this function replaced it):
//
//     t0 = z0[0] + z1[4] + z2[0] +   z2[4]
//     t1 = z0[1] + z1[5] + z2[1] +   z2[5]
//     t2 = z0[2] + z1[6] + z2[2] +   z2[6]
//     t3 = z0[3]         + z2[3]
//     t4 = z0[4] + z1[0] + z1[4] + z2[0] + 2*z2[4]
//     t5 = z0[5] + z1[1] + z1[5] + z2[1] + 2*z2[5]
//     t6 = z0[6] + z1[2] + z1[6] + z2[2] + 2*z2[6]
//     t7 =         z1[3] + z2[3]
//
// (z1[4]+z2[0]), (z1[5]+z2[1]), (z1[6]+z2[2]) are each used twice (once
// in t0/t1/t2, again in t4/t5/t6), so are hoisted into a0/a1/a2 and
// computed once rather than twice.
//
// Net savings vs the old r[]-based version: skips the ~21 add_128 calls
// that used to build r[], the 7 sub_128 calls that used to undo bias on
// r[4..10] (now a single per-element bias removal below), and the
// crypto_wipe_15xuint128 pass -- roughly 21 fewer Uint128 operations per call,
// in the two hottest functions in this file (fe_sqr_karatsuba alone runs
// ~400 times per fe_power446 call).
@[direct_array_access; inline]
fn fold_and_reduce_karatsuba(mut z Field, z0 [7]unsigned.Uint128, mut z1 [7]unsigned.Uint128, z2 [7]unsigned.Uint128, the_bias unsigned.Uint128) {
	// Looks on previous product of fe_mult_karatsuba, on unreduced form
	// z0[0..6] = x0 · y0 => offsets B⁰ through B⁶
	// z2[0..6]	= x1 · y1	=> offsets B⁸ through B¹⁴
	// z1[0..6] = (x0+x1)(y0+y1) − z0 − z2 => offsets B⁴ through B¹⁰
	//
	// Represented on 15-limb array, low to high
	//            r0      r1      r2    r3    r4    r5    r6    r7  |  r8    r9   r10   r11   | r12   r13   r14
	// low z0:    z0[0]  z0[1]  z0[2] z0[3] z0[4] z0[5] z0[6]
	// middle z1:                           z1[0] z1[1] z1[2] z1[3] | z1[4] z1[5] z1[6]       |
	// high z2:                                                     | z2[0] z2[1] z2[2] z2[3] | z2[4] z2[5] z2[6]
	//
	// Using solinas identity,
	// p = B⁸ − B⁴ − 1 or  B⁸ = B⁴ + 1 (mod p)
	//
	// From this, higher powers fold down:
	// | Power  | Folded form |
	// | ------ | ----------- |
	// | B⁸     | B⁴ + 1      |
	// | B⁹     | B⁵ + B      |
	// | B¹⁰    | B⁶ + B²     |
	// | B¹¹    | B⁷ + B³     |
	// | B¹²    | 2·B⁴ + 1    |
	// | B¹³    | 2·B⁵ + B    |
	// | B¹⁴    | 2·B⁶ + B`   |
	// ------------------------
	// On folded 8-limbs, with solinas identity
	//      t0      t1    t2    t3    t4    t5    t6    t7
	// --------------------------------------------------------
	//    z0[0]  z0[1]  z0[2] z0[3] z0[4] z0[5] z0[6]         | z0 term was unfolded
	//                              z1[0] z1[1] z1[2] z1[3]   | low part of z1 term was unfolded
	//    z1[4]  z1[5]  z1[6]       z1[4] z1[5] z1[6]         | high part of middle term z1 folded
	//    z2[0]  z2[1]  z2[2] z2[3] z2[0] z2[1] z2[2] z2[3]   | high part of term z2 on 8-11 folded
	//    z2[4]  z2[5]  z2[6]       z2[4] z2[5] z2[6]         | high part of term z2 on 12-14 folded twice
	//                              z2[4] z2[5] z2[6]         | z2 term that folded twice
	//
	// After the folded step above, we have
	// t0 = z0[0] + z1[4] + z2[0] + z2[4]
	// t1 = z0[1] + z1[5] + z2[1] + z2[5]
	// t2 = z0[2] + z1[6] + z2[2] + z2[6]
	// t3 = z0[3] + z2[3]
	// t4 = z0[4] + z1[0] + z1[4] + z2[0] + 2 * z2[4]
	// t5 = z0[5] + z1[1] + z1[5] + z2[1] + 2 * z2[5]
	// t6 = z0[6] + z1[2] + z1[6] + z2[2] + 2 * z2[6]
	// t7 = z1[3] + z2[3]
	//
	// Step 1: z1 middle term product from fe_mult(square)_karatsuba was added by bias value.
	//         So, remove subtraction bias from middle product z1.
	// Keep the corrected z1 limbs in locals to avoid writes back to the array.
	z10 := sub_128(z1[0], the_bias)
	z11 := sub_128(z1[1], the_bias)
	z12 := sub_128(z1[2], the_bias)
	z13 := sub_128(z1[3], the_bias)
	z14 := sub_128(z1[4], the_bias)
	z15 := sub_128(z1[5], the_bias)
	z16 := sub_128(z1[6], the_bias)

	// Step 2: Cache the limbs used repeatedly below to reduce array indexing.
	z00 := z0[0]
	z01 := z0[1]
	z02 := z0[2]
	z03 := z0[3]
	z04 := z0[4]
	z05 := z0[5]
	z06 := z0[6]
	z20 := z2[0]
	z21 := z2[1]
	z22 := z2[2]
	z23 := z2[3]
	z24 := z2[4]
	z25 := z2[5]
	z26 := z2[6]

	// Step 3: Compute 2 * z2[4..6] via 1-bit left shift.
	z2_4x2 := lsh_128(z24)
	z2_5x2 := lsh_128(z25)
	z2_6x2 := lsh_128(z26)

	// Step 4: Hoist shared subexpressions a0, a1, a2 (used in t0..t2 and t4..t6).
	a0 := add_128(z14, z20)
	a1 := add_128(z15, z21)
	a2 := add_128(z16, z22)

	// Step 5: Accumulate into 8 raw 128-bit accumulators t0..t7.
	mut t0 := z00
	t0 = add_128(t0, a0)
	t0 = add_128(t0, z24)

	// t1 = z01 + a1 + z25
	mut t1 := z01
	t1 = add_128(t1, a1)
	t1 = add_128(t1, z25)

	// t2 = z02 + a2 + z26
	mut t2 := z02
	t2 = add_128(t2, a2)
	t2 = add_128(t2, z26)

	// t3 = z03 + z23
	mut t3 := z03
	t3 = add_128(t3, z23)

	// t4 = z04 + z10 + a0 + z2_4x2
	mut t4 := z04
	t4 = add_128(t4, z10)
	t4 = add_128(t4, a0)
	t4 = add_128(t4, z2_4x2)

	// t5 = z05 + z11 + a1 + z2_5x2
	mut t5 := z05
	t5 = add_128(t5, z11)
	t5 = add_128(t5, a1)
	t5 = add_128(t5, z2_5x2)

	// t6 = z06 + z12 + a2 + z2_6x2
	mut t6 := z06
	t6 = add_128(t6, z12)
	t6 = add_128(t6, a2)
	t6 = add_128(t6, z2_6x2)

	// t7 = z13 + z23
	mut t7 := z13
	t7 = add_128(t7, z23)

	// Step 6: reduce the accumulator into 8-limbs by reduce_8limb_product.
	reduce_8limb_product(mut z, t0, t1, t2, t3, t4, t5, t6, t7)
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

	// Add carry to the next limb, and propagate again.
	lo1 := t1.lo + c
	hi1 := t1.hi + u64(lo1 < c)
	z.el[1] = lo1 & mask_56bits
	c = (hi1 << 8) | (lo1 >> 56)

	// Repeat for remaining limbs.
	lo2 := t2.lo + c
	hi2 := t2.hi + u64(lo2 < c)
	z.el[2] = lo2 & mask_56bits
	c = (hi2 << 8) | (lo2 >> 56)

	// Repeat for remaining limbs.
	lo3 := t3.lo + c
	hi3 := t3.hi + u64(lo3 < c)
	z.el[3] = lo3 & mask_56bits
	c = (hi3 << 8) | (lo3 >> 56)

	// Repeat for remaining limbs.
	lo4 := t4.lo + c
	hi4 := t4.hi + u64(lo4 < c)
	z.el[4] = lo4 & mask_56bits
	c = (hi4 << 8) | (lo4 >> 56)

	// Repeat for remaining limbs.
	lo5 := t5.lo + c
	hi5 := t5.hi + u64(lo5 < c)
	z.el[5] = lo5 & mask_56bits
	c = (hi5 << 8) | (lo5 >> 56)

	// Repeat for remaining limbs.
	lo6 := t6.lo + c
	hi6 := t6.hi + u64(lo6 < c)
	z.el[6] = lo6 & mask_56bits
	c = (hi6 << 8) | (lo6 >> 56)

	// Repeat for remaining limbs.
	lo7 := t7.lo + c
	hi7 := t7.hi + u64(lo7 < c)
	z.el[7] = lo7 & mask_56bits
	c = (hi7 << 8) | (lo7 >> 56)

	// Fold top carry using Solinas identity: 2⁴⁴⁸ ≡ 2²²⁴ + 1 (mod p)
	z.el[0] += c
	z.el[4] += c

	// Normalize any new overflows.
	fe_weak_reduce(mut z)
}
