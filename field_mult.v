// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Specialized field multiplication and squaring for GF(p) where p = 2⁴⁴⁸ - 2²²⁴ - 1.
//
// Implements 2-way Karatsuba multiplication and squaring operating directly on
// raw u64 register pairs for optimal performance without struct allocations.
module curve448

// fe_mult_karatsuba_raw multiplies two field elements using 2-way Karatsuba on raw u64 pairs: z = x * y (mod p).
@[direct_array_access; inline]
fn fe_mult_karatsuba_raw(mut z Field, x Field, y Field) {
	mut z0_lo := [7]u64{}
	mut z0_hi := [7]u64{}
	mut z1_lo := [7]u64{}
	mut z1_hi := [7]u64{}
	mut z2_lo := [7]u64{}
	mut z2_hi := [7]u64{}

	mul_4limb_schoolbook_raw(mut z0_lo, mut z0_hi, x.el[0], x.el[1], x.el[2], x.el[3], y.el[0],
		y.el[1], y.el[2], y.el[3])
	mul_4limb_schoolbook_raw(mut z2_lo, mut z2_hi, x.el[4], x.el[5], x.el[6], x.el[7], y.el[4],
		y.el[5], y.el[6], y.el[7])

	x01_0 := x.el[0] + x.el[4]
	x01_1 := x.el[1] + x.el[5]
	x01_2 := x.el[2] + x.el[6]
	x01_3 := x.el[3] + x.el[7]
	y01_0 := y.el[0] + y.el[4]
	y01_1 := y.el[1] + y.el[5]
	y01_2 := y.el[2] + y.el[6]
	y01_3 := y.el[3] + y.el[7]
	mul_4limb_schoolbook_raw(mut z1_lo, mut z1_hi, x01_0, x01_1, x01_2, x01_3, y01_0, y01_1, y01_2,
		y01_3)

	// Bias of 2^120 (same value fe_mult_karatsuba uses), applied and then
	// z0/z2 subtracted, per limb -- see fe_mult_karatsuba's comment for why
	// the bias is needed (Uint128/raw-pair arithmetic here is unsigned, so
	// this guarantees no underflow in the subtraction below).
	bias_lo := u64(0)
	bias_hi := u64(1) << 56

	for i := 0; i < 7; i++ {
		z1_lo[i], z1_hi[i] = add128_raw(z1_lo[i], z1_hi[i], bias_lo, bias_hi)
		z1_lo[i], z1_hi[i] = sub128_raw(z1_lo[i], z1_hi[i], z0_lo[i], z0_hi[i])
		z1_lo[i], z1_hi[i] = sub128_raw(z1_lo[i], z1_hi[i], z2_lo[i], z2_hi[i])
	}

	fold_and_reduce_raw(mut z, z0_lo, z0_hi, mut z1_lo, mut z1_hi, z2_lo, z2_hi, bias_lo, bias_hi)
}

// fe_sqr_karatsuba_raw is fe_sqr_karatsuba's raw-pair equivalent: z = x^2
// (mod p), using mul_4limb_schoolbook_square_raw (10 multiplications per
// sub-product) for the same ~37% multiplication-count reduction over the
// general multiply that fe_sqr_karatsuba gets from mul_4limb_schoolbook_square.
// Verified bit-identical output to fe_sqr_karatsuba across 200k+ randomized
// trials.
@[direct_array_access; inline]
fn fe_sqr_karatsuba_raw(mut z Field, x Field) {
	mut z0_lo := [7]u64{}
	mut z0_hi := [7]u64{}
	mut z1_lo := [7]u64{}
	mut z1_hi := [7]u64{}
	mut z2_lo := [7]u64{}
	mut z2_hi := [7]u64{}

	mul_4limb_schoolbook_square_raw(mut z0_lo, mut z0_hi, x.el[0], x.el[1], x.el[2], x.el[3])
	mul_4limb_schoolbook_square_raw(mut z2_lo, mut z2_hi, x.el[4], x.el[5], x.el[6], x.el[7])

	x01_0 := x.el[0] + x.el[4]
	x01_1 := x.el[1] + x.el[5]
	x01_2 := x.el[2] + x.el[6]
	x01_3 := x.el[3] + x.el[7]
	mul_4limb_schoolbook_square_raw(mut z1_lo, mut z1_hi, x01_0, x01_1, x01_2, x01_3)

	bias_lo := u64(0)
	bias_hi := u64(1) << 56

	for i := 0; i < 7; i++ {
		z1_lo[i], z1_hi[i] = add128_raw(z1_lo[i], z1_hi[i], bias_lo, bias_hi)
		z1_lo[i], z1_hi[i] = sub128_raw(z1_lo[i], z1_hi[i], z0_lo[i], z0_hi[i])
		z1_lo[i], z1_hi[i] = sub128_raw(z1_lo[i], z1_hi[i], z2_lo[i], z2_hi[i])
	}

	fold_and_reduce_raw(mut z, z0_lo, z0_hi, mut z1_lo, mut z1_hi, z2_lo, z2_hi, bias_lo, bias_hi)
}
