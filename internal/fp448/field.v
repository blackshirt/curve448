// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// This file contains low-level primitive in the mean of Galois-Field
// element over 448-bits for curve448 operations.
module fp448

import math.bits
import math.unsigned

// Field is an an opaque represents the field of 448-bits integer of GF modulo p = 2⁴⁴⁸ - 2²²⁴ - 1.
// Its represented as unsaturated (redundant) limb in the form of 8 of 56-bits limbs, ie:
//     t.e0*2⁰ + t.e1*2⁵⁶ + t.e2*2¹¹² + t.e3*2¹⁶⁸ + t.e4*2²²⁴ + t.e5*2²⁸⁰ + t.e6*2³³⁶ + t.e7*2³⁹²
//
@[noinit]
pub struct Field {
mut:
	// Between operations, all limbs are expected to be lower than 2⁵⁷ (ie, fits in 56-bits)
	el [8]u64
}

// new_field creates an empty field
@[inline]
pub fn new_field() Field {
	return fe_zero
}

// The size of field limb, in bits
const fe_limb_size = 56
// Masking value for field's limb value, ie, 0x00ff_ffff_ffff_ffff
const fe_masklow_56bits = u64(1) << 56 - 1

// zero field element
pub const fe_zero = Field{
	el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
}

// one field element
pub const fe_one = Field{
	el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
}

// fe_p is a prime modulus of the field, ie, p = 2⁴⁴⁸ - 2²²⁴ - 1
const fe_p = Field{
	el: [u64(0x00FF_FFFF_FFFF_FFFF), u64(0x00FF_FFFF_FFFF_FFFF), u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF), u64(0x00FF_FFFF_FFFF_FFFE), u64(0x00FF_FFFF_FFFF_FFFF),
		u64(0x00FF_FFFF_FFFF_FFFF), u64(0x00FF_FFFF_FFFF_FFFF)]!
}

// fe_add performs modular field addition, ie, sets z = a + b (mod p)
@[direct_array_access; inline]
pub fn fe_add(mut z Field, a Field, b Field) {
	mut c := []u64{len: 8}
	// perform limbs addition, fits in z limbs without getting worried for overflow
	for i := 0; i < 8; i++ {
		z.el[i] = a.el[i] + b.el[i]
		c[i] = z.el[i] >> fe_limb_size
		z.el[i] = (z.el[i] & fe_masklow_56bits)
	}

	// apply reduction
	z.el[0] += c[7]
	z.el[4] += c[7]
	for i := 1; i < 8; i++ {
		z.el[i] += c[i - 1]
	}
}

// fe_sub performs modular field subtraction, ie, z = a - b (mod p)
@[direct_array_access; inline]
pub fn fe_sub(mut z Field, a Field, b Field) {
	// Adds 2 * p into a, to make the subtraction won't underflow, and
	// then subtract with b.
	mut c := []u64{len: 8}
	for i := 0; i < 8; i++ {
		// left shift the p with 1 and get the carries
		z.el[i] = (a.el[i] + fe_p.el[i] << 1) - b.el[i]
		c[i] = z.el[i] >> fe_limb_size
		z.el[i] = z.el[i] & fe_masklow_56bits
	}
	// apply reduction
	z.el[0] += c[7]
	z.el[4] += c[7]
	for i := 1; i < 8; i++ {
		z.el[i] += c[i - 1]
	}
}

// fe_negate negates a (mod p), ie, z = - a (mod p)
@[direct_array_access; inline]
pub fn fe_negate(mut z Field, a Field) {
	// Add 2 * p, to guarantee the subtraction won't underflow, and
	// then subtract with a
	z.el[0] = u64(0x01fffffffffffffe) - a.el[0]
	z.el[1] = u64(0x01fffffffffffffe) - a.el[1]
	z.el[2] = u64(0x01fffffffffffffe) - a.el[2]
	z.el[3] = u64(0x01fffffffffffffe) - a.el[3]
	z.el[4] = u64(0x01fffffffffffffc) - a.el[4]
	z.el[5] = u64(0x01fffffffffffffe) - a.el[5]
	z.el[6] = u64(0x01fffffffffffffe) - a.el[6]
	z.el[7] = u64(0x01fffffffffffffe) - a.el[7]

	// propagates the carries
	mut c := []u64{len: 8}
	for i := 0; i < 8; i++ {
		c[i] = z.el[i] >> fe_limb_size
		z.el[i] = (z.el[i] & fe_masklow_56bits)
	}

	// apply reduction
	z.el[0] += c[7]
	z.el[4] += c[7]
	for i := 1; i < 8; i++ {
		z.el[i] += c[i - 1]
	}
}

// fe_clone clones x into z
@[direct_array_access; inline]
pub fn fe_clone(mut z Field, x Field) {
	for i := 0; i < 8; i++ {
		z.el[i] = x.el[i]
	}
}

// fe_mult multiplies a with b and stores into z, ie, z = a * b (mod p)
//
// This is the most intensive routines.
// TODO: optimize it with some well-known algorithm
@[direct_array_access]
pub fn fe_mult(mut z Field, x Field, y Field) {
	fe_mult_generic(mut z, x, y)
}

// fe_mult_generic is a general and unoptimized schoolbook field multiplication
@[direct_array_access; inline]
fn fe_mult_generic(mut z Field, x Field, y Field) {
	// Limb multiplication works like pen-and-paper columnar multiplication, but
	// with 56-bit limbs instead of digits.
	// 											  a7	a6	  a5	| a4	  a3	a2	  a1	a0
	//											  b7	b6	  b5	| b4	  b3	b2	  b1	b0	 x
	//											  ------------------------------------------------
	//								  			 | a7b0  a6b0  a5b0  | a4b0  a3b0  a2b0  a1b0  a0b0   +	
	//									    a7b1 | a6b1  a5b1  a4b1  | a3b1  a2b1  a1b1  a0b1		 +
	//								  a7b2  a6b2 | a5b2  a4b2  a3b2  | a2b2  a1b2  a0b2			 	 +
	//						    a7b3  a6b3  a5b3 | a4b3  a3b3  a2b3  | a1b3  a0b3					 +
	//					| a7b4  a6b4  a5b4  a4b4 | a3b4  a2b4  a1b4  | a0b4						 	 +
	//			   a7b5 | a6b5  a5b5  a4b5  a3b5 | a2b5  a1b5  a0b5	 |							 	 +
	// 		 a7b6  a6b6 | a5b6  a4b6  a3b6  a2b6 | a1b6  a0b6		 |							 	 +
	// a7b7  a6b7  a5b7 | a4b7  a3b7  a2b7  a1b7 | a0b7				 |							 	 +
	// ------------------------------------------------------------------------------------------
	// r14	 r13   r12	| r11    r10   r9	 r8	 |  r7	  r6	 r5	 |  r4    r3	 r2	  r1	r0
	//
	// As we know, p = 2⁴⁴⁸ - 2²²⁴ - 1 and we have reduction identity,
	// a * 2⁴⁴⁸ + b = a * (2²²⁴ + 1) + b
	// a * 2⁴⁴⁸ + b = a * 2²²⁴ + a + b
	//
	// we can use this to reduce the limbs that would overflow 448 bits.
	//  	r8  * 2⁴⁴⁸ 	=> r8 * 2²²⁴ * 2⁰ + r8 * 2⁰,
	//		r9  * 2⁵⁰⁴ 	=> r9 * 2⁴⁴⁸ * 2⁵⁶   	=> r9 * 2²²⁴ * 2⁵⁶ + r9 * 2⁵⁶
	// 		r10 * 2⁵⁶⁰ 	=> r10 * 2⁴⁴⁸ * 2¹¹²	=> r10 * 2²²⁴ * 2¹¹² + r10 * 2¹¹²
	// 		... etc
	// 		r12 * 2⁶⁷² 	=> r12 * 2⁴⁴⁸ + r12 * 2²²⁴
	//   				=> r12 * 2²²⁴ + r12 + r12 * 2²²⁴
	//   				=> 2 * r12 * 2²²⁴ + r12
	//
	// 			a7			a6	  			a5				| a4	  		  a3	a2	  		a1			a0
	//			b7			b6	  			b5				| b4	  		  b3	b2	  		b1			b0	 		x
	//			-----------------------------------------------------------------------------------------------------
	//			a7b0  		a6b0  			a5b0 			| a4b0  	 	  a3b0  a2b0  		a1b0  		a0b0  		+	
	//			a6b1  		a5b1  			a4b1 			| a3b1+a7b1  	  a2b1  a1b1  		a0b1  		a7b1	 	+
	//			a5b2  		a4b2  			a3b2+a7b2 		| a2b2+a6b2  	  a1b2  a0b2  		a7b2  		a6b2	 	+
	//			a4b3  		a3b3+a7b3  		a2b3+a6b3		| a1b3+a5b3  	  a0b3  a7b3  		a6b3  		a5b3	 	+
	//			a3b4+a7b4	a2b4+a6b4		a1b4+a5b4		| a0b4+a4b4	 	  a7b4  a6b4  		a5b4  		a4b4	 	+
	//			a2b5+a6b5  	a1b5+a5b5		a0b5+a4b5		| a3b5+a7b5+a7b5  a6b5 	a5b5  		a4b5  		a3b5+a7b5	+
	// 		 	a1b6+a5b6	a0b6+a4b6		a3b6+a7b6+a7b6 	| a2b6+a6b6+a6b6  a5b6  a4b6  	   	a3b6+a7b6 	a2b6+a6b6	+
	// 			a0b7+a4b7	a3b7+a7b7+a7b7 	a2b7+a6b7+a6b7	| a1b7+a5b7+a5b7  a4b7	a3b7+a7b7	a2b7+a6b7	a1b7+a5b7
	//			=========================================================================================================
	//			t7			t6				t5				  t4			  t3	t2			t1			t0
	//
	// unoptimizead a * b
	a0b0 := mult_64(x.el[0], y.el[0])
	a1b0 := mult_64(x.el[1], y.el[0])
	a2b0 := mult_64(x.el[2], y.el[0])
	a3b0 := mult_64(x.el[3], y.el[0])
	a4b0 := mult_64(x.el[4], y.el[0])
	a5b0 := mult_64(x.el[5], y.el[0])
	a6b0 := mult_64(x.el[6], y.el[0])
	a7b0 := mult_64(x.el[7], y.el[0])

	a0b1 := mult_64(x.el[0], y.el[1])
	a1b1 := mult_64(x.el[1], y.el[1])
	a2b1 := mult_64(x.el[2], y.el[1])
	a3b1 := mult_64(x.el[3], y.el[1])
	a4b1 := mult_64(x.el[4], y.el[1])
	a5b1 := mult_64(x.el[5], y.el[1])
	a6b1 := mult_64(x.el[6], y.el[1])
	a7b1 := mult_64(x.el[7], y.el[1])

	a0b2 := mult_64(x.el[0], y.el[2])
	a1b2 := mult_64(x.el[1], y.el[2])
	a2b2 := mult_64(x.el[2], y.el[2])
	a3b2 := mult_64(x.el[3], y.el[2])
	a4b2 := mult_64(x.el[4], y.el[2])
	a5b2 := mult_64(x.el[5], y.el[2])
	a6b2 := mult_64(x.el[6], y.el[2])
	a7b2 := mult_64(x.el[7], y.el[2])

	a0b3 := mult_64(x.el[0], y.el[3])
	a1b3 := mult_64(x.el[1], y.el[3])
	a2b3 := mult_64(x.el[2], y.el[3])
	a3b3 := mult_64(x.el[3], y.el[3])
	a4b3 := mult_64(x.el[4], y.el[3])
	a5b3 := mult_64(x.el[5], y.el[3])
	a6b3 := mult_64(x.el[6], y.el[3])
	a7b3 := mult_64(x.el[7], y.el[3])

	a0b4 := mult_64(x.el[0], y.el[4])
	a1b4 := mult_64(x.el[1], y.el[4])
	a2b4 := mult_64(x.el[2], y.el[4])
	a3b4 := mult_64(x.el[3], y.el[4])
	a4b4 := mult_64(x.el[4], y.el[4])
	a5b4 := mult_64(x.el[5], y.el[4])
	a6b4 := mult_64(x.el[6], y.el[4])
	a7b4 := mult_64(x.el[7], y.el[4])

	a0b5 := mult_64(x.el[0], y.el[5])
	a1b5 := mult_64(x.el[1], y.el[5])
	a2b5 := mult_64(x.el[2], y.el[5])
	a3b5 := mult_64(x.el[3], y.el[5])
	a4b5 := mult_64(x.el[4], y.el[5])
	a5b5 := mult_64(x.el[5], y.el[5])
	a6b5 := mult_64(x.el[6], y.el[5])
	a7b5 := mult_64(x.el[7], y.el[5])

	a0b6 := mult_64(x.el[0], y.el[6])
	a1b6 := mult_64(x.el[1], y.el[6])
	a2b6 := mult_64(x.el[2], y.el[6])
	a3b6 := mult_64(x.el[3], y.el[6])
	a4b6 := mult_64(x.el[4], y.el[6])
	a5b6 := mult_64(x.el[5], y.el[6])
	a6b6 := mult_64(x.el[6], y.el[6])
	a7b6 := mult_64(x.el[7], y.el[6])

	a0b7 := mult_64(x.el[0], y.el[7])
	a1b7 := mult_64(x.el[1], y.el[7])
	a2b7 := mult_64(x.el[2], y.el[7])
	a3b7 := mult_64(x.el[3], y.el[7])
	a4b7 := mult_64(x.el[4], y.el[7])
	a5b7 := mult_64(x.el[5], y.el[7])
	a6b7 := mult_64(x.el[6], y.el[7])
	a7b7 := mult_64(x.el[7], y.el[7])

	// t0 = a0b0 + a7b1 + a6b2 + a5b3 + a4b4 + a3b5+a7b5 + a2b6+a6b6 + a1b7+a5b7
	mut t0 := a0b0
	t0 = add_128(t0, a7b1)
	t0 = add_128(t0, a6b2)
	t0 = add_128(t0, a5b3)
	t0 = add_128(t0, a4b4)
	t0 = add_128(t0, a3b5)
	t0 = add_128(t0, a7b5)
	t0 = add_128(t0, a2b6)
	t0 = add_128(t0, a6b6)
	t0 = add_128(t0, a1b7)
	t0 = add_128(t0, a5b7)

	// t1 = a1b0 + a0b1 + a7b2 + a6b3 + a5b4 + a4b5 + a3b6+a7b6 + a2b7+a6b7
	mut t1 := a1b0
	t1 = add_128(t1, a0b1)
	t1 = add_128(t1, a7b2)
	t1 = add_128(t1, a6b3)
	t1 = add_128(t1, a5b4)
	t1 = add_128(t1, a4b5)
	t1 = add_128(t1, a3b6)
	t1 = add_128(t1, a7b6)
	t1 = add_128(t1, a2b7)
	t1 = add_128(t1, a6b7)

	// t2 = a2b0 + a1b1 + a0b2 + a7b3 + a6b4 + a5b5 + a4b6 + a3b7+a7b7
	mut t2 := add_128(a2b0, a1b1)
	t2 = add_128(t2, a0b2)
	t2 = add_128(t2, a7b3)
	t2 = add_128(t2, a6b4)
	t2 = add_128(t2, a5b5)
	t2 = add_128(t2, a4b6)
	t2 = add_128(t2, a3b7)
	t2 = add_128(t2, a7b7)

	// t3 = a3b0 a2b1 a1b2 a0b3 a7b4 a6b5 a5b6 a4b7
	mut t3 := add_128(a3b0, a2b1)
	t3 = add_128(t3, a1b2)
	t3 = add_128(t3, a0b3)
	t3 = add_128(t3, a7b4)
	t3 = add_128(t3, a6b5)
	t3 = add_128(t3, a5b6)
	t3 = add_128(t3, a4b7)

	// t4 = a4b0 + a3b1+a7b1 + a2b2+a6b2 + a1b3+a5b3 + a0b4+a4b4 + a3b5+a7b5+a7b5 + a2b6+a6b6+a6b6 + a1b7+a5b7+a5b7
	mut t4 := add_128(a4b0, a3b1)
	t4 = add_128(t4, a7b1)
	t4 = add_128(t4, a2b2)
	t4 = add_128(t4, a6b2)
	t4 = add_128(t4, a1b3)
	t4 = add_128(t4, a5b3)
	t4 = add_128(t4, a0b4)
	t4 = add_128(t4, a4b4)
	t4 = add_128(t4, a3b5)
	// left shift
	t4 = add_128(t4, lsh_128(a7b5))
	t4 = add_128(t4, a2b6)
	// left shift
	t4 = add_128(t4, lsh_128(a6b6))
	t4 = add_128(t4, a1b7)
	// left shift
	t4 = add_128(t4, lsh_128(a5b7))

	// t5 = a5b0 + a4b1 + a3b2+a7b2 + a2b3+a6b3 + a1b4+a5b4 + a0b5+a4b5 + a3b6+a7b6+a7b6 + a2b7+a6b7+a6b7
	mut t5 := add_128(a5b0, a4b1)
	t5 = add_128(t5, a3b2)
	t5 = add_128(t5, a7b2)
	t5 = add_128(t5, a2b3)
	t5 = add_128(t5, a6b3)
	t5 = add_128(t5, a1b4)
	t5 = add_128(t5, a5b4)
	t5 = add_128(t5, a0b5)
	t5 = add_128(t5, a4b5)
	t5 = add_128(t5, a3b6)
	// left shift
	t5 = add_128(t5, lsh_128(a7b6))
	t5 = add_128(t5, a2b7)
	// left shift
	t5 = add_128(t5, lsh_128(a6b7))

	// t6 = a6b0 + a5b1 + a4b2 + a3b3+a7b3 + a2b4+a6b4 + a1b5+a5b5 + a0b6+a4b6 +a3b7+a7b7+a7b7
	mut t6 := add_128(a6b0, a5b1)
	t6 = add_128(t6, a4b2)
	t6 = add_128(t6, a3b3)
	t6 = add_128(t6, a7b3)
	t6 = add_128(t6, a2b4)
	t6 = add_128(t6, a6b4)
	t6 = add_128(t6, a1b5)
	t6 = add_128(t6, a5b5)
	t6 = add_128(t6, a0b6)
	t6 = add_128(t6, a4b6)
	t6 = add_128(t6, a3b7)
	// left shift
	t6 = add_128(t6, lsh_128(a7b7))

	// t7 = a7b0 + a6b1 + a5b2 + a4b3 + a3b4+a7b4 + a2b5+a6b5 + a1b6+a5b6 + a0b7+a4b7
	mut t7 := add_128(a7b0, a6b1)
	t7 = add_128(t7, a5b2)
	t7 = add_128(t7, a4b3)
	t7 = add_128(t7, a3b4)
	t7 = add_128(t7, a7b4)
	t7 = add_128(t7, a2b5)
	t7 = add_128(t7, a6b5)
	t7 = add_128(t7, a1b6)
	t7 = add_128(t7, a5b6)
	t7 = add_128(t7, a0b7)
	t7 = add_128(t7, a4b7)

	// apply reduction
	mut c0 := shift_right_by56(mut t0)
	mut c1 := shift_right_by56(mut t1)
	mut c2 := shift_right_by56(mut t2)
	mut c3 := shift_right_by56(mut t3)
	mut c4 := shift_right_by56(mut t4)
	mut c5 := shift_right_by56(mut t5)
	mut c6 := shift_right_by56(mut t6)
	mut c7 := shift_right_by56(mut t7)

	z.el[0] = (t0.lo & fe_masklow_56bits) + c7
	z.el[1] = (t1.lo & fe_masklow_56bits) + c0
	z.el[2] = (t2.lo & fe_masklow_56bits) + c1
	z.el[3] = (t3.lo & fe_masklow_56bits) + c2
	z.el[4] = (t4.lo & fe_masklow_56bits) + c3 + c7
	z.el[5] = (t5.lo & fe_masklow_56bits) + c4
	z.el[6] = (t6.lo & fe_masklow_56bits) + c5
	z.el[7] = (t7.lo & fe_masklow_56bits) + c6

	// If there are carries generated, apply reduction step once more
	c0 = z.el[0] >> fe_limb_size
	c1 = z.el[1] >> fe_limb_size
	c2 = z.el[2] >> fe_limb_size
	c3 = z.el[3] >> fe_limb_size
	c4 = z.el[4] >> fe_limb_size
	c5 = z.el[5] >> fe_limb_size
	c6 = z.el[6] >> fe_limb_size
	c7 = z.el[7] >> fe_limb_size

	z.el[0] = (z.el[0] & fe_masklow_56bits) + c7
	z.el[1] = (z.el[1] & fe_masklow_56bits) + c0
	z.el[2] = (z.el[2] & fe_masklow_56bits) + c1
	z.el[3] = (z.el[3] & fe_masklow_56bits) + c2
	z.el[4] = (z.el[4] & fe_masklow_56bits) + c3 + c7
	z.el[5] = (z.el[5] & fe_masklow_56bits) + c4
	z.el[6] = (z.el[6] & fe_masklow_56bits) + c5
	z.el[7] = (z.el[7] & fe_masklow_56bits) + c6
}

// square squares a field, ie, z = a*a (mod p)
@[direct_array_access; inline]
pub fn fe_sqr(mut z Field, a Field) {
	fe_sqr_generic(mut z, a)
}

// fe_sqr_generic squares the field with generic way
@[direct_array_access; inline]
fn fe_sqr_generic(mut z Field, a Field) {
	// squaring works similar  with multiplication, but have special symmetric properties internally
	// between two's field multiplication, so its reduces calculation complexities
	// 											  a7	a6	  a5	| a4	  a3	a2	  a1	a0
	//											  a7	a6	  a5	| a4	  a3	a2	  a1	a0	 x
	//											  ------------------------------------------------
	//								  			 | a7a0  a6a0  a5a0  | a4a0  a3a0  a2a0  a1a0  a0a0   +	
	//									    a7a1 | a6a1  a5a1  a4a1  | a3a1  a2a1  a1a1  a0a1		 +
	//								  a7a2  a6a2 | a5a2  a4a2  a3a2  | a2a2  a1a2  a0a2			 	 +
	//						    a7a3  a6a3  a5a3 | a4a3  a3a3  a2a3  | a1a3  a0a3					 +
	//					| a7a4  a6a4  a5a4  a4a4 | a3a4  a2a4  a1a4  | a0a4						 	 +
	//			   a7a5 | a6a5  a5a5  a4a5  a3a5 | a2a5  a1a5  a0a5	 |							 	 +
	// 		 a7a6  a6a6 | a5a6  a4a6  a3a6  a2a6 | a1a6  a0a6		 |							 	 +
	// a7a7  a6a7  a5a7 | a4a7  a3a7  a2a7  a1a7 | a0a7				 |							 	 +
	// ------------------------------------------------------------------------------------------
	// r14	 r13   r12	| r11    r10   r9	 r8	 |  r7	  r6	 r5	 |  r4    r3	 r2	  r1	r0
	// -----------------------------------------------------------------------------------------------------
	// a7a0  		a6a0  			a5a0 			| a4a0  	 	  a3a0  a2a0  		a1a0  		a0a0  		+	
	// a6a1  		a5a1  			a4a1 			| a3a1+a7a1  	  a2a1  a1a1  		a0a1  		a7a1	 	+
	// a5a2  		a4a2  			a3a2+a7a2 		| a2a2+a6a2  	  a1a2  a0a2  		a7a2  		a6a2	 	+
	// a4a3  		a3a3+a7a3  		a2a3+a6a3		| a1a3+a5a3  	  a0a3  a7a3  		a6a3  		a5a3	 	+
	// a3a4+a7a4	a2a4+a6a4		a1a4+a5a4		| a0a4+a4a4	 	  a7a4  a6a4  		a5a4  		a4a4	 	+
	// a2a5+a6a5  	a1a5+a5a5		a0a5+a4a5		| a3a5+a7a5+a7a5  a6a5 	a5a5  		a4a5  		a3a5+a7a5	+
	// a1a6+a5a6	a0a6+a4a6		a3a6+a7a6+a7a6 	| a2a6+a6a6+a6a6  a5a6  a4a6  	   	a3a6+a7a6 	a2a6+a6a6	+
	// a0a7+a4a7	a3a7+a7a7+a7a7 	a2a7+a6a7+a6a7	| a1a7+a5a7+a5a7  a4a7	a3a7+a7a7	a2a7+a6a7	a1a7+a5a7
	// =========================================================================================================
	// t7			t6				t5				  t4			  t3	t2			t1			t0
	//
	// unoptimizead a * a
	// we have properties for symmetric field, aᵢ.aⱼ = aⱼ.aᵢ
	// so, we dont have need to recalculate some field products.
	a0a0 := mult_64(a.el[0], a.el[0])
	a1a0 := mult_64(a.el[1], a.el[0]) // = a0a1
	a2a0 := mult_64(a.el[2], a.el[0]) // = a0a2
	a3a0 := mult_64(a.el[3], a.el[0]) // = a0a3
	a4a0 := mult_64(a.el[4], a.el[0]) // = a0a4
	a5a0 := mult_64(a.el[5], a.el[0]) // = a0a5
	a6a0 := mult_64(a.el[6], a.el[0]) // = a0a6
	a7a0 := mult_64(a.el[7], a.el[0]) // = a0a7

	a1a1 := mult_64(a.el[1], a.el[1])
	a2a1 := mult_64(a.el[2], a.el[1])
	a3a1 := mult_64(a.el[3], a.el[1])
	a4a1 := mult_64(a.el[4], a.el[1])
	a5a1 := mult_64(a.el[5], a.el[1])
	a6a1 := mult_64(a.el[6], a.el[1])
	a7a1 := mult_64(a.el[7], a.el[1])

	a2a2 := mult_64(a.el[2], a.el[2])
	a3a2 := mult_64(a.el[3], a.el[2])
	a4a2 := mult_64(a.el[4], a.el[2])
	a5a2 := mult_64(a.el[5], a.el[2])
	a6a2 := mult_64(a.el[6], a.el[2])
	a7a2 := mult_64(a.el[7], a.el[2])

	a3a3 := mult_64(a.el[3], a.el[3])
	a4a3 := mult_64(a.el[4], a.el[3])
	a5a3 := mult_64(a.el[5], a.el[3])
	a6a3 := mult_64(a.el[6], a.el[3])
	a7a3 := mult_64(a.el[7], a.el[3])

	a4a4 := mult_64(a.el[4], a.el[4])
	a5a4 := mult_64(a.el[5], a.el[4])
	a6a4 := mult_64(a.el[6], a.el[4])
	a7a4 := mult_64(a.el[7], a.el[4])

	a5a5 := mult_64(a.el[5], a.el[5])
	a6a5 := mult_64(a.el[6], a.el[5])
	a7a5 := mult_64(a.el[7], a.el[5])

	a6a6 := mult_64(a.el[6], a.el[6])
	a7a6 := mult_64(a.el[7], a.el[6])

	a7a7 := mult_64(a.el[7], a.el[7])

	// t0 = a0a0 + a4a4 + a6a6 + (a7a1+a1a7) + (a6a2+ a2a6) + (a5a3+ a3a5)  + (a5a7+a7a5)
	mut t0 := add_128(a0a0, a4a4)
	t0 = add_128(t0, a6a6)
	t0 = add_128(t0, lsh_128(a7a1))
	t0 = add_128(t0, lsh_128(a6a2))
	t0 = add_128(t0, lsh_128(a5a3))
	t0 = add_128(t0, lsh_128(a7a5))

	// t1 = (a1a0 + a0a1) + (a7a2+ a2a7) + (a6a3+ a3a6) + (a5a4 + a4a5) + (a7a6 +a6a7)
	mut t1 := lsh_128(a1a0)
	t1 = add_128(t1, lsh_128(a7a2))
	t1 = add_128(t1, lsh_128(a6a3))
	t1 = add_128(t1, lsh_128(a5a4))
	t1 = add_128(t1, lsh_128(a7a6))

	// t2 = a1a1 + a5a5 + a7a7 + (a2a0+ a0a2) + (a7a3+ a3a7) + (a6a4+ a4a6)
	mut t2 := add_128(a1a1, a5a5)
	t2 = add_128(t2, a7a7)
	t2 = add_128(t2, lsh_128(a2a0))
	t2 = add_128(t2, lsh_128(a7a3))
	t2 = add_128(t2, lsh_128(a6a4))

	// t3 = (a3a0+ a0a3) + (a2a1+a1a2) + (a7a4+ a4a7) + (a6a5 + a5a6)
	mut t3 := lsh_128(a3a0)
	t3 = add_128(t3, lsh_128(a2a1))
	t3 = add_128(t3, lsh_128(a7a4))
	t3 = add_128(t3, lsh_128(a6a5))

	// t4 = a2a2 + a4a4 + (a4a0+a0a4) + (a3a1+a1a3) + (a7a1+a1a7) + (a2a6+a6a2) + (a5a3+a3a5)  + (a7a5+a7a5+a5a7+a5a7) + (a6a6+a6a6)
	mut t4 := add_128(a2a2, a4a4)
	t4 = add_128(t4, lsh_128(a4a0))
	t4 = add_128(t4, lsh_128(a3a1))
	t4 = add_128(t4, lsh_128(a7a1))
	t4 = add_128(t4, lsh_128(a6a2))
	t4 = add_128(t4, lsh_128(a5a3))
	t4 = add_128(t4, lsh_256(a7a5))
	t4 = add_128(t4, lsh_128(a6a6))

	// t5 = (a5a0+a0a5) + (a4a1+a1a4) + (a3a2+a2a3) + (a7a2+a2a7) + (a6a3 + a3a6) + (a5a4+a4a5) + (a7a6+a7a6+a6a7+a6a7)
	mut t5 := lsh_128(a5a0)
	t5 = add_128(t5, lsh_128(a4a1))
	t5 = add_128(t5, lsh_128(a3a2))
	t5 = add_128(t5, lsh_128(a7a2))
	t5 = add_128(t5, lsh_128(a6a3))
	t5 = add_128(t5, lsh_128(a5a4))
	t5 = add_128(t5, lsh_256(a7a6))

	// t6 = a3a3 + a5a5 + (a6a0+a0a6) + (a5a1+a1a5) + (a4a2+a2a4) + (a7a3+a3a7) + (a6a4+a4a6) + (a7a7+a7a7)
	mut t6 := add_128(a3a3, a5a5)
	t6 = add_128(t6, lsh_128(a6a0))
	t6 = add_128(t6, lsh_128(a5a1))
	t6 = add_128(t6, lsh_128(a4a2))
	t6 = add_128(t6, lsh_128(a7a3))
	t6 = add_128(t6, lsh_128(a6a4))
	t6 = add_128(t6, lsh_128(a7a7))

	// t7 = (a7a0+a0a7) + (a6a1+a1a6) + (a5a2+a2a5) + (a4a3+a3a4) + (a7a4+a4a7) + (a6a5+a5a6)
	mut t7 := lsh_128(a7a0)
	t7 = add_128(t7, lsh_128(a6a1))
	t7 = add_128(t7, lsh_128(a5a2))
	t7 = add_128(t7, lsh_128(a4a3))
	t7 = add_128(t7, lsh_128(a7a4))
	t7 = add_128(t7, lsh_128(a6a5))

	// apply reduction
	mut c0 := shift_right_by56(mut t0)
	mut c1 := shift_right_by56(mut t1)
	mut c2 := shift_right_by56(mut t2)
	mut c3 := shift_right_by56(mut t3)
	mut c4 := shift_right_by56(mut t4)
	mut c5 := shift_right_by56(mut t5)
	mut c6 := shift_right_by56(mut t6)
	mut c7 := shift_right_by56(mut t7)

	z.el[0] = (t0.lo & fe_masklow_56bits) + c7
	z.el[1] = (t1.lo & fe_masklow_56bits) + c0
	z.el[2] = (t2.lo & fe_masklow_56bits) + c1
	z.el[3] = (t3.lo & fe_masklow_56bits) + c2
	z.el[4] = (t4.lo & fe_masklow_56bits) + c3 + c7
	z.el[5] = (t5.lo & fe_masklow_56bits) + c4
	z.el[6] = (t6.lo & fe_masklow_56bits) + c5
	z.el[7] = (t7.lo & fe_masklow_56bits) + c6

	// If there are carries generated, apply reduction step once more
	c0 = z.el[0] >> fe_limb_size
	c1 = z.el[1] >> fe_limb_size
	c2 = z.el[2] >> fe_limb_size
	c3 = z.el[3] >> fe_limb_size
	c4 = z.el[4] >> fe_limb_size
	c5 = z.el[5] >> fe_limb_size
	c6 = z.el[6] >> fe_limb_size
	c7 = z.el[7] >> fe_limb_size

	z.el[0] = (z.el[0] & fe_masklow_56bits) + c7
	z.el[1] = (z.el[1] & fe_masklow_56bits) + c0
	z.el[2] = (z.el[2] & fe_masklow_56bits) + c1
	z.el[3] = (z.el[3] & fe_masklow_56bits) + c2
	z.el[4] = (z.el[4] & fe_masklow_56bits) + c3 + c7
	z.el[5] = (z.el[5] & fe_masklow_56bits) + c4
	z.el[6] = (z.el[6] & fe_masklow_56bits) + c5
	z.el[7] = (z.el[7] & fe_masklow_56bits) + c6
}

// fe_mult_32 multiplies x with u32 (mod p)
@[direct_array_access; inline]
pub fn fe_mult_32(mut z Field, x Field, y u32) {
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
}

// set_bytes sets the field values from bytes array
@[direct_array_access; inline]
pub fn (mut z Field) set_bytes(b []u8) {
	if b.len != 56 {
		panic('bad set_bytes input')
	}
	// in little-endian form
	z.el[0] = u64(b[0]) | u64(b[1]) << 8 | u64(b[2]) << 16 | u64(b[3]) << 24 | u64(b[4]) << 32 | u64(b[5]) << 40 | u64(b[6]) << 48
	z.el[1] = u64(b[7]) | u64(b[8]) << 8 | u64(b[9]) << 16 | u64(b[10]) << 24 | u64(b[11]) << 32 | u64(b[12]) << 40 | u64(b[13]) << 48
	z.el[2] = u64(b[14]) | u64(b[15]) << 8 | u64(b[16]) << 16 | u64(b[17]) << 24 + u64(b[18]) << 32 | u64(b[19]) << 40 | u64(b[20]) << 48
	z.el[3] = u64(b[21]) | u64(b[22]) << 8 | u64(b[23]) << 16 | u64(b[24]) << 24 + u64(b[25]) << 32 | u64(b[26]) << 40 | u64(b[27]) << 48
	z.el[4] = u64(b[28]) | u64(b[29]) << 8 | u64(b[30]) << 16 | u64(b[31]) << 24 + u64(b[32]) << 32 | u64(b[33]) << 40 | u64(b[34]) << 48
	z.el[5] = u64(b[35]) | u64(b[36]) << 8 | u64(b[37]) << 16 | u64(b[38]) << 24 + u64(b[39]) << 32 | u64(b[40]) << 40 | u64(b[41]) << 48
	z.el[6] = u64(b[42]) | u64(b[43]) << 8 | u64(b[44]) << 16 | u64(b[45]) << 24 + u64(b[46]) << 32 | u64(b[47]) << 40 | u64(b[48]) << 48
	z.el[7] = u64(b[49]) | u64(b[50]) << 8 | u64(b[51]) << 16 | u64(b[52]) << 24 + u64(b[53]) << 32 | u64(b[54]) << 40 | u64(b[55]) << 48
}

// bytes serializes reduced x field into bytes
@[direct_array_access; inline]
pub fn (mut x Field) bytes() []u8 {
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

	// serialized in little-endian form
	dst[0] = u8(x.el[0])
	dst[1] = u8(x.el[0] >> u64(8))
	dst[2] = u8(x.el[0] >> u64(16))
	dst[3] = u8(x.el[0] >> u64(24))
	dst[4] = u8(x.el[0] >> u64(32))
	dst[5] = u8(x.el[0] >> u64(40))
	dst[6] = u8(x.el[0] >> u64(48))

	dst[7] = u8(x.el[1])
	dst[8] = u8(x.el[1] >> u64(8))
	dst[9] = u8(x.el[1] >> u64(16))
	dst[10] = u8(x.el[1] >> u64(24))
	dst[11] = u8(x.el[1] >> u64(32))
	dst[12] = u8(x.el[1] >> u64(40))
	dst[13] = u8(x.el[1] >> u64(48))

	dst[14] = u8(x.el[2])
	dst[15] = u8(x.el[2] >> u64(8))
	dst[16] = u8(x.el[2] >> u64(16))
	dst[17] = u8(x.el[2] >> u64(24))
	dst[18] = u8(x.el[2] >> u64(32))
	dst[19] = u8(x.el[2] >> u64(40))
	dst[20] = u8(x.el[2] >> u64(48))

	dst[21] = u8(x.el[3])
	dst[22] = u8(x.el[3] >> u64(8))
	dst[23] = u8(x.el[3] >> u64(16))
	dst[24] = u8(x.el[3] >> u64(24))
	dst[25] = u8(x.el[3] >> u64(32))
	dst[26] = u8(x.el[3] >> u64(40))
	dst[27] = u8(x.el[3] >> u64(48))

	dst[28] = u8(x.el[4])
	dst[29] = u8(x.el[4] >> u64(8))
	dst[30] = u8(x.el[4] >> u64(16))
	dst[31] = u8(x.el[4] >> u64(24))
	dst[32] = u8(x.el[4] >> u64(32))
	dst[33] = u8(x.el[4] >> u64(40))
	dst[34] = u8(x.el[4] >> u64(48))

	dst[35] = u8(x.el[5])
	dst[36] = u8(x.el[5] >> u64(8))
	dst[37] = u8(x.el[5] >> u64(16))
	dst[38] = u8(x.el[5] >> u64(24))
	dst[39] = u8(x.el[5] >> u64(32))
	dst[40] = u8(x.el[5] >> u64(40))
	dst[41] = u8(x.el[5] >> u64(48))

	dst[42] = u8(x.el[6])
	dst[43] = u8(x.el[6] >> u64(8))
	dst[44] = u8(x.el[6] >> u64(16))
	dst[45] = u8(x.el[6] >> u64(24))
	dst[46] = u8(x.el[6] >> u64(32))
	dst[47] = u8(x.el[6] >> u64(40))
	dst[48] = u8(x.el[6] >> u64(48))

	dst[49] = u8(x.el[7])
	dst[50] = u8(x.el[7] >> u64(8))
	dst[51] = u8(x.el[7] >> u64(16))
	dst[52] = u8(x.el[7] >> u64(24))
	dst[53] = u8(x.el[7] >> u64(32))
	dst[54] = u8(x.el[7] >> u64(40))
	dst[55] = u8(x.el[7] >> u64(48))
}

// fe_reduce reduces x field (mod p)
@[direct_array_access; inline]
fn fe_reduce(mut x Field) {
	// by the light reduction, we have a field element representation
	// x < 2⁴⁴⁸ + 2²³² + 2⁸, but we need x < 2⁴⁴⁸ - 2²²⁴ - 1 (p).
	fe_carry_propagates(mut x)

	// If x >= 2⁴⁴⁸ - 2²²⁴ - 1, then x + 2²²⁴ + 1 >= 2⁴⁴⁸, which would overflow 2⁴⁴⁸ - 1,
	// ie, generating a carry. That is, c will be 0 if x < 2⁴⁴⁸ - 2²²⁴ - 1, and 1 otherwise.
	// Add 1 + 2²²⁴ to test carry generation
	mut c := u64(0)
	c = (x.el[0] + 1) >> fe_limb_size
	c = (x.el[1] + c) >> fe_limb_size
	c = (x.el[2] + c) >> fe_limb_size
	c = (x.el[3] + c) >> fe_limb_size
	c = (x.el[4] + c + 1) >> fe_limb_size
	c = (x.el[5] + c) >> fe_limb_size
	c = (x.el[6] + c) >> fe_limb_size
	c = (x.el[7] + c) >> fe_limb_size

	// If x < 2⁴⁴⁸ - 2²²⁴ - 1 and c = 0, this will be a no-op. Otherwise,
	// it's effectively applying the reduction identity to the carry.
	x.el[0] += c
	x.el[4] += c

	// additional carry
	x.el[1] += (x.el[0] >> fe_limb_size)
	x.el[0] &= fe_masklow_56bits

	x.el[2] += (x.el[1] >> fe_limb_size)
	x.el[1] &= fe_masklow_56bits

	x.el[3] += (x.el[2] >> fe_limb_size)
	x.el[2] &= fe_masklow_56bits

	x.el[4] += (x.el[3] >> fe_limb_size)
	x.el[3] &= fe_masklow_56bits

	x.el[5] += (x.el[4] >> fe_limb_size)
	x.el[4] &= fe_masklow_56bits

	x.el[6] += (x.el[5] >> fe_limb_size)
	x.el[5] &= fe_masklow_56bits

	x.el[7] += (x.el[6] >> fe_limb_size)
	x.el[6] &= fe_masklow_56bits

	// no additional carry
	x.el[7] &= fe_masklow_56bits
}

// carry_propagates brings the limbs below 56 bits by applying the reduction
@[direct_array_access; inline]
fn fe_carry_propagates(mut x Field) {
	// gets the carries for every limbs
	mut c := []u64{len: 8}
	for i := 0; i < 8; i++ {
		c[i] = x.el[i] >> fe_limb_size
	}

	// the modulo identity was p = 2⁴⁴⁸- 2²²⁴ - 1, ie, 2⁴⁴⁸ = 2²²⁴+1 (mod p)
	x.el[0] = (x.el[0] & fe_masklow_56bits) + c[7]
	x.el[1] = (x.el[1] & fe_masklow_56bits) + c[0]
	x.el[2] = (x.el[2] & fe_masklow_56bits) + c[1]
	x.el[3] = (x.el[3] & fe_masklow_56bits) + c[2]
	x.el[4] = (x.el[4] & fe_masklow_56bits) + c[3] + c[7]
	x.el[5] = (x.el[5] & fe_masklow_56bits) + c[4]
	x.el[6] = (x.el[6] & fe_masklow_56bits) + c[5]
	x.el[7] = (x.el[7] & fe_masklow_56bits) + c[6]
}

// fe_equal checks whether a == b, return 1 if it true, 0 otherwise
@[direct_array_access; inline]
pub fn fe_equal(a Field, b Field) bool {
	return fe_cmp(a, b) == 1
}

// fe_cmp compares the unreduced fields between a and b
@[direct_array_access; inline]
pub fn fe_cmp(a Field, b Field) int {
	// Initialize mask
	mut c := u64(0)
	// Compare a and b
	for i := 0; i < 8; i++ {
		// Constant time implementation
		c |= a.el[i] ^ b.el[i]
	}
	c = (c & 0xFFFFFFFF) | (c >> 32)
	c--
	// returns 1 if the a = b, else 0
	return int(c >> 63)
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
pub fn fe_cswap(mut a Field, mut b Field, c int) {
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
pub fn fe_inverse(mut z Field, x Field) {
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

// If u/v is square, fe_sqrtratio returns r and 0.
@[direct_array_access; inline]
pub fn fe_sqrtratio(mut r Field, u Field, v Field) (Field, int) {
	mut uv := Field{}
	fe_mult(mut uv, u, v)
	fe_power446(mut uv, uv)
	fe_mult(mut r, u, uv)

	mut ck := Field{}
	fe_sqr(mut ck, r)
	fe_mult(mut ck, v, ck)
	ws := fe_cmp(ck, u)

	return r, ws
}

// fe_abs return absolute value of u, ie, |u| (mod p)
@[direct_array_access; inline]
pub fn fe_abs(mut z Field, u Field) {
	mut x := Field{}
	fe_negate(mut x, u)
	fe_cselect(mut z, x, u, u.is_negative())
}

@[direct_array_access; inline]
pub fn (v Field) is_negative() int {
	mut x := Field{}
	fe_clone(mut x, v)
	fe_reduce(mut x)
	return int(x.el[0] & 1)
}

// Helpers
//

// mask_64bits returns u64(max_u64) if cond is 1, and 0 otherwise.
@[inline]
fn mask_64bits(cond int) u64 {
	return u64(0) - u64(cond)
}

// shift_right_by56 returns a >> 56. a is assumed to be at most 117 bits.
@[inline]
fn shift_right_by56(mut a unsigned.Uint128) u64 {
	return (a.hi << 8) | (a.lo >> 56)
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

// lsh_256 does a << 2
@[inline]
fn lsh_256(a unsigned.Uint128) unsigned.Uint128 {
	return unsigned.uint128_new(a.lo << 2, (a.hi << 2) | (a.lo >> 62))
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
	lo := ll & fe_masklow_56bits
	hi := (hh << 8) | (ll >> fe_limb_size)
	return lo, hi
}
