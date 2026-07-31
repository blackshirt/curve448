// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Specialized field multiplication and squaring for GF(p) where p = 2⁴⁴⁸ - 2²²⁴ - 1.
//
// Implements three multiplication variants:
// 1. Generic pen-and-paper schoolbook multiplication (reference implementation).
// 2. 2-way Karatsuba multiplication using unsigned.Uint128 struct accumulators.
// 3. Optimized 2-way Karatsuba multiplication operating directly on raw u64 register pairs
//    (default high-performance backend).
module curve448

import math.unsigned

// fe_mult_generic is a general reference schoolbook field multiplication: z = x · y (mod p).
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
	mut c0 := shift_right_by56(t0)
	mut c1 := shift_right_by56(t1)
	mut c2 := shift_right_by56(t2)
	mut c3 := shift_right_by56(t3)
	mut c4 := shift_right_by56(t4)
	mut c5 := shift_right_by56(t5)
	mut c6 := shift_right_by56(t6)
	mut c7 := shift_right_by56(t7)

	z.el[0] = (t0.lo & mask_56bits) + c7
	z.el[1] = (t1.lo & mask_56bits) + c0
	z.el[2] = (t2.lo & mask_56bits) + c1
	z.el[3] = (t3.lo & mask_56bits) + c2
	z.el[4] = (t4.lo & mask_56bits) + c3 + c7
	z.el[5] = (t5.lo & mask_56bits) + c4
	z.el[6] = (t6.lo & mask_56bits) + c5
	z.el[7] = (t7.lo & mask_56bits) + c6

	// If there are carries generated, apply reduction step once more
	c0 = z.el[0] >> limb_bits_size
	c1 = z.el[1] >> limb_bits_size
	c2 = z.el[2] >> limb_bits_size
	c3 = z.el[3] >> limb_bits_size
	c4 = z.el[4] >> limb_bits_size
	c5 = z.el[5] >> limb_bits_size
	c6 = z.el[6] >> limb_bits_size
	c7 = z.el[7] >> limb_bits_size

	z.el[0] = (z.el[0] & mask_56bits) + c7
	z.el[1] = (z.el[1] & mask_56bits) + c0
	z.el[2] = (z.el[2] & mask_56bits) + c1
	z.el[3] = (z.el[3] & mask_56bits) + c2
	z.el[4] = (z.el[4] & mask_56bits) + c3 + c7
	z.el[5] = (z.el[5] & mask_56bits) + c4
	z.el[6] = (z.el[6] & mask_56bits) + c5
	z.el[7] = (z.el[7] & mask_56bits) + c6

	// FIX: the two passes above use independent, parallel carry extraction
	// (each c_i computed from the *original* t_i / z_i of that pass, not a
	// running ripple), so unlike a sequential ripple, dirt from one pass's
	// fold-back can land on a limb that pass already finished processing.
	// For typical inputs this resolves within 2 passes, but for operands
	// near p specifically it does not: (p-1)*(p-1) leaves el[0] = mask+1,
	// and a sweep of operand pairs near p-1 left an unmasked limb in every
	// single case tested (up to mask+13). The computed *value* was always
	// correct mod p in every case -- this only affects the per-limb <=
	// mask_56bits normalization every other multiply/square path in this
	// file guarantees on return. One more pass (via fe_weak_reduce, already
	// proven to correctly absorb carries far larger than this) closes it;
	// verified against the same near-p-1 sweep plus 100k random trials with
	// zero remaining unmasked-limb cases and zero correctness regressions.
	fe_weak_reduce_1pass(mut z)
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
	mut c0 := shift_right_by56(t0)
	mut c1 := shift_right_by56(t1)
	mut c2 := shift_right_by56(t2)
	mut c3 := shift_right_by56(t3)
	mut c4 := shift_right_by56(t4)
	mut c5 := shift_right_by56(t5)
	mut c6 := shift_right_by56(t6)
	mut c7 := shift_right_by56(t7)

	z.el[0] = (t0.lo & mask_56bits) + c7
	z.el[1] = (t1.lo & mask_56bits) + c0
	z.el[2] = (t2.lo & mask_56bits) + c1
	z.el[3] = (t3.lo & mask_56bits) + c2
	z.el[4] = (t4.lo & mask_56bits) + c3 + c7
	z.el[5] = (t5.lo & mask_56bits) + c4
	z.el[6] = (t6.lo & mask_56bits) + c5
	z.el[7] = (t7.lo & mask_56bits) + c6

	// If there are carries generated, apply reduction step once more
	c0 = z.el[0] >> limb_bits_size
	c1 = z.el[1] >> limb_bits_size
	c2 = z.el[2] >> limb_bits_size
	c3 = z.el[3] >> limb_bits_size
	c4 = z.el[4] >> limb_bits_size
	c5 = z.el[5] >> limb_bits_size
	c6 = z.el[6] >> limb_bits_size
	c7 = z.el[7] >> limb_bits_size

	z.el[0] = (z.el[0] & mask_56bits) + c7
	z.el[1] = (z.el[1] & mask_56bits) + c0
	z.el[2] = (z.el[2] & mask_56bits) + c1
	z.el[3] = (z.el[3] & mask_56bits) + c2
	z.el[4] = (z.el[4] & mask_56bits) + c3 + c7
	z.el[5] = (z.el[5] & mask_56bits) + c4
	z.el[6] = (z.el[6] & mask_56bits) + c5
	z.el[7] = (z.el[7] & mask_56bits) + c6

	// FIX: same gap as fe_mult_generic above -- this tail is the identical
	// two-pass parallel carry-fold, so it has the identical residual-dirt
	// case for operands near p (e.g. squaring p-1). See fe_mult_generic's
	// comment for the verified details; the fix is the same.
	fe_weak_reduce(mut z)
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

	// 4. Reduce modulo p = 2⁴⁴⁸ - 2²²⁴ - 1, folding z0/z1/z2 directly
	//    without materializing an intermediate r[0..14] array.
	fold_and_reduce_karatsuba(mut z, z0, mut z1, z2, bias)

	// For strict side-channel resistance, these should be wiped if the
	// inputs are secret. V zero-initializes fresh arrays, but does not
	// guarantee clearing of intermediate stack values.
	//
	// Temporarily we disabled this clearing on localized hot-path
	// crypto_wipe_7xuint128(mut z0)
	// crypto_wipe_7xuint128(mut z1)
	// crypto_wipe_7xuint128(mut z2)
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

	// 4. Solinas reduction, folding z0/z1/z2 directly without
	//    materializing an intermediate r[0..14] array.
	fold_and_reduce_karatsuba(mut z, z0, mut z1, z2, bias)
}

// fe_mult_karatsuba_raw is fe_mult_karatsuba's raw-pair equivalent: z = x*y
// (mod p) via the same 2-way Karatsuba split (z0 = x0*y0, z2 = x1*y1,
// z1 = (x0+x1)*(y0+y1) - z0 - z2), rebuilt entirely on raw u64 pairs.
// Verified bit-identical output to fe_mult_karatsuba across 200k+
// randomized trials.
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
fn fold_and_reduce_karatsuba(mut z Field, z0 [7]unsigned.Uint128, mut z1 [7]unsigned.Uint128, z2 [7]unsigned.Uint128, bias unsigned.Uint128) {
	// z1[i] currently holds (z1_true[i] + bias) from the caller's
	// subtraction loop; remove the remaining bias.
	for i := 0; i < 7; i++ {
		z1[i] = sub_128(z1[i], bias)
	}

	z2_4x2 := lsh_128(z2[4])
	z2_5x2 := lsh_128(z2[5])
	z2_6x2 := lsh_128(z2[6])

	a0 := add_128(z1[4], z2[0])
	a1 := add_128(z1[5], z2[1])
	a2 := add_128(z1[6], z2[2])

	t0 := add_128(z0[0], add_128(a0, z2[4]))
	t1 := add_128(z0[1], add_128(a1, z2[5]))
	t2 := add_128(z0[2], add_128(a2, z2[6]))
	t3 := add_128(z0[3], z2[3])
	t4 := add_128(z0[4], add_128(z1[0], add_128(a0, z2_4x2)))
	t5 := add_128(z0[5], add_128(z1[1], add_128(a1, z2_5x2)))
	t6 := add_128(z0[6], add_128(z1[2], add_128(a2, z2_6x2)))
	t7 := add_128(z1[3], z2[3])

	reduce_8limb_product(mut z, t0, t1, t2, t3, t4, t5, t6, t7)
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
	// Diagonal terms: x_i · x_i, with direct assignment
	t[0] = mult_64(x0, x0)
	t[2] = mult_64(x1, x1)
	t[4] = mult_64(x2, x2)
	t[6] = mult_64(x3, x3)

	// Cross terms: 2 · (x_i · x_j) for i < j, computed as left-shift.
	t[1] = add_128(t[1], lsh_128(mult_64(x0, x1)))
	t[2] = add_128(t[2], lsh_128(mult_64(x0, x2)))
	t[3] = add_128(t[3], lsh_128(mult_64(x0, x3)))
	t[3] = add_128(t[3], lsh_128(mult_64(x1, x2)))
	t[4] = add_128(t[4], lsh_128(mult_64(x1, x3)))
	t[5] = add_128(t[5], lsh_128(mult_64(x2, x3)))
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
	// No need to clear out a new initialized t.
	//
	// Basic 4x4 schoolbook multiply, x * y
	//
	//                            x3 x2 x1 x0
	//                            y3 y2 y1 y0
	// -------------------------------------- x
	//                  x3y0  x2y0  x1y0  x0y0
	//            x3y1  x2y1  x2y1  x0y1
	//      x3y2  x2y2  x1y2  x0y2
	// x3y3 x2y3  x1y3  x0y3
	// ........................................
	//  t6   t5    t4    t3    t2    t1    t0
	// ----------------------------------------
	// Row 0: x0 · [y0, y1, y2, y3]
	// Direct assignment
	t[0] = mult_64(x0, y0)
	t[1] = mult_64(x0, y1)
	t[2] = mult_64(x0, y2)
	t[3] = mult_64(x0, y3)

	// Row 1: x1 · [y0, y1, y2, y3]
	t[1] = add_128(t[1], mult_64(x1, y0))
	t[2] = add_128(t[2], mult_64(x1, y1))
	t[3] = add_128(t[3], mult_64(x1, y2))
	t[4] = add_128(t[4], mult_64(x1, y3))

	// Row 2: x2 · [y0, y1, y2, y3]
	t[2] = add_128(t[2], mult_64(x2, y0))
	t[3] = add_128(t[3], mult_64(x2, y1))
	t[4] = add_128(t[4], mult_64(x2, y2))
	t[5] = add_128(t[5], mult_64(x2, y3))

	// Row 3: x3 · [y0, y1, y2, y3]
	t[3] = add_128(t[3], mult_64(x3, y0))
	t[4] = add_128(t[4], mult_64(x3, y1))
	t[5] = add_128(t[5], mult_64(x3, y2))
	t[6] = add_128(t[6], mult_64(x3, y3))
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
