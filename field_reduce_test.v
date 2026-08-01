// Copyright © 2026 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Tests for gap A: fe_reduce idempotency and boundary-value reduction.
// Tests for gap B: fe_cmp / fe_equal on non-canonical aliases.
//
// WHY THESE TESTS MATTER
// ----------------------
// The audit identified that fe_reduce may not fully reduce a value that
// sits in [p, 2p) when the input already passed through fe_weak_reduce
// once but the carry-test produced c=1 and the subsequent addition
// left a second overflow un-corrected (finding A).
//
// fe_cmp calls fe_reduce on both operands before comparing limbs.  If
// fe_reduce does not canonicalize reliably, two non-canonical
// representations of the same value can compare as unequal (finding B).
//
// These tests pin down both issues with exact boundary inputs so any
// regression shows up immediately.
module curve448

// ---------------------------------------------------------------------------
// Gap A — fe_reduce idempotency
// ---------------------------------------------------------------------------

// test_fe_reduce_idempotent checks that applying fe_reduce twice yields
// the same result as applying it once.  A correct implementation must
// always produce a canonical (fully-reduced) limb representation after
// one call; a second call must be a no-op.
fn test_fe_reduce_idempotent() {
	// Inputs include boundary cases where carry chains are deepest:
	//   - zero
	//   - one
	//   - p - 1  (largest canonical value)
	//   - p      (non-canonical alias of 0)
	//   - p + 1  (non-canonical alias of 1)
	//   - 2p - 1 (just below 2p; worst case for a single-subtraction reduce)
	//   - all-max limbs (2^57 - 1 each, i.e. limbs at 2× the documented bound)
	cases := [
		fe_zero,
		fe_one,
		fe_minus_one, // p - 1
		fe_prime, // p  ≡ 0
		Field{ // p + 1  ≡ 1
			el: [u64(0x0100_0000_0000_0000), 0x00FF_FFFF_FFFF_FFFF, 0x00FF_FFFF_FFFF_FFFF,
				0x00FF_FFFF_FFFF_FFFF, 0x00FF_FFFF_FFFF_FFFE, 0x00FF_FFFF_FFFF_FFFF,
				0x00FF_FFFF_FFFF_FFFF, 0x00FF_FFFF_FFFF_FFFF]!
		},
		Field{ // 2p - 1  ≡ p - 1
			el: [u64(0x01FF_FFFF_FFFF_FFFD), 0x01FF_FFFF_FFFF_FFFF, 0x01FF_FFFF_FFFF_FFFF,
				0x01FF_FFFF_FFFF_FFFF, 0x01FF_FFFF_FFFF_FFFC, 0x01FF_FFFF_FFFF_FFFF,
				0x01FF_FFFF_FFFF_FFFF, 0x01FF_FFFF_FFFF_FFFF]!
		},
		Field{ // all limbs at 2^57-1 (doubly over the 56-bit bound)
			el: [u64(0x01FF_FFFF_FFFF_FFFF), 0x01FF_FFFF_FFFF_FFFF, 0x01FF_FFFF_FFFF_FFFF,
				0x01FF_FFFF_FFFF_FFFF, 0x01FF_FFFF_FFFF_FFFF, 0x01FF_FFFF_FFFF_FFFF,
				0x01FF_FFFF_FFFF_FFFF, 0x01FF_FFFF_FFFF_FFFF]!
		},
	]

	for i, f in cases {
		mut once := f
		fe_reduce(mut once)

		mut twice := once
		fe_reduce(mut twice)

		// After two reductions the limb arrays must be bit-identical.
		assert once == twice, 'fe_reduce not idempotent on case ${i}'

		// Every limb must fit in 56 bits (canonical invariant).
		for limb in once.el {
			assert limb <= mask_56bits, 'limb exceeds 56 bits after fe_reduce on case ${i}'
		}
	}
}

// test_fe_reduce_p_aliases_zero checks the specific boundary value p
// (= 2^448 - 2^224 - 1) reduces to the zero element.
fn test_fe_reduce_p_aliases_zero() {
	mut x := fe_prime
	fe_reduce(mut x)
	assert fe_equal(x, fe_zero), 'fe_reduce(p) must equal 0'
	// Limbs must all be zero, not just fe_equal (which calls fe_reduce again).
	for limb in x.el {
		assert limb == 0, 'fe_reduce(p) must produce all-zero limbs'
	}
}

// test_fe_reduce_p_plus_one_aliases_one checks that p+1 reduces to 1.
fn test_fe_reduce_p_plus_one_aliases_one() {
	// p + 1 in unsaturated limbs: add 1 to limb 0 of fe_prime
	mut x := fe_prime
	x.el[0] += 1
	fe_reduce(mut x)
	assert fe_equal(x, fe_one), 'fe_reduce(p+1) must equal 1'
}

// test_fe_reduce_two_p_minus_one_aliases_p_minus_one checks that
// 2p-1 reduces to p-1 (= fe_minus_one).
fn test_fe_reduce_two_p_minus_one_aliases_p_minus_one() {
	// 2p - 1: double every limb of fe_prime, subtract 1 from limb 0.
	mut x := fe_prime
	for i in 0 .. 8 {
		x.el[i] *= 2
	}
	x.el[0] -= 1
	fe_reduce(mut x)
	assert fe_equal(x, fe_minus_one), 'fe_reduce(2p-1) must equal p-1'
}

// test_fe_reduce_boundary_carry_chain exercises a value whose limb-0
// carry ripples all the way through the carry chain before settling.
// Value: p - 1 + p  = 2p - 1 stored as (fe_minus_one.el + fe_prime.el).
fn test_fe_reduce_boundary_carry_chain() {
	mut x := Field{}
	// add fe_minus_one and fe_prime limb-wise (no modular reduction)
	for i in 0 .. 8 {
		x.el[i] = fe_minus_one.el[i] + fe_prime.el[i]
	}
	fe_reduce(mut x)
	assert fe_equal(x, fe_minus_one), 'fe_reduce(p-1 + p) must equal p-1'
}

// ---------------------------------------------------------------------------
// Gap B — fe_cmp / fe_equal on non-canonical representations
// ---------------------------------------------------------------------------

// test_fe_cmp_non_canonical_aliases checks that fe_cmp correctly identifies
// non-canonical representations of the same value as equal, and that
// non-canonical representations of different values compare as unequal.
fn test_fe_cmp_non_canonical_aliases() {
	// 0 and p are the same value; should compare equal.
	assert fe_equal(fe_zero, fe_prime), 'fe_equal(0, p) must be true'
	assert fe_cmp(fe_zero, fe_prime) == 1, 'fe_cmp(0, p) must return 1'

	// p+1 and 1 are the same value.
	mut p_plus_1 := fe_prime
	p_plus_1.el[0] += 1
	assert fe_equal(p_plus_1, fe_one), 'fe_equal(p+1, 1) must be true'

	// 2p-1 and p-1 are the same value.
	mut two_p_minus_1 := fe_prime
	for i in 0 .. 8 {
		two_p_minus_1.el[i] *= 2
	}
	two_p_minus_1.el[0] -= 1
	assert fe_equal(two_p_minus_1, fe_minus_one), 'fe_equal(2p-1, p-1) must be true'

	// 1 and p-1 are different values; must compare unequal.
	assert !fe_equal(fe_one, fe_minus_one), 'fe_equal(1, p-1) must be false'
	assert fe_cmp(fe_one, fe_minus_one) == 0, 'fe_cmp(1, p-1) must return 0'

	// 0 and 1 are different values.
	assert !fe_equal(fe_zero, fe_one), 'fe_equal(0, 1) must be false'
}

// test_fe_cmp_unreduced_self_equality checks that a value compares equal
// to itself even when it has not been reduced (limbs may exceed 56 bits).
fn test_fe_cmp_unreduced_self_equality() {
	// Construct a field element with over-full limbs (bit 57 set in each).
	over_full := Field{
		el: [u64(0x0180_0000_0000_0000), 0x0180_0000_0000_0000, 0x0180_0000_0000_0000,
			0x0180_0000_0000_0000, 0x0180_0000_0000_0000, 0x0180_0000_0000_0000,
			0x0180_0000_0000_0000, 0x0180_0000_0000_0000]!
	}
	// Must equal itself.
	assert fe_equal(over_full, over_full), 'unreduced element must equal itself'
	assert fe_cmp(over_full, over_full) == 1, 'fe_cmp of element with itself must return 1'
}

// test_fe_equal_consistent_with_fe_cmp verifies that fe_equal and fe_cmp
// agree on every pair of boundary values.
fn test_fe_equal_consistent_with_fe_cmp() {
	boundary := [fe_zero, fe_one, fe_minus_one, fe_prime]
	for i, a in boundary {
		for j, b in boundary {
			eq := fe_equal(a, b)
			cmp := fe_cmp(a, b)
			// fe_equal and fe_cmp == 1 must agree.
			assert eq == (cmp == 1), 'fe_equal and fe_cmp disagree on boundary pair (${i}, ${j})'
		}
	}
}
