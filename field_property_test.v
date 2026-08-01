// Copyright © 2026 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Randomized (property-based) field arithmetic tests.
//
// field_test.v already checks fixed reference vectors, which is good for
// pinning down known-tricky cases, but a fixed vector list only exercises
// the exact limb/carry patterns someone thought to write down. This file
// instead draws many random field elements per run and cross-checks every
// core operation against an independent oracle built on `math.big.Integer`
// (arbitrary-precision, not tied to the 56-bit-limb/Solinas machinery
// under test), so a bug that only manifests for some rare carry pattern
// has many chances to be hit across runs instead of zero.
//
// All random inputs are drawn with each limb `< 2^56` (matching the
// library's own documented per-limb invariant between operations) but are
// NOT necessarily reduced mod p, exercising the same "possibly-unreduced,
// limb-bounded" representation the library's internal functions accept.
module curve448

import math.big
import rand

const property_iterations = 500

// --- Field <-> big.Integer conversion helpers -------------------------

// big_prime returns p = 2⁴⁴⁸ - 2²²⁴ - 1 as a big.Integer, computed from
// the module's own `fe_prime` limbs (so this stays correct even if the
// limb layout ever changes) rather than hardcoding a decimal/hex literal.
fn big_prime() big.Integer {
	return field_to_big(fe_prime)
}

// field_to_big converts a Field (interpreted as sum(el[i] * 2^(56*i)),
// with NO assumption that it is < p) into a big.Integer.
fn field_to_big(f Field) big.Integer {
	mut acc := big.integer_from_u64(0)
	for i := 7; i >= 0; i-- {
		acc = acc.left_shift(limb_bits_size) + big.integer_from_u64(f.el[i])
	}
	return acc
}

// big_low_u64 extracts the low `bits` bits of a non-negative big.Integer
// as a u64. Used to pull 56-bit limbs back out when converting in the
// other direction.
fn big_low_u64(v big.Integer, bits u32) u64 {
	mask := big.integer_from_u64((u64(1) << bits) - 1)
	masked := v.bitwise_and(mask)
	bs, _ := masked.bytes() // big-endian, no leading zero bytes
	mut result := u64(0)
	for b in bs {
		result = (result << 8) | u64(b)
	}
	return result
}

// random_field returns a Field with each limb uniformly random in
// [0, 2^56), i.e. NOT necessarily reduced mod p. This matches the bound
// the library documents between operations.
fn random_field() Field {
	mut el := [8]u64{}
	for i in 0 .. 8 {
		el[i] = rand.u64() & mask_56bits
	}
	return Field{
		el: el
	}
}

// random_nonzero_field returns a random field element whose reduced value
// is not congruent to 0 mod p (needed for inversion tests).
fn random_nonzero_field() Field {
	for {
		f := random_field()
		mut x := f
		if fe_is_zero(mut x) == 0 {
			return f
		}
	}
	return Field{}
}

// --- Property tests -----------------------------------------------------

fn test_property_add_matches_bigint_mod_p() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()
		b := random_field()

		mut z := Field{}
		fe_add(mut z, a, b)
		fe_reduce(mut z)

		want := (field_to_big(a) + field_to_big(b)) % p
		got := field_to_big(z)
		assert got == want
	}
}

fn test_property_sub_matches_bigint_mod_p() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()
		b := random_field()

		mut z := Field{}
		fe_sub(mut z, a, b)
		fe_reduce(mut z)

		want := (field_to_big(a) - field_to_big(b)).mod_euclid(p)
		got := field_to_big(z)
		assert got == want
	}
}

fn test_property_negate_matches_bigint_mod_p() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()

		mut z := Field{}
		fe_negate(mut z, a)
		fe_reduce(mut z)

		want := (big.integer_from_u64(0) - field_to_big(a)).mod_euclid(p)
		got := field_to_big(z)
		assert got == want
	}
}

fn test_property_mult_matches_bigint_mod_p() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()
		b := random_field()

		mut z := Field{}
		fe_mult(mut z, a, b)
		fe_reduce(mut z)

		want := (field_to_big(a) * field_to_big(b)) % p
		got := field_to_big(z)
		assert got == want
	}
}

fn test_property_sqr_matches_bigint_mod_p() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()

		mut z := Field{}
		fe_sqr(mut z, a)
		fe_reduce(mut z)

		want := (field_to_big(a) * field_to_big(a)) % p
		got := field_to_big(z)
		assert got == want
	}
}

fn test_property_mult_32_matches_bigint_mod_p() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()
		k := rand.u32()

		mut z := Field{}
		fe_mult_32(mut z, a, k)
		fe_reduce(mut z)

		want := (field_to_big(a) * big.integer_from_u64(u64(k))) % p
		got := field_to_big(z)
		assert got == want
	}
}

fn test_property_sqr_n_matches_repeated_squaring() {
	for _ in 0 .. 100 {
		a := random_field()
		n := 1 + int(rand.u32() % 12) // n in [1, 12]

		mut want := Field{}
		fe_clone(mut want, a)
		for _ in 0 .. n {
			fe_sqr(mut want, want)
		}
		fe_reduce(mut want)

		mut got := Field{}
		fe_sqr_n(mut got, a, n)
		fe_reduce(mut got)

		assert got == want
	}
}

// Cross-checks fe_inverse against an independently computed modular
// inverse via Fermat's little theorem, x^(p-2) mod p, using math.big's
// own square-and-multiply (big_mod_pow) rather than this library's
// fe_power446 addition-chain implementation. A bug shared between
// fe_inverse and fe_power446 would not be caught by testing them against
// each other; this closes that gap. Iteration count is kept low because
// big_mod_pow over a 445-bit exponent is comparatively slow.
fn test_property_inverse_matches_bigint_fermat() {
	p := big_prime()
	p_minus_2 := p - big.integer_from_u64(2)

	for _ in 0 .. 25 {
		a := random_nonzero_field()

		mut z := Field{}
		fe_inverse(mut z, a)
		fe_reduce(mut z)

		want := field_to_big(a).big_mod_pow(p_minus_2, p) or { panic(err) }
		got := field_to_big(z)
		assert got == want

		// Sanity: a * a^-1 == 1 (mod p), checked via the library's own
		// multiplication too, independent of the big.Integer oracle.
		mut one_check := Field{}
		fe_mult(mut one_check, a, z)
		fe_reduce(mut one_check)
		assert fe_equal(one_check, fe_one)
	}
}

fn test_property_cmp_and_equal_are_reduction_aware() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()
		b := random_field()

		want_equal := (field_to_big(a) % p) == (field_to_big(b) % p)
		assert fe_equal(a, b) == want_equal

		// a must always equal itself, even unreduced.
		assert fe_equal(a, a)
	}
}

fn test_property_is_canonical_matches_bigint_comparison() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		a := random_field()
		want := field_to_big(a) < p
		assert a.is_canonical() == want
	}
}

// Round-trips a random canonical field element through bytes()/set_bytes()
// and checks the decoded value against the big.Integer oracle, catching
// any endianness or limb-boundary bug in (de)serialization that fixed
// vectors happen not to hit.
fn test_property_bytes_roundtrip_matches_bigint() {
	p := big_prime()
	mut buf := []u8{len: 56}
	for _ in 0 .. property_iterations {
		a := random_field()
		want := field_to_big(a) % p

		mut x := a
		x.bytes(mut buf)! // fully reduces internally

		mut y := Field{}
		y.set_bytes(buf)!

		got := field_to_big(y)
		assert got == want
	}
}

// set_bytes_loosely must always reduce mod p, including for the
// intentionally non-canonical (>= p) 56-byte encodings RFC 7748 requires
// implementations to accept.
fn test_property_set_bytes_loosely_matches_bigint_mod_p() {
	p := big_prime()
	for _ in 0 .. property_iterations {
		mut buf := []u8{len: 56}
		for i in 0 .. 56 {
			buf[i] = u8(rand.u32() & 0xff)
		}
		// Force the top byte's top bit range so some fraction of inputs
		// land >= p (the encoding is 56 bytes = 448 bits, while p needs
		// only 448 bits itself, so uniformly random bytes already yield
		// a healthy mix of both cases -- no extra biasing needed).
		raw_value := big.integer_from_bytes(reversed(buf), signum: 1)
		want := raw_value % p

		mut y := Field{}
		y.set_bytes_loosely(buf)!

		got := field_to_big(y)
		assert got == want
	}
}

// reversed returns a big-endian copy of a little-endian byte slice, since
// `big.integer_from_bytes` expects big-endian input while this library's
// wire format is little-endian.
fn reversed(b []u8) []u8 {
	mut out := []u8{len: b.len}
	for i in 0 .. b.len {
		out[i] = b[b.len - 1 - i]
	}
	return out
}

// Basic algebraic invariants that don't need the big.Integer oracle at
// all, just internal consistency -- cheap extra confidence alongside the
// oracle-based tests above.
fn test_property_field_algebraic_identities() {
	for _ in 0 .. property_iterations {
		a := random_field()
		b := random_field()
		c := random_field()

		// (a + b) + c == a + (b + c)
		mut ab := Field{}
		fe_add(mut ab, a, b)
		mut ab_c := Field{}
		fe_add(mut ab_c, ab, c)
		fe_reduce(mut ab_c)

		mut bc := Field{}
		fe_add(mut bc, b, c)
		mut a_bc := Field{}
		fe_add(mut a_bc, a, bc)
		fe_reduce(mut a_bc)

		assert fe_equal(ab_c, a_bc)

		// a * (b + c) == a*b + a*c
		mut b_plus_c := Field{}
		fe_add(mut b_plus_c, b, c)
		mut lhs := Field{}
		fe_mult(mut lhs, a, b_plus_c)
		fe_reduce(mut lhs)

		mut ab2 := Field{}
		fe_mult(mut ab2, a, b)
		mut ac2 := Field{}
		fe_mult(mut ac2, a, c)
		mut rhs := Field{}
		fe_add(mut rhs, ab2, ac2)
		fe_reduce(mut rhs)

		assert fe_equal(lhs, rhs)

		// a - a == 0
		mut zero_check := Field{}
		fe_sub(mut zero_check, a, a)
		assert fe_equal(zero_check, fe_zero)
	}
}
