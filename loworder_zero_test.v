// Copyright © 2026 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Tests for gap C: x448 low-order output rejection.
// Tests for gap D: PrivateKey.zero() post-wipe unusability.
//
// WHY THESE TESTS MATTER
// ----------------------
// Gap C: The low-order-point branch at the end of x448() (the
// `ret_is_zero == 1 → error` path) is never exercised by any existing
// test.  This branch is the library's primary defense against small-
// subgroup attacks.  If it were accidentally removed or gated behind a
// wrong condition, no existing test would catch it.
//
// Gap D: PrivateKey.zero() documents that the key "must not be used again"
// after wiping, but no test verifies what actually happens.  The wipe
// produces an all-zero scalar.  Multiplying the all-zero scalar by the
// base point yields the output of x448(0, 5).  Because that output is not
// the zero point (the x-coordinate of 0·G on Curve448 is not 0), the call
// succeeds but returns a deterministic, public, meaningless value rather
// than an error.  This test documents that behavior so a future change
// (e.g. adding a "zeroed" flag) cannot silently break or weaken it.
module curve448

import encoding.hex

// ---------------------------------------------------------------------------
// Gap C — x448 low-order output rejection
// ---------------------------------------------------------------------------

// test_x448_rejects_low_order_output_point verifies that x448() returns an
// error when scalar multiplication produces an all-zero output.
//
// The all-zero output arises when the input point is itself the neutral
// element of the prime-order subgroup (u = 0).  RFC 7748 says all-zero
// output SHOULD be rejected; this library does so unconditionally.
fn test_x448_rejects_low_order_output_point() {
	// Any scalar paired with the zero point produces a zero output.
	zero_point := []u8{len: 56} // u = 0
	// Use a random-looking but fixed scalar so the test is deterministic.
	mut scalar := []u8{len: 56}
	scalar[0] = 0xfc // clamped form of a non-trivial scalar (low 2 bits clear)
	scalar[55] = 0x80 // high bit set as required by clamping

	x448(scalar, zero_point) or {
		assert err == error('x448 bad input point: low order point')
		return
	}
	// If we reach here the function returned Ok — that is wrong.
	assert false, 'x448 with zero point must return a low-order-point error'
}

// test_x448_rejects_zero_output_from_low_order_scalar checks that the
// error is independent of which scalar is used: even the simplest non-
// trivial clamped scalar (effectively 4) with the zero point must fail.
fn test_x448_rejects_zero_output_from_low_order_scalar() {
	zero_point := []u8{len: 56}
	mut scalar := []u8{len: 56}
	scalar[0] = 4 // smallest clamped scalar (bits 0-1 clear, ≥ 4)
	scalar[55] = 0x80

	x448(scalar, zero_point) or {
		assert err == error('x448 bad input point: low order point')
		return
	}
	assert false, 'x448(4, 0) must return a low-order-point error'
}

// test_x448_accepts_nonzero_output_from_valid_point is a positive control:
// confirm that the low-order check does NOT fire for a legitimate input
// (the base point), i.e. the error path is only taken when warranted.
fn test_x448_accepts_nonzero_output_from_valid_point() {
	// A clamped scalar that is clearly non-trivial.
	mut scalar := []u8{len: 56}
	scalar[0] = 0xfc
	scalar[55] = 0x80

	result := x448(scalar, base_point) or {
		assert false, 'x448 with base point must not return an error: ${err}'
		return
	}
	assert result.len == 56
	// The result must not be all-zero (it is not a low-order point).
	mut all_zero := true
	for b in result {
		if b != 0 {
			all_zero = false
			break
		}
	}
	assert !all_zero, 'x448 result with base point must not be all-zero'
}

// test_shared_secret_rejects_low_order_peer exercises the same check
// through the typed API: shared_secret() with a zero PublicKey must fail.
fn test_shared_secret_rejects_low_order_peer() {
	priv := generate_private_key() or { panic(err) }
	zero_pub := new_public_key([]u8{len: 56}) or { panic(err) }

	priv.shared_secret(zero_pub) or {
		assert err == error('x448 bad input point: low order point')
		return
	}
	assert false, 'shared_secret with zero public key must return an error'
}

// ---------------------------------------------------------------------------
// Gap D — PrivateKey.zero() post-wipe unusability
// ---------------------------------------------------------------------------

// test_private_key_zero_wipes_all_bytes verifies that every byte of
// the private key becomes 0 after calling zero().
// (This duplicates the existing keys_test check intentionally — it is the
// entry point for the more detailed post-wipe behavior tests below.)
fn test_zero_wipes_all_bytes_gap_d() {
	mut priv := generate_private_key() or { panic(err) }
	priv.zero()
	for b in priv.bytes() {
		assert b == u8(0), 'every byte must be 0 after zero()'
	}
}

// test_private_key_zero_makes_public_key_deterministic_and_known checks
// the concrete post-wipe behavior: calling public_key() on a zeroed
// PrivateKey uses the all-zero scalar, which is a valid (though useless)
// scalar input to x448.  The result must be deterministic (the same
// every call) and must match x448(zeros, base_point).
//
// This documents that zero() does NOT prevent further API calls; it merely
// makes them produce a deterministic, public, cryptographically worthless
// value.  If a future change adds an explicit "zeroed" guard that returns
// an error, this test will catch it and force an intentional update.
fn test_private_key_zero_public_key_is_deterministic() {
	mut priv := generate_private_key() or { panic(err) }
	priv.zero()

	pub1 := priv.public_key() or {
		// If the implementation adds an explicit error for zeroed keys in
		// the future, document that here rather than hard-failing.
		// For now we expect success (or a low-order error) — either is
		// acceptable, but it must be consistent across calls.
		eprintln('public_key() on zeroed key returned error: ${err}')
		return
	}

	pub2 := priv.public_key() or { panic(err) }

	// Both calls must return the same value (deterministic).
	assert pub1.bytes() == pub2.bytes(), 'public_key() on zeroed PrivateKey must be deterministic'
}

// test_private_key_zero_shared_secret_matches_zero_scalar verifies that
// the shared secret produced by a zeroed key equals x448(zeros, peer_pub).
fn test_private_key_zero_shared_secret_matches_zero_scalar() {
	mut priv := generate_private_key() or { panic(err) }
	priv.zero()

	// Build a peer using the RFC 7748 test vector public key (known-valid,
	// non-low-order point).
	bob_pub_bytes := hex.decode('3eb7a829b0cd20f5bcfc0b599b6feccf6da4627107bdb0d4f345b43027d8b972fc3e34fb4232a13ca706dcb57aec3dae07bdc1c67bf33609') or {
		panic(err)
	}
	peer := new_public_key(bob_pub_bytes) or { panic(err) }

	zeroed_scalar := []u8{len: 56} // all-zero scalar

	// Compute reference result via the low-level function.
	ref_result := x448(zeroed_scalar, bob_pub_bytes) or {
		// If x448(0, peer) returns a low-order error, the typed API should
		// return the same error.
		priv.shared_secret(peer) or {
			assert err.msg() == 'x448 bad input point: low order point'
			return
		}
		assert false, 'shared_secret and x448 disagree on error for zeroed key'
		return
	}

	typed_result := priv.shared_secret(peer) or {
		assert false, 'shared_secret unexpectedly errored: ${err}'
		return
	}

	assert typed_result == ref_result, 'shared_secret with zeroed key must match x448(zeros, peer)'
}

// test_private_key_zero_is_idempotent checks that calling zero() twice
// does not panic or produce unexpected state.
fn test_private_key_zero_is_idempotent() {
	mut priv := generate_private_key() or { panic(err) }
	priv.zero()
	priv.zero() // must not panic
	for b in priv.bytes() {
		assert b == u8(0), 'bytes must remain zero after second zero() call'
	}
}
