// Copyright © 2026 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
module curve448

import encoding.hex

// Cross-checks the typed API against the RFC 7748 §5.2 test vectors and
// against the free `x448()` function, to make sure the wrapper types are
// pure plumbing and don't change any computed value.
fn test_keys_api_matches_rfc7748_vector() ! {
	a_raw :=
		hex.decode('9a8f4925d1519f5775cf46b04b5800d4ee9ee8bae8bc5565d498c28dd9c9baf574a9419744897391006382a6f127ab1d9ac2d8c0a598726b')!
	exp_alice_pub :=
		hex.decode('9b08f7cc31b7e3e67d22d5aea121074a273bd2b83de09c63faa73d2c22c5d9bbc836647241d953d40c5b12da88120d53177f80e532c41fa0')!
	b_raw :=
		hex.decode('1c306a7ac2a0e2e0990b294470cba339e6453772b075811d8fad0d1d6927c120bb5ee8972b0d3e21374c9c921b09d1b0366f10b65173992d')!
	exp_bob_pub :=
		hex.decode('3eb7a829b0cd20f5bcfc0b599b6feccf6da4627107bdb0d4f345b43027d8b972fc3e34fb4232a13ca706dcb57aec3dae07bdc1c67bf33609')!
	exp_shared :=
		hex.decode('07fff4181ac6cc95ec1c16a94a0f74d12da232ce40a77552281d282bb60c0b56fd2464c335543936521c24403085d59a449a5037514a879d')!

	alice_priv := new_private_key(a_raw)!
	bob_priv := new_private_key(b_raw)!

	alice_pub := alice_priv.public_key()!
	bob_pub := bob_priv.public_key()!

	assert alice_pub.bytes() == exp_alice_pub
	assert bob_pub.bytes() == exp_bob_pub

	// public_key() must agree with calling the free function directly.
	assert alice_pub.bytes() == x448(a_raw, base_point)!
	assert bob_pub.bytes() == x448(b_raw, base_point)!

	alice_shared := alice_priv.shared_secret(bob_pub)!
	bob_shared := bob_priv.shared_secret(alice_pub)!

	assert alice_shared == exp_shared
	assert bob_shared == exp_shared

	// shared_secret() must agree with calling the free function directly.
	assert alice_shared == x448(a_raw, exp_bob_pub)!
}

fn test_generate_private_key_round_trips() ! {
	priv := generate_private_key()!
	assert priv.bytes().len == 56

	pub_key := priv.public_key()!
	assert pub_key.bytes().len == 56

	// Deriving twice from the same private key must be deterministic.
	pub_key2 := priv.public_key()!
	assert pub_key.bytes() == pub_key2.bytes()
}

fn test_new_private_key_rejects_bad_length() {
	new_private_key([]u8{len: 55}) or {
		assert err == error('new_private_key: expected 56 bytes, got 55')
		return
	}
	assert false
}

fn test_new_public_key_rejects_bad_length() {
	new_public_key([]u8{len: 10}) or {
		assert err == error('new_public_key: expected 56 bytes, got 10')
		return
	}
	assert false
}

fn test_public_key_validate_rejects_low_order_point() {
	zero_point := []u8{len: 56}
	pub_key := new_public_key(zero_point) or { panic(err) }
	pub_key.validate() or {
		assert err == error('x448: low order point')
		return
	}
	assert false
}

fn test_public_key_validate_accepts_base_point() ! {
	pub_key := new_public_key(base_point)!
	pub_key.validate()!
}

fn test_private_key_zero_wipes_bytes() ! {
	mut priv := generate_private_key()!
	priv.zero()
	for b in priv.bytes() {
		assert b == 0
	}
}
