// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
module curve448

import encoding.hex

// The first two test is a pair of test vectors that consist of expected outputs for the given inputs.
fn test_x448_rfc7748_1() ! {
	k :=
		hex.decode('3d262fddf9ec8e88495266fea19a34d28882acef045104d0d1aae121700a779c984c24f8cdd78fbff44943eba368f54b29259a4f1c600ad3')!
	u :=
		hex.decode('06fce640fa3487bfda5f6cf2d5263f8aad88334cbd07437f020f08f9814dc031ddbdc38c19c6da2583fa5429db94ada18aa7a7fb4ef8a086')!

	out := x448(k, u)!
	expected :=
		hex.decode('ce3e4ff95a60dc6697da1db1d85e6afbdf79b50a2412d7546d5f239fe14fbaadeb445fc66a01b0779d98223961111e21766282f73dd96b6f')!

	assert out == expected
}

fn test_x448_rfc7748_2() ! {
	k :=
		hex.decode('203d494428b8399352665ddca42f9de8fef600908e0d461cb021f8c538345dd77c3e4806e25f46d3315c44e0a5b4371282dd2c8d5be3095f')!
	u :=
		hex.decode('0fbcc2f993cd56d3305b0b7d9e55d4c1a8fb5dbb52f8e9a1e9b6201b165d015894e56c4d3570bee52fe205e28a78b91cdfbde71ce8d157db')!

	out := x448(k, u)!
	expected :=
		hex.decode('884a02576239ff7a2f2f63b2db6a9ff37047ac13568e1e30fe63c4a7ad1b3ee3a5700df34321d62077e63633c575c1c954514e99da7c179d')!

	assert out == expected
}

// The second type of test vector consists of the result of calling the
// function in question a specified number of times.
fn test_x448_rfc7748_3() ! {
	mut k := []u8{len: 56}
	k[0] = 5
	mut u := k.clone()
	// After one iteration:
	ref1 :=
		hex.decode('3f482c8a9f19b01e6c46ee9711d9dc14fd4bf67af30765c2ae2b846a4d23a8cd0db897086239492caf350b51f833868b9bc2b3bca9cf4113')!
	// After 1,000 iterations:
	ref1000 :=
		hex.decode('aa3b4749d55b9daf1e5b00288826c467274ce3ebbdd5c17b975e09d4af6c67cf10d087202db88286e2b79fceea3ec353ef54faa26e219f38')!
	// After 1,000,000 iterations:
	ref1m :=
		hex.decode('077f453681caca3693198420bbe515cae0002472519b3e67661a7e89cab94695c8f4bcd66e61b9b9c946da8d524de3d69bd9d9d66b997e37')!

	// For each iteration, set k to be the result of calling the function
	// and u to be the old value of k. The final result is the value left in k.
	for i in 0 .. 1000 {
		r := x448(k, u)!
		unsafe {
			u = k
			k = r
		}
		if i == 0 {
			assert k == ref1
		} else if i == 999 {
			assert k == ref1000
		}
	}
}

fn test_rfc7448_4() ! {
	/*
     Alice's private key, a:
      9a8f4925d1519f5775cf46b04b5800d4ee9ee8bae8bc5565d498c28d
      d9c9baf574a9419744897391006382a6f127ab1d9ac2d8c0a598726b
    Alice's public key, X448(a, 5):
      9b08f7cc31b7e3e67d22d5aea121074a273bd2b83de09c63faa73d2c
      22c5d9bbc836647241d953d40c5b12da88120d53177f80e532c41fa0
    Bob's private key, b:
      1c306a7ac2a0e2e0990b294470cba339e6453772b075811d8fad0d1d
      6927c120bb5ee8972b0d3e21374c9c921b09d1b0366f10b65173992d
    Bob's public key, X448(b, 5):
      3eb7a829b0cd20f5bcfc0b599b6feccf6da4627107bdb0d4f345b430
      27d8b972fc3e34fb4232a13ca706dcb57aec3dae07bdc1c67bf33609
    Their shared secret, K:
      07fff4181ac6cc95ec1c16a94a0f74d12da232ce40a77552281d282b
      b60c0b56fd2464c335543936521c24403085d59a449a5037514a879d
	*/
	// Alice key
	a :=
		hex.decode('9a8f4925d1519f5775cf46b04b5800d4ee9ee8bae8bc5565d498c28dd9c9baf574a9419744897391006382a6f127ab1d9ac2d8c0a598726b')!
	// Alice public key
	exp_alice_pbk :=
		hex.decode('9b08f7cc31b7e3e67d22d5aea121074a273bd2b83de09c63faa73d2c22c5d9bbc836647241d953d40c5b12da88120d53177f80e532c41fa0')!
	// calculates alice pubkey
	alice_pbk := x448(a, base_point.bytes())!
	assert alice_pbk == exp_alice_pbk

	// Bob's private key, b:
	b :=
		hex.decode('1c306a7ac2a0e2e0990b294470cba339e6453772b075811d8fad0d1d6927c120bb5ee8972b0d3e21374c9c921b09d1b0366f10b65173992d')!
	// Bob's public key, X448(b, 5):
	exp_bob_pbk :=
		hex.decode('3eb7a829b0cd20f5bcfc0b599b6feccf6da4627107bdb0d4f345b43027d8b972fc3e34fb4232a13ca706dcb57aec3dae07bdc1c67bf33609')!
	// Calculated Bob's public key
	bob_pbk := x448(b, base_point.bytes())!
	assert bob_pbk == exp_bob_pbk

	// Alice calc shared secret
	alice_shared := x448(a, exp_bob_pbk)!
	bob_shared := x448(b, exp_alice_pbk)!
	assert alice_shared == bob_shared
}
