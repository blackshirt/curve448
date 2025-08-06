// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
module curve448

import encoding.hex

// The first two test is a pair of test vectors that consist of expected outputs for the given inputs.
fn test_x448_rfc7748_1() ! {
	mut k := hex.decode('3d262fddf9ec8e88495266fea19a34d28882acef045104d0d1aae121700a779c984c24f8cdd78fbff44943eba368f54b29259a4f1c600ad3')!
	u := hex.decode('06fce640fa3487bfda5f6cf2d5263f8aad88334cbd07437f020f08f9814dc031ddbdc38c19c6da2583fa5429db94ada18aa7a7fb4ef8a086')!

	out := x448(mut k, u)!
	expected := hex.decode('ce3e4ff95a60dc6697da1db1d85e6afbdf79b50a2412d7546d5f239fe14fbaadeb445fc66a01b0779d98223961111e21766282f73dd96b6f')!

	assert out == expected
}

fn test_x448_rfc7748_2() ! {
	mut k := hex.decode('203d494428b8399352665ddca42f9de8fef600908e0d461cb021f8c538345dd77c3e4806e25f46d3315c44e0a5b4371282dd2c8d5be3095f')!
	u := hex.decode('0fbcc2f993cd56d3305b0b7d9e55d4c1a8fb5dbb52f8e9a1e9b6201b165d015894e56c4d3570bee52fe205e28a78b91cdfbde71ce8d157db')!

	out := x448(mut k, u)!
	expected := hex.decode('884a02576239ff7a2f2f63b2db6a9ff37047ac13568e1e30fe63c4a7ad1b3ee3a5700df34321d62077e63633c575c1c954514e99da7c179d')!

	assert out == expected
}

// The second type of test vector consists of the result of calling the
// function in question a specified number of times.
fn test_x448_rfc7748_3() ! {
	mut k := []u8{len: 56}
	k[0] = 5
	mut u := k.clone()
	// After one iteration:
	ref1 := hex.decode('3f482c8a9f19b01e6c46ee9711d9dc14fd4bf67af30765c2ae2b846a4d23a8cd0db897086239492caf350b51f833868b9bc2b3bca9cf4113')!
	// After 1,000 iterations:
	ref1000 := hex.decode('aa3b4749d55b9daf1e5b00288826c467274ce3ebbdd5c17b975e09d4af6c67cf10d087202db88286e2b79fceea3ec353ef54faa26e219f38')!
	// After 1,000,000 iterations:
	ref1m := hex.decode('077f453681caca3693198420bbe515cae0002472519b3e67661a7e89cab94695c8f4bcd66e61b9b9c946da8d524de3d69bd9d9d66b997e37')!

	mut r := []u8{len: 56}
	// For each iteration, set k to be the result of calling the function
	// and u to be the old value of k.  The final result is the value left
	// in k.
	for i in 0 .. 1000 {
		// println('start i: ${i}')
		tmp_k := k.clone()
		r = x448(mut k, u)!
		unsafe {
			u = tmp_k
		}
		unsafe {
			k = r
		}
		if i == 0 {
			assert k == ref1
		} else if i == 999 {
			assert k == ref1000
		}
		// else if i == 999999 {
		// assert k == ref1m
		// }
	}
}
