// Copyright © 2025 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
module fp448

struct AddTests {
	x Field
	y Field
	r Field
}

const tests_add = [
	AddTests{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
	},
]

fn test_field_add() {
	for item in tests_add {
		mut z := Field{}
		fe_add(mut z, item.x, item.y)
		fe_reduce(mut z)
		assert z == item.r
	}
}

struct SubTests {
	x Field
	y Field
	r Field
}

const tests_sub = [
	SubTests{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
	},
]

fn test_field_subtract() {
	for item in tests_sub {
		mut z := Field{}
		fe_sub(mut z, item.x, item.y)
		fe_reduce(mut z)
		assert z == item.r
	}
}

fn test_field_square() {
	for item in tests_square {
		mut z := Field{}
		fe_sqr(mut z, item.x)
		assert z == item.r
	}
}

struct TestSquare {
	x Field
	r Field
}

const tests_square = [
	TestSquare{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(0), 1, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 1, 0, 0, 0, 0, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(0), 0, 1, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 0, 0, 1, 0, 0, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(0), 0, 0, 1, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 1, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(0), 0, 0, 0, 1, 0, 0, 0]!
		}
		r: Field{
			el: [u64(1), 0, 0, 0, 1, 0, 0, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 1, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 1, 0, 0, 0, 1, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 1, 0]!
		}
		r: Field{
			el: [u64(1), 0, 0, 0, 2, 0, 0, 0]!
		}
	},
	TestSquare{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(0), 0, 1, 0, 0, 0, 2, 0]!
		}
	},
]

fn test_mult() {
	a := Field{
		el: [u64(5), 0, 0, 0, 0, 0, 0, 0]!
	}
	aa := Field{
		el: [u64(5), 0, 0, 0, 0, 0, 0, 0]!
	}
	assert fe_equal(a, aa) == true

	b := Field{
		el: [u64(210), 0, 0, 0, 0, 0, 0, 0]!
	}
	c := Field{
		el: [u64(1050), 0, 0, 0, 0, 0, 0, 0]!
	}
	mut z := Field{}
	fe_mult(mut z, a, b)

	assert fe_equal(z, c) == true
}

struct TestMult {
	x Field
	y Field
	r Field
}

const tests_mult = [
	TestMult{
		x: Field{
			el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 1, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 1, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 1, 0, 0, 0, 0, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 1, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 1, 0]!
		}
		r: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 1, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(1), 0, 0, 0, 1, 0, 0, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 0, 0, 0, 1, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(0), 0, 0, 1, 0, 0, 0, 1]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 1, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(1), 0, 0, 0, 2, 0, 0, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 1, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(0), 1, 0, 0, 0, 2, 0, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(0), 0, 1, 0, 0, 0, 2, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0xaaaaaaaaaaaaaa), 0, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0xaaaaaaaaaaaaaa), 0, 0, 0, 0, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0xe38e38e38e38e4), 0x71c71c71c71c70, 0, 0, 0, 0, 0, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(1), 0, 0, 0, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 1, 0, 0, 0]!
		}
		r: Field{
			el: [u64(0), 0, 0, 0, 1, 0, 0, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 1, 1, 1, 0, 0, 0, 1]!
		}
		y: Field{
			el: [u64(0), 1, 0, 0, 1, 0, 0, 1]!
		}
		r: Field{
			el: [u64(2), 1, 3, 2, 3, 2, 4, 2]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 0, 0, 1, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 1, 0, 0, 1, 0]!
		}
		r: Field{
			el: [u64(0), 1, 0, 0, 0, 1, 1, 0]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 0, 0, 0, 1, 0, 0, 1]!
		}
		y: Field{
			el: [u64(0), 1, 0, 1, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(1), 0, 2, 1, 1, 1, 3, 2]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(1), 0, 0, 1, 0, 0, 0, 0]!
		}
		y: Field{
			el: [u64(0), 0, 0, 0, 0, 0, 0, 1]!
		}
		r: Field{
			el: [u64(0), 0, 1, 0, 0, 0, 1, 1]!
		}
	},
	TestMult{
		x: Field{
			el: [u64(0), 0, 0, 0, 1, 0, 1, 1]!
		}
		y: Field{
			el: [u64(0), 1, 1, 1, 0, 1, 0, 0]!
		}
		r: Field{
			el: [u64(3), 3, 1, 1, 4, 4, 2, 3]!
		}
	},
]

fn test_field_mult() {
	for item in tests_mult {
		mut z := Field{}
		fe_mult(mut z, item.x, item.y)
		assert z == item.r
	}
}

fn test_select_swap() {
	mut a := Field{[u64(0xbeee3fe4f8720f), 0xaf4abe14cdfa87, 0x743db59a7609ca, 0xa305baf38087e1,
		0x636c880ad0ba04, 0x9c67547aef0e39, 0xc762e2e801e21c, 0x36fccdeaaafccc]!}
	mut b := Field{[u64(0x4e4fd52cfb4cc0), 0x27311d6937b71d, 0x01e04a5644c6f4, 0x3e8bf7151334b9,
		0x9c4060a93baedc, 0x82486c2061b8f6, 0xed8ab5be2052d9, 0x9b9c0d091de1e8]!}

	mut c := Field{}
	mut d := Field{}

	fe_cselect(mut c, a, b, 1)
	fe_cselect(mut d, a, b, 0)

	// equal
	assert fe_equal(c, a) == true
	assert fe_equal(d, b) == true

	fe_cswap(mut c, mut d, 0)
	assert fe_equal(c, a) == true
	assert fe_equal(d, b) == true

	fe_cswap(mut c, mut d, 1)
	assert fe_equal(c, b) == true
	assert fe_equal(d, a) == true
}

fn test_sqrtratio() {
	x := Field{
		el: [
			u64(0x26a82bc70cc05e),
			0x80e18b00938e26,
			0xf72ab66511433b,
			0xa3d3a46412ae1a,
			0x0f1767ea6de324,
			0x36da9e14657047,
			0xed221d15a622bf,
			0x4f1970c66bed0d,
		]!
	}
	u := Field{
		el: [u64(0xfdbea9c1016921), 0x7ce9fb5b58ed6b, 0xb7182b43475674, 0x537802431535a5,
			0x6ee99099c9bdaf, 0x2d3b302e3babea, 0x71c5d7678ec053, 0x74366fc32eea26]!
	}
	v := Field{
		el: [u64(0x485756bfa5233f), 0x9c4ad3e553250c, 0xc75b7e3a92c2ee, 0xa46ead1f2530e3,
			0x19f43ab1316864, 0xff51be0c885062, 0x6c7f4fe091a63b, 0xf5b4544b009911]!
	}

	mut r := Field{}
	rr, ws := fe_sqrtratio(mut r, u, v)
	fe_abs(mut r, rr)

	assert fe_equal(r, x) == true

	assert ws == 1
}

fn test_unreduced_comparison() {
	a := fe_zero
	b := fe_p
	assert fe_equal(a, b) == true
}
