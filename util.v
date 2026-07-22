// Copyright © 2026 blackshirt.
// Use of this source code is governed by an MIT license
// that can be found in the LICENSE file.
//
// Some helpers used accross the module
module curve448

@[inline]
fn secure_zero_ptr(ptr voidptr, len isize) {
	if isnil(ptr) || len == 0 {
		return
	}
	unsafe {
		// 1. Fast zeroing via built-in vmemset
		vmemset(ptr, 0, len)

		// 2. Pure V Volatile Read Dependency
		// Reading a byte via a volatile pointer forces the compiler to commit
		// all prior memory stores before executing the read.
		mut volatile vptr := &u8(ptr)
		_ = vptr[0]
	}
}

// secure_zeroise zeroises buf data securely.
@[inline]
fn secure_zeroise(mut buf []u8) {
	if buf.len == 0 {
		return
	}

	unsafe {
		// 1. Fast zeroing
		vmemset(buf.data, 0, buf.len)

		// 2. Pure V Compiler Barrier
		// Force a volatile read on the first byte.
		// The compiler cannot elide the `vmemset` store above because
		// it must satisfy this subsequent volatile read access.
		mut volatile vp := &u8(buf.data)
		_ = vp[0]
	}
}
