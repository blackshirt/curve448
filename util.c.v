// util.c.v — V bindings for 128-bit integer arithmetic (C interop)
//
// Thin wrapper around `util.h` (C header) exposing portable 128-bit
// primitives via V's C foreign-function interface.
//
// All operations use a split 64-bit representation:
//     value = (hi << 64) | lo
//
// The C backend handles three paths transparently:
//   • GCC/Clang  — unsigned __int128 (fastest)
//   • MSVC x64   — _umul128 / _addcarry_u64 / _subborrow_u64
//   • Generic    — pure software fallback (C99 compliant)
//
// Usage example:
//     mut hi := u64(0)
//     lo := mul_64_hw(0xFFFF_FFFF_FFFF_FFFF, 2, &hi)
//     // lo == 0xFFFF_FFFF_FFFF_FFFE, hi == 1
module curve448

#include "util.h"

// ------------------------------------------------------------------
// 64 × 64 → 128-bit full-width multiplication
// ------------------------------------------------------------------

// mul_64_hw performs an unsigned 64×64-bit multiplication and returns
// the full 128-bit product.
//
// Parameters:
//   a   — First multiplicand.
//   b   — Second multiplicand.
//   hi  — Out-pointer; receives the high 64 bits of the product.
//         Must be non-null; behaviour is undefined otherwise.
//
// Returns:
//   The low 64 bits of the product.
//
// The complete result is logically:  (*hi << 64) | return.
//
// Safety:
//   `hi` must point to valid writable memory. No overflow can occur;
//   the product always fits in 128 bits.
fn C.mul_64_hw(a u64, b u64, hi &u64) u64

// ------------------------------------------------------------------
// 128-bit addition & subtraction
// ------------------------------------------------------------------

// add_128_hw adds two 128-bit integers represented as 64-bit halves.
//
// Parameters:
//   a_lo    — Low 64 bits of the first addend.
//   a_hi    — High 64 bits of the first addend.
//   b_lo    — Low 64 bits of the second addend.
//   b_hi    — High 64 bits of the second addend.
//   out_hi  — Out-pointer; receives the high 64 bits of the sum.
//             Must be non-null.
//
// Returns:
//   The low 64 bits of the sum.
//
// The operation performed is:
//     (a_hi:a_lo) + (b_hi:b_lo)  →  (out_hi:return)
//
// Wrap-around is defined modulo 2^128 (no carry flag is exposed).
fn C.add_128_hw(a_lo u64, a_hi u64, b_lo u64, b_hi u64, out_hi &u64) u64

// sub_128_hw subtracts two 128-bit integers represented as 64-bit halves.
//
// Parameters:
//   a_lo    — Low 64 bits of the minuend.
//   a_hi    — High 64 bits of the minuend.
//   b_lo    — Low 64 bits of the subtrahend.
//   b_hi    — High 64 bits of the subtrahend.
//   out_hi  — Out-pointer; receives the high 64 bits of the difference.
//             Must be non-null.
//
// Returns:
//   The low 64 bits of the difference.
//
// The operation performed is:
//     (a_hi:a_lo) − (b_hi:b_lo)  →  (out_hi:return)
//
// Wrap-around is defined modulo 2^128 (no borrow flag is exposed).
fn C.sub_128_hw(a_lo u64, a_hi u64, b_lo u64, b_hi u64, out_hi &u64) u64
