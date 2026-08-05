/**
 * @file util128.h
 * @brief Portable 128-bit unsigned integer arithmetic primitives.
 *
 * Provides inline, zero-overhead functions for 64x64->128 multiplication,
 * 128-bit addition, subtraction, and packing/unpacking primitives.
 * Automatically selects the fastest strategy available:
 *   1. Compiler native __int128 (GCC / Clang / ICC)
 *   2. MSVC x64 intrinsics (_umul128, _addcarry_u64, _subborrow_u64)
 *   3. Pure C software fallback (32-bit / non-x64 compilers)
 *
 * Header-only; no external compilation unit or linking required.
 */

#ifndef UTIL128_H
#define UTIL128_H

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdint.h>

#if defined(_MSC_VER) && defined(_M_X64)
#include <intrin.h>
#endif

    /* ------------------------------------------------------------------ */
    /* Inlining & Portability Macros                                      */
    /* ------------------------------------------------------------------ */

#if defined(_MSC_VER)
#define UTIL128_INLINE __forceinline
#elif defined(__GNUC__) || defined(__clang__)
#define UTIL128_INLINE inline __attribute__((always_inline))
#else
#define UTIL128_INLINE inline
#endif

    /* ------------------------------------------------------------------ */
    /* Feature Detection for Native 128-bit Integer Support               */
    /* ------------------------------------------------------------------ */

#if defined(__SIZEOF_INT128__)
#define UTIL128_HAS_INT128 1
    /** @brief Native unsigned 128-bit integer type (GCC/Clang/ICC). */
    typedef unsigned __int128 uint128_t;
#else
#define UTIL128_HAS_INT128 0
#endif

    /* ------------------------------------------------------------------ */
    /* Packing / Unpacking (Native 128-bit types)                         */
    /* ------------------------------------------------------------------ */

#if UTIL128_HAS_INT128
    /**
     * pack128() - Assemble a native 128-bit integer from two 64-bit halves.
     *
     * @param lo  Least significant 64 bits [63:0].
     * @param hi  Most significant 64 bits [127:64].
     *
     * @return The combined 128-bit integer: (hi << 64) | lo.
     * @see lo128(), hi128()
     */
    static UTIL128_INLINE uint128_t pack128(uint64_t lo, uint64_t hi)
    {
        return ((uint128_t)hi << 64) | (uint128_t)lo;
    }

    /**
     * lo128() - Extract the lower 64 bits of a native 128-bit integer.
     *
     * @param v  Native 128-bit input value.
     *
     * @return Bits [63:0] of @p v.
     */
    static UTIL128_INLINE uint64_t lo128(uint128_t v)
    {
        return (uint64_t)v;
    }

    /**
     * hi128() - Extract the upper 64 bits of a native 128-bit integer.
     *
     * @param v  Native 128-bit input value.
     *
     * @return Bits [127:64] of @p v.
     */
    static UTIL128_INLINE uint64_t hi128(uint128_t v)
    {
        return (uint64_t)(v >> 64);
    }
#endif

    /* ------------------------------------------------------------------ */
    /* 64 × 64 → 128-bit Full-Width Multiplication                        */
    /* ------------------------------------------------------------------ */

    /**
     * mul_64_hw() - Multiply two unsigned 64-bit integers with a 128-bit result.
     *
     * Computes: (a * b) -> 128-bit product (hi:return)
     *
     * @param a    First multiplicand.
     * @param b    Second multiplicand.
     * @param hi   [out] Pointer to receiving buffer for upper 64 bits of product.
     *             Must be non-NULL; behavior is undefined if NULL.
     *
     * @return Lower 64 bits of the 128-bit product.
     *
     * @note Overflow cannot occur; any 64x64 product is fully representable in 128 bits.
     *
     * Example:
     * @code
     * uint64_t hi;
     * uint64_t lo = mul_64_hw(0xFFFFFFFFFFFFFFFFULL, 2, &hi);
     * // lo == 0xFFFFFFFFFFFFFFFE, hi == 1
     * @endcode
     */
    static UTIL128_INLINE uint64_t mul_64_hw(uint64_t a, uint64_t b, uint64_t *hi)
    {
#if UTIL128_HAS_INT128
        uint128_t r = (uint128_t)a * (uint128_t)b;
        *hi = hi128(r);
        return lo128(r);
#elif defined(_MSC_VER) && defined(_M_X64)
    return _umul128(a, b, hi);
#else
    /* Software 64x64 -> 128 multiplication via 32-bit partial products */
    uint64_t a_lo = (uint32_t)a;
    uint64_t a_hi = a >> 32;
    uint64_t b_lo = (uint32_t)b;
    uint64_t b_hi = b >> 32;

    uint64_t p0 = a_lo * b_lo;
    uint64_t p1 = a_lo * b_hi;
    uint64_t p2 = a_hi * b_lo;
    uint64_t p3 = a_hi * b_hi;

    uint64_t cy = (p0 >> 32) + (uint32_t)p1 + (uint32_t)p2;
    *hi = p3 + (p1 >> 32) + (p2 >> 32) + (cy >> 32);
    return p0 + (p1 << 32) + (p2 << 32);
#endif
    }

    /* ------------------------------------------------------------------ */
    /* 128-bit Addition & Subtraction                                     */
    /* ------------------------------------------------------------------ */

    /**
     * add_128_hw() - Add two 128-bit integers represented as split 64-bit pairs.
     *
     * Computes: (a_hi:a_lo) + (b_hi:b_lo) -> (out_hi:return)
     *
     * @param a_lo    Lower 64 bits of the first addend.
     * @param a_hi    Upper 64 bits of the first addend.
     * @param b_lo    Lower 64 bits of the second addend.
     * @param b_hi    Upper 64 bits of the second addend.
     * @param out_hi  [out] Pointer to receiving buffer for upper 64 bits of sum.
     *                Must be non-NULL; behavior is undefined if NULL.
     *
     * @return Lower 64 bits of the sum.
     *
     * @note Arithmetic wraps around modulo 2^128 (carry bit beyond bit 127 is discarded).
     */
    static UTIL128_INLINE uint64_t add_128_hw(uint64_t a_lo, uint64_t a_hi,
                                              uint64_t b_lo, uint64_t b_hi,
                                              uint64_t *out_hi)
    {
#if UTIL128_HAS_INT128
        uint128_t r = pack128(a_lo, a_hi) + pack128(b_lo, b_hi);
        *out_hi = hi128(r);
        return lo128(r);
#elif defined(_MSC_VER) && defined(_M_X64)
    uint64_t res_lo;
    unsigned char carry = _addcarry_u64(0, a_lo, b_lo, &res_lo);
    _addcarry_u64(carry, a_hi, b_hi, out_hi);
    return res_lo;
#else
    /* Portable manual carry propagation */
    uint64_t res_lo = a_lo + b_lo;
    uint64_t carry = (res_lo < a_lo);
    *out_hi = a_hi + b_hi + carry;
    return res_lo;
#endif
    }

    /**
     * sub_128_hw() - Subtract two 128-bit integers represented as split 64-bit pairs.
     *
     * Computes: (a_hi:a_lo) - (b_hi:b_lo) -> (out_hi:return)
     *
     * @param a_lo    Lower 64 bits of the minuend.
     * @param a_hi    Upper 64 bits of the minuend.
     * @param b_lo    Lower 64 bits of the subtrahend.
     * @param b_hi    Upper 64 bits of the subtrahend.
     * @param out_hi  [out] Pointer to receiving buffer for upper 64 bits of difference.
     *                Must be non-NULL; behavior is undefined if NULL.
     *
     * @return Lower 64 bits of the difference.
     *
     * @note Arithmetic wraps around modulo 2^128 (borrow bit beyond bit 127 is discarded).
     */
    static UTIL128_INLINE uint64_t sub_128_hw(uint64_t a_lo, uint64_t a_hi,
                                              uint64_t b_lo, uint64_t b_hi,
                                              uint64_t *out_hi)
    {
#if UTIL128_HAS_INT128
        uint128_t r = pack128(a_lo, a_hi) - pack128(b_lo, b_hi);
        *out_hi = hi128(r);
        return lo128(r);
#elif defined(_MSC_VER) && defined(_M_X64)
    uint64_t res_lo;
    unsigned char borrow = _subborrow_u64(0, a_lo, b_lo, &res_lo);
    _subborrow_u64(borrow, a_hi, b_hi, out_hi);
    return res_lo;
#else
    /* Portable manual borrow propagation */
    uint64_t borrow = (a_lo < b_lo);
    *out_hi = a_hi - b_hi - borrow;
    return a_lo - b_lo;
#endif
    }

#ifdef __cplusplus
}
#endif

#endif /* UTIL128_H */