// ============================================================================
// CLEANED-UP COMMENT SECTIONS FOR FIELD.V
//
// This file shows improved inline comments for key sections of field.v,
// focusing on clarity, reduced redundancy, and better structure.
// ============================================================================

// ============================================================================
// SECTION 1: Solinas Reduction (Reusable Explanation)
// ============================================================================
//
// CORE CONCEPT: Solinas Reduction
//
// For Curve448, the prime p = 2⁴⁴⁸ - 2²²⁴ - 1 admits a fast reduction rule:
//
//   2⁴⁴⁸ ≡ 2²²⁴ + 1  (mod p)
//
// This means any overflow at the top limb (limb 7) can be folded back by
// adding its carry to limbs 0 and 4. In effect, it replaces an expensive
// full modular reduction with cheap additions to two limbs.
//
// Used throughout: fe_add, fe_sub, fe_negate, fe_weak_reduce, fe_reduce,
// fe_mult_32, and all carry-propagation routines.

// ============================================================================
// SECTION 2: fe_sub with Improved Comments
// ============================================================================

/// fe_sub computes modular field subtraction: z = a - b (mod p).
///
/// The key challenge: direct subtraction risks underflow since b might be
/// "redundant" (limbs up to 2⁵⁷). Solution: use 4×p as an offset.
///
/// Why 4×p (not 2×p)?
/// - Each limb b[i] can reach ~2⁵⁷ before reduction.
/// - Using 2×p leaves only a 1–3 unit safety margin.
/// - 4×p provides comfortable headroom and is still fast to precompute.
///
/// Algorithm:
///   1. Compute (a + 4p) - b per limb. The 4p offset prevents underflow.
///   2. Extract 56-bit portion and carry for each result.
///   3. Propagate carries left-to-right (limbs 0..6 to their next).
///   4. Fold the top carry (c7) back via Solinas: c7 → limbs 0 and 4.
///   5. Apply single-pass weak reduction (all limbs back to <2⁵⁶).
fn fe_sub(mut z Field, a Field, b Field) {
	// Per-limb: (a + 4p) - b, extracting 56-bit result and carry.
	// 4×p ensures (a[i] + 4p[i]) ≥ b[i] even if b is redundant.
	z0 := (a.el[0] + fe_4p_limbs[0]) - b.el[0]
	c0 := z0 >> limb_bits_size
	z.el[0] = z0 & mask_56bits

	z1 := (a.el[1] + fe_4p_limbs[1]) - b.el[1]
	c1 := z1 >> limb_bits_size
	z.el[1] = z1 & mask_56bits

	// [... limbs 2–6 follow same pattern ...]

	z7 := (a.el[7] + fe_4p_limbs[7]) - b.el[7]
	c7 := z7 >> limb_bits_size
	z.el[7] = z7 & mask_56bits

	// Fold top carry into limbs 0 and 4 (Solinas: 2⁴⁴⁸ ≡ 2²²⁴ + 1 mod p).
	z.el[0] += c7
	z.el[4] += c7

	// Ripple lower carries c0..c6 to adjacent higher limbs.
	z.el[1] += c0
	z.el[2] += c1
	// [... and so on ...]

	// Single pass: all limbs now in [0, 2⁵⁶).
	fe_weak_reduce_1pass(mut z)
}

// ============================================================================
// SECTION 3: fe_cmp with Better Flow Description
// ============================================================================

/// fe_cmp compares two field elements in constant-time.
///
/// Returns: 1 if a ≡ b (mod p), 0 otherwise.
///
/// Constant-time design (no branches on secret data):
///   - Both inputs reduced to canonical form [0, p-1].
///   - Compare all 8 limbs via XOR (bitwise, not conditional).
///   - Any differing bit sets accumulator → result is 0.
///   - No early exit if a mismatch is found.
fn fe_cmp(a Field, b Field) int {
	// Reduce both to [0, p-1] canonical form.
	mut x := a
	mut y := b
	fe_reduce(mut x)
	fe_reduce(mut y)

	// Accumulate XOR of all limbs. If any limb differs, c != 0.
	mut c := u64(0)
	c |= x.el[0] ^ y.el[0]
	// [... all 8 limbs ...]

	// Branchless: convert c=0 → return 1, c≠0 → return 0
	// Trick: (c | -c) has bit 63 set iff c ≠ 0. Right-shift by 63 gives 0 or 1.
	return int(1 - ((c | (0 - c)) >> 63))
}

// ============================================================================
// SECTION 4: fe_power446 with Better Structure
// ============================================================================

/// fe_power446 computes v = z^((p-3)/4) (mod p).
///
/// Used in:
///   - fe_inverse: via Fermat's Little Theorem (x⁻¹ ≡ x^(p-2) mod p)
///   - fe_sqrtratio: to extract square roots
///
/// Strategy: addition chain with pre-computed powers.
/// The exponent factors as: 2⁴⁴⁶ - 2²²² - 1 = (2²²² - 1)·2²²⁴ + (2²²² - 1)
///
/// Intermediate powers (built bottom-up):
/// - Level 1 (small): t3, t6, t9
/// - Level 2 (medium): t18, t37
/// - Level 3 (large): t111, t222, t223
/// - Final: v = z^((p-3)/4)
///
/// Each power is computed via doubling and multiplication to match the
/// exponent's binary form. This beats naive repeated squaring.
fn fe_power446(mut v Field, z Field) {
	mut t1 := Field{}
	mut t2 := Field{}
	mut t3 := Field{}

	// Base case: t3 = z^3 (via z², z⁴, z³, then z³·z⁴ = z⁷ = 2³-1)
	fe_sqr(mut t1, z)
	fe_sqr(mut t2, t1)
	fe_mult(mut t3, z, t1)
	fe_mult(mut t3, t3, t2)

	// Level 1: t6 = z^(2⁶-1) by squaring t3 three times and multiplying by t3.
	mut t6 := Field{}
	fe_sqr_n(mut t6, t3, 3)  // t6 = z^(7·2³)
	fe_mult(mut t6, t6, t3)   // t6 = z^(7·2³ + 7) = z^(2⁶-1)

	// Level 2: t9, t18, t37 follow the same pattern with larger exponents.
	// [... see code for details ...]

	// Final: combine t223 and t222 to get the full exponent.
	fe_sqr_n(mut v, t223, 223)
	fe_mult(mut v, v, t222)
}

// ============================================================================
// SECTION 5: fe_is_canonical with Simplified Explanation
// ============================================================================

/// fe_is_canonical checks if z ∈ [0, p-1] in one constant-time pass.
///
/// Two conditions must both hold for canonicality:
///   (a) Every limb fits in 56 bits (no carry overflow)
///   (b) Numeric value < p = 2⁴⁴⁸ - 2²²⁴ - 1
///
/// Clever trick: add the Solinas constant (2²²⁴ + 1) and check for overflow.
/// - If z < p, then z + (2²²⁴ + 1) < 2⁴⁴⁸ (no final carry).
/// - If z ≥ p, then z + (2²²⁴ + 1) ≥ 2⁴⁴⁸ (carry out = 1).
/// - As a bonus, any limb > 56 bits also causes a spurious carry → c=1.
///
/// Result: single-pass carry propagation catches both overflow conditions.
/// Branchless, no data-dependent memory access.
fn fe_is_canonical(z Field) int {
	// Add 2²²⁴ + 1 = [1, 0, 0, 0, 1, 0, 0, 0] with carry propagation.
	s0 := z.el[0] + u64(1)
	c0 := s0 >> 56

	s1 := z.el[1] + c0
	c1 := s1 >> 56

	// [... limbs 2–3 ...]

	// Second half: add the 2²²⁴ part (into limb 4).
	s4 := z.el[4] + u64(1) + c3
	c4 := s4 >> 56

	// [... limbs 5–7 ...]

	// c7 == 1 ↔ z >= p  (NOT canonical)
	// c7 == 0 ↔ z < p   (canonical)
	return int(1 - c7)
}

// ============================================================================
// SECTION 6: fe_reduce with Better Algorithm Explanation
// ============================================================================

/// fe_reduce produces the unique canonical representative z ∈ [0, p-1].
///
/// PRECONDITION: all limbs must be < 2⁵⁶ (normalized form from fe_weak_reduce).
///
/// Algorithm (4 steps):
///
/// Step 1: Normalize limbs via fe_weak_reduce (ensure all < 2⁵⁶).
///
/// Step 2: Test if z ≥ p by checking overflow of z + (2²²⁴ + 1).
///   Result: c = 1 if z ≥ p, else c = 0.
///
/// Step 3: Conditionally add (2²²⁴ + 1) to limbs 0 and 4.
///   - If c=0: z unchanged, already in [0, p-1].
///   - If c=1: z + (2²²⁴ + 1) now in [p + 2²²⁴ + 1, 2⁴⁴⁸ + 2²²⁴].
///
/// Step 4: Propagate carries. The top carry c is discarded (deliberate).
///   Discarding c is equivalent to the Solinas subtraction:
///     x - p ≡ x - (2⁴⁴⁸ - 2²²⁴ - 1)  (mod p)
///   The result x - p is in [0, 2²²⁴] ⊂ [0, p), already canonical.
///
/// No further reduction needed after this.
fn fe_reduce(mut x Field) {
	fe_weak_reduce(mut x)

	// Test if x ≥ p by adding Solinas constant and checking overflow.
	mut c := u64(1)
	c = (x.el[0] + c) >> 56
	c = (x.el[1] + c) >> 56
	// [... propagate through limbs 2–7 ...]

	// Conditionally add Solinas constant to pull x into [0, p).
	x.el[0] += c
	x.el[4] += c

	// Extract 56-bit chunks. Top carry is intentionally lost.
	mut s := x.el[0]
	x.el[0] = s & mask_56bits; c = s >> 56; s = x.el[1] + c
	x.el[1] = s & mask_56bits; c = s >> 56; s = x.el[2] + c
	// [... continue for all limbs ...]
	x.el[7] = s & mask_56bits
	// Final c is discarded (the 2⁴⁴⁸ term).
}

// ============================================================================
// SECTION 7: fe_weak_reduce Explained
// ============================================================================

/// fe_weak_reduce normalizes all limbs to [0, 2⁵⁶) via carry propagation.
///
/// Used internally after addition/subtraction/multiplication before full
/// reduction. The result is "weakly reduced" (limbs < 2⁵⁶) but not necessarily
/// canonical (value may still be ≥ p).
///
/// Algorithm (3 parts):
///
/// Part 1: First pass — extract 56-bit limbs, propagate carries left-to-right.
/// Part 2: Fold top carry via Solinas (c7 → limbs 0, 4).
/// Part 3: Repeat pass + fold a second time (mathematically sufficient).
/// Part 4: Final ripple — clean up any single-bit overflow in limbs 0 or 4.
///
/// Two passes suffice because the Solinas fold reduces the carry magnitude
/// faster than naive propagation.
fn fe_weak_reduce(mut x Field) {
	// Pass 1: Extract 56-bit limbs, propagate carries.
	mut c := u64(0)
	mut s := x.el[0] + c
	x.el[0] = s & mask_56bits; c = s >> 56; s = x.el[1] + c
	// [... limbs 1–7 follow same pattern ...]

	// Solinas fold: top carry back to limbs 0 and 4.
	x.el[0] += c
	x.el[4] += c

	// Pass 2: Repeat extraction and carry propagation.
	c = x.el[0] >> 56
	x.el[0] &= mask_56bits; s = x.el[1] + c
	// [... limbs 1–7 ...]

	// Solinas fold again.
	x.el[0] += c
	x.el[4] += c

	// Final ripple: any overflow in limb 0 or 4 after the folds.
	x.el[1] += x.el[0] >> limb_bits_size
	x.el[0] &= mask_56bits
	x.el[5] += x.el[4] >> limb_bits_size
	x.el[4] &= mask_56bits
}

// ============================================================================
// SECTION 8: Constant-Time Selection Primitives
// ============================================================================

/// fe_cselect and fe_cswap implement constant-time conditional logic.
///
/// These are used to avoid data-dependent branches when comparing or
/// selecting between field elements (e.g., during ladder steps in ECDH).
///
/// Both use a derived bitmask from the condition:
///   m = 0xFFFF...FFFF if c ≠ 0 (via mask_64bits)
///   m = 0x0000...0000 if c = 0
///
/// fe_cselect:
///   z = (a & m) | (b & ~m)   → z = a if c≠0, else b
///
/// fe_cswap:
///   d = m & (a ^ b)  (difference mask)
///   a ^= d           (apply difference)
///   b ^= d           (apply opposite)
///   Result: swapped if c≠0, unchanged if c=0
///
/// Critically: no branches, no data-dependent memory accesses.
/// All operations are bitwise, executed unconditionally.

// ============================================================================
// SECTION 9: Limb Representation and Bounds
// ============================================================================

/// FIELD ELEMENT REPRESENTATION
///
/// Each Field element is 8 limbs of u64, interpreted as 56-bit chunks in
/// little-endian order:
///
///   value = el[0]·2⁰  + el[1]·2⁵⁶ + el[2]·2¹¹² + el[3]·2¹⁶⁸
///         + el[4]·2²²⁴ + el[5]·2²⁸⁰ + el[6]·2³³⁶ + el[7]·2³⁹²
///
/// LIMB BOUNDS:
///
/// - CANONICAL: each limb < 2⁵⁶ (fits in 56 bits), and value < p.
///   Only canonical form is suitable for serialization (bytes()).
///
/// - NORMALIZED: each limb < 2⁵⁶ but value may be ≥ p.
///   Produced by fe_weak_reduce; used internally before fe_reduce.
///
/// - REDUNDANT: intermediate computations allow limbs up to ~2⁵⁷.
///   Used between arithmetic operations before normalization.
///
/// WHY UNSATURATED?
///
/// Storing each 56-bit chunk in a u64 wastes 8 bits but:
///   - Avoids expensive 56-bit multiplies (hardware usually does 64-bit).
///   - Allows lazy carry handling (batch multiple operations).
///   - Simplifies logic: all operations fit in u64, no fancy math needed.

