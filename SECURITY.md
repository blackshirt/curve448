# Security Policy

`curve448` is a pure-V implementation of Curve448 / X448 (RFC 7748 §5). This
document describes what the library defends against, what it explicitly does
not, and how to report a suspected vulnerability. It exists mainly because
those caveats were previously scattered across individual function comments
(`fe_clear`, the low-order-point check in `x448()`, etc.) — this consolidates
them into one place a downstream consumer or auditor can check first.

## Reporting a vulnerability

Please **do not open a public GitHub issue** for a suspected security
vulnerability (timing leak, incorrect point validation, memory-safety bug,
or any deviation from RFC 7748 that has security consequences).

Instead, use GitHub's private vulnerability reporting for this repository
(**Security** tab → **Report a vulnerability**), which opens a private
advisory visible only to the maintainer until a fix is ready. If that
isn't available, open a regular issue asking for a private contact channel
rather than describing the issue in public.

Please include:
- The affected function(s) and V/compiler version.
- A minimal reproduction (test vector, or a `v test` case).
- Your assessment of impact (e.g. "leaks scalar bit via timing", "accepts
  an invalid point as valid").

There is currently no bug bounty program. As a solo/small-maintainer
project, response times are best-effort, not SLA-backed.

## Threat model

This library implements the **X448 Diffie-Hellman function** as a
cryptographic primitive: `Field` arithmetic mod `p = 2⁴⁴⁸ - 2²²⁴ - 1`, the
Montgomery ladder, and RFC 7748 point (de)serialization/validation. It is
**not** a protocol implementation — key derivation, transcript binding,
authentication, and replay protection are the caller's responsibility (see
[Integration notes](#integration-notes) below).

Within that scope, the design goal is: an attacker who can measure
**wall-clock timing and control-flow behavior**, but who has **no direct
access to secret-dependent memory addresses or register contents**, should
not learn anything about the private scalar beyond what the protocol
intentionally reveals (the public output point, and whether it happened to
be a low-order point).

## What is implemented, and how

- **Fixed-trip-count Montgomery ladder.** The scalar loop in `x448()`
  always runs exactly 448 iterations, regardless of scalar value. The
  per-bit `kt` value is derived only from the public loop counter `t` and
  read from a scalar byte at an index derived only from `t` — not from any
  previously-computed secret state.
- **Branchless conditional swap/select.** `fe_cswap`/`fe_cselect` use a
  bitmask derived from the condition (`mask_64bits`, via the
  `(x | -x) >> 63` trick) rather than an `if`, so the executed instruction
  sequence and memory access pattern do not depend on the swap condition.
- **Branchless comparison.** `fe_cmp`/`fe_equal`/`fe_is_zero` accumulate
  differences via XOR/OR across all limbs rather than short-circuiting, so
  comparison time does not depend on *where* two values first differ.
- **Fixed-size, uniform field representation.** Every `Field` operation
  processes all 8 limbs unconditionally; there are no data-dependent loop
  bounds or early returns inside the field-arithmetic hot path (`fe_add`,
  `fe_sub`, `fe_mult`, `fe_sqr`, `fe_reduce`, `fe_weak_reduce`).
- **Scalar clamping and zeroing.** `x448()` clones the input scalar,
  clamps it per RFC 7748, and wipes both the clamped clone and all
  `Field` temporaries (`a`, `aa`, `b`, `bb`, `e`, `c`, `d`, `da`, `cb`,
  `x1`..`z3`, the final `ret`) via `defer` blocks before returning.
- **RFC 7748 point handling.** `set_bytes_loosely` reduces non-canonical
  input points (`u >= p`) mod `p` rather than rejecting them, matching the
  RFC's mandated behavior for the `x448()` entry point.
  `validate_point()`/`PublicKey.validate()` additionally reject known
  low-order points (`u ∈ {0, 1, p-1}`) for callers who want strict
  validation instead.
- **One intentional data-dependent branch.** After the ladder completes,
  `x448()` branches on whether the output is all-zero
  (`ret_is_zero == 1`) to decide whether to return an error. This is safe
  *because* the branch condition is a function of the already-public
  output value — the decoded output bytes reveal the same information to
  anyone who receives them regardless of which branch was taken, so
  branching on it in-process leaks nothing additional.

## What this library does **not** claim

Being explicit about these matters more than the guarantees above, since
overclaiming here is worse than not claiming at all:

- **No protection against physical side channels.** Power analysis (SPA/DPA),
  electromagnetic emission analysis, and acoustic side channels are out of
  scope. The techniques above address *timing and control-flow* leakage
  observable by a co-located software attacker, not physical measurement.
- **No verified protection against cache-timing / microarchitectural
  attacks** (e.g. Spectre-class, cache-occupancy side channels). Data-
  independent memory *access patterns* are a necessary ingredient for
  cache-timing resistance and are followed here, but the library has not
  been evaluated against microarchitectural attack frameworks, and V's
  code generation (through its C backend, or the native backend) is not
  independently verified to preserve the source-level constant-time
  properties at the machine-code level.
- **Best-effort zeroization only.** `secure_zero_ptr` uses a `volatile`
  byte-pointer write loop to resist dead-store elimination, matching common
  practice (comparable to `explicit_bzero`/`memset_s`-style approaches),
  but this has not been audited at the generated C/assembly level for this
  specific toolchain and optimization settings. Compiler upgrades or
  alternate backends could in principle change this. If your threat model
  requires a hard zeroization guarantee, audit the generated output for
  your specific build configuration before relying on it.
- **No independent side-channel testing has been performed.** There is no
  `dudect`-style statistical timing test, formal verification, or
  third-party security audit of this codebase to date. Correctness is
  covered by RFC 7748 test vectors and randomized property-based tests
  against an independent `math.big` oracle (see `field_property_test.v`);
  neither of those establishes constant-time behavior, only functional
  correctness.
- **No signature scheme.** This library implements X448 (Diffie-Hellman)
  only. Ed448 (EdDSA signatures) is a separate curve model (twisted
  Edwards vs. this Montgomery representation) and is not implemented here.
  A few primitives that a future Ed448/Decaf-style layer would need
  (`fe_sqrtratio`, `fe_abs`, `is_negative`) exist and are unit-tested but
  are currently unused by `x448()` itself.
- **CSPRNG quality is delegated, not evaluated here.**
  `generate_private_key()` sources randomness from `crypto.rand.bytes()`
  in V's standard library, which in turn depends on the OS-provided CSPRNG.
  This library does not implement, audit, or add any entropy-quality
  checks of its own.
- **Not a protocol implementation.** Authentication, transcript binding,
  key confirmation, downgrade/replay protection, and safe key derivation
  from the raw shared secret (e.g. via HKDF) are all the caller's
  responsibility. Passing the raw `x448()` output directly to a symmetric
  cipher as a key, without a KDF, is a caller error this library cannot
  detect or prevent.

## Integration notes

- Treat the output of `x448()` / `PrivateKey.shared_secret()` as raw
  Diffie-Hellman output, not a symmetric key — run it through a KDF (e.g.
  HKDF) bound to the protocol transcript before use, per standard ECDH
  guidance.
- Prefer the typed `PrivateKey`/`PublicKey` API (`keys.v`) over the free
  `x448(scalar, point)` function where possible: it removes the
  argument-order confusion that the untyped `[]u8`/`[]u8` signature
  otherwise allows (see the `keys.v` doc comment for the specific failure
  mode this prevents).
- Call `PrivateKey.zero()` once a private key is no longer needed. Note
  that this wipes the `PrivateKey`'s own storage only — any other copy of
  the scalar bytes you made yourself (e.g. the original `[]u8` passed to
  `new_private_key`) is not tracked or wiped by this library.

## Dependency policy

Zero C dependencies beyond what V's standard library (`vlib`) itself
wraps. No third-party V packages. This keeps the supply-chain surface
limited to the V toolchain and standard library.
