# curve448

A pure [V language](https://vlang.io/) implementation of **Curve448 / X448** elliptic-curve cryptography, conforming to [RFC 7748 (Section 5)](https://datatracker.ietf.org/doc/html/rfc7748).

`Curve448` (also known as `Curve448-Goldilocks`) is a Montgomery elliptic curve 
defined over the prime field $\mathbb{F}_p$ where:
$$p = 2^{448} - 2^{224} - 1$$

It offers ~224 bits of security (Level 5 security in NIST terminology) and 
is intended for use with the Elliptic-Curve Diffie–Hellman (ECDH) key agreement scheme.

---

## Features

- **Pure V Implementation**: Zero external C dependencies.
- **RFC 7748 Compliant**: Implements the standard `X448` Diffie-Hellman function, 
  handling scalar clamping and automatic reduction of non-canonical point inputs modulo $p$.
- **High-Performance Field Arithmetic**:
  - Uses an unsaturated 8-limb $\times$ 56-bit representation tailored to 
    Solinas reduction ($2^{448} \equiv 2^{224} + 1 \pmod p$).
  - Fast-path 2-way Karatsuba multiplication and dedicated squaring operation.
- **Constant-Time Ladder**: 448-step Montgomery ladder with branchless conditional swapping 
  (`fe_cswap`) to mitigate timing side-channel attacks.
- **Strict & Loose Point Validation**: Functions provided for both strict canonicality checks 
  (`validate_point`) and loose RFC 7748 input handling (`set_bytes_loosely`).

---

## Usage

### 1. Key Exchange (ECDH)

```v
import crypto.rand
import curve448

// Alice generates scalar key (56 bytes) and public key
alice_private := rand.bytes(56)! // ... fill with 56 random bytes ...
alice_public := curve448.x448(alice_private, curve448.base_point)!

// Bob generates scalar key (56 bytes) and public key
bob_private := rand.bytes(56)! // ... fill with 56 random bytes ...
bob_public := curve448.x448(bob_private, curve448.base_point)!

// Alice and Bob compute shared secret
alice_shared := curve448.x448(alice_private, bob_public)!
bob_shared := curve448.x448(bob_private, alice_public)!

assert alice_shared == bob_shared
```

### 2. Point Validation

```v
import curve448

// Validates that a 56-byte slice is a valid, canonical, non-low-order point
curve448.validate_point(public_key) or { println('Invalid public key: ${err}') }
```

---

## API Reference

### `fn x448(scalar []u8, point []u8) ![]u8`
Computes the X448 Diffie-Hellman function according to RFC 7748.
- `scalar`: 56-byte secret key (internally clamped).
- `point`: 56-byte $u$-coordinate of the input curve point.
- **Returns**: 56-byte little-endian encoded $u$-coordinate output point, 
  or an error if inputs are invalid or result in a low-order point.

### `fn validate_point(point []u8) !`
Validates that `point` is a valid 56-byte canonical, non-low-order point for X448.
- Returns an error if `point.len != 56`, if $u \ge p$ (non-canonical), 
- or if $u \in \{0, 1, p-1\}$ (known low-order points).

---

## Testing

Run unit tests and RFC 7748 test vectors:

```bash
v test .
```

---

## License

MIT License. See [LICENSE](LICENSE) for details.
