# curve448

A pure [V language](https://vlang.io/) implementation of **Curve448 / X448** elliptic-curve Diffie–Hellman, conforming to [RFC 7748 §5](https://datatracker.ietf.org/doc/html/rfc7748#section-5).

`Curve448` (also known as `Curve448-Goldilocks`) is a Montgomery elliptic curve defined over the prime field $\mathbb{F}_p$ where:

$$p = 2^{448} - 2^{224} - 1$$

It offers ~224 bits of security and is a standard choice for ECDH key agreement when 128-bit security (P-256, X25519) is not sufficient.

---

## Features

- **Pure V** — zero external C dependencies beyond V's standard library.
- **RFC 7748 compliant** — correct scalar clamping; non-canonical input points are automatically reduced mod $p$ per the RFC.
- **Type-safe key API** — distinct `PrivateKey` and `PublicKey` types prevent accidentally swapping arguments to the scalar multiplication function.
- **High-performance field arithmetic** — unsaturated 8-limb × 56-bit representation with Solinas reduction ($2^{448} \equiv 2^{224} + 1 \pmod{p}$), Karatsuba multiplication, and a dedicated squaring path.
- **Constant-time ladder** — 448-step Montgomery ladder with branchless `fe_cswap` to mitigate timing side-channel attacks.
- **Point validation** — both strict canonical validation (`validate_point`) and lenient RFC 7748 input handling (`set_bytes_loosely`) are provided.

---

## Installation

```bash
v install blackshirt.curve448
```

Or clone directly and reference the module path in your project.

---

## Usage

### Key exchange (ECDH) — recommended API

Use the typed `PrivateKey` / `PublicKey` API. The compiler rejects swapped arguments at compile time, removing an entire class of silent key-misuse bugs.

```v
import curve448

// Alice generates her key pair
alice_priv := curve448.generate_private_key()!
alice_pub := alice_priv.public_key()!

// Bob generates his key pair
bob_priv := curve448.generate_private_key()!
bob_pub := bob_priv.public_key()!

// Both sides derive the same shared secret
alice_shared := alice_priv.shared_secret(bob_pub)!
bob_shared := bob_priv.shared_secret(alice_pub)!

assert alice_shared == bob_shared

// Wipe private key material when done
alice_priv.zero()
bob_priv.zero()
```

> **Important:** the raw output of `shared_secret()` is Diffie–Hellman output, not a symmetric key. Run it through a KDF (e.g. HKDF) bound to your protocol transcript before using it as a key.

### Key exchange — low-level byte-slice API

The free `x448()` function is still available for code that works directly with `[]u8` buffers (e.g. TLS `key_share` parsers):

```v
import curve448

alice_shared := curve448.x448(alice_private_bytes, bob_public_bytes)!
```

Scalar clamping and low-order-point rejection are applied the same way as in the typed API.

### Constructing keys from existing bytes

```v
import curve448

priv_key := curve448.new_private_key(raw_scalar_56_bytes)!
pub_key := curve448.new_public_key(raw_point_56_bytes)!
```

### Point validation

`validate_point` / `PublicKey.validate()` enforce strict RFC 7748 rules: the point must be canonical ($u < p$) and must not be a known low-order point ($u \notin \{0, 1, p-1\}$).

```v
import curve448

// Validate before use when strict checking is required
pub_key.validate() or { return error('rejected: ${err}') }
```

`x448()` and `shared_secret()` already reject low-order output points at the end of the ladder, so explicit pre-validation is optional for ECDH; it is mainly useful when you want to reject suspicious peer keys early rather than after computation.

---

## API Reference

### Types

#### `PrivateKey`

A 56-byte X448 secret scalar. Created via `generate_private_key()` or `new_private_key(b []u8)`.

| Method | Description |
|---|---|
| `pub_key() !PublicKey` | Derives the corresponding public key (scalar × base point). |
| `shared_secret(peer PublicKey) ![]u8` | Computes the ECDH shared secret. Returns an error on low-order output. |
| `bytes() []u8` | Returns a copy of the raw scalar bytes. |
| `zero()` | Wipes the scalar bytes in place. Call when the key is no longer needed. |

#### `PublicKey`

A 56-byte X448 point $u$-coordinate. Created via `new_public_key(b []u8)`.

| Method | Description |
|---|---|
| `validate() !` | Strict RFC 7748 point validation (canonical + non-low-order). |
| `bytes() []u8` | Returns a copy of the raw point bytes. |

### Free functions

#### `fn x448(scalar []u8, point []u8) ![]u8`

Low-level scalar multiplication. Both `scalar` and `point` must be exactly 56 bytes. The scalar is clamped internally. Non-canonical point bytes are reduced mod $p$. Returns an error if the output is a low-order point.

#### `fn validate_point(point []u8) !`

Strict point validation. Returns an error if `point.len != 56`, if $u \geq p$, or if $u \in \{0, 1, p-1\}$.

#### `fn generate_private_key() !PrivateKey`

Generates a fresh `PrivateKey` from the OS CSPRNG (`crypto.rand`).

#### `fn new_private_key(b []u8) !PrivateKey`

Wraps an existing 56-byte scalar into a `PrivateKey`. No validation beyond length; clamping is applied at use time.

#### `fn new_public_key(b []u8) !PublicKey`

Wraps an existing 56-byte point into a `PublicKey`. Non-canonical or low-order inputs are accepted here per RFC 7748; call `.validate()` explicitly if you need strict checking.

### Constants

| Name | Value | Description |
|---|---|---|
| `base_point` | `[5, 0, 0, …]` (56 bytes LE) | Standard generator, $u = 5$. |
| `scalar_size` | `56` | Byte length of scalars and point coordinates. |

---

## Security notes

The library targets software timing-channel resistance:

- **Fixed-trip-count ladder** — always 448 iterations; scalar bits never control branches or memory addresses.
- **Branchless field operations** — `fe_cswap`, `fe_cselect`, and all comparisons use bitmasks rather than conditional branches.
- **Scalar and field zeroization** — clamped scalar copies and all ladder temporaries are wiped with `defer` blocks after use.

There are important caveats. This implementation has **not** been audited, has no `dudect`-style statistical timing tests, and makes no claims about physical side channels (power, EM) or microarchitectural attacks (Spectre, cache occupancy). See [SECURITY.md](SECURITY.md) for the full threat model and a detailed list of what this library does and does not protect against.

---

## Testing

Run unit tests and RFC 7748 test vectors:

```bash
v test .
```

Tests include:
- RFC 7748 §6.2 known-answer vectors for `x448`.
- Randomized property-based tests against a `math.big` oracle (`field_property_test.v`).
- Key API round-trip tests (`keys_test.v`).

---

## License

MIT. See [LICENSE](LICENSE) for details.