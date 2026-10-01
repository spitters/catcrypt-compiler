#!/usr/bin/env python3
"""Check the RV64 X25519 objects against RFC 7748.

Usage: check.py <runner...>          (for example: check.py qemu-riscv64 gen/driver)
       check.py --full <runner...>   (for example: check.py --full qemu-riscv64 gen/driver_x25519)

Without --full the driver runs the ladder and prints its projective result (x2, z2);
this script forms x2 / z2 mod p. With --full the driver runs the whole X25519 function
on the unclamped scalar and unmasked u and prints its 32 output bytes. Either way the
result is compared with the RFC 7748 Section 5 algorithm below, on the Section 5.2
vectors and on random inputs. The reference itself is checked against the published
outputs first.
"""
import random
import subprocess
import sys

P = 2**255 - 19
A24 = 121665


def clamp(k):
    k = bytearray(k)
    k[0] &= 248
    k[31] &= 127
    k[31] |= 64
    return bytes(k)


def mask_u(u):
    u = bytearray(u)
    u[31] &= 127
    return bytes(u)


def x25519_ref(k, u):
    k = int.from_bytes(clamp(k), "little")
    x1 = int.from_bytes(mask_u(u), "little")
    x2, z2, x3, z3, swap = 1, 0, x1, 1, 0
    for t in range(254, -1, -1):
        kt = (k >> t) & 1
        swap ^= kt
        if swap:
            x2, x3, z2, z3 = x3, x2, z3, z2
        swap = kt
        a = (x2 + z2) % P
        aa = a * a % P
        b = (x2 - z2) % P
        bb = b * b % P
        e = (aa - bb) % P
        c = (x3 + z3) % P
        d = (x3 - z3) % P
        da = d * a % P
        cb = c * b % P
        x3 = (da + cb) ** 2 % P
        z3 = x1 * (da - cb) ** 2 % P
        x2 = aa * bb % P
        z2 = e * (aa + A24 * e) % P
    if swap:
        x2, x3, z2, z3 = x3, x2, z3, z2
    return (x2 * pow(z2, P - 2, P) % P).to_bytes(32, "little")


RFC_VECTORS = [
    ("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
     "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
     "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"),
    ("4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
     "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
     "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"),
    # Section 5.2, the iterated test after one iteration: k = u = 9.
    ("09" + "00" * 31, "09" + "00" * 31,
     "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079"),
]


def main():
    full = sys.argv[1:2] == ["--full"]
    runner = sys.argv[2:] if full else sys.argv[1:]
    if not runner:
        sys.exit(__doc__)
    for k, u, out in RFC_VECTORS:
        got = x25519_ref(bytes.fromhex(k), bytes.fromhex(u)).hex()
        if got != out:
            sys.exit(f"reference disagrees with RFC 7748: {got} != {out}")
    rng = random.Random(7748)
    cases = [(bytes.fromhex(k), bytes.fromhex(u)) for k, u, _ in RFC_VECTORS]
    cases += [(rng.randbytes(32), rng.randbytes(32)) for _ in range(32)]
    if full:
        lines = "".join(f"{k.hex()} {u.hex()}\n" for k, u in cases)
    else:
        lines = "".join(f"{clamp(k).hex()} {mask_u(u).hex()}\n" for k, u in cases)
    res = subprocess.run(runner, input=lines, capture_output=True, text=True, check=True)
    outs = res.stdout.split("\n")[: len(cases)]
    if len(outs) != len(cases):
        sys.exit(f"expected {len(cases)} lines, got {len(outs)}")
    for (k, u), line in zip(cases, outs):
        if full:
            got = bytes.fromhex(line.strip())
        else:
            x2h, z2h = line.split()
            x2 = int.from_bytes(bytes.fromhex(x2h), "little")
            z2 = int.from_bytes(bytes.fromhex(z2h), "little")
            got = (x2 * pow(z2, P - 2, P) % P).to_bytes(32, "little")
        want = x25519_ref(k, u)
        if got != want:
            sys.exit(f"MISMATCH k={k.hex()} u={u.hex()}: {got.hex()} != {want.hex()}")
    what = "x25519" if full else "ladder"
    print(f"riscv_x25519 ({what}): {len(cases)} cases agree with RFC 7748 "
          f"({len(RFC_VECTORS)} published vectors, {len(cases) - len(RFC_VECTORS)} random)")


if __name__ == "__main__":
    main()
