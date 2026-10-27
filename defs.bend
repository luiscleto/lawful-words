import Base

# lawful-words definitions. The laws are in LAWS.bend.

# 2^32, for prose and tests. The laws write Nat.pow(2n, 32n) inline instead:
# the checker evaluates a named constant when comparing terms, and 2^32 in
# unary is too deep to evaluate. (A Nat literal of 2^32 or more is not allowed.)
def two32() -> Nat:
  Nat.pow(2n, 32n)

# n modulo 2^32: the number U32.from_nat(n) stands for (the laws write
# Nat.mod(n, Nat.pow(2n, 32n)) inline, for the same reason).
def wrap(n: Nat) -> Nat:
  Nat.mod(n, two32())

# Bit k of a word (bit 0 is the lowest; every bit from 32 up is 0).
def bit(a: U32, k: Nat) -> Bool:
  Nat.is_eq(Nat.mod(Nat.div(U32.to_nat(a), Nat.pow(2n, k)), 2n), 1n)

# Byte j of a word (byte 0 is the lowest): (w >> 8j) & 255.
def byte(w: U32, j: Nat) -> U32:
  U32.and(U32.shrn(w, Nat.mul(8n, j)), 255)

# w with byte j replaced by b: (w & ~(255 << 8j)) | (b << 8j). Meant for
# b < 256 and j < 4: a larger b spills into the next byte, and from j = 4 up
# the word is unchanged.
def put_byte(w: U32, +j: Nat, b: U32) -> U32:
  U32.or(U32.and(w, U32.not(U32.shln(255, Nat.mul(8n, j)))), U32.shln(b, Nat.mul(8n, j)))

# The word whose bytes 0 to 3 are b0 to b3: b0 | b1 << 8 | b2 << 16 | b3 << 24.
# Meant for bytes below 256: larger values spill into the next byte.
def pack4(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  U32.or(b0, U32.or(U32.shln(b1, 8n), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n))))

# The j-th of four values (j = 0 to 3; b3 from 3 up).
def nth4(j: Nat, b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  match j:
    case 0n:
      b0
    case 1n+p:
      match p:
        case 0n:
          b1
        case 1n+q:
          match q:
            case 0n:
              b2
            case 1n+t:
              b3

# The word that starts r bytes into the pair (lo, hi), r from 0 to 4:
# (lo >> 8r) | (hi << 8(4 - r)). Copying at any alignment reads such words.
def merge(lo: U32, hi: U32, +r: Nat) -> U32:
  U32.or(U32.shrn(lo, Nat.mul(8n, r)), U32.shln(hi, Nat.mul(8n, Nat.sub(4n, r))))

# The zero-byte flags: (v - 0x01010101) & ~v & 0x80808080. It is zero exactly
# when no byte of v is zero (law zb_zero); individual flags are not exact.
def zb(+v: U32) -> U32:
  U32.and(U32.and(U32.sub(v, 16843009), U32.not(v)), 2155905152)

# A byte repeated in all four bytes: searching for b is searching xor(w, bcast(b))
# for a zero byte.
def bcast(+b: U32) -> U32:
  pack4(b, b, b, b)
