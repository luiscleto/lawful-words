# lawful-words

Laws for Bend's `U32`: what addition, subtraction, shifts, masks and comparisons do to the number a
word stands for, plus helpers for the four bytes inside a word, with laws of their own. Bend's proof
checker has verified every law, so a proof about code that does arithmetic or byte tricks on words
can reason about plain numbers and bytes instead of 32 separate bits. The zero-byte test, which
checks four bytes at once, is proven to agree with checking each byte in turn.

## Use

```python
import lawful-words@0.1.0.0/defs.bend as W   # the byte helpers
import lawful-words@0.1.0.0/LAWS.bend as L   # the laws, for your own proofs
import lawful-words@0.1.0.0/PROOF.bend as P  # their proofs, needed when a proof uses a law
```

Finding a byte in a word, four bytes at a time:

```python
import Base
import lawful-words@0.1.0.0/defs.bend as W

# Is byte b anywhere in the word w? One test covers all four bytes.
def has_byte(w: U32, b: U32) -> Bool:
  Bool.not(U32.is_zero(W.zb(U32.xor(w, W.bcast(b)))))

# The bytes of "hi\n!" packed into one word.
def word() -> U32:
  W.pack4(104, 105, 10, 33)

def main() -> U32 & Bool & Bool:
  ( W.byte(word(), 1n)                           # byte 1
  , has_byte(word(), 10)                         # a newline in it?
  , has_byte(W.put_byte(word(), 2n, 32), 10) )   # and once byte 2 is a space?
```

```
$ bend example.bend
(105, True{}, False{})
```

## What's in it

Bytes are numbered from 0, the lowest.

| operation | signature | what it does |
|---|---|---|
| `byte` | `(w: U32, j: Nat) -> U32` | byte j of w: `(w >> 8j) & 255` |
| `put_byte` | `(w: U32, j: Nat, b: U32) -> U32` | w with byte j replaced by b (b below 256, j below 4) |
| `pack4` | `(b0, b1, b2, b3: U32) -> U32` | the word whose bytes are b0 to b3 |
| `nth4` | `(j: Nat, b0, b1, b2, b3: U32) -> U32` | the j-th of four values |
| `merge` | `(lo: U32, hi: U32, r: Nat) -> U32` | the word starting r bytes into the pair (lo, hi), as an unaligned read sees it |
| `zb` | `(v: U32) -> U32` | zero exactly when no byte of v is zero |
| `bcast` | `(b: U32) -> U32` | b repeated in all four bytes |
| `bit` | `(a: U32, k: Nat) -> Bool` | bit k of a |
| `two32` | `() -> Nat` | 2^32 |
| `wrap` | `(n: Nat) -> Nat` | n modulo 2^32, the number `U32.from_nat(n)` stands for |

The laws also cover Base's own `U32` operations: arithmetic modulo 2^32 and exact when the result
fits, comparisons, division, shifts, masks and bitwise operations, plus facts about `Nat` that Base
lacks.

To use a law in a proof, call it by name with its arguments. A hypothesis that evaluation settles,
such as `1 < 4`, is `{==}`:

```python
# A byte written into slot 1 reads back from slot 1.
law put_get:
  for w: U32
  for b: U32
  for hb: {U32.is_lt(b, 256) == True{} : Bool}
  {W.byte(W.put_byte(w, 1n, b), 1n) == b : U32}

def put_get(w, b, hb):
  L.byte_put_same(w, 1n, b, {==}, hb)
```

The laws are proven. Below version 1.0 they have been reviewed by AI models but not yet by a human
expert. [docs/LAWS.md](docs/LAWS.md) lists them all in plain words.

## License

MIT (see `LICENSE`).
