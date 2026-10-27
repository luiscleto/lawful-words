# lawful-words: a guide to the laws

`LAWS.bend` holds 83 laws: what Base's `U32` operations do to the number a word stands for,
`U32.to_nat(a)` (0 to 2^32 - 1). This guide says what each group of laws means. The Bend text is
the authority.

## Conventions

- **Hypotheses are written as tests in code:** `{U32.is_lt(a, b) == True{}}` or
  `{Nat.is_le(k, 32n) == True{}}`. A fact from an `if` in code plugs in directly.
- **2^32 is written `Nat.pow(2n, 32n)`** in every law, and "modulo 2^32" as
  `Nat.mod(x, Nat.pow(2n, 32n))`. Bend's checker evaluates named constants when it compares terms,
  and 2^32 in unary is too deep to evaluate (see `../NOTES.md`).
- **Byte j of a word** is `byte(w, j) = (w >> 8j) & 255`; byte 0 is the lowest.

## The laws

| group | laws | in plain terms |
|---|---|---|
| Numbers | `to_nat_lt`, `to_nat_inj`, `from_nat_to_nat`, `to_nat_from_nat`, `wrap_small` | a word's number is below 2^32; different words have different numbers; `from_nat` takes a number modulo 2^32, so it is unchanged below 2^32 |
| Comparisons | `cmp_to_nat`, `is_eq/lt/le/gt/ge/ne/zero_to_nat`, `is_zero_xor`, `is_eq_true` | words compare exactly as their numbers do; `a xor b` is zero exactly when `a == b`; a passed equality test gives equal words |
| Arithmetic modulo 2^32 | `to_nat_inc`, `to_nat_add`, `to_nat_sub`, `to_nat_mul`, `from_nat_add`, `from_nat_mul` | `inc`, `add`, `sub`, `mul` wrap around at 2^32 (`a - b` is `a + 2^32 - b` modulo 2^32) |
| Exact arithmetic | `to_nat_inc_lt`, `to_nat_add_fits`, `to_nat_sub_le`, `to_nat_mul_fits` | when the result fits (or `b <= a` for subtraction), it is the plain sum, difference or product; a counter below some word steps up by exactly 1 |
| Division, min, max | `to_nat_div`, `to_nat_mod`, `to_nat_min`, `to_nat_max` | as on numbers; dividing by 0 gives 0 and the remainder is `a`, in Base and in Nat alike |
| Shifts | `to_nat_shr`, `to_nat_shl`, `to_nat_shrn`, `to_nat_shln`, `to_nat_shln_fits`, `to_nat_shln_mod`, `to_nat_shrn_lt` | a right shift by k divides by 2^k; a left shift multiplies by 2^k modulo 2^32; shifting by 32 or more gives 0 |
| Masks and indexes | `to_nat_split`, `shrn_lt_words`, `to_nat_and_mask`, `to_nat_not`, `to_nat_or_split`, `to_nat_xor_split` | `a & (2^k - 1)` is `a mod 2^k`; a byte index splits as `i = 4(i >> 2) + (i & 3)`; or and xor of words with no bit in common is their sum |
| Bits | `bit_and`, `bit_or`, `bit_xor`, `bit_not`, `bit_ext` | the bitwise operations, bit by bit; two words with the same bits are equal |
| Bytes in a word | `to_nat_byte`, `byte_put_same`, `byte_put_other`, `to_nat_pack4`, `byte_pack4`, `pack4_bytes`, `byte_ext`, `byte_lt` | reading byte j; replacing byte j leaves the other bytes; packing four bytes and unpacking them again; every byte is below 256 |
| Bytes and operations | `byte_and/or/xor/not`, `byte_shrn`, `byte_shln_high`, `byte_shln_low`, `byte_merge_lo`, `byte_merge_hi` | bitwise operations work byte by byte; shifts by whole bytes move bytes; `merge(lo, hi, r)` is the word starting r bytes into the pair (lo, hi), which is how unaligned copies read |
| The zero-byte test | `zb_zero` | `zb(v) = (v - 0x01010101) & ~v & 0x80808080` is zero exactly when no byte of v is zero. This is the trick that lets a search test four bytes at once |
| Nat facts Base lacks | `nat_*` (18 laws) | commutativity, associativity, distributivity, transitivity; division and remainder identities; powers |

## Where to look hardest

- **`zb_zero` holds only for the whole word.** A flag above a zero byte can be set even when that
  byte is not zero: `0x01010100` flags all four bytes. Code must use the test only to skip words
  with no zero byte, then check bytes one by one. Ignoring this was the real bug in lawful-bytes'
  fast search (see `../NOTES.md`).
- **`to_nat_and_mask`:** the mask is any word standing for `2^k - 1`, so a literal such as 255
  qualifies. No word stands for `2^k - 1` when k > 32, so in practice k <= 32.
- **`byte_put_same` and `to_nat_pack4` require bytes below 256.** A larger value spills into the
  next byte.

## Left out on purpose

- **Signed arithmetic:** Base's U32 is unsigned.
- **A numeric law for and/or in general:** there is no simple formula. The bit laws and the
  split laws cover the uses.
- **Laws for any word width:** the proofs are by induction on the width (`Word(n)`), but the
  published laws are about U32 only.
