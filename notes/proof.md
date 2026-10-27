# Proof notes: lawful-words

## Status (2026-10-27)

All 83 laws are proven. `./check.sh` (bend2 `--check-only`, then the kernel
`--verdict`) prints ALL PROOFS CHECK twice; no `@unsafe`, no foreign code.
`bend test/spot.bend`: 59 checks, all True. About 4000 lines of proof.

Files:
- `proof_nat.bend`: Bool/Nat facts (add/mul algebra, doubling, order, the
  Nat.divmod loop invariant, div/mod uniqueness, remainders in sums and
  products, powers of 2). Proves the 18 Nat laws.
- `proof_word.bend`: Word(n) as numbers, by induction on n: value < 2^n,
  injectivity, Word.cmp = Nat.cmp, inc/adc/sub/not/shl/shr/mul with their carry
  out, bits (`wbit`), masks, or/xor of disjoint words, `wext` (equal at the
  first differing bit gives equal words).
- `proof_u32.bend`: the U32 laws (n = 32), division through U32.divmod.go's
  loop invariant (`DMOK`), min/max, shifts, indexes, bits.
- `proof_bytes.bend`: bytes in a word. Most byte laws compare words bit by bit
  (`U.bit_ext`), with the bits of `D.byte`, shifts and 255 (`bit_byte`,
  `bit_shrn`, `bit_shln`, `bit_255`, `bsel`) and small Bool lemmas.
  `to_nat_pack4` goes through or_split with 2^8 abstract (`pk.m`).
- `proof_zb.bend`: `zb_zero`. The word is split into four 8-bit words
  (`app8`); `zb_byte` (all 256 bytes, generated) says that with no borrow in,
  a byte's flag is set and a borrow goes out exactly when the byte is zero;
  `allz_mask` (256 cases) reads a byte through the 255 mask.
- `PROOF.bend`: forwards each law to its proof.

Used by ../lawful-arrays (do not rename): `N.div_mul_add`, `N.mod_lt`,
`N.mod_small`, `N.mul_comm`, `U.is_le_to_nat`, `U.is_lt_to_nat`,
`U.to_nat_and_mask`, `U.to_nat_shln_fits_p`, `U.to_nat_shr`,
`U.to_nat_sub_le`.

## Resolved blocker: 13 laws could not be checked as first stated

`to_nat_lt`, `to_nat_from_nat`, `wrap_small`, `to_nat_inc`, `to_nat_add`,
`to_nat_sub`, `to_nat_mul`, `to_nat_add_fits`, `to_nat_mul_fits`,
`to_nat_shl`, `to_nat_shln`, `to_nat_shln_fits`, `to_nat_not` mention
`D.two32()` or `D.wrap(n)`. They are true, but no proof of them can pass the
checker:

- bend2 compares two terms that are not syntactically identical by evaluating
  them, and a Nat is unary: once `D.two32()` (2^32) is unfolded inside such a
  comparison the comparison recurses about 2^32 deep and overflows ("the
  machine stack overflowed"). Already `{Nat.pow(2n, 16n) ==
  Nat.mul(Nat.pow(2n, 8n), Nat.pow(2n, 8n))}` overflows, and so do
  `{D.two32() == Nat.pow(2n, 32n)}`, `{D.wrap(x) == Nat.mod(x, D.two32())}`
  and even `{f(x) == Nat.add(x, D.two32())}` where `def f(x) = Nat.add(x,
  D.two32())`. There is no syntactic shortcut inside the comparison: only the
  whole two terms being identical avoids the evaluation.
- So a proof can use `D.two32()` only as an opaque constant: nothing ever
  unfolds it, so nothing relates it to the words.
- `--verdict` is stricter still: the kernel runs out of fuel on
  `{Nat.is_lt(5n, D.two32()) == True{}}`, which bend2 accepts.

What works: `Nat.pow(2n, 32n)` written inline, provided it only ever meets
itself syntactically. The 13 laws are proven in that form in
`proof_u32.bend` as `*_p` lemmas (e.g. `to_nat_lt_p`, `to_nat_inc_p`,
`to_nat_add_fits_p`), with `D.two32()` replaced by `Nat.pow(2n, 32n)` and
`D.wrap(n)` by `Nat.mod(n, Nat.pow(2n, 32n))`. The lead restated
the laws that way (commit d08b8f0); `PROOF.bend` forwards them to the `*_p`
lemmas.

## Where it got hard (research data)

- Rewrite direction, as warned: `%e : G` needs `e : {new == old}` with `old`
  in the goal. Most lemmas are stated `{complex == simple}`, so simplifying
  the goal needs `Equal.sym(...)` almost every time; I got it backwards about
  25 times in the first files. The rule that finally stuck: the same rule
  holds when a rewrite transforms a hypothesis passed as an argument (the
  argument's expected type is the "goal", the hypothesis is the body).
- Big closed Nats (above): the dominant difficulty of the U32 layer. Pattern
  used: every lemma whose proof needs 2^32 is proven as `name.m` for an
  abstract `m` with `hm : {Nat.pow(2n, 32n) == m}` (all conversions are then
  cheap), and `hm` rewrites `m` into `Nat.pow(2n, 32n)` only right before a
  Word lemma of exactly that type. An error inside such a proof crashes the
  error printer (it normalizes `hm`'s type); debugging used a copy with 2^3.
- Affinity: a function-typed hypothesis (`bit_ext`'s `h`) can be called once,
  so `bit_ext` calls it once, at `W.wdiff` (the lowest bit where the two words
  differ), and `W.wext` turns that single equation into word equality.
- Matching: `match` on a pattern-bound Bool after other matches is refused
  ("matched after a local statement"); nested constructor patterns
  (`WCon{False{}, t}`) work instead. A `let` holding a rewrite term needs an
  annotation `{... : T}`.
- U32 division: Base's long division is a loop over the dividend's bits with a
  U32 remainder; its invariant (`DMOK`: q * b + r = a, r < b) needs the
  remainder update (2r + bit, minus b when it is >= b, computed by U32.sub
  with the shifted-out top bit) as numbers: about 120 lines.
- Closed constants 2^16 and 2^24 (to_nat_pack4) hit the same trap as 2^32:
  `pk.m` keeps 2^8 abstract (`a`) and gets 2^16, 2^24, 2^32 as products of
  `a` by `pow_add`, with the exponent sum (`8n + 8n == 16n`) rewritten by a
  small `{==}`, so no conversion ever unfolds a big number.
- Brute force was cheap: the two 256-case lemmas of proof_zb.bend (generated
  by a script, each case `{==}`) check in well under a second. Script-
  generated case splits were the simplest route for zb_zero.
- Bit-level reasoning (bit_ext + per-bit Bool lemmas) was much easier than
  numbers for put_byte, merge, pack4 and shifts by whole bytes: index
  arithmetic stays in Nat (8j + k), and each law ends in a 2-4 variable Bool
  identity proven by case split.
