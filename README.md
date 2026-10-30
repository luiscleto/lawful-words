# lawful-words

What Bend's `U32` operations compute, as laws that a proof checker verifies. Each law says what an
operation does to the number a word stands for (`U32.to_nat`): arithmetic modulo 2^32 and exactly
when the result fits, comparisons, shifts, masks, bytes inside a word (read, replace, pack, the
zero-byte test, words read across a boundary), and the facts about `Nat` that Base does not have.

It is the bottom layer for `lawful-bytes` (bytes packed four to a word): with these laws, proofs
about packed data reason about numbers and bytes, never about 32 separate bits.

Status: the laws (`LAWS.bend`, definitions in `defs.bend`) were reviewed in three rounds by
Claude, GPT and Grok (`reviews/`), and all 83 are proven (`PROOF.bend`): `./check.sh` checks them
with `bend` and with the Lean-proven kernel (`--verdict`).

`bend test/spot.bend` evaluates both sides of many laws on concrete values.

## Use

Published on [BendHub](https://hub.bend-lang.com/name/lawful-words) with its laws and proofs. Bend fetches
an import by name and checks it against the package's hash:

```python
import lawful-words@0.1.0.0/defs.bend as W   # the definitions the laws are about
import lawful-words@0.1.0.0/LAWS.bend as L   # the laws, to use in your own proofs
import lawful-words@0.1.0.0/PROOF.bend as P  # their proofs, which a proof using a law needs loaded
```

Versions below 1.0 have laws reviewed by three AI models but not yet by a human expert.

MIT (see `LICENSE`).
