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

MIT (see `LICENSE`).
