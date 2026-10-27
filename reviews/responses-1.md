# Round 1: responses (2026-10-27)

Reviewers: Claude (Opus 5.5, plan mode), GPT (GPT-6.1-Sol, codex read-only), Grok (4.7, plan mode).
Gemini was out of quota. Reports: `claude-r1.md`, `gpt-r1.md`, `grok-r1.md`.

No reviewer found a false law; all three worked the edge cases out by hand from Base's definitions:
- shifts by 32 or more;
- masks of 0 and 32 bits;
- `bit_not`'s guard;
- `sub` with a borrow;
- `Nat.div`/`Nat.mod` by zero.

Every finding was about laws that are missing or that proofs cannot use.

| # | finding | raised by | change |
|---|---|---|---|
| 1 | Nothing removes the `mod 2^32`: no proof can conclude `n(inc i) = n(i) + 1` | Claude (blocker), GPT, Grok | `wrap_small`; exact forms `to_nat_inc_lt`, `to_nat_add_fits`, `to_nat_sub_le`, `to_nat_mul_fits`, `to_nat_shln_fits` |
| 2 | `or_disjoint`'s premise (`a & b == 0`) cannot be established; bit laws are cut off from numbers | Claude (blocker), GPT, Grok | replaced by `to_nat_or_split` (numeric premises); `to_nat_xor_split`; `bit_ext` |
| 3 | `and_low` only matches `from_nat(2^k - 1)`, not literals like `255`; `k <= 32` is unnecessary | Claude, GPT, Grok | `to_nat_and_mask`: the mask is any word standing for `2^k - 1`; no bound on k |
| 4 | No `U32.div`/`mod` laws | Claude, GPT, Grok | `to_nat_div`, `to_nat_mod` (unconditional: both sides agree at 0) |
| 5 | No `min`/`max` laws | Claude, GPT, Grok | `to_nat_min`, `to_nat_max` |
| 6 | Only eq/lt/le; `is_gt`/`is_ge` are not swaps of them by unfolding | Claude, GPT, Grok | `cmp_to_nat` plus `is_*_to_nat` for eq, lt, le, gt, ge |
| 7 | No reflection from a passed `is_eq` test to word equality | GPT | `is_eq_true` |
| 8 | No `from_nat` round trip or homomorphism | Claude, GPT, Grok | `from_nat_to_nat`, `from_nat_add`, `from_nat_mul` (no `sub`: `Nat.sub` truncates; Grok) |
| 9 | No numeric `not` | Claude, GPT, Grok | `to_nat_not` |
| 10 | Byte extraction, packing, replacement are long chains | Claude, GPT, Grok | defs `byte`, `put_byte`, `pack4` with `to_nat_byte`, `byte_put_same`, `byte_put_other`, `to_nat_pack4`, `byte_pack4`, `pack4_bytes`, `byte_lt` |
| 11 | Index split `i = 4(i >> 2) + (i & 3)` and Nat division facts are missing from Base | Claude, GPT | Nat section: `nat_div_mod`, `nat_mod_lt`, `nat_mod_small`, `nat_div_small`, `nat_pow_add`, `nat_div_div` |
| 12 | Names read as operations (`add`, `same`, `below`, `of_nat`) | Claude, GPT, Grok | `to_nat_*` scheme |
| 13 | Laws said `D.W.n`, but code says `U32.to_nat`; namespaces two deep | Claude, Grok | laws use `U32.to_nat`; defs renamed without the `W.` prefix |
| 14 | Mixed hypothesis styles | Claude | tests as in code: `{U32.is_lt(a, b) == True{}}`; Nat facts as `{Nat.is_lt(..) == True{}}` |
| 15 | Header comment overclaimed | Claude | rewritten |

Not taken:
- separate `bit_shln`/`bit_shrn` laws (Claude): the numeric shift and split laws cover packing;
- shift-boundary corollaries (GPT, minor): they follow from `to_nat_shrn` with `nat_div_small`.
