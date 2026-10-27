# Round 2: responses (2026-10-27)

No reviewer found a false law in revision 2 (53 laws). Changes in revision 3 (83 laws):

| finding | raised by | change |
|---|---|---|
| Zero-byte trick has no law; per-byte flags lie above a zero byte (0x01010100 flags all four) | Claude (blocker), GPT, Grok | defs `zb`, `bcast`; law `zb_zero` (whole word only: zero exactly when no byte is zero), plus `is_zero_xor` and byte-wise laws for searching any byte |
| Shifted copy across words unreachable | Claude, GPT, Grok | def `merge(lo, hi, r)`; `byte_merge_lo`, `byte_merge_hi`; `byte_shrn`, `byte_shln_high`, `byte_shln_low`; `to_nat_shln_mod`, `to_nat_shrn_lt` |
| Byte-wise and/or/xor/not | Claude, GPT | `byte_and`, `byte_or`, `byte_xor`, `byte_not` (as xor with 255, j < 4: GPT) |
| `byte_pack4` cannot be rewritten (Maybe/List.get) | Claude, GPT, Grok | def `nth4`; `byte_pack4` concludes `byte(pack4(..), j) == nth4(j, ..)` with j a parameter (Grok: in code j is i & 3) |
| Byte extensionality | GPT | `byte_ext` (four byte equalities give word equality) |
| Index split and word-index bound | Grok, GPT, Claude | `to_nat_split` (mask form), `shrn_lt_words` (bound stated in Nat, not `U32.mul`, which wraps: Grok) |
| Nat facts for indexing (and Base has none) | Claude, Grok | `nat_add_comm/assoc`, `nat_mul_comm/assoc`, `nat_mul_add`, `nat_lt_le_trans`, `nat_le_trans`, `nat_div_lt`, `nat_div_mul_add`, `nat_mod_mul_add`, `nat_mul_mod`, `nat_mod_mod_pow` |
| `is_ne`, `is_zero` laws | Claude | `is_ne_to_nat`, `is_zero_to_nat` |
| `byte_put_other`'s `j < 4` unnecessary | Claude | dropped (put_byte from j = 4 up changes nothing) |
| `to_nat_and_mask` comment wrong for k > 32 | Claude, GPT, Grok | comment fixed: no word stands for 2^k - 1 when k > 32 |
| `put_byte`/`pack4` comments omit b < 256, j < 4 | GPT, Grok | comments state the ranges and what happens outside them |
| Spot tests never near 2^32 | Claude | 24 cases added, compared as words (59 in all, all pass) |

Noted for lawful-bytes, not this package:
- ceiling division by 4 must not wrap: `(n + 3) >> 2` wraps at n = 2^32 - 1 (GPT);
- the final partial word's zero padding must not be read as data (GPT);
- Base has no Array laws; lawful-bytes needs get/set laws (Claude).

Not taken:
- the exact zero-byte variant `~(((v & 0x7F7F7F7F) + 0x7F7F7F7F) | v | 0x7F7F7F7F)` (Claude): the search skips words with no flag and tests bytes one by one, so only `zb_zero` is needed;
- `byte_at(w, i: U32)` (Claude): left to lawful-bytes, which owns its index type.
