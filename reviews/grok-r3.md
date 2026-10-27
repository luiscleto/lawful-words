ACCEPT

The 83 laws typecheck, and `bend test/spot.bend` passes all 59 checks. No law is false, and nothing lawful-bytes needs from this package is out of reach.

The new equations hold at the edges where a hypothesis is doing real work. `byte_not` and `byte_pack4` need `j < 4`: at `j = 4`, `byte` is `0` while `xor(0, 255)` and `nth4` are not. `byte_merge_hi` needs `r ≤ 4`: at `r = 5` the merge is `hi`, but the right-hand side reads `byte(hi, j+1)`. `shrn_lt_words` is strict, so `i = 4`, `k = 2`, `w = 1` is correctly excluded (`4 < 4` is false and `1 < 1` is false). `zb_zero` is only the whole-word claim: `v = 0x01010100` lights all four flags and still has a zero byte, so both sides are false together. `nat_mul_mod` holds at `b = 0` because `mod(0, 0) = 0`, and `nat_div_mul_add` never divides by zero because `r < 0` is impossible.

A packed read, a `put_byte`, an unaligned `merge`, and a search for a byte below 256 (via `bcast`, `byte_xor`, `byte_pack4`, `is_zero_xor`, and `zb_zero`) all follow from these laws.
