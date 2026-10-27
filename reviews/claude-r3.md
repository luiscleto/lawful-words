❯ Round 3. LAWS.bend (now 83 laws) and defs.bend are revised after round 2;
  reviews/responses-2.md lists each round-2 finding and the change.
  test/spot.bend now has 59 checks, all passing (bend test/spot.bend). Please
  check: (1) is any law false? Give a counterexample worked from Base's
  definitions. Pay attention to the new ones: zb_zero, byte_merge_lo/hi,
  byte_shrn, byte_shln_high/low, byte_not, byte_pack4 with nth4, to_nat_split,
  shrn_lt_words and the Nat facts. (2) Is anything still a blocker for
  lawful-bytes, meaning a proof it needs that these laws cannot reach? Report
  only false laws and blockers; minor shape preferences can wait until the
  proofs show what is awkward. If you find neither, say ACCEPT. Read-only: do
  not modify any file. End with the full report as your final message.

  Read 2 files (ctrl+o to expand)

● Bash(bend test/spot.bend 2>&1 | tr ',' '\n' | sort | uniq -c; bend LAWS.bend
      --check-only 2>&1 | tail -2)
  ⎿       57  True{}
           1  True{}]
           1 [True{}
     … +2 lines (ctrl+o to expand)
  ⎿  Allowed by auto mode classifier

● Review, round 3: lawful-words (83 laws)

  ACCEPT. None of the 83 laws is false, and nothing in this package blocks
  lawful-bytes. bend test/spot.bend gives 59 × True{}, and bend LAWS.bend
  --check-only reports 83 TODOs, as expected.

  False laws: none

  I worked each law you flagged by hand from Base's definitions, including where
  it fails when a hypothesis is missing:

  - zb_zero: true both ways.
    - No zero byte: subtracting 16843009 (0x01010101) borrows nowhere, so byte j
      becomes b_j − 1. Its top bit can be set only if b_j ≥ 129, and then ~v
      clears that bit. So zb = 0.
    - Some zero byte: take the lowest zero byte j. No borrow reaches it, so it
      becomes 0xFF, ~v keeps the top bit, and the flag is set.
    - Edge cases: v = 0 gives 0x80808080; v = 0xFFFFFFFF gives 0. The constants
      are right: 0x01010101 = 16843009 and 0x80808080 = 2155905152.
  - byte_merge_lo: holds with only j + r < 4. Byte j of shrn(lo, 8r) is byte(lo,
    j+r), and byte j of shln(hi, 8(4−r)) is 0 because j < 4 − r.
  - byte_merge_hi: with r ≤ 4, Nat.sub(4n, r) doesn't truncate.
    - The lo part is byte(lo, j+r) with j + r ≥ 4, so it is 0.
    - The hi part is byte(hi, j − (4−r)) = byte(hi, j+r−4).
    - At r = 0 the hypotheses contradict each other, so the law is vacuous
      there.
  - byte_shrn: needs no hypothesis. Both sides are ⌊n / 2^(8(j+s))⌋ mod 256, and
    both are 0 once j + s ≥ 4.
  - byte_shln_high: with s ≤ j < 4, the byte sits inside the 32 bits, so the
    wrap in the shift doesn't touch it.
  - byte_shln_low: with j < s, the byte is 0. That includes s ≥ 4, where the
    shift gives 0, and j ≥ 4.
  - byte_not: true, and the hj hypothesis is needed. With j = 4, the left side
    is 0 and the right side is 255.
  - byte_pack4 with nth4: true for j < 4, and nth4 picks the right byte for 0
    to 3.
  - to_nat_split: true for k ≤ 32. For k > 32 no mask satisfies h, so the law is
    vacuous. At k = 0 the mask is 0 and shrn(a, 0) = a.
  - shrn_lt_words: true. n(i) < 2^k · n(w) and 2^k > 0 give n(i) / 2^k < n(w).
  - to_nat_shln_mod: true. For k ≤ 32, 2^k divides 2^32; for k > 32 the shift
    gives 0.
  - to_nat_shrn_lt: true. Because Nat.sub truncates, the bound is 1 from k = 32
    up, where the shift gives 0.
  - byte_and, byte_or, byte_xor: true with no hypothesis. A right shift
    distributes over these operations, and both sides are 0 from j = 4 up.
  - byte_put_other without j < 4: true. From j = 4 up, put_byte returns w
    unchanged.
  - is_ne_to_nat, is_zero_to_nat, is_zero_xor, byte_ext: true.
  - Nat facts: nat_div_lt, nat_div_mul_add, nat_mod_mul_add, nat_mod_mod_pow,
    both transitivity laws and the comm/assoc/distributivity laws are all true.
    Where the divisor or a factor can be 0, it agrees with Base's Nat.divmod(a,
    0) = (0, a): nat_mul_mod at b = 0 is 0 mod 0 = 0, and nat_div_div at x = 0
    or y = 0 is 0 on both sides.

  Blockers: none in this package

  Each pattern lawful-bytes needs is now covered:

  - Reading byte i as byte(word(i >> 2), i & 3):
    - to_nat_shrn, to_nat_and_mask (k=2) and to_nat_split give the offset and
      the split.
    - nat_mod_lt gives the offset is below 4.
    - shrn_lt_words gives the word index is in range.
    - nat_div_mul_add and nat_mod_mul_add show that byte 4k + j lives in word k
      at offset j.
  - Byte search: zb_zero and byte_xor, with byte_pack4 applied to bcast(b)
    (nth4(k, b, b, b, b) closes by matching on k). is_zero_xor turns a zero byte
    into byte(w, k) == b. U32.is_ne(x, 0) unfolds definitionally to
    Bool.not(U32.is_zero(x)).
  - Shifted copy: merge with byte_merge_lo and byte_merge_hi, then byte_ext to
    conclude word equality.
  - Masked partial-word writes: byte_and, byte_or, byte_not and byte_pack4 cover
    these. Byte-level and with 255 or 0 and or with 0 follow from
    to_nat_and_mask, to_nat_or_split and nat_mod_small.
  - Counters and bounds: to_nat_inc_lt and the is_*_to_nat laws.

  Two things remain for lawful-bytes, but neither is a missing law here:

  - Base still has no Array get/set laws. responses-2.md already lists this; it
    is the remaining real blocker for lawful-bytes, and its home has to be
    decided outside this package.
  - Some Nat facts in Bool-test form are left to the user. Examples:
    Nat.is_eq(a, b) == True{} implies a == b, and Nat.is_lt implies Nat.is_le.
    They come up when turning i ≠ i' into offset inequality. Each is a short
    induction on Nat.cmp, so it can be proven downstream without a long chain.

✻ Worked for 1m 30s · done 8:00 PM

────────────────────────────────────────────────────────────────────────────────
❯ 
────────────────────────────────────────────────────────────────────────────────
  ⏸ plan mode on (shift+tab to cycle)
                                    Update available! Run: mise upgrade claude
