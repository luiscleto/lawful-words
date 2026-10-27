import Base
import ./defs.bend as D

# lawful-words: what Base's U32 operations compute, stated as arithmetic on
# natural numbers. U32.to_nat(a) is the number a word stands for (0 to 2^32-1).
# Each law says what an operation does to that number: modulo 2^32 in general,
# and exactly when the result fits. Bytes inside a word (D.byte, D.put_byte,
# D.pack4) get get/set laws, and a few facts about Nat that Base lacks come
# last. Hypotheses are tests written as in code: {U32.is_lt(a, b) == True{}}.

# ==========================================================================
# Numbers
# ==========================================================================

# Every word stands for a number below 2^32.
law to_nat_lt:
  for a: U32
  {Nat.is_lt(U32.to_nat(a), D.two32()) == True{} : Bool}

# Two words that stand for the same number are the same word.
law to_nat_inj:
  for a: U32
  for b: U32
  for h: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}

law from_nat_to_nat:
  for a: U32
  {U32.from_nat(U32.to_nat(a)) == a : U32}

law to_nat_from_nat:
  for n: Nat
  {U32.to_nat(U32.from_nat(n)) == D.wrap(n) : Nat}

# A number below 2^32 is unchanged by wrapping.
law wrap_small:
  for n: Nat
  for h: {Nat.is_lt(n, D.two32()) == True{} : Bool}
  {D.wrap(n) == n : Nat}

# ==========================================================================
# Comparisons
# ==========================================================================

# Words compare as their numbers; every U32.is_* test follows from this one.
law cmp_to_nat:
  for a: U32
  for b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

law is_eq_to_nat:
  for a: U32
  for b: U32
  {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}

law is_lt_to_nat:
  for a: U32
  for b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

law is_le_to_nat:
  for a: U32
  for b: U32
  {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}

law is_gt_to_nat:
  for a: U32
  for b: U32
  {U32.is_gt(a, b) == Nat.is_gt(U32.to_nat(a), U32.to_nat(b)) : Bool}

law is_ge_to_nat:
  for a: U32
  for b: U32
  {U32.is_ge(a, b) == Nat.is_ge(U32.to_nat(a), U32.to_nat(b)) : Bool}

law is_ne_to_nat:
  for a: U32
  for b: U32
  {U32.is_ne(a, b) == Bool.not(Nat.is_eq(U32.to_nat(a), U32.to_nat(b))) : Bool}

law is_zero_to_nat:
  for a: U32
  {U32.is_zero(a) == Nat.is_eq(U32.to_nat(a), 0n) : Bool}

# Two words are equal exactly when their xor is zero.
law is_zero_xor:
  for a: U32
  for b: U32
  {U32.is_zero(U32.xor(a, b)) == U32.is_eq(a, b) : Bool}

# A passed equality test gives equal words.
law is_eq_true:
  for a: U32
  for b: U32
  for h: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

# ==========================================================================
# Arithmetic modulo 2^32
# ==========================================================================

law to_nat_inc:
  for a: U32
  {U32.to_nat(U32.inc(a)) == D.wrap(Nat.add(U32.to_nat(a), 1n)) : Nat}

law to_nat_add:
  for a: U32
  for b: U32
  {U32.to_nat(U32.add(a, b)) == D.wrap(Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}

# a - b wraps: it is a + 2^32 - b, modulo 2^32.
law to_nat_sub:
  for a: U32
  for b: U32
  {U32.to_nat(U32.sub(a, b)) == D.wrap(Nat.sub(Nat.add(U32.to_nat(a), D.two32()), U32.to_nat(b))) : Nat}

law to_nat_mul:
  for a: U32
  for b: U32
  {U32.to_nat(U32.mul(a, b)) == D.wrap(Nat.mul(U32.to_nat(a), U32.to_nat(b))) : Nat}

law from_nat_add:
  for x: Nat
  for y: Nat
  {U32.from_nat(Nat.add(x, y)) == U32.add(U32.from_nat(x), U32.from_nat(y)) : U32}

law from_nat_mul:
  for x: Nat
  for y: Nat
  {U32.from_nat(Nat.mul(x, y)) == U32.mul(U32.from_nat(x), U32.from_nat(y)) : U32}

# ==========================================================================
# Arithmetic when the result fits (counters and indexes)
# ==========================================================================

# A counter below some word steps up by exactly one.
law to_nat_inc_lt:
  for a: U32
  for b: U32
  for h: {U32.is_lt(a, b) == True{} : Bool}
  {U32.to_nat(U32.inc(a)) == Nat.add(U32.to_nat(a), 1n) : Nat}

law to_nat_add_fits:
  for a: U32
  for b: U32
  for h: {Nat.is_lt(Nat.add(U32.to_nat(a), U32.to_nat(b)), D.two32()) == True{} : Bool}
  {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law to_nat_sub_le:
  for a: U32
  for b: U32
  for h: {U32.is_le(b, a) == True{} : Bool}
  {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

law to_nat_mul_fits:
  for a: U32
  for b: U32
  for h: {Nat.is_lt(Nat.mul(U32.to_nat(a), U32.to_nat(b)), D.two32()) == True{} : Bool}
  {U32.to_nat(U32.mul(a, b)) == Nat.mul(U32.to_nat(a), U32.to_nat(b)) : Nat}

# ==========================================================================
# Division, remainder, minimum, maximum
# ==========================================================================

# As in Base, dividing by 0 gives 0 and the remainder is a; so does Nat.
law to_nat_div:
  for a: U32
  for b: U32
  {U32.to_nat(U32.div(a, b)) == Nat.div(U32.to_nat(a), U32.to_nat(b)) : Nat}

law to_nat_mod:
  for a: U32
  for b: U32
  {U32.to_nat(U32.mod(a, b)) == Nat.mod(U32.to_nat(a), U32.to_nat(b)) : Nat}

law to_nat_min:
  for a: U32
  for b: U32
  {U32.to_nat(U32.min(a, b)) == Nat.min(U32.to_nat(a), U32.to_nat(b)) : Nat}

law to_nat_max:
  for a: U32
  for b: U32
  {U32.to_nat(U32.max(a, b)) == Nat.max(U32.to_nat(a), U32.to_nat(b)) : Nat}

# ==========================================================================
# Shifts (shifting by 32 or more gives 0)
# ==========================================================================

law to_nat_shr:
  for a: U32
  {U32.to_nat(U32.shr(a)) == Nat.div(U32.to_nat(a), 2n) : Nat}

law to_nat_shl:
  for a: U32
  {U32.to_nat(U32.shl(a)) == D.wrap(Nat.mul(U32.to_nat(a), 2n)) : Nat}

law to_nat_shrn:
  for a: U32
  for k: Nat
  {U32.to_nat(U32.shrn(a, k)) == Nat.div(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

law to_nat_shln:
  for a: U32
  for k: Nat
  {U32.to_nat(U32.shln(a, k)) == D.wrap(Nat.mul(U32.to_nat(a), Nat.pow(2n, k))) : Nat}

law to_nat_shln_fits:
  for a: U32
  for k: Nat
  for h: {Nat.is_lt(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), D.two32()) == True{} : Bool}
  {U32.to_nat(U32.shln(a, k)) == Nat.mul(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

# A left shift by k leaves the low k bits zero.
law to_nat_shln_mod:
  for a: U32
  for k: Nat
  {Nat.mod(U32.to_nat(U32.shln(a, k)), Nat.pow(2n, k)) == 0n : Nat}

# A right shift by k leaves a number below 2^(32-k) (below 1 from k = 32 up).
law to_nat_shrn_lt:
  for a: U32
  for k: Nat
  {Nat.is_lt(U32.to_nat(U32.shrn(a, k)), Nat.pow(2n, Nat.sub(32n, k))) == True{} : Bool}

# ==========================================================================
# Indexes: a byte index i is word i >> 2, byte i & 3
# ==========================================================================

# A word splits into its high part (a >> k) and its low k bits (a & m).
law to_nat_split:
  for a: U32
  for m: U32
  for k: Nat
  for h: {U32.to_nat(m) == Nat.sub(Nat.pow(2n, k), 1n) : Nat}
  {U32.to_nat(a) == Nat.add(Nat.mul(U32.to_nat(U32.shrn(a, k)), Nat.pow(2n, k)), U32.to_nat(U32.and(a, m))) : Nat}

# An index below 2^k * w words-worth has its word index below w.
law shrn_lt_words:
  for i: U32
  for w: U32
  for k: Nat
  for h: {Nat.is_lt(U32.to_nat(i), Nat.mul(Nat.pow(2n, k), U32.to_nat(w))) == True{} : Bool}
  {U32.is_lt(U32.shrn(i, k), w) == True{} : Bool}

# ==========================================================================
# Bitwise operations as numbers
# ==========================================================================

# And with a mask of the low k bits takes the number modulo 2^k. The mask is
# any word standing for 2^k - 1, so a literal such as 255 or 3 qualifies. No
# word stands for 2^k - 1 when k > 32, so in practice k <= 32 (k = 32 is the
# all-ones word).
law to_nat_and_mask:
  for a: U32
  for m: U32
  for k: Nat
  for h: {U32.to_nat(m) == Nat.sub(Nat.pow(2n, k), 1n) : Nat}
  {U32.to_nat(U32.and(a, m)) == Nat.mod(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

law to_nat_not:
  for a: U32
  {U32.to_nat(U32.not(a)) == Nat.sub(Nat.sub(D.two32(), 1n), U32.to_nat(a)) : Nat}

# Or of a word with only bits from k up and a word below 2^k is their sum
# (no bit in common). Xor likewise.
law to_nat_or_split:
  for a: U32
  for b: U32
  for k: Nat
  for ha: {Nat.mod(U32.to_nat(a), Nat.pow(2n, k)) == 0n : Nat}
  for hb: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, k)) == True{} : Bool}
  {U32.to_nat(U32.or(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law to_nat_xor_split:
  for a: U32
  for b: U32
  for k: Nat
  for ha: {Nat.mod(U32.to_nat(a), Nat.pow(2n, k)) == 0n : Nat}
  for hb: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, k)) == True{} : Bool}
  {U32.to_nat(U32.xor(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

# ==========================================================================
# Bitwise operations bit by bit
# ==========================================================================

law bit_and:
  for a: U32
  for b: U32
  for k: Nat
  {D.bit(U32.and(a, b), k) == (D.bit(a, k) && D.bit(b, k)) : Bool}

law bit_or:
  for a: U32
  for b: U32
  for k: Nat
  {D.bit(U32.or(a, b), k) == (D.bit(a, k) || D.bit(b, k)) : Bool}

law bit_xor:
  for a: U32
  for b: U32
  for k: Nat
  {D.bit(U32.xor(a, b), k) == Bool.xor(D.bit(a, k), D.bit(b, k)) : Bool}

# not flips the 32 bits, and only those.
law bit_not:
  for a: U32
  for k: Nat
  {D.bit(U32.not(a), k) == (Nat.is_lt(k, 32n) && Bool.not(D.bit(a, k))) : Bool}

# Two words with the same bits are the same word.
law bit_ext:
  for a: U32
  for b: U32
  for h: @k: Nat -> {D.bit(a, k) == D.bit(b, k) : Bool}
  {a == b : U32}

# ==========================================================================
# Bytes in a word
# ==========================================================================

law to_nat_byte:
  for w: U32
  for j: Nat
  {U32.to_nat(D.byte(w, j)) == Nat.mod(Nat.div(U32.to_nat(w), Nat.pow(2n, Nat.mul(8n, j))), Nat.pow(2n, 8n)) : Nat}

# Byte j of a word whose byte j was set to b (below 256) is b.
law byte_put_same:
  for w: U32
  for j: Nat
  for b: U32
  for hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for hb: {U32.is_lt(b, 256) == True{} : Bool}
  {D.byte(D.put_byte(w, j, b), j) == b : U32}

# Setting byte j leaves every other byte as it was (from j = 4 up,
# put_byte changes nothing).
law byte_put_other:
  for w: U32
  for i: Nat
  for j: Nat
  for b: U32
  for hb: {U32.is_lt(b, 256) == True{} : Bool}
  for hij: {Nat.is_eq(i, j) == False{} : Bool}
  {D.byte(D.put_byte(w, j, b), i) == D.byte(w, i) : U32}

# The number a packed word stands for.
law to_nat_pack4:
  for b0: U32
  for b1: U32
  for b2: U32
  for b3: U32
  for h0: {U32.is_lt(b0, 256) == True{} : Bool}
  for h1: {U32.is_lt(b1, 256) == True{} : Bool}
  for h2: {U32.is_lt(b2, 256) == True{} : Bool}
  for h3: {U32.is_lt(b3, 256) == True{} : Bool}
  {U32.to_nat(D.pack4(b0, b1, b2, b3)) == Nat.add(U32.to_nat(b0), Nat.add(Nat.mul(U32.to_nat(b1), Nat.pow(2n, 8n)), Nat.add(Nat.mul(U32.to_nat(b2), Nat.pow(2n, 16n)), Nat.mul(U32.to_nat(b3), Nat.pow(2n, 24n))))) : Nat}

# Unpacking a packed word gives its bytes back. j is any index below 4 (in
# code it is i & 3, not a literal).
law byte_pack4:
  for b0: U32
  for b1: U32
  for b2: U32
  for b3: U32
  for j: Nat
  for h0: {U32.is_lt(b0, 256) == True{} : Bool}
  for h1: {U32.is_lt(b1, 256) == True{} : Bool}
  for h2: {U32.is_lt(b2, 256) == True{} : Bool}
  for h3: {U32.is_lt(b3, 256) == True{} : Bool}
  for hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {D.byte(D.pack4(b0, b1, b2, b3), j) == D.nth4(j, b0, b1, b2, b3) : U32}

# Packing a word's four bytes gives the word back.
law pack4_bytes:
  for w: U32
  {D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)) == w : U32}

# Two words with the same four bytes are the same word.
law byte_ext:
  for a: U32
  for b: U32
  for h0: {D.byte(a, 0n) == D.byte(b, 0n) : U32}
  for h1: {D.byte(a, 1n) == D.byte(b, 1n) : U32}
  for h2: {D.byte(a, 2n) == D.byte(b, 2n) : U32}
  for h3: {D.byte(a, 3n) == D.byte(b, 3n) : U32}
  {a == b : U32}

# Bitwise operations work byte by byte.
law byte_and:
  for a: U32
  for b: U32
  for j: Nat
  {D.byte(U32.and(a, b), j) == U32.and(D.byte(a, j), D.byte(b, j)) : U32}

law byte_or:
  for a: U32
  for b: U32
  for j: Nat
  {D.byte(U32.or(a, b), j) == U32.or(D.byte(a, j), D.byte(b, j)) : U32}

law byte_xor:
  for a: U32
  for b: U32
  for j: Nat
  {D.byte(U32.xor(a, b), j) == U32.xor(D.byte(a, j), D.byte(b, j)) : U32}

law byte_not:
  for a: U32
  for j: Nat
  for hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {D.byte(U32.not(a), j) == U32.xor(D.byte(a, j), 255) : U32}

# Shifting by whole bytes moves bytes.
law byte_shrn:
  for w: U32
  for s: Nat
  for j: Nat
  {D.byte(U32.shrn(w, Nat.mul(8n, s)), j) == D.byte(w, Nat.add(j, s)) : U32}

law byte_shln_high:
  for w: U32
  for s: Nat
  for j: Nat
  for hs: {Nat.is_le(s, j) == True{} : Bool}
  for hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {D.byte(U32.shln(w, Nat.mul(8n, s)), j) == D.byte(w, Nat.sub(j, s)) : U32}

law byte_shln_low:
  for w: U32
  for s: Nat
  for j: Nat
  for hj: {Nat.is_lt(j, s) == True{} : Bool}
  {D.byte(U32.shln(w, Nat.mul(8n, s)), j) == 0 : U32}

# A word read r bytes into the pair (lo, hi): bytes r.. of lo, then bytes of hi.
law byte_merge_lo:
  for lo: U32
  for hi: U32
  for r: Nat
  for j: Nat
  for h: {Nat.is_lt(Nat.add(j, r), 4n) == True{} : Bool}
  {D.byte(D.merge(lo, hi, r), j) == D.byte(lo, Nat.add(j, r)) : U32}

law byte_merge_hi:
  for lo: U32
  for hi: U32
  for r: Nat
  for j: Nat
  for hr: {Nat.is_le(r, 4n) == True{} : Bool}
  for hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for h: {Nat.is_le(4n, Nat.add(j, r)) == True{} : Bool}
  {D.byte(D.merge(lo, hi, r), j) == D.byte(hi, Nat.sub(Nat.add(j, r), 4n)) : U32}

# The zero-byte test: zb(v) is zero exactly when no byte of v is zero. (Only
# this whole-word statement holds: a flag above a zero byte can be set even
# though that byte is not zero, e.g. v = 0x01010100 flags all four bytes.)
law zb_zero:
  for v: U32
  {U32.is_zero(D.zb(v)) == (U32.is_ne(D.byte(v, 0n), 0) && (U32.is_ne(D.byte(v, 1n), 0) && (U32.is_ne(D.byte(v, 2n), 0) && U32.is_ne(D.byte(v, 3n), 0)))) : Bool}

# Every byte is below 256.
law byte_lt:
  for w: U32
  for j: Nat
  {U32.is_lt(D.byte(w, j), 256) == True{} : Bool}

# ==========================================================================
# Facts about Nat that Base does not have
# ==========================================================================

law nat_mod_lt:
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}

law nat_mod_small:
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.mod(a, b) == a : Nat}

law nat_div_small:
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.div(a, b) == 0n : Nat}

# a = (a / b) * b + a % b (also for b = 0: a / 0 = 0 and a % 0 = a).
law nat_div_mod:
  for a: Nat
  for b: Nat
  {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat}

law nat_pow_add:
  for b: Nat
  for j: Nat
  for k: Nat
  {Nat.pow(b, Nat.add(j, k)) == Nat.mul(Nat.pow(b, j), Nat.pow(b, k)) : Nat}

# Dividing by 2^j then by 2^k is dividing by 2^(j+k).
law nat_div_div:
  for a: Nat
  for x: Nat
  for y: Nat
  {Nat.div(Nat.div(a, x), y) == Nat.div(a, Nat.mul(x, y)) : Nat}

law nat_add_comm:
  for a: Nat
  for b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

law nat_add_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

law nat_mul_comm:
  for a: Nat
  for b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

law nat_mul_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

law nat_mul_add:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}

law nat_lt_le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for h1: {Nat.is_lt(a, b) == True{} : Bool}
  for h2: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

law nat_le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for h1: {Nat.is_le(a, b) == True{} : Bool}
  for h2: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

# a < b * c with b > 0 gives a / b < c.
law nat_div_lt:
  for a: Nat
  for b: Nat
  for c: Nat
  for hb: {Nat.is_lt(0n, b) == True{} : Bool}
  for h: {Nat.is_lt(a, Nat.mul(b, c)) == True{} : Bool}
  {Nat.is_lt(Nat.div(a, b), c) == True{} : Bool}

# (q * b + r) / b = q and (q * b + r) % b = r, for r < b.
law nat_div_mul_add:
  for q: Nat
  for b: Nat
  for r: Nat
  for h: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat}

law nat_mod_mul_add:
  for q: Nat
  for b: Nat
  for r: Nat
  for h: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}

law nat_mul_mod:
  for a: Nat
  for b: Nat
  {Nat.mod(Nat.mul(a, b), b) == 0n : Nat}

# (a % 2^m) % 2^k = a % 2^k for k <= m.
law nat_mod_mod_pow:
  for a: Nat
  for k: Nat
  for m: Nat
  for h: {Nat.is_le(k, m) == True{} : Bool}
  {Nat.mod(Nat.mod(a, Nat.pow(2n, m)), Nat.pow(2n, k)) == Nat.mod(a, Nat.pow(2n, k)) : Nat}
