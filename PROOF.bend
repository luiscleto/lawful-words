import Base
import ./LAWS.bend as L
import ./proof_nat.bend as N
import ./proof_u32.bend as U
import ./proof_bytes.bend as Y
import ./proof_zb.bend as Z

# Proofs of the laws of LAWS.bend: `def L.name` proves `law name`. Each
# forwards to the proof file that restates the law with every variable
# reusable: proof_nat.bend (Nat), proof_word.bend (Word(n), used by the
# others), proof_u32.bend (U32), proof_bytes.bend (bytes in a word),
# proof_zb.bend (the zero-byte test).

# Numbers
# =======

def L.to_nat_lt(a):
  U.to_nat_lt_p(a)

def L.to_nat_from_nat(n):
  U.to_nat_from_nat_p(n)

def L.wrap_small(n, h):
  U.wrap_small_p(n, h)

def L.to_nat_inc(a):
  U.to_nat_inc_p(a)

def L.to_nat_add(a, b):
  U.to_nat_add_p(a, b)

def L.to_nat_sub(a, b):
  U.to_nat_sub_p(a, b)

def L.to_nat_mul(a, b):
  U.to_nat_mul_p(a, b)

def L.to_nat_add_fits(a, b, h):
  U.to_nat_add_fits_p(a, b, h)

def L.to_nat_mul_fits(a, b, h):
  U.to_nat_mul_fits_p(a, b, h)

def L.to_nat_shl(a):
  U.to_nat_shl_p(a)

def L.to_nat_shln(a, k):
  U.to_nat_shln_p(a, k)

def L.to_nat_shln_fits(a, k, h):
  U.to_nat_shln_fits_p(a, k, h)

def L.to_nat_not(a):
  U.to_nat_not_p(a)

def L.to_nat_inj(a, b, h):
  U.to_nat_inj(a, b, h)

def L.from_nat_to_nat(a):
  U.from_nat_to_nat(a)

# Comparisons
# ===========

def L.cmp_to_nat(a, b):
  U.cmp_to_nat(a, b)

def L.is_eq_to_nat(a, b):
  U.is_eq_to_nat(a, b)

def L.is_lt_to_nat(a, b):
  U.is_lt_to_nat(a, b)

def L.is_le_to_nat(a, b):
  U.is_le_to_nat(a, b)

def L.is_gt_to_nat(a, b):
  U.is_gt_to_nat(a, b)

def L.is_ge_to_nat(a, b):
  U.is_ge_to_nat(a, b)

def L.is_ne_to_nat(a, b):
  U.is_ne_to_nat(a, b)

def L.is_zero_to_nat(a):
  U.is_zero_to_nat(a)

def L.is_zero_xor(a, b):
  U.is_zero_xor(a, b)

def L.is_eq_true(a, b, h):
  U.is_eq_true(a, b, h)

# Arithmetic modulo 2^32
# ======================

def L.from_nat_add(x, y):
  U.from_nat_add(x, y)

def L.from_nat_mul(x, y):
  U.from_nat_mul(x, y)

# Arithmetic when the result fits
# ===============================

def L.to_nat_inc_lt(a, b, h):
  U.to_nat_inc_lt(a, b, h)

def L.to_nat_sub_le(a, b, h):
  U.to_nat_sub_le(a, b, h)

# Division, remainder, minimum, maximum
# =====================================

def L.to_nat_div(a, b):
  U.to_nat_div(a, b)

def L.to_nat_mod(a, b):
  U.to_nat_mod(a, b)

def L.to_nat_min(a, b):
  U.to_nat_min(a, b)

def L.to_nat_max(a, b):
  U.to_nat_max(a, b)

# Shifts
# ======

def L.to_nat_shr(a):
  U.to_nat_shr(a)

def L.to_nat_shrn(a, k):
  U.to_nat_shrn(a, k)

def L.to_nat_shln_mod(a, k):
  U.to_nat_shln_mod(a, k)

def L.to_nat_shrn_lt(a, k):
  U.to_nat_shrn_lt(a, k)

# Indexes
# =======

def L.to_nat_split(a, m, k, h):
  U.to_nat_split(a, m, k, h)

def L.shrn_lt_words(i, w, k, h):
  U.shrn_lt_words(i, w, k, h)

# Bitwise operations as numbers
# =============================

def L.to_nat_and_mask(a, m, k, h):
  U.to_nat_and_mask(a, m, k, h)

def L.to_nat_or_split(a, b, k, ha, hb):
  U.to_nat_or_split(a, b, k, ha, hb)

def L.to_nat_xor_split(a, b, k, ha, hb):
  U.to_nat_xor_split(a, b, k, ha, hb)

# Bitwise operations bit by bit
# =============================

def L.bit_and(a, b, k):
  U.bit_and(a, b, k)

def L.bit_or(a, b, k):
  U.bit_or(a, b, k)

def L.bit_xor(a, b, k):
  U.bit_xor(a, b, k)

def L.bit_not(a, k):
  U.bit_not(a, k)

def L.bit_ext(a, b, h):
  U.bit_ext(a, b, h)

# Bytes in a word
# ===============

def L.to_nat_byte(w, j):
  Y.to_nat_byte(w, j)

def L.byte_put_same(w, j, b, hj, hb):
  Y.byte_put_same(w, j, b, hj, hb)

def L.byte_put_other(w, i, j, b, hb, hij):
  Y.byte_put_other(w, i, j, b, hb, hij)

def L.to_nat_pack4(b0, b1, b2, b3, h0, h1, h2, h3):
  Y.to_nat_pack4(b0, b1, b2, b3, h0, h1, h2, h3)

def L.byte_pack4(b0, b1, b2, b3, j, h0, h1, h2, h3, hj):
  Y.byte_pack4(b0, b1, b2, b3, j, h0, h1, h2, h3, hj)

def L.pack4_bytes(w):
  Y.pack4_bytes(w)

def L.byte_ext(a, b, h0, h1, h2, h3):
  Y.byte_ext(a, b, h0, h1, h2, h3)

def L.byte_and(a, b, j):
  Y.byte_and(a, b, j)

def L.byte_or(a, b, j):
  Y.byte_or(a, b, j)

def L.byte_xor(a, b, j):
  Y.byte_xor(a, b, j)

def L.byte_not(a, j, hj):
  Y.byte_not(a, j, hj)

def L.byte_shrn(w, s, j):
  Y.byte_shrn(w, s, j)

def L.byte_shln_high(w, s, j, hs, hj):
  Y.byte_shln_high(w, s, j, hs, hj)

def L.byte_shln_low(w, s, j, hj):
  Y.byte_shln_low(w, s, j, hj)

def L.byte_merge_lo(lo, hi, r, j, h):
  Y.byte_merge_lo(lo, hi, r, j, h)

def L.byte_merge_hi(lo, hi, r, j, hr, hj, h):
  Y.byte_merge_hi(lo, hi, r, j, hr, hj, h)

def L.zb_zero(v):
  Z.zb_zero(v)

def L.byte_lt(w, j):
  Y.byte_lt(w, j)

# Facts about Nat
# ===============

def L.nat_mod_lt(a, b, h):
  N.mod_lt(a, b, h)

def L.nat_mod_small(a, b, h):
  N.mod_small(a, b, h)

def L.nat_div_small(a, b, h):
  N.div_small(a, b, h)

def L.nat_div_mod(a, b):
  N.div_mod(a, b)

def L.nat_pow_add(b, j, k):
  N.pow_add(b, j, k)

def L.nat_div_div(a, x, y):
  N.div_div(a, x, y)

def L.nat_add_comm(a, b):
  N.add_comm(a, b)

def L.nat_add_assoc(a, b, c):
  N.add_assoc(a, b, c)

def L.nat_mul_comm(a, b):
  N.mul_comm(a, b)

def L.nat_mul_assoc(a, b, c):
  N.mul_assoc(a, b, c)

def L.nat_mul_add(a, b, c):
  N.mul_add(a, b, c)

def L.nat_lt_le_trans(a, b, c, h1, h2):
  N.lt_le_trans(a, b, c, h1, h2)

def L.nat_le_trans(a, b, c, h1, h2):
  N.le_trans(a, b, c, h1, h2)

def L.nat_div_lt(a, b, c, hb, h):
  N.div_lt(a, b, c, hb, h)

def L.nat_div_mul_add(q, b, r, h):
  N.div_mul_add(q, b, r, h)

def L.nat_mod_mul_add(q, b, r, h):
  N.mod_mul_add(q, b, r, h)

def L.nat_mul_mod(a, b):
  N.mul_mod(a, b)

def L.nat_mod_mod_pow(a, k, m, h):
  N.mod_mod_pow(a, k, m, h)
