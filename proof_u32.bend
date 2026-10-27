import Base
import ./proof_nat.bend as N
import ./proof_word.bend as W
import ./defs.bend as D

# The U32 laws, restated with every variable reusable. Most are the Word(n)
# lemmas of proof_word.bend at n = 32.
#
# 2^32 is a closed Nat, and the checker compares two different terms that
# contain it by unfolding it in unary, which overflows. So a lemma whose proof
# needs 2^32 is first proven as `name.m`, for any m with Nat.pow(2n, 32n) == m
# (hm), where conversions are cheap; Nat.pow(2n, 32n) only appears where hm
# rewrites m into it right before a Word lemma of exactly that type. The
# statement itself then takes m = Nat.pow(2n, 32n) and hm = {==}.

# The Word lemmas at n = 32, with m for 2^32
# ==========================================

law wlt.m:
  for +w: Word(32n)
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.is_lt(Word.to_nat(32n, w), m) == True{} : Bool}

def wlt.m(w, m, hm):
  %hm : {Nat.is_lt(Word.to_nat(32n, w), _) == True{} : Bool}
  W.wlt(32n, w)

law winc.m:
  for +w: Word(32n)
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.add(Word.to_nat(32n, Word.inc(32n, w)), Nat.mul(N.bn(W.incc(32n, w)), m)) == 1n+Word.to_nat(32n, w) : Nat}

def winc.m(w, m, hm):
  %hm : {Nat.add(Word.to_nat(32n, Word.inc(32n, w)), Nat.mul(N.bn(W.incc(32n, w)), _)) == 1n+Word.to_nat(32n, w) : Nat}
  W.winc(32n, w)

law wadc.m:
  for +x: Word(32n)
  for +y: Word(32n)
  for +c: Bool
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.add(Word.to_nat(32n, Word.adc(32n, x, y, False{}, c)), Nat.mul(N.bn(W.cout(32n, x, y, c)), m))
    == Nat.add(N.bn(c), Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y))) : Nat}

def wadc.m(x, y, c, m, hm):
  %hm : {Nat.add(Word.to_nat(32n, Word.adc(32n, x, y, False{}, c)), Nat.mul(N.bn(W.cout(32n, x, y, c)), _))
    == Nat.add(N.bn(c), Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y))) : Nat}
  W.wadc(32n, x, y, c)

law wnot.m:
  for +w: Word(32n)
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {1n+Nat.add(Word.to_nat(32n, Word.not(32n, w)), Word.to_nat(32n, w)) == m : Nat}

def wnot.m(w, m, hm):
  %hm : {1n+Nat.add(Word.to_nat(32n, Word.not(32n, w)), Word.to_nat(32n, w)) == _ : Nat}
  W.wnot(32n, w)

law wshl.m:
  for +w: Word(32n)
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.add(Word.to_nat(32n, Word.shl(32n, w)), Nat.mul(N.bn(W.shtop(32n, w)), m)) == Nat.double(Word.to_nat(32n, w)) : Nat}

def wshl.m(w, m, hm):
  %hm : {Nat.add(Word.to_nat(32n, Word.shl(32n, w)), Nat.mul(N.bn(W.shtop(32n, w)), _)) == Nat.double(Word.to_nat(32n, w)) : Nat}
  W.wshl(32n, w)

law wput.m:
  for +c: Bool
  for +w: Word(32n)
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.add(Word.to_nat(32n, Word.shl.put(32n, c, w)), Nat.mul(N.bn(W.stop(32n, c, w)), m))
    == Nat.add(N.bn(c), Nat.double(Word.to_nat(32n, w))) : Nat}

def wput.m(c, w, m, hm):
  %hm : {Nat.add(Word.to_nat(32n, Word.shl.put(32n, c, w)), Nat.mul(N.bn(W.stop(32n, c, w)), _))
    == Nat.add(N.bn(c), Nat.double(Word.to_nat(32n, w))) : Nat}
  W.wput(32n, c, w)

law wmul.m:
  for +x: Word(32n)
  for +y: Word(32n)
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Word.to_nat(32n, Word.mul.go(32n, 32n, x, y, Word.zero(32n)))
    == Nat.mod(Nat.add(Word.to_nat(32n, Word.zero(32n)), Nat.mul(Word.to_nat(32n, x), Word.to_nat(32n, y))), m) : Nat}

def wmul.m(x, y, m, hm):
  %hm : {Word.to_nat(32n, Word.mul.go(32n, 32n, x, y, Word.zero(32n)))
    == Nat.mod(Nat.add(Word.to_nat(32n, Word.zero(32n)), Nat.mul(Word.to_nat(32n, x), Word.to_nat(32n, y))), _) : Nat}
  W.wmul_go(32n, 32n, x, y, Word.zero(32n))

law wsub_val.m:
  for +x: Word(32n)
  for +y: Word(32n)
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.sub(Nat.add(Word.to_nat(32n, x), m), Word.to_nat(32n, y))
    == 1n+Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, Word.not(32n, y))) : Nat}

def wsub_val.m(x, y, m, hm):
  %hm : {Nat.sub(Nat.add(Word.to_nat(32n, x), _), Word.to_nat(32n, y))
    == 1n+Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, Word.not(32n, y))) : Nat}
  W.wsub_val(32n, x, y)

# Numbers
# =======

law to_nat_lt.m:
  for +a: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.is_lt(U32.to_nat(a), m) == True{} : Bool}

def to_nat_lt.m(a, m, hm):
  match a:
    case U32{+w}:
      wlt.m(w, m, hm)

law to_nat_lt_p:
  for +a: U32
  {Nat.is_lt(U32.to_nat(a), Nat.pow(2n, 32n)) == True{} : Bool}

def to_nat_lt_p(a):
  to_nat_lt.m(a, Nat.pow(2n, 32n), {==})

law to_nat_inj:
  for +a: U32
  for +b: U32
  for +h: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}

def to_nat_inj(a, b, h):
  match a b:
    case U32{+x} U32{+y}:
      %W.winj(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

law wrap_small_p:
  for +n: Nat
  for +h: {Nat.is_lt(n, Nat.pow(2n, 32n)) == True{} : Bool}
  {Nat.mod(n, Nat.pow(2n, 32n)) == n : Nat}

def wrap_small_p(n, h):
  N.mod_small(n, Nat.pow(2n, 32n), h)

law to_nat_inc.m:
  for +a: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.inc(a)) == Nat.mod(Nat.add(U32.to_nat(a), 1n), m) : Nat}

def to_nat_inc.m(a, m, hm):
  match a:
    case U32{+w}:
      %Equal.sym(Nat, Nat.add(Word.to_nat(32n, w), 1n), 1n+Word.to_nat(32n, w), N.add_one(Word.to_nat(32n, w))) :
        {Word.to_nat(32n, Word.inc(32n, w)) == Nat.mod(_, m) : Nat}
      Equal.sym(Nat, Nat.mod(1n+Word.to_nat(32n, w), m), Word.to_nat(32n, Word.inc(32n, w)),
        W.carry_mod(Word.to_nat(32n, Word.inc(32n, w)), N.bn(W.incc(32n, w)), m, 1n+Word.to_nat(32n, w), winc.m(w, m, hm), wlt.m(Word.inc(32n, w), m, hm)))

law to_nat_inc_p:
  for +a: U32
  {U32.to_nat(U32.inc(a)) == Nat.mod(Nat.add(U32.to_nat(a), 1n), Nat.pow(2n, 32n)) : Nat}

def to_nat_inc_p(a):
  to_nat_inc.m(a, Nat.pow(2n, 32n), {==})

law to_nat_from_nat.m:
  for +n: Nat
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.from_nat(n)) == Nat.mod(n, m) : Nat}

def to_nat_from_nat.m(n, m, hm):
  match n:
    case 0n:
      Equal.sym(Nat, Nat.mod(0n, m), 0n, N.mod_zero_l(m))
    case 1n+p:
      %Equal.sym(Nat, U32.to_nat(U32.inc(U32.from_nat(p))), Nat.mod(Nat.add(U32.to_nat(U32.from_nat(p)), 1n), m), to_nat_inc.m(U32.from_nat(p), m, hm)) :
        {_ == Nat.mod(1n+p, m) : Nat}
      %Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), Nat.mod(p, m), to_nat_from_nat.m(p, m, hm)) : {Nat.mod(Nat.add(_, 1n), m) == Nat.mod(1n+p, m) : Nat}
      %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(p, m), 1n), m), Nat.mod(Nat.add(p, 1n), m), N.mod_add_mod_l(p, 1n, m)) : {_ == Nat.mod(1n+p, m) : Nat}
      %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, N.add_one(p)) : {Nat.mod(_, m) == Nat.mod(1n+p, m) : Nat}
      {==}

law to_nat_from_nat_p:
  for +n: Nat
  {U32.to_nat(U32.from_nat(n)) == Nat.mod(n, Nat.pow(2n, 32n)) : Nat}

def to_nat_from_nat_p(n):
  to_nat_from_nat.m(n, Nat.pow(2n, 32n), {==})

law from_nat_to_nat.m:
  for +a: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.from_nat(U32.to_nat(a)) == a : U32}

def from_nat_to_nat.m(a, m, hm):
  to_nat_inj(U32.from_nat(U32.to_nat(a)), a,
    Equal.trans(Nat, U32.to_nat(U32.from_nat(U32.to_nat(a))), Nat.mod(U32.to_nat(a), m), U32.to_nat(a),
      to_nat_from_nat.m(U32.to_nat(a), m, hm), N.mod_small(U32.to_nat(a), m, to_nat_lt.m(a, m, hm))))

law from_nat_to_nat:
  for +a: U32
  {U32.from_nat(U32.to_nat(a)) == a : U32}

def from_nat_to_nat(a):
  from_nat_to_nat.m(a, Nat.pow(2n, 32n), {==})

# Comparisons
# ===========

law cmp_to_nat:
  for +a: U32
  for +b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

def cmp_to_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      W.wcmp(32n, x, y)

law is_eq_to_nat:
  for +a: U32
  for +b: U32
  {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}

def is_eq_to_nat(a, b):
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), cmp_to_nat(a, b))

law is_lt_to_nat:
  for +a: U32
  for +b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def is_lt_to_nat(a, b):
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), cmp_to_nat(a, b))

law is_le_to_nat:
  for +a: U32
  for +b: U32
  {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}

def is_le_to_nat(a, b):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), cmp_to_nat(a, b))

law is_gt_to_nat:
  for +a: U32
  for +b: U32
  {U32.is_gt(a, b) == Nat.is_gt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def is_gt_to_nat(a, b):
  Equal.cong(Cmp, Bool, c => Cmp.is_gt(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), cmp_to_nat(a, b))

law is_ge_to_nat:
  for +a: U32
  for +b: U32
  {U32.is_ge(a, b) == Nat.is_ge(U32.to_nat(a), U32.to_nat(b)) : Bool}

def is_ge_to_nat(a, b):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), cmp_to_nat(a, b))

law is_ne_to_nat:
  for +a: U32
  for +b: U32
  {U32.is_ne(a, b) == Bool.not(Nat.is_eq(U32.to_nat(a), U32.to_nat(b))) : Bool}

def is_ne_to_nat(a, b):
  Equal.cong(Cmp, Bool, c => Bool.not(Cmp.is_eq(c)), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), cmp_to_nat(a, b))

law is_zero_to_nat:
  for +a: U32
  {U32.is_zero(a) == Nat.is_eq(U32.to_nat(a), 0n) : Bool}

def is_zero_to_nat(a):
  is_eq_to_nat(a, 0)

law is_eq_true:
  for +a: U32
  for +b: U32
  for +h: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def is_eq_true(a, b, h):
  to_nat_inj(a, b, N.eq_sound(U32.to_nat(a), U32.to_nat(b),
    %is_eq_to_nat(a, b) : {_ == True{} : Bool}
    h))

law fin_eq:
  for +a: Bool
  for +b: Bool
  for +t: Cmp
  {Cmp.is_eq(Word.cmp.fin(a, b, t)) == Bool.and(Cmp.is_eq(t), Cmp.is_eq(Bool.cmp(a, b))) : Bool}

def fin_eq(a, b, t):
  match t:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law xor_bit_eq:
  for +x: Bool
  for +y: Bool
  {Cmp.is_eq(Bool.cmp(Bool.xor(x, y), False{})) == Cmp.is_eq(Bool.cmp(x, y)) : Bool}

def xor_bit_eq(x, y):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law wxor_zero:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Cmp.is_eq(Word.cmp(n, Word.xor(n, a, b), Word.zero(n))) == Cmp.is_eq(Word.cmp(n, a, b)) : Bool}

def wxor_zero(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(Bool.xor(x, y), False{}, Word.cmp(p, Word.xor(p, at, bt), Word.zero(p)))),
              Bool.and(Cmp.is_eq(Word.cmp(p, Word.xor(p, at, bt), Word.zero(p))), Cmp.is_eq(Bool.cmp(Bool.xor(x, y), False{}))),
              fin_eq(Bool.xor(x, y), False{}, Word.cmp(p, Word.xor(p, at, bt), Word.zero(p)))) :
            {_ == Cmp.is_eq(Word.cmp.fin(x, y, Word.cmp(p, at, bt))) : Bool}
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(x, y, Word.cmp(p, at, bt))), Bool.and(Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(Bool.cmp(x, y))),
              fin_eq(x, y, Word.cmp(p, at, bt))) :
            {Bool.and(Cmp.is_eq(Word.cmp(p, Word.xor(p, at, bt), Word.zero(p))), Cmp.is_eq(Bool.cmp(Bool.xor(x, y), False{}))) == _ : Bool}
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp(p, Word.xor(p, at, bt), Word.zero(p))), Cmp.is_eq(Word.cmp(p, at, bt)), wxor_zero(p, at, bt)) :
            {Bool.and(_, Cmp.is_eq(Bool.cmp(Bool.xor(x, y), False{}))) == Bool.and(Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(Bool.cmp(x, y))) : Bool}
          %Equal.sym(Bool, Cmp.is_eq(Bool.cmp(Bool.xor(x, y), False{})), Cmp.is_eq(Bool.cmp(x, y)), xor_bit_eq(x, y)) :
            {Bool.and(Cmp.is_eq(Word.cmp(p, at, bt)), _) == Bool.and(Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(Bool.cmp(x, y))) : Bool}
          {==}

law is_zero_xor:
  for +a: U32
  for +b: U32
  {U32.is_zero(U32.xor(a, b)) == U32.is_eq(a, b) : Bool}

def is_zero_xor(a, b):
  match a b:
    case U32{+x} U32{+y}:
      wxor_zero(32n, x, y)

# Arithmetic modulo 2^32
# ======================

law to_nat_add.m:
  for +a: U32
  for +b: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), m) : Nat}

def to_nat_add.m(a, b, m, hm):
  match a b:
    case U32{+x} U32{+y}:
      Equal.sym(Nat, Nat.mod(Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)), m), Word.to_nat(32n, Word.adc(32n, x, y, False{}, False{})),
        W.carry_mod(Word.to_nat(32n, Word.adc(32n, x, y, False{}, False{})), N.bn(W.cout(32n, x, y, False{})), m,
          Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)), wadc.m(x, y, False{}, m, hm), wlt.m(Word.adc(32n, x, y, False{}, False{}), m, hm)))

law to_nat_add_p:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)) : Nat}

def to_nat_add_p(a, b):
  to_nat_add.m(a, b, Nat.pow(2n, 32n), {==})

law to_nat_sub.m:
  for +a: U32
  for +b: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.sub(a, b)) == Nat.mod(Nat.sub(Nat.add(U32.to_nat(a), m), U32.to_nat(b)), m) : Nat}

def to_nat_sub.m(a, b, m, hm):
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Word(32n), Word.adc(32n, x, y, True{}, True{}), Word.adc(32n, x, Word.not(32n, y), False{}, True{}), W.adc_t(32n, x, y, True{})) :
        {Word.to_nat(32n, _) == Nat.mod(Nat.sub(Nat.add(Word.to_nat(32n, x), m), Word.to_nat(32n, y)), m) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(Word.to_nat(32n, x), m), Word.to_nat(32n, y)), 1n+Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, Word.not(32n, y))), wsub_val.m(x, y, m, hm)) :
        {Word.to_nat(32n, Word.adc(32n, x, Word.not(32n, y), False{}, True{})) == Nat.mod(_, m) : Nat}
      Equal.sym(Nat, Nat.mod(1n+Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, Word.not(32n, y))), m), Word.to_nat(32n, Word.adc(32n, x, Word.not(32n, y), False{}, True{})),
        W.carry_mod(Word.to_nat(32n, Word.adc(32n, x, Word.not(32n, y), False{}, True{})), N.bn(W.cout(32n, x, Word.not(32n, y), True{})), m,
          1n+Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, Word.not(32n, y))),
          wadc.m(x, Word.not(32n, y), True{}, m, hm), wlt.m(Word.adc(32n, x, Word.not(32n, y), False{}, True{}), m, hm)))

law to_nat_sub_p:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.sub(a, b)) == Nat.mod(Nat.sub(Nat.add(U32.to_nat(a), Nat.pow(2n, 32n)), U32.to_nat(b)), Nat.pow(2n, 32n)) : Nat}

def to_nat_sub_p(a, b):
  to_nat_sub.m(a, b, Nat.pow(2n, 32n), {==})

law to_nat_mul.m:
  for +a: U32
  for +b: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.mul(a, b)) == Nat.mod(Nat.mul(U32.to_nat(a), U32.to_nat(b)), m) : Nat}

def to_nat_mul.m(a, b, m, hm):
  match a b:
    case U32{+x} U32{+y}:
      wmul.m(x, y, m, hm)

law to_nat_mul_p:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.mul(a, b)) == Nat.mod(Nat.mul(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)) : Nat}

def to_nat_mul_p(a, b):
  to_nat_mul.m(a, b, Nat.pow(2n, 32n), {==})

law from_nat_add.m:
  for +x: Nat
  for +y: Nat
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.from_nat(Nat.add(x, y)) == U32.add(U32.from_nat(x), U32.from_nat(y)) : U32}

def from_nat_add.m(x, y, m, hm):
  to_nat_inj(U32.from_nat(Nat.add(x, y)), U32.add(U32.from_nat(x), U32.from_nat(y)),
    %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.add(x, y))), Nat.mod(Nat.add(x, y), m), to_nat_from_nat.m(Nat.add(x, y), m, hm)) :
      {_ == U32.to_nat(U32.add(U32.from_nat(x), U32.from_nat(y))) : Nat}
    %Equal.sym(Nat, U32.to_nat(U32.add(U32.from_nat(x), U32.from_nat(y))), Nat.mod(Nat.add(U32.to_nat(U32.from_nat(x)), U32.to_nat(U32.from_nat(y))), m),
        to_nat_add.m(U32.from_nat(x), U32.from_nat(y), m, hm)) : {Nat.mod(Nat.add(x, y), m) == _ : Nat}
    %Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), Nat.mod(x, m), to_nat_from_nat.m(x, m, hm)) :
      {Nat.mod(Nat.add(x, y), m) == Nat.mod(Nat.add(_, U32.to_nat(U32.from_nat(y))), m) : Nat}
    %Equal.sym(Nat, U32.to_nat(U32.from_nat(y)), Nat.mod(y, m), to_nat_from_nat.m(y, m, hm)) :
      {Nat.mod(Nat.add(x, y), m) == Nat.mod(Nat.add(Nat.mod(x, m), _), m) : Nat}
    %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(x, m), Nat.mod(y, m)), m), Nat.mod(Nat.add(x, Nat.mod(y, m)), m), N.mod_add_mod_l(x, Nat.mod(y, m), m)) :
      {Nat.mod(Nat.add(x, y), m) == _ : Nat}
    %Equal.sym(Nat, Nat.mod(Nat.add(x, Nat.mod(y, m)), m), Nat.mod(Nat.add(x, y), m), N.mod_add_mod_r(x, y, m)) :
      {Nat.mod(Nat.add(x, y), m) == _ : Nat}
    {==})

law from_nat_add:
  for +x: Nat
  for +y: Nat
  {U32.from_nat(Nat.add(x, y)) == U32.add(U32.from_nat(x), U32.from_nat(y)) : U32}

def from_nat_add(x, y):
  from_nat_add.m(x, y, Nat.pow(2n, 32n), {==})

law from_nat_mul.m:
  for +x: Nat
  for +y: Nat
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.from_nat(Nat.mul(x, y)) == U32.mul(U32.from_nat(x), U32.from_nat(y)) : U32}

def from_nat_mul.m(x, y, m, hm):
  to_nat_inj(U32.from_nat(Nat.mul(x, y)), U32.mul(U32.from_nat(x), U32.from_nat(y)),
    %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.mul(x, y))), Nat.mod(Nat.mul(x, y), m), to_nat_from_nat.m(Nat.mul(x, y), m, hm)) :
      {_ == U32.to_nat(U32.mul(U32.from_nat(x), U32.from_nat(y))) : Nat}
    %Equal.sym(Nat, U32.to_nat(U32.mul(U32.from_nat(x), U32.from_nat(y))), Nat.mod(Nat.mul(U32.to_nat(U32.from_nat(x)), U32.to_nat(U32.from_nat(y))), m),
        to_nat_mul.m(U32.from_nat(x), U32.from_nat(y), m, hm)) : {Nat.mod(Nat.mul(x, y), m) == _ : Nat}
    %Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), Nat.mod(x, m), to_nat_from_nat.m(x, m, hm)) :
      {Nat.mod(Nat.mul(x, y), m) == Nat.mod(Nat.mul(_, U32.to_nat(U32.from_nat(y))), m) : Nat}
    %Equal.sym(Nat, U32.to_nat(U32.from_nat(y)), Nat.mod(y, m), to_nat_from_nat.m(y, m, hm)) :
      {Nat.mod(Nat.mul(x, y), m) == Nat.mod(Nat.mul(Nat.mod(x, m), _), m) : Nat}
    %Equal.sym(Nat, Nat.mod(Nat.mul(Nat.mod(x, m), Nat.mod(y, m)), m), Nat.mod(Nat.mul(x, Nat.mod(y, m)), m), N.mod_mul_mod_l(x, Nat.mod(y, m), m)) :
      {Nat.mod(Nat.mul(x, y), m) == _ : Nat}
    %Equal.sym(Nat, Nat.mod(Nat.mul(x, Nat.mod(y, m)), m), Nat.mod(Nat.mul(x, y), m), N.mod_mul_mod_r(x, y, m)) :
      {Nat.mod(Nat.mul(x, y), m) == _ : Nat}
    {==})

law from_nat_mul:
  for +x: Nat
  for +y: Nat
  {U32.from_nat(Nat.mul(x, y)) == U32.mul(U32.from_nat(x), U32.from_nat(y)) : U32}

def from_nat_mul(x, y):
  from_nat_mul.m(x, y, Nat.pow(2n, 32n), {==})

# Arithmetic when the result fits
# ===============================

law to_nat_inc_lt.m:
  for +a: U32
  for +b: U32
  for +h: {U32.is_lt(a, b) == True{} : Bool}
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.inc(a)) == Nat.add(U32.to_nat(a), 1n) : Nat}

def to_nat_inc_lt.m(a, b, h, m, hm):
  Equal.trans(Nat, U32.to_nat(U32.inc(a)), Nat.mod(Nat.add(U32.to_nat(a), 1n), m), Nat.add(U32.to_nat(a), 1n),
    to_nat_inc.m(a, m, hm),
    N.mod_small(Nat.add(U32.to_nat(a), 1n), m,
      %Equal.sym(Nat, Nat.add(U32.to_nat(a), 1n), 1n+U32.to_nat(a), N.add_one(U32.to_nat(a))) : {Nat.is_lt(_, m) == True{} : Bool}
      N.le_lt_trans(1n+U32.to_nat(a), U32.to_nat(b), m,
        %Equal.sym(Bool, Nat.is_le(1n+U32.to_nat(a), U32.to_nat(b)), Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), N.le_succ_lt(U32.to_nat(a), U32.to_nat(b))) : {_ == True{} : Bool}
        %is_lt_to_nat(a, b) : {_ == True{} : Bool}
        h,
        to_nat_lt.m(b, m, hm))))

law to_nat_inc_lt:
  for +a: U32
  for +b: U32
  for +h: {U32.is_lt(a, b) == True{} : Bool}
  {U32.to_nat(U32.inc(a)) == Nat.add(U32.to_nat(a), 1n) : Nat}

def to_nat_inc_lt(a, b, h):
  to_nat_inc_lt.m(a, b, h, Nat.pow(2n, 32n), {==})

law to_nat_add_fits_p:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_lt(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)) == True{} : Bool}
  {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_add_fits_p(a, b, h):
  Equal.trans(Nat, U32.to_nat(U32.add(a, b)), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)), Nat.add(U32.to_nat(a), U32.to_nat(b)),
    to_nat_add_p(a, b), N.mod_small(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n), h))

law to_nat_mul_fits_p:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_lt(Nat.mul(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)) == True{} : Bool}
  {U32.to_nat(U32.mul(a, b)) == Nat.mul(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_mul_fits_p(a, b, h):
  Equal.trans(Nat, U32.to_nat(U32.mul(a, b)), Nat.mod(Nat.mul(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)), Nat.mul(U32.to_nat(a), U32.to_nat(b)),
    to_nat_mul_p(a, b), N.mod_small(Nat.mul(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n), h))

# (x + m) - y = (x - y) + m for y <= x.
law sub_add_comm:
  for +x: Nat
  for +m: Nat
  for +y: Nat
  for +h: {Nat.is_le(y, x) == True{} : Bool}
  {Nat.sub(Nat.add(x, m), y) == Nat.add(Nat.sub(x, y), m) : Nat}

def sub_add_comm(x, m, y, h):
  %N.le_sub_add(y, x, h) : {Nat.sub(Nat.add(_, m), y) == Nat.add(Nat.sub(x, y), m) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(y, Nat.sub(x, y)), m), Nat.add(y, Nat.add(Nat.sub(x, y), m)), N.add_assoc(y, Nat.sub(x, y), m)) :
    {Nat.sub(_, y) == Nat.add(Nat.sub(x, y), m) : Nat}
  N.sub_add_l(y, Nat.add(Nat.sub(x, y), m))

law sub_le:
  for +x: Nat
  for +y: Nat
  {Nat.is_le(Nat.sub(x, y), x) == True{} : Bool}

def sub_le(x, y):
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), N.lt_to_le(p, 1n+p, %Equal.sym(Bool, Nat.is_lt(p, 1n+p), Nat.is_le(p, p), N.lt_succ_iff(p, p)) : {_ == True{} : Bool}; N.le_refl(p)))

law mod_add_self:
  for +d: Nat
  for +m: Nat
  {Nat.mod(Nat.add(d, m), m) == Nat.mod(d, m) : Nat}

def mod_add_self(d, m):
  %Equal.trans(Nat, Nat.add(Nat.mul(1n, m), d), Nat.add(m, d), Nat.add(d, m),
      Equal.cong(Nat, Nat, t => Nat.add(t, d), Nat.mul(1n, m), m, N.add_zero(m)), N.add_comm(m, d)) :
    {Nat.mod(_, m) == Nat.mod(d, m) : Nat}
  N.mod_add_mul(1n, m, d)

law to_nat_sub_le.m:
  for +a: U32
  for +b: U32
  for +h: {U32.is_le(b, a) == True{} : Bool}
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_sub_le.m(a, b, h, m, hm):
  +x = U32.to_nat(a)
  +y = U32.to_nat(b)
  %Equal.sym(Nat, U32.to_nat(U32.sub(a, b)), Nat.mod(Nat.sub(Nat.add(x, m), y), m), to_nat_sub.m(a, b, m, hm)) : {_ == Nat.sub(x, y) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(x, m), y), Nat.add(Nat.sub(x, y), m), sub_add_comm(x, m, y, %is_le_to_nat(b, a) : {_ == True{} : Bool}; h)) : {Nat.mod(_, m) == Nat.sub(x, y) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.sub(x, y), m), m), Nat.mod(Nat.sub(x, y), m), mod_add_self(Nat.sub(x, y), m)) : {_ == Nat.sub(x, y) : Nat}
  N.mod_small(Nat.sub(x, y), m, N.le_lt_trans(Nat.sub(x, y), x, m, sub_le(x, y), to_nat_lt.m(a, m, hm)))

law to_nat_sub_le:
  for +a: U32
  for +b: U32
  for +h: {U32.is_le(b, a) == True{} : Bool}
  {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_sub_le(a, b, h):
  to_nat_sub_le.m(a, b, h, Nat.pow(2n, 32n), {==})

# Division and remainder
# ======================

law shl_out:
  for +n: Nat
  for +c: Bool
  for +w: Word(n)
  {Word.shl.out(n, c, w) == (W.stop(n, c, w), Word.shl.put(n, c, w)) : Bool & Word(n)}

def shl_out(n, c, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Bool & Word(p), Word.shl.out(p, b, t), (W.stop(p, b, t), Word.shl.put(p, b, t)), shl_out(p, b, t)) :
            {Word.shl.out.con(p, c, _) == (W.stop(p, b, t), WCon{c, Word.shl.put(p, b, t)}) : Bool & Word(1n+p)}
          {==}

# What U32.divmod.go(k, a, b) returns: q * b + r = a and r < b.
def DMOK(k: Nat, A: Nat, B: Nat, qr: Word(k) & U32) -> Type:
  match qr:
    case (q, r):
      Pair({Nat.add(Nat.mul(Word.to_nat(k, q), B), U32.to_nat(r)) == A : Nat}, {Nat.is_lt(U32.to_nat(r), B) == True{} : Bool})

# One step of long division, as numbers (quotient bit 1, then 0).
law divstep1:
  for +q: Nat
  for +b: Nat
  for +r: Nat
  for +h: Nat
  for +a0: Bool
  for +r2: Nat
  for +e1: {Nat.add(Nat.mul(q, b), r) == h : Nat}
  for +e: {Nat.add(b, r2) == Nat.add(N.bn(a0), Nat.double(r)) : Nat}
  {Nat.add(Nat.mul(1n+Nat.double(q), b), r2) == Nat.add(N.bn(a0), Nat.double(h)) : Nat}

def divstep1(q, b, r, h, a0, r2, e1, e):
  +x = Nat.mul(Nat.double(q), b)
  %Equal.trans(Nat, Nat.add(x, Nat.add(b, r2)), Nat.add(b, Nat.add(x, r2)), Nat.add(Nat.add(b, x), r2),
      Equal.sym(Nat, Nat.add(b, Nat.add(x, r2)), Nat.add(x, Nat.add(b, r2)), N.add_left_comm(b, x, r2)),
      Equal.sym(Nat, Nat.add(Nat.add(b, x), r2), Nat.add(b, Nat.add(x, r2)), N.add_assoc(b, x, r2))) :
    {_ == Nat.add(N.bn(a0), Nat.double(h)) : Nat}
  %Equal.sym(Nat, Nat.add(b, r2), Nat.add(N.bn(a0), Nat.double(r)), e) : {Nat.add(x, _) == Nat.add(N.bn(a0), Nat.double(h)) : Nat}
  %e1 : {Nat.add(x, Nat.add(N.bn(a0), Nat.double(r))) == Nat.add(N.bn(a0), Nat.double(_)) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.mul(q, b), r)), Nat.add(Nat.double(Nat.mul(q, b)), Nat.double(r)), N.dbl_dist(Nat.mul(q, b), r)) :
    {Nat.add(x, Nat.add(N.bn(a0), Nat.double(r))) == Nat.add(N.bn(a0), _) : Nat}
  %N.mul_dbl_l(q, b) : {Nat.add(x, Nat.add(N.bn(a0), Nat.double(r))) == Nat.add(N.bn(a0), Nat.add(_, Nat.double(r))) : Nat}
  N.add_left_comm(x, N.bn(a0), Nat.double(r))

law divstep0:
  for +q: Nat
  for +b: Nat
  for +r: Nat
  for +h: Nat
  for +a0: Bool
  for +s: Nat
  for +e1: {Nat.add(Nat.mul(q, b), r) == h : Nat}
  for +e: {s == Nat.add(N.bn(a0), Nat.double(r)) : Nat}
  {Nat.add(Nat.mul(Nat.double(q), b), s) == Nat.add(N.bn(a0), Nat.double(h)) : Nat}

def divstep0(q, b, r, h, a0, s, e1, e):
  +x = Nat.mul(Nat.double(q), b)
  %Equal.sym(Nat, s, Nat.add(N.bn(a0), Nat.double(r)), e) : {Nat.add(x, _) == Nat.add(N.bn(a0), Nat.double(h)) : Nat}
  %e1 : {Nat.add(x, Nat.add(N.bn(a0), Nat.double(r))) == Nat.add(N.bn(a0), Nat.double(_)) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.mul(q, b), r)), Nat.add(Nat.double(Nat.mul(q, b)), Nat.double(r)), N.dbl_dist(Nat.mul(q, b), r)) :
    {Nat.add(x, Nat.add(N.bn(a0), Nat.double(r))) == Nat.add(N.bn(a0), _) : Nat}
  %N.mul_dbl_l(q, b) : {Nat.add(x, Nat.add(N.bn(a0), Nat.double(r))) == Nat.add(N.bn(a0), Nat.add(_, Nat.double(r))) : Nat}
  N.add_left_comm(x, N.bn(a0), Nat.double(r))

law lt_add_cancel_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

def lt_add_cancel_l(c, a, b, h):
  match c:
    case 0n:
      h
    case 1n+p:
      lt_add_cancel_l(p, a, b, h)

# x < 2b and b <= x give x - b < b.
law sub_lt_dbl:
  for +x: Nat
  for +b: Nat
  for +h1: {Nat.is_lt(x, Nat.double(b)) == True{} : Bool}
  for +h2: {Nat.is_le(b, x) == True{} : Bool}
  {Nat.is_lt(Nat.sub(x, b), b) == True{} : Bool}

def sub_lt_dbl(x, b, h1, h2):
  lt_add_cancel_l(b, Nat.sub(x, b), b,
    %Equal.sym(Nat, Nat.add(b, Nat.sub(x, b)), x, N.le_sub_add(b, x, h2)) : {Nat.is_lt(_, Nat.add(b, b)) == True{} : Bool}
    %N.dbl_add(b) : {Nat.is_lt(x, _) == True{} : Bool}
    h1)

law ge_le:
  for +x: Nat
  for +y: Nat
  {Nat.is_ge(x, y) == Nat.is_le(y, x) : Bool}

def ge_le(x, y):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ge_le(p, q)

# The quotient bit is 1: the remainder becomes 2r + a0 - b.
def dm_fin.t(+p: Nat, +q: Word(p), +s: Word(32n), +t: Bool, +b: U32, +a0: Bool, +hi: Word(p), +r: Nat, +m: Nat,
  +hm: {Nat.pow(2n, 32n) == m : Nat}, +g: Bool,
  +eg: {Bool.or(t, U32.is_ge(U32{s}, b)) == g : Bool},
  +e1: {Nat.add(Nat.mul(Word.to_nat(p, q), U32.to_nat(b)), r) == Word.to_nat(p, hi) : Nat},
  +e2: {Nat.is_lt(r, U32.to_nat(b)) == True{} : Bool},
  +ep: {Nat.add(Word.to_nat(32n, s), Nat.mul(N.bn(t), m)) == Nat.add(N.bn(a0), Nat.double(r)) : Nat}) ->
  DMOK(1n+p, Nat.add(N.bn(a0), Nat.double(Word.to_nat(p, hi))), U32.to_nat(b), U32.divmod.go.fin(p, q, U32{s}, b, g)):
  match t g:
    case True{} True{}:
      +bb = U32.to_nat(b)
      +sv = Word.to_nat(32n, s)
      +rr = Nat.add(N.bn(a0), Nat.double(r))
      # 2r + a0 = s + m
      +er = Equal.trans(Nat, rr, Nat.add(sv, Nat.mul(1n, m)), Nat.add(sv, m), Equal.sym(Nat, Nat.add(sv, Nat.mul(1n, m)), rr, ep),
        Equal.cong(Nat, Nat, z => Nat.add(sv, z), Nat.mul(1n, m), m, N.add_zero(m)))
      +hle = N.lt_to_le(bb, rr, %Equal.sym(Nat, rr, Nat.add(sv, m), er) : {Nat.is_lt(bb, _) == True{} : Bool}; N.lt_le_trans(bb, m, Nat.add(sv, m), to_nat_lt.m(b, m, hm), N.le_add_l(m, sv)))
      +hlt = sub_lt_dbl(rr, bb, W.lt_dbl_bit(r, bb, a0, e2), hle)
      +ev = Equal.trans(Nat, U32.to_nat(U32.sub(U32{s}, b)), Nat.mod(Nat.sub(Nat.add(sv, m), bb), m), Nat.sub(rr, bb),
        to_nat_sub.m(U32{s}, b, m, hm),
        %er : {Nat.mod(Nat.sub(_, bb), m) == Nat.sub(rr, bb) : Nat}
        N.mod_small(Nat.sub(rr, bb), m, N.lt_trans(Nat.sub(rr, bb), bb, m, hlt, to_nat_lt.m(b, m, hm))))
      (%Equal.sym(Nat, U32.to_nat(U32.sub(U32{s}, b)), Nat.sub(rr, bb), ev) : {Nat.add(Nat.mul(1n+Nat.double(Word.to_nat(p, q)), bb), _) == Nat.add(N.bn(a0), Nat.double(Word.to_nat(p, hi))) : Nat}
        divstep1(Word.to_nat(p, q), bb, r, Word.to_nat(p, hi), a0, Nat.sub(rr, bb), e1, N.le_sub_add(bb, rr, hle)),
       %Equal.sym(Nat, U32.to_nat(U32.sub(U32{s}, b)), Nat.sub(rr, bb), ev) : {Nat.is_lt(_, bb) == True{} : Bool}; hlt)
    case True{} False{}:
      Empty.absurd(DMOK(1n+p, Nat.add(N.bn(a0), Nat.double(Word.to_nat(p, hi))), U32.to_nat(b), (WCon{False{}, q}, U32{s})), N.true_ne_false(eg))
    case False{} True{}:
      +bb = U32.to_nat(b)
      +sv = Word.to_nat(32n, s)
      +rr = Nat.add(N.bn(a0), Nat.double(r))
      +er = Equal.trans(Nat, rr, Nat.add(sv, 0n), sv, Equal.sym(Nat, Nat.add(sv, 0n), rr, ep), N.add_zero(sv))
      +hle = {%Equal.sym(Nat, rr, sv, er) : {Nat.is_le(bb, _) == True{} : Bool}; %ge_le(sv, bb) : {_ == True{} : Bool}; %is_ge_to_nat(U32{s}, b) : {_ == True{} : Bool}; eg :
        {Nat.is_le(bb, rr) == True{} : Bool}}
      +hlt = sub_lt_dbl(rr, bb, W.lt_dbl_bit(r, bb, a0, e2), hle)
      +ev = Equal.trans(Nat, U32.to_nat(U32.sub(U32{s}, b)), Nat.mod(Nat.sub(Nat.add(sv, m), bb), m), Nat.sub(rr, bb),
        to_nat_sub.m(U32{s}, b, m, hm),
        %Equal.sym(Nat, rr, sv, er) : {Nat.mod(Nat.sub(Nat.add(sv, m), bb), m) == Nat.sub(_, bb) : Nat}
        %Equal.sym(Nat, Nat.sub(Nat.add(sv, m), bb), Nat.add(Nat.sub(sv, bb), m), sub_add_comm(sv, m, bb, %er : {Nat.is_le(bb, _) == True{} : Bool}; hle)) :
          {Nat.mod(_, m) == Nat.sub(sv, bb) : Nat}
        %Equal.sym(Nat, Nat.mod(Nat.add(Nat.sub(sv, bb), m), m), Nat.mod(Nat.sub(sv, bb), m), mod_add_self(Nat.sub(sv, bb), m)) : {_ == Nat.sub(sv, bb) : Nat}
        N.mod_small(Nat.sub(sv, bb), m, N.le_lt_trans(Nat.sub(sv, bb), sv, m, sub_le(sv, bb), wlt.m(s, m, hm))))
      (%Equal.sym(Nat, U32.to_nat(U32.sub(U32{s}, b)), Nat.sub(rr, bb), ev) : {Nat.add(Nat.mul(1n+Nat.double(Word.to_nat(p, q)), bb), _) == Nat.add(N.bn(a0), Nat.double(Word.to_nat(p, hi))) : Nat}
        divstep1(Word.to_nat(p, q), bb, r, Word.to_nat(p, hi), a0, Nat.sub(rr, bb), e1, N.le_sub_add(bb, rr, hle)),
       %Equal.sym(Nat, U32.to_nat(U32.sub(U32{s}, b)), Nat.sub(rr, bb), ev) : {Nat.is_lt(_, bb) == True{} : Bool}; hlt)
    case False{} False{}:
      +bb = U32.to_nat(b)
      +sv = Word.to_nat(32n, s)
      +er = Equal.trans(Nat, sv, Nat.add(sv, 0n), Nat.add(N.bn(a0), Nat.double(r)), Equal.sym(Nat, Nat.add(sv, 0n), sv, N.add_zero(sv)), ep)
      +hlt = N.not_le_lt(bb, sv, %ge_le(sv, bb) : {_ == False{} : Bool}; %is_ge_to_nat(U32{s}, b) : {_ == False{} : Bool}; eg)
      (divstep0(Word.to_nat(p, q), bb, r, Word.to_nat(p, hi), a0, sv, e1, er), hlt)

def dm_rec(+p: Nat, +a0: Bool, +hi: Word(p), +b: U32, +m: Nat, +hm: {Nat.pow(2n, 32n) == m : Nat},
  qr: Word(p) & U32, ih: DMOK(p, Word.to_nat(p, hi), U32.to_nat(b), qr)) ->
  DMOK(1n+p, Word.to_nat(1n+p, WCon{a0, hi}), U32.to_nat(b), U32.divmod.go.rec(p, a0, b, qr)):
  match qr:
    case (+q, +r):
      match r:
        case U32{+rw}:
          match ih:
            case (+e1, +e2):
              %Equal.sym(Nat, Word.to_nat(1n+p, WCon{a0, hi}), Nat.add(N.bn(a0), Nat.double(Word.to_nat(p, hi))), W.wcon(p, a0, hi)) :
                DMOK(1n+p, _, U32.to_nat(b), U32.divmod.go.rec(p, a0, b, (q, U32{rw})))
              %Equal.sym(Bool & Word(32n), Word.shl.out(32n, a0, rw), (W.stop(32n, a0, rw), Word.shl.put(32n, a0, rw)), shl_out(32n, a0, rw)) :
                DMOK(1n+p, Nat.add(N.bn(a0), Nat.double(Word.to_nat(p, hi))), U32.to_nat(b), U32.divmod.go.shl(p, q, b, _))
              dm_fin.t(p, q, Word.shl.put(32n, a0, rw), W.stop(32n, a0, rw), b, a0, hi, Word.to_nat(32n, rw), m, hm,
                Bool.or(W.stop(32n, a0, rw), U32.is_ge(U32{Word.shl.put(32n, a0, rw)}, b)), {==}, e1, e2, wput.m(a0, rw, m, hm))

law dm_ok:
  for +k: Nat
  for +a: Word(k)
  for +b: U32
  for +hb: {Nat.is_lt(0n, U32.to_nat(b)) == True{} : Bool}
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  DMOK(k, Word.to_nat(k, a), U32.to_nat(b), U32.divmod.go(k, a, b))

def dm_ok(k, a, b, hb, m, hm):
  match k a:
    case 0n WNil{}:
      ({==}, hb)
    case 1n+p WCon{+a0, +hi}:
      dm_rec(p, a0, hi, b, m, hm, U32.divmod.go(p, hi, b), dm_ok(p, hi, b, hb, m, hm))

def div_fin_ok(+x: Nat, +y: Nat, qr: Word(32n) & U32, d: DMOK(32n, x, y, qr)) -> {U32.to_nat(U32.div.fin(qr)) == Nat.div(x, y) : Nat}:
  match qr:
    case (+q, +r):
      match d:
        case (+e1, +e2):
          %e1 : {Word.to_nat(32n, q) == Nat.div(_, y) : Nat}
          Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(Word.to_nat(32n, q), y), U32.to_nat(r)), y), Word.to_nat(32n, q), N.div_mul_add(Word.to_nat(32n, q), y, U32.to_nat(r), e2))

def mod_fin_ok(+x: Nat, +y: Nat, qr: Word(32n) & U32, d: DMOK(32n, x, y, qr)) -> {U32.to_nat(U32.mod.fin(qr)) == Nat.mod(x, y) : Nat}:
  match qr:
    case (+q, +r):
      match d:
        case (+e1, +e2):
          %e1 : {U32.to_nat(r) == Nat.mod(_, y) : Nat}
          Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(Word.to_nat(32n, q), y), U32.to_nat(r)), y), U32.to_nat(r), N.mod_mul_add(Word.to_nat(32n, q), y, U32.to_nat(r), e2))

law ne_zero_pos:
  for +y: Nat
  for +h: {Nat.is_eq(y, 0n) == False{} : Bool}
  {Nat.is_lt(0n, y) == True{} : Bool}

def ne_zero_pos(y, h):
  match y:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.true_ne_false(h))
    case 1n+p:
      {==}

def div_if_ok(+x: Word(32n), +y: Word(32n), +m: Nat, +hm: {Nat.pow(2n, 32n) == m : Nat}, z: Bool, +ez: {U32.is_zero(U32{y}) == z : Bool}) ->
  {U32.to_nat(U32.div.if(x, U32{y}, z)) == Nat.div(Word.to_nat(32n, x), Word.to_nat(32n, y)) : Nat}:
  match z:
    case True{}:
      %Equal.sym(Nat, Word.to_nat(32n, y), 0n, N.eq_sound(Word.to_nat(32n, y), 0n, %is_zero_to_nat(U32{y}) : {_ == True{} : Bool}; ez)) :
        {0n == Nat.div(Word.to_nat(32n, x), _) : Nat}
      {==}
    case False{}:
      div_fin_ok(Word.to_nat(32n, x), Word.to_nat(32n, y), U32.divmod.go(32n, x, U32{y}),
        dm_ok(32n, x, U32{y}, ne_zero_pos(Word.to_nat(32n, y), %is_zero_to_nat(U32{y}) : {_ == False{} : Bool}; ez), m, hm))

def mod_if_ok(+x: Word(32n), +y: Word(32n), +m: Nat, +hm: {Nat.pow(2n, 32n) == m : Nat}, z: Bool, +ez: {U32.is_zero(U32{y}) == z : Bool}) ->
  {U32.to_nat(U32.mod.if(x, U32{y}, z)) == Nat.mod(Word.to_nat(32n, x), Word.to_nat(32n, y)) : Nat}:
  match z:
    case True{}:
      %Equal.sym(Nat, Word.to_nat(32n, y), 0n, N.eq_sound(Word.to_nat(32n, y), 0n, %is_zero_to_nat(U32{y}) : {_ == True{} : Bool}; ez)) :
        {Word.to_nat(32n, x) == Nat.mod(Word.to_nat(32n, x), _) : Nat}
      {==}
    case False{}:
      mod_fin_ok(Word.to_nat(32n, x), Word.to_nat(32n, y), U32.divmod.go(32n, x, U32{y}),
        dm_ok(32n, x, U32{y}, ne_zero_pos(Word.to_nat(32n, y), %is_zero_to_nat(U32{y}) : {_ == False{} : Bool}; ez), m, hm))

law to_nat_div:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.div(a, b)) == Nat.div(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_div(a, b):
  match a b:
    case U32{+x} U32{+y}:
      div_if_ok(x, y, Nat.pow(2n, 32n), {==}, U32.is_zero(U32{y}), {==})

law to_nat_mod:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.mod(a, b)) == Nat.mod(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_mod(a, b):
  match a b:
    case U32{+x} U32{+y}:
      mod_if_ok(x, y, Nat.pow(2n, 32n), {==}, U32.is_zero(U32{y}), {==})

# Minimum and maximum
# ===================

law min_lt:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.min(x, y) == x : Nat}

def min_lt(x, y, h):
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.min(1n+p, 0n) == 1n+p : Nat}, N.false_ne_true(h))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(p, q), p, min_lt(p, q, h))

law min_nlt:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(x, y) == False{} : Bool}
  {Nat.min(x, y) == y : Nat}

def min_nlt(x, y, h):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.min(0n, 1n+q) == 1n+q : Nat}, N.true_ne_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(p, q), q, min_nlt(p, q, h))

law max_lt:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.max(x, y) == y : Nat}

def max_lt(x, y, h):
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.max(1n+p, 0n) == 0n : Nat}, N.false_ne_true(h))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(p, q), q, max_lt(p, q, h))

law max_nlt:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(x, y) == False{} : Bool}
  {Nat.max(x, y) == x : Nat}

def max_nlt(x, y, h):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.max(0n, 1n+q) == 0n : Nat}, N.true_ne_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(p, q), p, max_nlt(p, q, h))

def min_ok(+a: U32, +b: U32, z: Bool, +ez: {U32.is_lt(a, b) == z : Bool}) ->
  {U32.to_nat(Bool.pick(U32, z, a, b)) == Nat.min(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match z:
    case True{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(a),
        min_lt(U32.to_nat(a), U32.to_nat(b), %is_lt_to_nat(a, b) : {_ == True{} : Bool}; ez))
    case False{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(b),
        min_nlt(U32.to_nat(a), U32.to_nat(b), %is_lt_to_nat(a, b) : {_ == False{} : Bool}; ez))

def max_ok(+a: U32, +b: U32, z: Bool, +ez: {U32.is_lt(a, b) == z : Bool}) ->
  {U32.to_nat(Bool.pick(U32, z, b, a)) == Nat.max(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match z:
    case True{}:
      Equal.sym(Nat, Nat.max(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(b),
        max_lt(U32.to_nat(a), U32.to_nat(b), %is_lt_to_nat(a, b) : {_ == True{} : Bool}; ez))
    case False{}:
      Equal.sym(Nat, Nat.max(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(a),
        max_nlt(U32.to_nat(a), U32.to_nat(b), %is_lt_to_nat(a, b) : {_ == False{} : Bool}; ez))

law to_nat_min:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.min(a, b)) == Nat.min(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_min(a, b):
  match a b:
    case U32{+x} U32{+y}:
      min_ok(U32{x}, U32{y}, U32.is_lt(U32{x}, U32{y}), {==})

law to_nat_max:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.max(a, b)) == Nat.max(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_max(a, b):
  match a b:
    case U32{+x} U32{+y}:
      max_ok(U32{x}, U32{y}, U32.is_lt(U32{x}, U32{y}), {==})

# Shifts
# ======

law to_nat_shr:
  for +a: U32
  {U32.to_nat(U32.shr(a)) == Nat.div(U32.to_nat(a), 2n) : Nat}

def to_nat_shr(a):
  match a:
    case U32{+x}:
      W.wshr(32n, x)

law to_nat_shl.m:
  for +a: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.shl(a)) == Nat.mod(Nat.mul(U32.to_nat(a), 2n), m) : Nat}

def to_nat_shl.m(a, m, hm):
  match a:
    case U32{+w}:
      %Equal.sym(Nat, Nat.mul(Word.to_nat(32n, w), 2n), Nat.double(Word.to_nat(32n, w)), N.mul2_r(Word.to_nat(32n, w))) :
        {Word.to_nat(32n, Word.shl(32n, w)) == Nat.mod(_, m) : Nat}
      Equal.sym(Nat, Nat.mod(Nat.double(Word.to_nat(32n, w)), m), Word.to_nat(32n, Word.shl(32n, w)),
        W.carry_mod(Word.to_nat(32n, Word.shl(32n, w)), N.bn(W.shtop(32n, w)), m, Nat.double(Word.to_nat(32n, w)), wshl.m(w, m, hm), wlt.m(Word.shl(32n, w), m, hm)))

law to_nat_shl_p:
  for +a: U32
  {U32.to_nat(U32.shl(a)) == Nat.mod(Nat.mul(U32.to_nat(a), 2n), Nat.pow(2n, 32n)) : Nat}

def to_nat_shl_p(a):
  to_nat_shl.m(a, Nat.pow(2n, 32n), {==})

law to_nat_shrn:
  for +a: U32
  for +k: Nat
  {U32.to_nat(U32.shrn(a, k)) == Nat.div(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

def to_nat_shrn(a, k):
  match k:
    case 0n:
      Equal.sym(Nat, Nat.div(U32.to_nat(a), 1n), U32.to_nat(a), N.div_one(U32.to_nat(a)))
    case 1n+p:
      +x = U32.to_nat(a)
      +pp = Nat.pow(2n, p)
      %Equal.sym(Nat, U32.to_nat(U32.shr(U32.shrn(a, p))), Nat.div(U32.to_nat(U32.shrn(a, p)), 2n), to_nat_shr(U32.shrn(a, p))) :
        {_ == Nat.div(x, Nat.mul(2n, pp)) : Nat}
      %Equal.sym(Nat, U32.to_nat(U32.shrn(a, p)), Nat.div(x, pp), to_nat_shrn(a, p)) : {Nat.div(_, 2n) == Nat.div(x, Nat.mul(2n, pp)) : Nat}
      %Equal.sym(Nat, Nat.div(Nat.div(x, pp), 2n), Nat.div(x, Nat.mul(pp, 2n)), N.div_div(x, pp, 2n)) : {_ == Nat.div(x, Nat.mul(2n, pp)) : Nat}
      %N.mul_comm(2n, pp) : {Nat.div(x, _) == Nat.div(x, Nat.mul(2n, pp)) : Nat}
      {==}

law to_nat_shln.m:
  for +a: U32
  for +k: Nat
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.shln(a, k)) == Nat.mod(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), m) : Nat}

def to_nat_shln.m(a, k, m, hm):
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.mul(U32.to_nat(a), 1n), U32.to_nat(a), N.mul_one(U32.to_nat(a))) : {U32.to_nat(a) == Nat.mod(_, m) : Nat}
      Equal.sym(Nat, Nat.mod(U32.to_nat(a), m), U32.to_nat(a), N.mod_small(U32.to_nat(a), m, to_nat_lt.m(a, m, hm)))
    case 1n+p:
      +x = U32.to_nat(a)
      +pp = Nat.pow(2n, p)
      %Equal.sym(Nat, U32.to_nat(U32.shl(U32.shln(a, p))), Nat.mod(Nat.mul(U32.to_nat(U32.shln(a, p)), 2n), m), to_nat_shl.m(U32.shln(a, p), m, hm)) :
        {_ == Nat.mod(Nat.mul(x, Nat.mul(2n, pp)), m) : Nat}
      %Equal.sym(Nat, U32.to_nat(U32.shln(a, p)), Nat.mod(Nat.mul(x, pp), m), to_nat_shln.m(a, p, m, hm)) :
        {Nat.mod(Nat.mul(_, 2n), m) == Nat.mod(Nat.mul(x, Nat.mul(2n, pp)), m) : Nat}
      %Equal.sym(Nat, Nat.mod(Nat.mul(Nat.mod(Nat.mul(x, pp), m), 2n), m), Nat.mod(Nat.mul(Nat.mul(x, pp), 2n), m), N.mod_mul_mod_l(Nat.mul(x, pp), 2n, m)) :
        {_ == Nat.mod(Nat.mul(x, Nat.mul(2n, pp)), m) : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.mul(x, pp), 2n), Nat.mul(x, Nat.mul(pp, 2n)), N.mul_assoc(x, pp, 2n)) :
        {Nat.mod(_, m) == Nat.mod(Nat.mul(x, Nat.mul(2n, pp)), m) : Nat}
      %N.mul_comm(2n, pp) : {Nat.mod(Nat.mul(x, _), m) == Nat.mod(Nat.mul(x, Nat.mul(2n, pp)), m) : Nat}
      {==}

law to_nat_shln_p:
  for +a: U32
  for +k: Nat
  {U32.to_nat(U32.shln(a, k)) == Nat.mod(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), Nat.pow(2n, 32n)) : Nat}

def to_nat_shln_p(a, k):
  to_nat_shln.m(a, k, Nat.pow(2n, 32n), {==})

law to_nat_shln_fits_p:
  for +a: U32
  for +k: Nat
  for +h: {Nat.is_lt(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), Nat.pow(2n, 32n)) == True{} : Bool}
  {U32.to_nat(U32.shln(a, k)) == Nat.mul(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

def to_nat_shln_fits_p(a, k, h):
  Equal.trans(Nat, U32.to_nat(U32.shln(a, k)), Nat.mod(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), Nat.pow(2n, 32n)), Nat.mul(U32.to_nat(a), Nat.pow(2n, k)),
    to_nat_shln_p(a, k), N.mod_small(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), Nat.pow(2n, 32n), h))

def shln_mod.go(+x: Nat, +k: Nat, +m: Nat, +hm: {Nat.pow(2n, 32n) == m : Nat}, z: Bool, +ez: {Nat.is_le(k, 32n) == z : Bool}) ->
  {Nat.mod(Nat.mod(Nat.mul(x, Nat.pow(2n, k)), m), Nat.pow(2n, k)) == 0n : Nat}:
  match z:
    case True{}:
      %hm : {Nat.mod(Nat.mod(Nat.mul(x, Nat.pow(2n, k)), _), Nat.pow(2n, k)) == 0n : Nat}
      %Equal.sym(Nat, Nat.mod(Nat.mod(Nat.mul(x, Nat.pow(2n, k)), Nat.pow(2n, 32n)), Nat.pow(2n, k)), Nat.mod(Nat.mul(x, Nat.pow(2n, k)), Nat.pow(2n, k)),
          N.mod_mod_pow(Nat.mul(x, Nat.pow(2n, k)), k, 32n, ez)) :
        {_ == 0n : Nat}
      N.mul_mod(x, Nat.pow(2n, k))
    case False{}:
      +d = Nat.sub(k, 32n)
      +pd = Nat.pow(2n, d)
      +inner = {
        %N.le_sub_add(32n, k, N.lt_to_le(32n, k, N.not_le_lt(k, 32n, ez))) : {Nat.mod(Nat.mul(x, Nat.pow(2n, _)), m) == 0n : Nat}
        %Equal.sym(Nat, Nat.pow(2n, Nat.add(32n, d)), Nat.mul(Nat.pow(2n, 32n), pd), N.pow_add(2n, 32n, d)) :
          {Nat.mod(Nat.mul(x, _), m) == 0n : Nat}
        %Equal.sym(Nat, Nat.pow(2n, 32n), m, hm) : {Nat.mod(Nat.mul(x, Nat.mul(_, pd)), m) == 0n : Nat}
        %N.mul_comm(pd, m) : {Nat.mod(Nat.mul(x, _), m) == 0n : Nat}
        %N.mul_assoc(x, pd, m) : {Nat.mod(_, m) == 0n : Nat}
        N.mul_mod(Nat.mul(x, pd), m) : {Nat.mod(Nat.mul(x, Nat.pow(2n, k)), m) == 0n : Nat}}
      %Equal.sym(Nat, Nat.mod(Nat.mul(x, Nat.pow(2n, k)), m), 0n, inner) : {Nat.mod(_, Nat.pow(2n, k)) == 0n : Nat}
      N.mod_zero_l(Nat.pow(2n, k))

law to_nat_shln_mod.m:
  for +a: U32
  for +k: Nat
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.mod(U32.to_nat(U32.shln(a, k)), Nat.pow(2n, k)) == 0n : Nat}

def to_nat_shln_mod.m(a, k, m, hm):
  %Equal.sym(Nat, U32.to_nat(U32.shln(a, k)), Nat.mod(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), m), to_nat_shln.m(a, k, m, hm)) :
    {Nat.mod(_, Nat.pow(2n, k)) == 0n : Nat}
  shln_mod.go(U32.to_nat(a), k, m, hm, Nat.is_le(k, 32n), {==})

law to_nat_shln_mod:
  for +a: U32
  for +k: Nat
  {Nat.mod(U32.to_nat(U32.shln(a, k)), Nat.pow(2n, k)) == 0n : Nat}

def to_nat_shln_mod(a, k):
  to_nat_shln_mod.m(a, k, Nat.pow(2n, 32n), {==})

law to_nat_shrn_lt.m:
  for +a: U32
  for +k: Nat
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {Nat.is_lt(U32.to_nat(U32.shrn(a, k)), Nat.pow(2n, Nat.sub(32n, k))) == True{} : Bool}

def to_nat_shrn_lt.m(a, k, m, hm):
  +x = U32.to_nat(a)
  +e = Nat.sub(32n, k)
  %Equal.sym(Nat, U32.to_nat(U32.shrn(a, k)), Nat.div(x, Nat.pow(2n, k)), to_nat_shrn(a, k)) : {Nat.is_lt(_, Nat.pow(2n, e)) == True{} : Bool}
  N.div_lt(x, Nat.pow(2n, k), Nat.pow(2n, e), N.pow_pos(k),
    %N.pow_add(2n, k, e) : {Nat.is_lt(x, _) == True{} : Bool}
    N.lt_le_trans(x, m, Nat.pow(2n, Nat.add(k, e)), to_nat_lt.m(a, m, hm),
      %hm : {Nat.is_le(_, Nat.pow(2n, Nat.add(k, Nat.sub(32n, k)))) == True{} : Bool}
      N.pow_le(32n, Nat.add(k, Nat.sub(32n, k)), N.le_add_sub(32n, k))))

law to_nat_shrn_lt:
  for +a: U32
  for +k: Nat
  {Nat.is_lt(U32.to_nat(U32.shrn(a, k)), Nat.pow(2n, Nat.sub(32n, k))) == True{} : Bool}

def to_nat_shrn_lt(a, k):
  to_nat_shrn_lt.m(a, k, Nat.pow(2n, 32n), {==})

# Bitwise operations as numbers
# =============================

law to_nat_and_mask:
  for +a: U32
  for +m: U32
  for +k: Nat
  for +h: {U32.to_nat(m) == Nat.sub(Nat.pow(2n, k), 1n) : Nat}
  {U32.to_nat(U32.and(a, m)) == Nat.mod(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

def to_nat_and_mask(a, m, k, h):
  match a m:
    case U32{+x} U32{+y}:
      W.and_mask(32n, x, y, k, h)

law to_nat_not.m:
  for +a: U32
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {U32.to_nat(U32.not(a)) == Nat.sub(Nat.sub(m, 1n), U32.to_nat(a)) : Nat}

def to_nat_not.m(a, m, hm):
  match a:
    case U32{+w}:
      +x = Word.to_nat(32n, w)
      +y = Word.to_nat(32n, Word.not(32n, w))
      %wnot.m(w, m, hm) : {y == Nat.sub(Nat.sub(_, 1n), x) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(y, x), 0n), Nat.add(y, x), N.sub_zero(Nat.add(y, x))) : {y == Nat.sub(_, x) : Nat}
      Equal.sym(Nat, Nat.sub(Nat.add(y, x), x), y, N.sub_add(y, x))

law to_nat_not_p:
  for +a: U32
  {U32.to_nat(U32.not(a)) == Nat.sub(Nat.sub(Nat.pow(2n, 32n), 1n), U32.to_nat(a)) : Nat}

def to_nat_not_p(a):
  to_nat_not.m(a, Nat.pow(2n, 32n), {==})

law to_nat_or_split:
  for +a: U32
  for +b: U32
  for +k: Nat
  for +ha: {Nat.mod(U32.to_nat(a), Nat.pow(2n, k)) == 0n : Nat}
  for +hb: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, k)) == True{} : Bool}
  {U32.to_nat(U32.or(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_or_split(a, b, k, ha, hb):
  match a b:
    case U32{+x} U32{+y}:
      W.or_split(32n, x, y, k, ha, hb)

law to_nat_xor_split:
  for +a: U32
  for +b: U32
  for +k: Nat
  for +ha: {Nat.mod(U32.to_nat(a), Nat.pow(2n, k)) == 0n : Nat}
  for +hb: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, k)) == True{} : Bool}
  {U32.to_nat(U32.xor(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

def to_nat_xor_split(a, b, k, ha, hb):
  match a b:
    case U32{+x} U32{+y}:
      W.xor_split(32n, x, y, k, ha, hb)

# Indexes
# =======

law to_nat_split:
  for +a: U32
  for +m: U32
  for +k: Nat
  for +h: {U32.to_nat(m) == Nat.sub(Nat.pow(2n, k), 1n) : Nat}
  {U32.to_nat(a) == Nat.add(Nat.mul(U32.to_nat(U32.shrn(a, k)), Nat.pow(2n, k)), U32.to_nat(U32.and(a, m))) : Nat}

def to_nat_split(a, m, k, h):
  +x = U32.to_nat(a)
  +pk = Nat.pow(2n, k)
  %Equal.sym(Nat, U32.to_nat(U32.shrn(a, k)), Nat.div(x, pk), to_nat_shrn(a, k)) :
    {x == Nat.add(Nat.mul(_, pk), U32.to_nat(U32.and(a, m))) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.and(a, m)), Nat.mod(x, pk), to_nat_and_mask(a, m, k, h)) :
    {x == Nat.add(Nat.mul(Nat.div(x, pk), pk), _) : Nat}
  Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(x, pk), pk), Nat.mod(x, pk)), x, N.div_mod(x, pk))

law shrn_lt_words:
  for +i: U32
  for +w: U32
  for +k: Nat
  for +h: {Nat.is_lt(U32.to_nat(i), Nat.mul(Nat.pow(2n, k), U32.to_nat(w))) == True{} : Bool}
  {U32.is_lt(U32.shrn(i, k), w) == True{} : Bool}

def shrn_lt_words(i, w, k, h):
  %Equal.sym(Bool, U32.is_lt(U32.shrn(i, k), w), Nat.is_lt(U32.to_nat(U32.shrn(i, k)), U32.to_nat(w)), is_lt_to_nat(U32.shrn(i, k), w)) :
    {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.shrn(i, k)), Nat.div(U32.to_nat(i), Nat.pow(2n, k)), to_nat_shrn(i, k)) :
    {Nat.is_lt(_, U32.to_nat(w)) == True{} : Bool}
  N.div_lt(U32.to_nat(i), Nat.pow(2n, k), U32.to_nat(w), N.pow_pos(k), h)

# Bits
# ====

law bitw:
  for +w: Word(32n)
  for +k: Nat
  {D.bit(U32{w}, k) == W.wbit(32n, w, k) : Bool}

def bitw(w, k):
  W.wbit_num(32n, w, k)

law bit_and:
  for +a: U32
  for +b: U32
  for +k: Nat
  {D.bit(U32.and(a, b), k) == (D.bit(a, k) && D.bit(b, k)) : Bool}

def bit_and(a, b, k):
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Bool, D.bit(U32{Word.and(32n, x, y)}, k), W.wbit(32n, Word.and(32n, x, y), k), bitw(Word.and(32n, x, y), k)) :
        {_ == Bool.and(D.bit(U32{x}, k), D.bit(U32{y}, k)) : Bool}
      %Equal.sym(Bool, D.bit(U32{x}, k), W.wbit(32n, x, k), bitw(x, k)) : {W.wbit(32n, Word.and(32n, x, y), k) == Bool.and(_, D.bit(U32{y}, k)) : Bool}
      %Equal.sym(Bool, D.bit(U32{y}, k), W.wbit(32n, y, k), bitw(y, k)) : {W.wbit(32n, Word.and(32n, x, y), k) == Bool.and(W.wbit(32n, x, k), _) : Bool}
      W.wbit_and(32n, x, y, k)

law bit_or:
  for +a: U32
  for +b: U32
  for +k: Nat
  {D.bit(U32.or(a, b), k) == (D.bit(a, k) || D.bit(b, k)) : Bool}

def bit_or(a, b, k):
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Bool, D.bit(U32{Word.or(32n, x, y)}, k), W.wbit(32n, Word.or(32n, x, y), k), bitw(Word.or(32n, x, y), k)) :
        {_ == Bool.or(D.bit(U32{x}, k), D.bit(U32{y}, k)) : Bool}
      %Equal.sym(Bool, D.bit(U32{x}, k), W.wbit(32n, x, k), bitw(x, k)) : {W.wbit(32n, Word.or(32n, x, y), k) == Bool.or(_, D.bit(U32{y}, k)) : Bool}
      %Equal.sym(Bool, D.bit(U32{y}, k), W.wbit(32n, y, k), bitw(y, k)) : {W.wbit(32n, Word.or(32n, x, y), k) == Bool.or(W.wbit(32n, x, k), _) : Bool}
      W.wbit_or(32n, x, y, k)

law bit_xor:
  for +a: U32
  for +b: U32
  for +k: Nat
  {D.bit(U32.xor(a, b), k) == Bool.xor(D.bit(a, k), D.bit(b, k)) : Bool}

def bit_xor(a, b, k):
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Bool, D.bit(U32{Word.xor(32n, x, y)}, k), W.wbit(32n, Word.xor(32n, x, y), k), bitw(Word.xor(32n, x, y), k)) :
        {_ == Bool.xor(D.bit(U32{x}, k), D.bit(U32{y}, k)) : Bool}
      %Equal.sym(Bool, D.bit(U32{x}, k), W.wbit(32n, x, k), bitw(x, k)) : {W.wbit(32n, Word.xor(32n, x, y), k) == Bool.xor(_, D.bit(U32{y}, k)) : Bool}
      %Equal.sym(Bool, D.bit(U32{y}, k), W.wbit(32n, y, k), bitw(y, k)) : {W.wbit(32n, Word.xor(32n, x, y), k) == Bool.xor(W.wbit(32n, x, k), _) : Bool}
      W.wbit_xor(32n, x, y, k)

law bit_not:
  for +a: U32
  for +k: Nat
  {D.bit(U32.not(a), k) == (Nat.is_lt(k, 32n) && Bool.not(D.bit(a, k))) : Bool}

def bit_not(a, k):
  match a:
    case U32{+x}:
      %Equal.sym(Bool, D.bit(U32{Word.not(32n, x)}, k), W.wbit(32n, Word.not(32n, x), k), bitw(Word.not(32n, x), k)) :
        {_ == Bool.and(Nat.is_lt(k, 32n), Bool.not(D.bit(U32{x}, k))) : Bool}
      %Equal.sym(Bool, D.bit(U32{x}, k), W.wbit(32n, x, k), bitw(x, k)) : {W.wbit(32n, Word.not(32n, x), k) == Bool.and(Nat.is_lt(k, 32n), Bool.not(_)) : Bool}
      W.wbit_not(32n, x, k)

law bit_ext:
  for +a: U32
  for +b: U32
  for h: @k: Nat -> {D.bit(a, k) == D.bit(b, k) : Bool}
  {a == b : U32}

def bit_ext(a, b, h):
  match a b:
    case U32{+x} U32{+y}:
      +d = W.wdiff(32n, x, y)
      %W.wext(32n, x, y, Equal.trans(Bool, W.wbit(32n, x, d), D.bit(U32{x}, d), W.wbit(32n, y, d),
          Equal.sym(Bool, D.bit(U32{x}, d), W.wbit(32n, x, d), bitw(x, d)),
          Equal.trans(Bool, D.bit(U32{x}, d), D.bit(U32{y}, d), W.wbit(32n, y, d), h(d), bitw(y, d)))) :
        {U32{x} == U32{_} : U32}
      {==}
