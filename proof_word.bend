import Base
import ./proof_nat.bend as N

# Facts about Word(n), n bits lowest first, as numbers: W(n, w) is
# Word.to_nat(n, w) and P(n) is 2^n. Proven once for every width by
# induction on n; proof_u32.bend specializes them to 32.

# Numbers
# =======

# The value of a word with head bit b and tail t.
law wcon:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  {Word.to_nat(1n+p, WCon{b, t}) == Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t))) : Nat}

def wcon(p, b, t):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bn_lt2:
  for +b: Bool
  {Nat.is_lt(N.bn(b), 2n) == True{} : Bool}

def bn_lt2(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# The same value as t * 2 + b.
law wcon2:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  {Word.to_nat(1n+p, WCon{b, t}) == Nat.add(Nat.mul(Word.to_nat(p, t), 2n), N.bn(b)) : Nat}

def wcon2(p, b, t):
  +x = Word.to_nat(p, t)
  %Equal.sym(Nat, Nat.mul(x, 2n), Nat.double(x), N.mul2_r(x)) : {Word.to_nat(1n+p, WCon{b, t}) == Nat.add(_, N.bn(b)) : Nat}
  %N.add_comm(N.bn(b), Nat.double(x)) : {Word.to_nat(1n+p, WCon{b, t}) == _ : Nat}
  wcon(p, b, t)

# b + 2x < 2y when x < y.
law lt_dbl_bit:
  for +x: Nat
  for +y: Nat
  for +b: Bool
  for +h: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.is_lt(Nat.add(N.bn(b), Nat.double(x)), Nat.double(y)) == True{} : Bool}

def lt_dbl_bit(x, y, b, h):
  match x y:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.add(N.bn(b), Nat.double(x)), 0n) == True{} : Bool},
        N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, N.lt_zero(x)), h)))
    case 0n 1n+q:
      match b:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p 1n+q:
      match b:
        case False{}:
          lt_dbl_bit(p, q, False{}, h)
        case True{}:
          lt_dbl_bit(p, q, True{}, h)

# b + 2x < 2y gives x < y.
law lt_dbl_inv:
  for +x: Nat
  for +y: Nat
  for +b: Bool
  for +h: {Nat.is_lt(Nat.add(N.bn(b), Nat.double(x)), Nat.double(y)) == True{} : Bool}
  {Nat.is_lt(x, y) == True{} : Bool}

def lt_dbl_inv(x, y, b, h):
  match x y:
    case 0n 0n:
      match b:
        case False{}:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.false_ne_true(h))
        case True{}:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      match b:
        case False{}:
          Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, N.false_ne_true(h))
        case True{}:
          Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, N.false_ne_true(h))
    case 1n+p 1n+q:
      match b:
        case False{}:
          lt_dbl_inv(p, q, False{}, h)
        case True{}:
          lt_dbl_inv(p, q, True{}, h)

# (b + 2x) % 2q = b + 2 (x % q).
law moddbl:
  for +b: Bool
  for +x: Nat
  for +q: Nat
  for +hq: {Nat.is_lt(0n, q) == True{} : Bool}
  {Nat.mod(Nat.add(N.bn(b), Nat.double(x)), Nat.double(q)) == Nat.add(N.bn(b), Nat.double(Nat.mod(x, q))) : Nat}

def moddbl(b, x, q, hq):
  +d = Nat.div(x, q)
  +r = Nat.mod(x, q)
  +dq = Nat.double(q)
  %N.div_mod(x, q) : {Nat.mod(Nat.add(N.bn(b), Nat.double(_)), dq) == Nat.add(N.bn(b), Nat.double(r)) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.mul(d, q), r)), Nat.add(Nat.double(Nat.mul(d, q)), Nat.double(r)), N.dbl_dist(Nat.mul(d, q), r)) :
    {Nat.mod(Nat.add(N.bn(b), _), dq) == Nat.add(N.bn(b), Nat.double(r)) : Nat}
  %N.mul_dbl_r(d, q) : {Nat.mod(Nat.add(N.bn(b), Nat.add(_, Nat.double(r))), dq) == Nat.add(N.bn(b), Nat.double(r)) : Nat}
  %N.add_left_comm(Nat.mul(d, dq), N.bn(b), Nat.double(r)) : {Nat.mod(_, dq) == Nat.add(N.bn(b), Nat.double(r)) : Nat}
  N.mod_mul_add(d, dq, Nat.add(N.bn(b), Nat.double(r)), lt_dbl_bit(r, q, b, N.mod_lt(x, q, hq)))

# Every word stands for a number below 2^n.
law wlt:
  for +n: Nat
  for +w: Word(n)
  {Nat.is_lt(Word.to_nat(n, w), Nat.pow(2n, n)) == True{} : Bool}

def wlt(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.double(Nat.pow(2n, p)), N.pow2s(p)) :
            {Nat.is_lt(Word.to_nat(1n+p, WCon{b, t}), _) == True{} : Bool}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b, t}), Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t))), wcon(p, b, t)) :
            {Nat.is_lt(_, Nat.double(Nat.pow(2n, p))) == True{} : Bool}
          lt_dbl_bit(Word.to_nat(p, t), Nat.pow(2n, p), b, wlt(p, t))

# r + c * m = x with r < m gives x % m = r.
law carry_mod:
  for +r: Nat
  for +c: Nat
  for +m: Nat
  for +x: Nat
  for +e: {Nat.add(r, Nat.mul(c, m)) == x : Nat}
  for +h: {Nat.is_lt(r, m) == True{} : Bool}
  {Nat.mod(x, m) == r : Nat}

def carry_mod(r, c, m, x, e, h):
  %Equal.trans(Nat, Nat.add(Nat.mul(c, m), r), Nat.add(r, Nat.mul(c, m)), x, N.add_comm(Nat.mul(c, m), r), e) :
    {Nat.mod(_, m) == r : Nat}
  N.mod_mul_add(c, m, r, h)

# Comparison
# ==========

law cmp_dbl:
  for +x: Nat
  for +y: Nat
  for +a: Bool
  for +b: Bool
  {Word.cmp.fin(a, b, Nat.cmp(x, y)) == Nat.cmp(Nat.add(N.bn(a), Nat.double(x)), Nat.add(N.bn(b), Nat.double(y))) : Cmp}

def cmp_dbl(x, y, a, b):
  match x y:
    case 0n 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 1n+q:
      match a b:
        case False{} False{}:
          cmp_dbl(p, q, False{}, False{})
        case False{} True{}:
          cmp_dbl(p, q, False{}, True{})
        case True{} False{}:
          cmp_dbl(p, q, True{}, False{})
        case True{} True{}:
          cmp_dbl(p, q, True{}, True{})

# Words compare as their numbers.
law wcmp:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

def wcmp(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), wcmp(p, at, bt)) :
            {Word.cmp.fin(x, y, _) == Nat.cmp(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, at}), Nat.add(N.bn(x), Nat.double(Word.to_nat(p, at))), wcon(p, x, at)) :
            {Word.cmp.fin(x, y, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.cmp(_, Word.to_nat(1n+p, WCon{y, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), Nat.add(N.bn(y), Nat.double(Word.to_nat(p, bt))), wcon(p, y, bt)) :
            {Word.cmp.fin(x, y, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.cmp(Nat.add(N.bn(x), Nat.double(Word.to_nat(p, at))), _) : Cmp}
          cmp_dbl(Word.to_nat(p, at), Word.to_nat(p, bt), x, y)

def Cmp.disc_eq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case o:
      Unit

def lt_ne_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : Cmp.disc_eq(_)
  Unit{}

def gt_ne_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : Cmp.disc_eq(_)
  Unit{}

def bool_cmp_eq(+a: Bool, +b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, lt_ne_eq(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, gt_ne_eq(e))
    case True{} True{}:
      {==}

def word_fin_t(+ab: Bool, +bb: Bool, +t: Cmp, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, lt_ne_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, gt_ne_eq(e))

def word_fin_b(+ab: Bool, +bb: Bool, +t: Cmp, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {Bool.cmp(ab, bb) == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({Bool.cmp(ab, bb) == EQ{} : Cmp}, lt_ne_eq(e))
    case EQ{}:
      e
    case GT{}:
      Empty.absurd({Bool.cmp(ab, bb) == EQ{} : Cmp}, gt_ne_eq(e))

def word_cmp_eq(+n: Nat, +a: Word(n), +b: Word(n), +e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %bool_cmp_eq(ab, bb, word_fin_b(ab, bb, Word.cmp(p, at, bt), e)) : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %word_cmp_eq(p, at, bt, word_fin_t(ab, bb, Word.cmp(p, at, bt), e)) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# Two words that stand for the same number are the same word.
law winj:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}

def winj(n, a, b, e):
  word_cmp_eq(n, a, b,
    %Equal.sym(Cmp, Word.cmp(n, a, b), Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)), wcmp(n, a, b)) : {_ == EQ{} : Cmp}
    %e : {Nat.cmp(Word.to_nat(n, a), _) == EQ{} : Cmp}
    N.cmp_refl(Word.to_nat(n, a)))

# Increment, addition, subtraction
# ================================

# The carry out of Word.inc: set when every bit is set.
def incc(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          False{}
        case WCon{True{}, t}:
          incc(p, t)

law winc:
  for +n: Nat
  for +w: Word(n)
  {Nat.add(Word.to_nat(n, Word.inc(n, w)), Nat.mul(N.bn(incc(n, w)), Nat.pow(2n, n))) == 1n+Word.to_nat(n, w) : Nat}

def winc(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          %Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(p, t)), 0n), Nat.double(Word.to_nat(p, t)), N.add_zero(Nat.double(Word.to_nat(p, t)))) :
            {1n+_ == 1n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}
        case WCon{True{}, +t}:
          +i = Word.to_nat(p, Word.inc(p, t))
          +c = N.bn(incc(p, t))
          +pp = Nat.pow(2n, p)
          %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.double(pp), N.pow2s(p)) :
            {Nat.add(Nat.double(i), Nat.mul(c, _)) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          %Equal.sym(Nat, Nat.mul(c, Nat.double(pp)), Nat.double(Nat.mul(c, pp)), N.mul_dbl_r(c, pp)) :
            {Nat.add(Nat.double(i), _) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          %N.dbl_dist(i, Nat.mul(c, pp)) : {_ == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          %Equal.sym(Nat, Nat.add(i, Nat.mul(c, pp)), 1n+Word.to_nat(p, t), winc(p, t)) : {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}

# The carry out of Word.adc without inversion (f = False).
def cout(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{bb, bt}:
          cout(p, at, bt, Bool.and(bb, c))
        case WCon{True{}, at} WCon{bb, bt}:
          cout(p, at, bt, Bool.or(bb, c))

# One bit of the sum, as numbers.
law adc_step:
  for +p: Nat
  for +x: Nat
  for +y: Nat
  for +c: Nat
  for +s: Nat
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for +r: Nat
  for +co: Nat
  for +ih: {Nat.add(r, Nat.mul(co, Nat.pow(2n, p))) == Nat.add(k, Nat.add(a, b)) : Nat}
  for +bit: {Nat.add(s, Nat.double(k)) == Nat.add(c, Nat.add(x, y)) : Nat}
  {Nat.add(Nat.add(s, Nat.double(r)), Nat.mul(co, Nat.pow(2n, 1n+p)))
    == Nat.add(c, Nat.add(Nat.add(x, Nat.double(a)), Nat.add(y, Nat.double(b)))) : Nat}

def adc_step(p, x, y, c, s, k, a, b, r, co, ih, bit):
  +pp = Nat.pow(2n, p)
  +dr = Nat.double(r)
  +da = Nat.double(a)
  +db = Nat.double(b)
  +dk = Nat.double(k)
  +rhs = Nat.add(c, Nat.add(Nat.add(x, da), Nat.add(y, db)))
  %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.double(pp), N.pow2s(p)) :
    {Nat.add(Nat.add(s, dr), Nat.mul(co, _)) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(co, Nat.double(pp)), Nat.double(Nat.mul(co, pp)), N.mul_dbl_r(co, pp)) :
    {Nat.add(Nat.add(s, dr), _) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(s, dr), Nat.double(Nat.mul(co, pp))), Nat.add(s, Nat.add(dr, Nat.double(Nat.mul(co, pp)))),
      N.add_assoc(s, dr, Nat.double(Nat.mul(co, pp)))) :
    {_ == rhs : Nat}
  %N.dbl_dist(r, Nat.mul(co, pp)) : {Nat.add(s, _) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(r, Nat.mul(co, pp)), Nat.add(k, Nat.add(a, b)), ih) : {Nat.add(s, Nat.double(_)) == rhs : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(k, Nat.add(a, b))), Nat.add(dk, Nat.double(Nat.add(a, b))), N.dbl_dist(k, Nat.add(a, b))) :
    {Nat.add(s, _) == rhs : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(a, b)), Nat.add(da, db), N.dbl_dist(a, b)) :
    {Nat.add(s, Nat.add(dk, _)) == rhs : Nat}
  %N.add_assoc(s, dk, Nat.add(da, db)) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(s, dk), Nat.add(c, Nat.add(x, y)), bit) : {Nat.add(_, Nat.add(da, db)) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(c, Nat.add(x, y)), Nat.add(da, db)), Nat.add(c, Nat.add(Nat.add(x, y), Nat.add(da, db))),
      N.add_assoc(c, Nat.add(x, y), Nat.add(da, db))) :
    {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x, y), Nat.add(da, db)), Nat.add(Nat.add(x, da), Nat.add(y, db)), N.add_swap(x, y, da, db)) :
    {Nat.add(c, _) == rhs : Nat}
  {==}

# The sum with its carry out: r + co * 2^n = c + a + b.
law wadc:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.mul(N.bn(cout(n, a, b, c)), Nat.pow(2n, n)))
    == Nat.add(N.bn(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}

def wadc(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          adc_step(p, 0n, 0n, 0n, 0n, 0n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.bn(cout(p, at, bt, False{})), wadc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          adc_step(p, 0n, 0n, 1n, 1n, 0n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.bn(cout(p, at, bt, False{})), wadc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          adc_step(p, 0n, 1n, 0n, 1n, 0n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.bn(cout(p, at, bt, False{})), wadc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          adc_step(p, 0n, 1n, 1n, 0n, 1n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.bn(cout(p, at, bt, True{})), wadc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          adc_step(p, 1n, 0n, 0n, 1n, 0n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.bn(cout(p, at, bt, False{})), wadc(p, at, bt, False{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          adc_step(p, 1n, 0n, 1n, 0n, 1n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.bn(cout(p, at, bt, True{})), wadc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          adc_step(p, 1n, 1n, 0n, 0n, 1n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.bn(cout(p, at, bt, True{})), wadc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          adc_step(p, 1n, 1n, 1n, 1n, 1n, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.bn(cout(p, at, bt, True{})), wadc(p, at, bt, True{}), {==})

# Subtraction is addition of the complement with carry in.
def adc_t.con(-p: Nat, at: Word(p), bt: Word(p), sk: Bool & Bool,
  ih: @k: Bool -> {Word.adc(p, at, bt, True{}, k) == Word.adc(p, at, Word.not(p, bt), False{}, k) : Word(p)}) ->
  {Word.adc.con(p, at, bt, True{}, sk) == Word.adc.con(p, at, Word.not(p, bt), False{}, sk) : Word(1n+p)}:
  match sk:
    case (s, k):
      %ih(k) : {WCon{s, Word.adc(p, at, bt, True{}, k)} == WCon{s, _} : Word(1n+p)}
      {==}

law adc_t:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Word.adc(n, a, b, True{}, c) == Word.adc(n, a, Word.not(n, b), False{}, c) : Word(n)}

def adc_t(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          adc_t.con(p, at, bt, Bool.full_add(ab, Bool.not(bb), c), k => adc_t(p, at, bt, k))

# not w and w add up to 2^n - 1.
law wnot:
  for +n: Nat
  for +w: Word(n)
  {1n+Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)) == Nat.pow(2n, n) : Nat}

def wnot(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          +x = Word.to_nat(p, Word.not(p, t))
          +y = Word.to_nat(p, t)
          %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.double(Nat.pow(2n, p)), N.pow2s(p)) : {2n+Nat.add(Nat.double(x), Nat.double(y)) == _ : Nat}
          %wnot(p, t) : {2n+Nat.add(Nat.double(x), Nat.double(y)) == Nat.double(_) : Nat}
          %Equal.sym(Nat, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), N.dbl_dist(x, y)) :
            {2n+Nat.add(Nat.double(x), Nat.double(y)) == 2n+_ : Nat}
          {==}
        case WCon{True{}, +t}:
          +x = Word.to_nat(p, Word.not(p, t))
          +y = Word.to_nat(p, t)
          %Equal.sym(Nat, Nat.add(Nat.double(x), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(x), Nat.double(y)), N.add_succ(Nat.double(x), Nat.double(y))) :
            {1n+_ == Nat.pow(2n, 1n+p) : Nat}
          %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.double(Nat.pow(2n, p)), N.pow2s(p)) : {2n+Nat.add(Nat.double(x), Nat.double(y)) == _ : Nat}
          %wnot(p, t) : {2n+Nat.add(Nat.double(x), Nat.double(y)) == Nat.double(_) : Nat}
          %Equal.sym(Nat, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), N.dbl_dist(x, y)) :
            {2n+Nat.add(Nat.double(x), Nat.double(y)) == 2n+_ : Nat}
          {==}

# (a + 2^n) - b = 1 + a + not b.
law wsub_val:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Nat.sub(Nat.add(Word.to_nat(n, a), Nat.pow(2n, n)), Word.to_nat(n, b))
    == 1n+Nat.add(Word.to_nat(n, a), Word.to_nat(n, Word.not(n, b))) : Nat}

def wsub_val(n, a, b):
  +x = Word.to_nat(n, a)
  +y = Word.to_nat(n, b)
  +z = Word.to_nat(n, Word.not(n, b))
  %wnot(n, b) : {Nat.sub(Nat.add(x, _), y) == 1n+Nat.add(x, z) : Nat}
  %Equal.sym(Nat, Nat.add(x, 1n+Nat.add(z, y)), 1n+Nat.add(x, Nat.add(z, y)), N.add_succ(x, Nat.add(z, y))) :
    {Nat.sub(_, y) == 1n+Nat.add(x, z) : Nat}
  %N.add_assoc(x, z, y) : {Nat.sub(1n+_, y) == 1n+Nat.add(x, z) : Nat}
  N.sub_add(1n+Nat.add(x, z), y)

# Shifts
# ======

# The bit shifted out of the top by Word.shl.put.
def stop(n: Nat, c: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match w:
        case WCon{b, t}:
          stop(p, b, t)

law wput:
  for +n: Nat
  for +c: Bool
  for +w: Word(n)
  {Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), Nat.mul(N.bn(stop(n, c, w)), Nat.pow(2n, n)))
    == Nat.add(N.bn(c), Nat.double(Word.to_nat(n, w))) : Nat}

def wput(n, c, w):
  match n:
    case 0n:
      match c w:
        case False{} WNil{}:
          {==}
        case True{} WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          +s = Word.to_nat(p, Word.shl.put(p, b, t))
          +o = N.bn(stop(p, b, t))
          +pp = Nat.pow(2n, p)
          +rhs = Nat.add(N.bn(c), Nat.double(Word.to_nat(1n+p, WCon{b, t})))
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{c, Word.shl.put(p, b, t)}), Nat.add(N.bn(c), Nat.double(s)), wcon(p, c, Word.shl.put(p, b, t))) :
            {Nat.add(_, Nat.mul(o, Nat.pow(2n, 1n+p))) == rhs : Nat}
          %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.double(pp), N.pow2s(p)) :
            {Nat.add(Nat.add(N.bn(c), Nat.double(s)), Nat.mul(o, _)) == rhs : Nat}
          %Equal.sym(Nat, Nat.mul(o, Nat.double(pp)), Nat.double(Nat.mul(o, pp)), N.mul_dbl_r(o, pp)) :
            {Nat.add(Nat.add(N.bn(c), Nat.double(s)), _) == rhs : Nat}
          %Equal.sym(Nat, Nat.add(Nat.add(N.bn(c), Nat.double(s)), Nat.double(Nat.mul(o, pp))), Nat.add(N.bn(c), Nat.add(Nat.double(s), Nat.double(Nat.mul(o, pp)))),
              N.add_assoc(N.bn(c), Nat.double(s), Nat.double(Nat.mul(o, pp)))) :
            {_ == rhs : Nat}
          %N.dbl_dist(s, Nat.mul(o, pp)) : {Nat.add(N.bn(c), _) == rhs : Nat}
          %Equal.sym(Nat, Nat.add(s, Nat.mul(o, pp)), Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t))), wput(p, b, t)) :
            {Nat.add(N.bn(c), Nat.double(_)) == rhs : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b, t}), Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t))), wcon(p, b, t)) :
            {Nat.add(N.bn(c), Nat.double(Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t))))) == Nat.add(N.bn(c), Nat.double(_)) : Nat}
          {==}

# The bit shifted out of the top by Word.shl.
def shtop(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          stop(p, b, t)

law wshl:
  for +n: Nat
  for +w: Word(n)
  {Nat.add(Word.to_nat(n, Word.shl(n, w)), Nat.mul(N.bn(shtop(n, w)), Nat.pow(2n, n))) == Nat.double(Word.to_nat(n, w)) : Nat}

def wshl(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          +s = Word.to_nat(p, Word.shl.put(p, b, t))
          +o = N.bn(stop(p, b, t))
          +pp = Nat.pow(2n, p)
          +rhs = Nat.double(Word.to_nat(1n+p, WCon{b, t}))
          %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.double(pp), N.pow2s(p)) :
            {Nat.add(Nat.double(s), Nat.mul(o, _)) == rhs : Nat}
          %Equal.sym(Nat, Nat.mul(o, Nat.double(pp)), Nat.double(Nat.mul(o, pp)), N.mul_dbl_r(o, pp)) :
            {Nat.add(Nat.double(s), _) == rhs : Nat}
          %N.dbl_dist(s, Nat.mul(o, pp)) : {_ == rhs : Nat}
          %Equal.sym(Nat, Nat.add(s, Nat.mul(o, pp)), Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t))), wput(p, b, t)) :
            {Nat.double(_) == rhs : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b, t}), Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t))), wcon(p, b, t)) :
            {Nat.double(Nat.add(N.bn(b), Nat.double(Word.to_nat(p, t)))) == Nat.double(_) : Nat}
          {==}

law wshl_mod:
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(n, Word.shl(n, w)) == Nat.mod(Nat.double(Word.to_nat(n, w)), Nat.pow(2n, n)) : Nat}

def wshl_mod(n, w):
  Equal.sym(Nat, Nat.mod(Nat.double(Word.to_nat(n, w)), Nat.pow(2n, n)), Word.to_nat(n, Word.shl(n, w)),
    carry_mod(Word.to_nat(n, Word.shl(n, w)), N.bn(shtop(n, w)), Nat.pow(2n, n), Nat.double(Word.to_nat(n, w)),
      wshl(n, w), wlt(n, Word.shl(n, w))))

law wpad:
  for +p: Nat
  for +t: Word(p)
  {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat}

def wpad(p, t):
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{False{}, +u}:
          Equal.cong(Nat, Nat, x => Nat.double(x), Word.to_nat(1n+q, Word.shr.pad(q, u)), Word.to_nat(q, u), wpad(q, u))
        case WCon{True{}, +u}:
          Equal.cong(Nat, Nat, x => 1n+Nat.double(x), Word.to_nat(1n+q, Word.shr.pad(q, u)), Word.to_nat(q, u), wpad(q, u))

law wdiv2:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  {Nat.div(Word.to_nat(1n+p, WCon{b, t}), 2n) == Word.to_nat(p, t) : Nat}

def wdiv2(p, b, t):
  %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b, t}), Nat.add(Nat.mul(Word.to_nat(p, t), 2n), N.bn(b)), wcon2(p, b, t)) :
    {Nat.div(_, 2n) == Word.to_nat(p, t) : Nat}
  N.div_mul_add(Word.to_nat(p, t), 2n, N.bn(b), bn_lt2(b))

law wshr:
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(n, Word.shr(n, w)) == Nat.div(Word.to_nat(n, w), 2n) : Nat}

def wshr(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Nat, Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), Nat.div(Word.to_nat(1n+p, WCon{b, t}), 2n),
            wpad(p, t), Equal.sym(Nat, Nat.div(Word.to_nat(1n+p, WCon{b, t}), 2n), Word.to_nat(p, t), wdiv2(p, b, t)))

# Addition and multiplication modulo 2^n
# ======================================

law wadd_mod:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.mod(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n)) : Nat}

def wadd_mod(n, a, b):
  +r = Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))
  Equal.sym(Nat, Nat.mod(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n)), r,
    carry_mod(r, N.bn(cout(n, a, b, False{})), Nat.pow(2n, n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)),
      wadc(n, a, b, False{}), wlt(n, Word.adc(n, a, b, False{}, False{}))))

law modmulin:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +m: Nat
  {Nat.mod(Nat.add(x, Nat.mul(y, Nat.mod(z, m))), m) == Nat.mod(Nat.add(x, Nat.mul(y, z)), m) : Nat}

def modmulin(x, y, z, m):
  %N.mod_add_mod_r(x, Nat.mul(y, Nat.mod(z, m)), m) : {_ == Nat.mod(Nat.add(x, Nat.mul(y, z)), m) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.mul(y, Nat.mod(z, m)), m), Nat.mod(Nat.mul(y, z), m), N.mod_mul_mod_r(y, z, m)) :
    {Nat.mod(Nat.add(x, _), m) == Nat.mod(Nat.add(x, Nat.mul(y, z)), m) : Nat}
  N.mod_add_mod_r(x, Nat.mul(y, z), m)

law wmul_go:
  for +n: Nat
  for +m: Nat
  for +a: Word(m)
  for +b: Word(n)
  for +acc: Word(n)
  {Word.to_nat(n, Word.mul.go(n, m, a, b, acc))
    == Nat.mod(Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(m, a), Word.to_nat(n, b))), Nat.pow(2n, n)) : Nat}

def wmul_go(n, m, a, b, acc):
  match m:
    case 0n:
      match a:
        case WNil{}:
          +c = Word.to_nat(n, acc)
          %Equal.sym(Nat, Nat.add(c, 0n), c, N.add_zero(c)) : {c == Nat.mod(_, Nat.pow(2n, n)) : Nat}
          Equal.sym(Nat, Nat.mod(c, Nat.pow(2n, n)), c, N.mod_small(c, Nat.pow(2n, n), wlt(n, acc)))
    case 1n+mp:
      match a:
        case WCon{False{}, +at}:
          +c = Word.to_nat(n, acc)
          +x = Word.to_nat(mp, at)
          +y = Word.to_nat(n, b)
          +pn = Nat.pow(2n, n)
          +rhs = Nat.mod(Nat.add(c, Nat.mul(Nat.double(x), y)), pn)
          Equal.trans(Nat, Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)),
            Nat.mod(Nat.add(c, Nat.mul(x, Word.to_nat(n, Word.shl(n, b)))), pn), rhs,
            wmul_go(n, mp, at, Word.shl(n, b), acc),
            %Equal.sym(Nat, Word.to_nat(n, Word.shl(n, b)), Nat.mod(Nat.double(y), pn), wshl_mod(n, b)) :
              {Nat.mod(Nat.add(c, Nat.mul(x, _)), pn) == rhs : Nat}
            %Equal.sym(Nat, Nat.mod(Nat.add(c, Nat.mul(x, Nat.mod(Nat.double(y), pn))), pn), Nat.mod(Nat.add(c, Nat.mul(x, Nat.double(y))), pn),
                modmulin(c, x, Nat.double(y), pn)) :
              {_ == rhs : Nat}
            %Equal.sym(Nat, Nat.mul(x, Nat.double(y)), Nat.double(Nat.mul(x, y)), N.mul_dbl_r(x, y)) :
              {Nat.mod(Nat.add(c, _), pn) == rhs : Nat}
            %Equal.sym(Nat, Nat.mul(Nat.double(x), y), Nat.double(Nat.mul(x, y)), N.mul_dbl_l(x, y)) :
              {Nat.mod(Nat.add(c, Nat.double(Nat.mul(x, y))), pn) == Nat.mod(Nat.add(c, _), pn) : Nat}
            {==})
        case WCon{True{}, +at}:
          +c = Word.to_nat(n, acc)
          +x = Word.to_nat(mp, at)
          +y = Word.to_nat(n, b)
          +pn = Nat.pow(2n, n)
          +rhs = Nat.mod(Nat.add(c, Nat.add(y, Nat.mul(Nat.double(x), y))), pn)
          Equal.trans(Nat, Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))),
            Nat.mod(Nat.add(Word.to_nat(n, Word.add(n, acc, b)), Nat.mul(x, Word.to_nat(n, Word.shl(n, b)))), pn), rhs,
            wmul_go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)),
            %Equal.sym(Nat, Word.to_nat(n, Word.add(n, acc, b)), Nat.mod(Nat.add(c, y), pn), wadd_mod(n, acc, b)) :
              {Nat.mod(Nat.add(_, Nat.mul(x, Word.to_nat(n, Word.shl(n, b)))), pn) == rhs : Nat}
            %Equal.sym(Nat, Word.to_nat(n, Word.shl(n, b)), Nat.mod(Nat.double(y), pn), wshl_mod(n, b)) :
              {Nat.mod(Nat.add(Nat.mod(Nat.add(c, y), pn), Nat.mul(x, _)), pn) == rhs : Nat}
            %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(c, y), pn), Nat.mul(x, Nat.mod(Nat.double(y), pn))), pn),
                Nat.mod(Nat.add(Nat.add(c, y), Nat.mul(x, Nat.mod(Nat.double(y), pn))), pn),
                N.mod_add_mod_l(Nat.add(c, y), Nat.mul(x, Nat.mod(Nat.double(y), pn)), pn)) :
              {_ == rhs : Nat}
            %Equal.sym(Nat, Nat.mod(Nat.add(Nat.add(c, y), Nat.mul(x, Nat.mod(Nat.double(y), pn))), pn), Nat.mod(Nat.add(Nat.add(c, y), Nat.mul(x, Nat.double(y))), pn),
                modmulin(Nat.add(c, y), x, Nat.double(y), pn)) :
              {_ == rhs : Nat}
            %Equal.sym(Nat, Nat.mul(x, Nat.double(y)), Nat.double(Nat.mul(x, y)), N.mul_dbl_r(x, y)) :
              {Nat.mod(Nat.add(Nat.add(c, y), _), pn) == rhs : Nat}
            %Equal.sym(Nat, Nat.mul(Nat.double(x), y), Nat.double(Nat.mul(x, y)), N.mul_dbl_l(x, y)) :
              {Nat.mod(Nat.add(Nat.add(c, y), Nat.double(Nat.mul(x, y))), pn) == Nat.mod(Nat.add(c, Nat.add(y, _)), pn) : Nat}
            %Equal.sym(Nat, Nat.add(Nat.add(c, y), Nat.double(Nat.mul(x, y))), Nat.add(c, Nat.add(y, Nat.double(Nat.mul(x, y)))),
                N.add_assoc(c, y, Nat.double(Nat.mul(x, y)))) :
              {Nat.mod(_, pn) == Nat.mod(Nat.add(c, Nat.add(y, Nat.double(Nat.mul(x, y)))), pn) : Nat}
            {==})

# Bits
# ====

# Bit k of a word (False from n up).
def wbit(n: Nat, w: Word(n), k: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              b
            case 1n+j:
              wbit(p, t, j)

law is_eq_bn:
  for +b: Bool
  {Nat.is_eq(N.bn(b), 1n) == b : Bool}

def is_eq_bn(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# The numeric bit (as in D.bit) is the word's bit.
law wbit_num:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  {Nat.is_eq(Nat.mod(Nat.div(Word.to_nat(n, w), Nat.pow(2n, k)), 2n), 1n) == wbit(n, w, k) : Bool}

def wbit_num(n, w, k):
  match n:
    case 0n:
      match w:
        case WNil{}:
          %Equal.sym(Nat, Nat.div(0n, Nat.pow(2n, k)), 0n, N.div_zero_l(Nat.pow(2n, k))) :
            {Nat.is_eq(Nat.mod(_, 2n), 1n) == False{} : Bool}
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match k:
            case 0n:
              +x = Word.to_nat(1n+p, WCon{b, t})
              %Equal.sym(Nat, Nat.div(x, 1n), x, N.div_one(x)) : {Nat.is_eq(Nat.mod(_, 2n), 1n) == b : Bool}
              %Equal.sym(Nat, x, Nat.add(Nat.mul(Word.to_nat(p, t), 2n), N.bn(b)), wcon2(p, b, t)) : {Nat.is_eq(Nat.mod(_, 2n), 1n) == b : Bool}
              %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(Word.to_nat(p, t), 2n), N.bn(b)), 2n), N.bn(b), N.mod_mul_add(Word.to_nat(p, t), 2n, N.bn(b), bn_lt2(b))) :
                {Nat.is_eq(_, 1n) == b : Bool}
              is_eq_bn(b)
            case 1n+j:
              +x = Word.to_nat(1n+p, WCon{b, t})
              %N.div_div(x, 2n, Nat.pow(2n, j)) : {Nat.is_eq(Nat.mod(_, 2n), 1n) == wbit(p, t, j) : Bool}
              %Equal.sym(Nat, Nat.div(x, 2n), Word.to_nat(p, t), wdiv2(p, b, t)) :
                {Nat.is_eq(Nat.mod(Nat.div(_, Nat.pow(2n, j)), 2n), 1n) == wbit(p, t, j) : Bool}
              wbit_num(p, t, j)

law wbit_and:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  {wbit(n, Word.and(n, a, b), k) == Bool.and(wbit(n, a, k), wbit(n, b, k)) : Bool}

def wbit_and(n, a, b, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              wbit_and(p, at, bt, j)

law wbit_or:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  {wbit(n, Word.or(n, a, b), k) == Bool.or(wbit(n, a, k), wbit(n, b, k)) : Bool}

def wbit_or(n, a, b, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              wbit_or(p, at, bt, j)

law wbit_xor:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  {wbit(n, Word.xor(n, a, b), k) == Bool.xor(wbit(n, a, k), wbit(n, b, k)) : Bool}

def wbit_xor(n, a, b, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              wbit_xor(p, at, bt, j)

law wbit_not:
  for +n: Nat
  for +a: Word(n)
  for +k: Nat
  {wbit(n, Word.not(n, a), k) == Bool.and(Nat.is_lt(k, n), Bool.not(wbit(n, a, k))) : Bool}

def wbit_not(n, a, k):
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+p:
      match a:
        case WCon{+x, +at}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              wbit_not(p, at, j)

# The lowest bit where two words differ (0 if they are equal).
def wdiff(n: Nat, a: Word(n), b: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          1n+wdiff(p, at, bt)
        case WCon{False{}, at} WCon{True{}, bt}:
          0n
        case WCon{True{}, at} WCon{False{}, bt}:
          0n
        case WCon{True{}, at} WCon{True{}, bt}:
          1n+wdiff(p, at, bt)

# Two words with the same bit where they would first differ are equal.
law wext:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {wbit(n, a, wdiff(n, a, b)) == wbit(n, b, wdiff(n, a, b)) : Bool}
  {a == b : Word(n)}

def wext(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %wext(p, at, bt, e) : {WCon{False{}, at} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)}, N.false_ne_true(e))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)}, N.true_ne_false(e))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %wext(p, at, bt, e) : {WCon{True{}, at} == WCon{True{}, _} : Word(1n+p)}
          {==}

# Masks and disjoint words
# ========================

law moddbl_w:
  for +p: Nat
  for +x: Bool
  for +t: Word(p)
  for +j: Nat
  {Nat.mod(Word.to_nat(1n+p, WCon{x, t}), Nat.pow(2n, 1n+j)) == Nat.add(N.bn(x), Nat.double(Nat.mod(Word.to_nat(p, t), Nat.pow(2n, j)))) : Nat}

def moddbl_w(p, x, t, j):
  %Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, t}), Nat.add(N.bn(x), Nat.double(Word.to_nat(p, t))), wcon(p, x, t)) :
    {Nat.mod(_, Nat.pow(2n, 1n+j)) == Nat.add(N.bn(x), Nat.double(Nat.mod(Word.to_nat(p, t), Nat.pow(2n, j)))) : Nat}
  %Equal.sym(Nat, Nat.pow(2n, 1n+j), Nat.double(Nat.pow(2n, j)), N.pow2s(j)) :
    {Nat.mod(Nat.add(N.bn(x), Nat.double(Word.to_nat(p, t))), _) == Nat.add(N.bn(x), Nat.double(Nat.mod(Word.to_nat(p, t), Nat.pow(2n, j)))) : Nat}
  moddbl(x, Word.to_nat(p, t), Nat.pow(2n, j), N.pow_pos(j))

law lt_w:
  for +p: Nat
  for +y: Bool
  for +t: Word(p)
  for +j: Nat
  for +h: {Nat.is_lt(Word.to_nat(1n+p, WCon{y, t}), Nat.pow(2n, 1n+j)) == True{} : Bool}
  {Nat.is_lt(Word.to_nat(p, t), Nat.pow(2n, j)) == True{} : Bool}

def lt_w(p, y, t, j, h):
  lt_dbl_inv(Word.to_nat(p, t), Nat.pow(2n, j), y,
    %wcon(p, y, t) : {Nat.is_lt(_, Nat.double(Nat.pow(2n, j))) == True{} : Bool}
    %N.pow2s(j) : {Nat.is_lt(Word.to_nat(1n+p, WCon{y, t}), _) == True{} : Bool}
    h)

law mask_step:
  for +p: Nat
  for +x: Bool
  for +t: Word(p)
  for +j: Nat
  for +r: Nat
  for +ih: {r == Nat.mod(Word.to_nat(p, t), Nat.pow(2n, j)) : Nat}
  {Nat.add(N.bn(x), Nat.double(r)) == Nat.mod(Word.to_nat(1n+p, WCon{x, t}), Nat.pow(2n, 1n+j)) : Nat}

def mask_step(p, x, t, j, r, ih):
  %Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{x, t}), Nat.pow(2n, 1n+j)), Nat.add(N.bn(x), Nat.double(Nat.mod(Word.to_nat(p, t), Nat.pow(2n, j)))), moddbl_w(p, x, t, j)) :
    {Nat.add(N.bn(x), Nat.double(r)) == _ : Nat}
  %ih : {Nat.add(N.bn(x), Nat.double(r)) == Nat.add(N.bn(x), Nat.double(_)) : Nat}
  {==}

# And with a word standing for 2^k - 1 keeps the low k bits.
law and_mask:
  for +n: Nat
  for +a: Word(n)
  for +m: Word(n)
  for +k: Nat
  for +h: {Word.to_nat(n, m) == Nat.sub(Nat.pow(2n, k), 1n) : Nat}
  {Word.to_nat(n, Word.and(n, a, m)) == Nat.mod(Word.to_nat(n, a), Nat.pow(2n, k)) : Nat}

def and_mask(n, a, m, k, h):
  match n:
    case 0n:
      match a m:
        case WNil{} WNil{}:
          Equal.sym(Nat, Nat.mod(0n, Nat.pow(2n, k)), 0n, N.mod_zero_l(Nat.pow(2n, k)))
    case 1n+p:
      match a m k:
        case WCon{+x, +at} WCon{False{}, +mt} 0n:
          +ih = and_mask(p, at, mt, 0n, N.dbl_zero(Word.to_nat(p, mt), h))
          +r = Word.to_nat(p, Word.and(p, at, mt))
          %Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{x, at}), 1n), 0n, N.mod_one(Word.to_nat(1n+p, WCon{x, at}))) :
            {Word.to_nat(1n+p, WCon{Bool.and(x, False{}), Word.and(p, at, mt)}) == _ : Nat}
          %Equal.sym(Bool, Bool.and(x, False{}), False{}, N.and_false_r(x)) :
            {Word.to_nat(1n+p, WCon{_, Word.and(p, at, mt)}) == 0n : Nat}
          %Equal.sym(Nat, r, Nat.mod(Word.to_nat(p, at), 1n), ih) : {Nat.double(_) == 0n : Nat}
          %Equal.sym(Nat, Nat.mod(Word.to_nat(p, at), 1n), 0n, N.mod_one(Word.to_nat(p, at))) : {Nat.double(_) == 0n : Nat}
          {==}
        case WCon{+x, +at} WCon{True{}, +mt} 0n:
          Empty.absurd({Word.to_nat(1n+p, WCon{Bool.and(x, True{}), Word.and(p, at, mt)}) == Nat.mod(Word.to_nat(1n+p, WCon{x, at}), 1n) : Nat},
            N.succ_ne_zero(Nat.double(Word.to_nat(p, mt)), h))
        case WCon{+x, +at} WCon{False{}, +mt} 1n+j:
          Empty.absurd({Word.to_nat(1n+p, WCon{Bool.and(x, False{}), Word.and(p, at, mt)}) == Nat.mod(Word.to_nat(1n+p, WCon{x, at}), Nat.pow(2n, 1n+j)) : Nat},
            N.dbl_ne_odd(Word.to_nat(p, mt), Nat.sub(Nat.pow(2n, j), 1n),
              Equal.trans(Nat, Nat.double(Word.to_nat(p, mt)), Nat.sub(Nat.pow(2n, 1n+j), 1n), 1n+Nat.double(Nat.sub(Nat.pow(2n, j), 1n)), h, N.pow_sub1(j))))
        case WCon{+x, +at} WCon{True{}, +mt} 1n+j:
          +hm = N.dbl_inj(Word.to_nat(p, mt), Nat.sub(Nat.pow(2n, j), 1n),
            N.succ_inj(Nat.double(Word.to_nat(p, mt)), Nat.double(Nat.sub(Nat.pow(2n, j), 1n)),
              Equal.trans(Nat, 1n+Nat.double(Word.to_nat(p, mt)), Nat.sub(Nat.pow(2n, 1n+j), 1n), 1n+Nat.double(Nat.sub(Nat.pow(2n, j), 1n)), h, N.pow_sub1(j))))
          %Equal.sym(Bool, Bool.and(x, True{}), x, N.and_true_r_id(x)) :
            {Word.to_nat(1n+p, WCon{_, Word.and(p, at, mt)}) == Nat.mod(Word.to_nat(1n+p, WCon{x, at}), Nat.pow(2n, 1n+j)) : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, Word.and(p, at, mt)}), Nat.add(N.bn(x), Nat.double(Word.to_nat(p, Word.and(p, at, mt)))), wcon(p, x, Word.and(p, at, mt))) :
            {_ == Nat.mod(Word.to_nat(1n+p, WCon{x, at}), Nat.pow(2n, 1n+j)) : Nat}
          mask_step(p, x, at, j, Word.to_nat(p, Word.and(p, at, mt)), and_mask(p, at, mt, j, hm))

# x < 1 gives x = 0.
law lt_one:
  for +x: Nat
  for +h: {Nat.is_lt(x, 1n) == True{} : Bool}
  {x == 0n : Nat}

def lt_one(x, h):
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, N.lt_zero(p)), h)))

law or_zero:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +h: {Word.to_nat(n, b) == 0n : Nat}
  {Word.to_nat(n, Word.or(n, a, b)) == Word.to_nat(n, a) : Nat}

def or_zero(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(p, Word.or(p, at, bt)), Word.to_nat(p, at), or_zero(p, at, bt, N.dbl_zero(Word.to_nat(p, bt), h)))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Word.to_nat(p, Word.or(p, at, bt)), Word.to_nat(p, at), or_zero(p, at, bt, N.dbl_zero(Word.to_nat(p, bt), h)))
        case WCon{+x, +at} WCon{True{}, +bt}:
          Empty.absurd({Word.to_nat(1n+p, Word.or(1n+p, WCon{x, at}, WCon{True{}, bt})) == Word.to_nat(1n+p, WCon{x, at}) : Nat},
            N.succ_ne_zero(Nat.double(Word.to_nat(p, bt)), h))

law xor_zero:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +h: {Word.to_nat(n, b) == 0n : Nat}
  {Word.to_nat(n, Word.xor(n, a, b)) == Word.to_nat(n, a) : Nat}

def xor_zero(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(p, Word.xor(p, at, bt)), Word.to_nat(p, at), xor_zero(p, at, bt, N.dbl_zero(Word.to_nat(p, bt), h)))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Word.to_nat(p, Word.xor(p, at, bt)), Word.to_nat(p, at), xor_zero(p, at, bt, N.dbl_zero(Word.to_nat(p, bt), h)))
        case WCon{+x, +at} WCon{True{}, +bt}:
          Empty.absurd({Word.to_nat(1n+p, Word.xor(1n+p, WCon{x, at}, WCon{True{}, bt})) == Word.to_nat(1n+p, WCon{x, at}) : Nat},
            N.succ_ne_zero(Nat.double(Word.to_nat(p, bt)), h))

# y + 2r = 2a + (y + 2b) when r = a + b.
law split_step:
  for +y: Bool
  for +a: Nat
  for +b: Nat
  for +r: Nat
  for +ih: {r == Nat.add(a, b) : Nat}
  {Nat.add(N.bn(y), Nat.double(r)) == Nat.add(Nat.double(a), Nat.add(N.bn(y), Nat.double(b))) : Nat}

def split_step(y, a, b, r, ih):
  %Equal.sym(Nat, r, Nat.add(a, b), ih) : {Nat.add(N.bn(y), Nat.double(_)) == Nat.add(Nat.double(a), Nat.add(N.bn(y), Nat.double(b))) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(a, b)), Nat.add(Nat.double(a), Nat.double(b)), N.dbl_dist(a, b)) :
    {Nat.add(N.bn(y), _) == Nat.add(Nat.double(a), Nat.add(N.bn(y), Nat.double(b))) : Nat}
  N.add_left_comm(N.bn(y), Nat.double(a), Nat.double(b))

def or_split.s(+p: Nat, +x: Bool, +y: Bool, +at: Word(p), +bt: Word(p), +j: Nat,
  ha: {Nat.mod(Word.to_nat(1n+p, WCon{x, at}), Nat.pow(2n, 1n+j)) == 0n : Nat},
  hb: {Nat.is_lt(Word.to_nat(1n+p, WCon{y, bt}), Nat.pow(2n, 1n+j)) == True{} : Bool},
  ih: {Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j)) == 0n : Nat} -> {Nat.is_lt(Word.to_nat(p, bt), Nat.pow(2n, j)) == True{} : Bool} ->
    {Word.to_nat(p, Word.or(p, at, bt)) == Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)) : Nat}) ->
  {Word.to_nat(1n+p, Word.or(1n+p, WCon{x, at}, WCon{y, bt})) == Nat.add(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})) : Nat}:
  match x y:
    case True{} _:
      Empty.absurd({Word.to_nat(1n+p, Word.or(1n+p, WCon{True{}, at}, WCon{y, bt})) == Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{y, bt})) : Nat},
        N.succ_ne_zero(Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))),
          Equal.trans(Nat, 1n+Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), Nat.mod(Word.to_nat(1n+p, WCon{True{}, at}), Nat.pow(2n, 1n+j)), 0n,
            Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{True{}, at}), Nat.pow(2n, 1n+j)), 1n+Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), moddbl_w(p, True{}, at, j)),
            ha)))
    case False{} False{}:
      split_step(False{}, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.or(p, at, bt)),
        ih(N.dbl_zero(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j)),
          Equal.trans(Nat, Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), 0n,
            Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), moddbl_w(p, False{}, at, j)),
            ha)))(lt_w(p, False{}, bt, j, hb)))
    case False{} True{}:
      split_step(True{}, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.or(p, at, bt)),
        ih(N.dbl_zero(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j)),
          Equal.trans(Nat, Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), 0n,
            Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), moddbl_w(p, False{}, at, j)),
            ha)))(lt_w(p, True{}, bt, j, hb)))

# Or of a word with only bits from k up and a word below 2^k is their sum.
law or_split:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  for +ha: {Nat.mod(Word.to_nat(n, a), Nat.pow(2n, k)) == 0n : Nat}
  for +hb: {Nat.is_lt(Word.to_nat(n, b), Nat.pow(2n, k)) == True{} : Bool}
  {Word.to_nat(n, Word.or(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

def or_split(n, a, b, k, ha, hb):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b k:
        case WCon{+x, +at} WCon{+y, +bt} 0n:
          +ea = Word.to_nat(1n+p, WCon{x, at})
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), 0n, lt_one(Word.to_nat(1n+p, WCon{y, bt}), hb)) : {Word.to_nat(1n+p, Word.or(1n+p, WCon{x, at}, WCon{y, bt})) == Nat.add(ea, _) : Nat}
          %Equal.sym(Nat, Nat.add(ea, 0n), ea, N.add_zero(ea)) : {Word.to_nat(1n+p, Word.or(1n+p, WCon{x, at}, WCon{y, bt})) == _ : Nat}
          or_zero(1n+p, WCon{x, at}, WCon{y, bt}, lt_one(Word.to_nat(1n+p, WCon{y, bt}), hb))
        case WCon{+x, +at} WCon{+y, +bt} 1n+j:
          or_split.s(p, x, y, at, bt, j, ha, hb, ha2 => hb2 => or_split(p, at, bt, j, ha2, hb2))

def xor_split.s(+p: Nat, +x: Bool, +y: Bool, +at: Word(p), +bt: Word(p), +j: Nat,
  ha: {Nat.mod(Word.to_nat(1n+p, WCon{x, at}), Nat.pow(2n, 1n+j)) == 0n : Nat},
  hb: {Nat.is_lt(Word.to_nat(1n+p, WCon{y, bt}), Nat.pow(2n, 1n+j)) == True{} : Bool},
  ih: {Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j)) == 0n : Nat} -> {Nat.is_lt(Word.to_nat(p, bt), Nat.pow(2n, j)) == True{} : Bool} ->
    {Word.to_nat(p, Word.xor(p, at, bt)) == Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)) : Nat}) ->
  {Word.to_nat(1n+p, Word.xor(1n+p, WCon{x, at}, WCon{y, bt})) == Nat.add(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})) : Nat}:
  match x y:
    case True{} _:
      Empty.absurd({Word.to_nat(1n+p, Word.xor(1n+p, WCon{True{}, at}, WCon{y, bt})) == Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{y, bt})) : Nat},
        N.succ_ne_zero(Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))),
          Equal.trans(Nat, 1n+Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), Nat.mod(Word.to_nat(1n+p, WCon{True{}, at}), Nat.pow(2n, 1n+j)), 0n,
            Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{True{}, at}), Nat.pow(2n, 1n+j)), 1n+Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), moddbl_w(p, True{}, at, j)),
            ha)))
    case False{} False{}:
      split_step(False{}, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.xor(p, at, bt)),
        ih(N.dbl_zero(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j)),
          Equal.trans(Nat, Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), 0n,
            Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), moddbl_w(p, False{}, at, j)),
            ha)))(lt_w(p, False{}, bt, j, hb)))
    case False{} True{}:
      split_step(True{}, Word.to_nat(p, at), Word.to_nat(p, bt), Word.to_nat(p, Word.xor(p, at, bt)),
        ih(N.dbl_zero(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j)),
          Equal.trans(Nat, Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), 0n,
            Equal.sym(Nat, Nat.mod(Word.to_nat(1n+p, WCon{False{}, at}), Nat.pow(2n, 1n+j)), Nat.double(Nat.mod(Word.to_nat(p, at), Nat.pow(2n, j))), moddbl_w(p, False{}, at, j)),
            ha)))(lt_w(p, True{}, bt, j, hb)))

# Xor likewise.
law xor_split:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  for +ha: {Nat.mod(Word.to_nat(n, a), Nat.pow(2n, k)) == 0n : Nat}
  for +hb: {Nat.is_lt(Word.to_nat(n, b), Nat.pow(2n, k)) == True{} : Bool}
  {Word.to_nat(n, Word.xor(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

def xor_split(n, a, b, k, ha, hb):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b k:
        case WCon{+x, +at} WCon{+y, +bt} 0n:
          +ea = Word.to_nat(1n+p, WCon{x, at})
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), 0n, lt_one(Word.to_nat(1n+p, WCon{y, bt}), hb)) : {Word.to_nat(1n+p, Word.xor(1n+p, WCon{x, at}, WCon{y, bt})) == Nat.add(ea, _) : Nat}
          %Equal.sym(Nat, Nat.add(ea, 0n), ea, N.add_zero(ea)) : {Word.to_nat(1n+p, Word.xor(1n+p, WCon{x, at}, WCon{y, bt})) == _ : Nat}
          xor_zero(1n+p, WCon{x, at}, WCon{y, bt}, lt_one(Word.to_nat(1n+p, WCon{y, bt}), hb))
        case WCon{+x, +at} WCon{+y, +bt} 1n+j:
          xor_split.s(p, x, y, at, bt, j, ha, hb, ha2 => hb2 => xor_split(p, at, bt, j, ha2, hb2))
