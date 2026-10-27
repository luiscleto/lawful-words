import Base

# Facts about Bool and Nat used by the other proof files. Every variable is
# reusable (+), so the lemmas can be used inside each other's proofs. Some are
# copied from ../framebender/proof_base.bend (same author, MIT).

# Bool
# ====

def Bool.disc_ft(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law false_ne_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_ne_true(e):
  %e : Bool.disc_ft(_)
  Unit{}

law true_ne_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_ne_false(e):
  false_ne_true(Equal.sym(Bool, True{}, False{}, e))

law and_true_r_id:
  for +a: Bool
  {Bool.and(a, True{}) == a : Bool}

def and_true_r_id(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law and_false_r:
  for +a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false_r(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law or_false_r:
  for +a: Bool
  {Bool.or(a, False{}) == a : Bool}

def or_false_r(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law and_true_l:
  for +a: Bool
  for +b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_true_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(e))

law and_true_r:
  for +a: Bool
  for +b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_true_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(e))

# A Bool as a number: 0 or 1.
def bn(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# Nat: equality
# =============

def Nat.disc_z(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

law succ_ne_zero:
  for -n: Nat
  for e: {1n+n == 0n : Nat}
  Empty

def succ_ne_zero(n, e):
  %e : Nat.disc_z(_)
  Unit{}

law zero_ne_succ:
  for -n: Nat
  for e: {0n == 1n+n : Nat}
  Empty

def zero_ne_succ(n, e):
  succ_ne_zero(n, Equal.sym(Nat, 0n, 1n+n, e))

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

law succ_inj:
  for +a: Nat
  for +b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  Equal.cong(Nat, Nat, n => pred(n), 1n+a, 1n+b, e)

law eq_refl:
  for +n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def eq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

law cmp_refl:
  for +n: Nat
  {Nat.cmp(n, n) == EQ{} : Cmp}

def cmp_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_refl(p)

law eq_sound:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def eq_sound(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, false_ne_true(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, false_ne_true(e))
    case 1n+p 1n+q:
      %eq_sound(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# Nat: addition
# =============

law add_zero:
  for +n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law add_one:
  for +n: Nat
  {Nat.add(n, 1n) == 1n+n : Nat}

def add_one(n):
  %add_zero(n) : {Nat.add(n, 1n) == 1n+_ : Nat}
  add_succ(n, 0n)

law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), add_comm(p, b)) :
        {1n+_ == Nat.add(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p))

law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

law add_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_left_comm(a, b, c):
  %add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), add_comm(a, b)) :
    {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  add_assoc(b, a, c)

law add_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def add_swap(a, b, c, d):
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), add_assoc(a, b, Nat.add(c, d))) :
    {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), add_assoc(a, c, Nat.add(b, d))) :
    {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %Equal.sym(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), add_left_comm(b, c, d)) :
    {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  {==}

# a + x = a + y gives x = y.
law add_cancel_l:
  for +a: Nat
  for +x: Nat
  for +y: Nat
  for e: {Nat.add(a, x) == Nat.add(a, y) : Nat}
  {x == y : Nat}

def add_cancel_l(a, x, y, e):
  match a:
    case 0n:
      e
    case 1n+p:
      add_cancel_l(p, x, y, succ_inj(Nat.add(p, x), Nat.add(p, y), e))

# x + a = y + a gives x = y.
law add_cancel_r:
  for +a: Nat
  for +x: Nat
  for +y: Nat
  for e: {Nat.add(x, a) == Nat.add(y, a) : Nat}
  {x == y : Nat}

def add_cancel_r(a, x, y, e):
  add_cancel_l(a, x, y,
    %add_comm(x, a) : {_ == Nat.add(a, y) : Nat}
    %add_comm(y, a) : {Nat.add(x, a) == _ : Nat}
    e)

# x + y = x gives y = 0.
law add_self_r:
  for +x: Nat
  for +y: Nat
  for e: {Nat.add(x, y) == x : Nat}
  {y == 0n : Nat}

def add_self_r(x, y, e):
  add_cancel_l(x, y, 0n,
    %Equal.sym(Nat, Nat.add(x, 0n), x, add_zero(x)) : {Nat.add(x, y) == _ : Nat}
    e)

# x + y = 0 gives x = 0 (and y = 0).
law add_eq_zero_l:
  for +x: Nat
  for +y: Nat
  for e: {Nat.add(x, y) == 0n : Nat}
  {x == 0n : Nat}

def add_eq_zero_l(x, y, e):
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, succ_ne_zero(Nat.add(p, y), e))

law add_eq_zero_r:
  for +x: Nat
  for +y: Nat
  for e: {Nat.add(x, y) == 0n : Nat}
  {y == 0n : Nat}

def add_eq_zero_r(x, y, e):
  match x:
    case 0n:
      e
    case 1n+p:
      Empty.absurd({y == 0n : Nat}, succ_ne_zero(Nat.add(p, y), e))

# Nat: subtraction
# ================

law sub_zero:
  for +i: Nat
  {Nat.sub(i, 0n) == i : Nat}

def sub_zero(i):
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}

# (x + y) - y = x.
law sub_add:
  for +x: Nat
  for +y: Nat
  {Nat.sub(Nat.add(x, y), y) == x : Nat}

def sub_add(x, y):
  match y:
    case 0n:
      %Equal.sym(Nat, Nat.add(x, 0n), x, add_zero(x)) : {Nat.sub(_, 0n) == x : Nat}
      sub_zero(x)
    case 1n+q:
      %Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), add_succ(x, q)) :
        {Nat.sub(_, 1n+q) == x : Nat}
      sub_add(x, q)

# (y + x) - y = x.
law sub_add_l:
  for +y: Nat
  for +x: Nat
  {Nat.sub(Nat.add(y, x), y) == x : Nat}

def sub_add_l(y, x):
  %add_comm(x, y) : {Nat.sub(_, y) == x : Nat}
  sub_add(x, y)

# Nat: multiplication
# ===================

law mul_zero_r:
  for +a: Nat
  {Nat.mul(a, 0n) == 0n : Nat}

def mul_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero_r(p)

law mul_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}

def mul_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +x = Nat.mul(p, b)
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, x), mul_succ_r(p, b)) :
        {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, x)) : Nat}
      %Equal.sym(Nat, Nat.add(b, Nat.add(p, x)), Nat.add(p, Nat.add(b, x)), add_left_comm(b, p, x)) :
        {1n+_ == 1n+Nat.add(p, Nat.add(b, x)) : Nat}
      {==}

law mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

def mul_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, mul_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, b), Nat.mul(b, p), mul_comm(p, b)) :
        {Nat.add(b, _) == Nat.mul(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), mul_succ_r(b, p))

law mul_one:
  for +a: Nat
  {Nat.mul(a, 1n) == a : Nat}

def mul_one(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_one(p) : {1n+Nat.mul(p, 1n) == 1n+_ : Nat}
      {==}

law mul_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}

def mul_add(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, Nat.add(b, c)), Nat.add(Nat.mul(p, b), Nat.mul(p, c)), mul_add(p, b, c)) : {Nat.add(Nat.add(b, c), _) == Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))) : Nat}
      add_swap(b, c, Nat.mul(p, b), Nat.mul(p, c))

law mul_add_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

def mul_add_r(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), mul_add_r(p, b, c)) :
        {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
        add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

law mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)), mul_add_r(b, Nat.mul(p, b), c)) :
        {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# Doubling
# ========

law dbl_add:
  for +x: Nat
  {Nat.double(x) == Nat.add(x, x) : Nat}

def dbl_add(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      %dbl_add(p) : {2n+Nat.double(p) == 2n+_ : Nat}
      {==}

law dbl_dist:
  for +x: Nat
  for +y: Nat
  {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}

def dbl_dist(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %dbl_dist(p, y) : {2n+Nat.double(Nat.add(p, y)) == 2n+_ : Nat}
      {==}

law mul2:
  for +x: Nat
  {Nat.mul(2n, x) == Nat.double(x) : Nat}

def mul2(x):
  %Equal.sym(Nat, Nat.add(x, 0n), x, add_zero(x)) : {Nat.add(x, _) == Nat.double(x) : Nat}
  Equal.sym(Nat, Nat.double(x), Nat.add(x, x), dbl_add(x))

law mul2_r:
  for +x: Nat
  {Nat.mul(x, 2n) == Nat.double(x) : Nat}

def mul2_r(x):
  %mul_comm(2n, x) : {_ == Nat.double(x) : Nat}
  mul2(x)

law mul_dbl_r:
  for +a: Nat
  for +x: Nat
  {Nat.mul(a, Nat.double(x)) == Nat.double(Nat.mul(a, x)) : Nat}

def mul_dbl_r(a, x):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, Nat.double(x)), Nat.double(Nat.mul(p, x)), mul_dbl_r(p, x)) : {Nat.add(Nat.double(x), _) == Nat.double(Nat.add(x, Nat.mul(p, x))) : Nat}
      Equal.sym(Nat, Nat.double(Nat.add(x, Nat.mul(p, x))), Nat.add(Nat.double(x), Nat.double(Nat.mul(p, x))), dbl_dist(x, Nat.mul(p, x)))

law mul_dbl_l:
  for +a: Nat
  for +x: Nat
  {Nat.mul(Nat.double(a), x) == Nat.double(Nat.mul(a, x)) : Nat}

def mul_dbl_l(a, x):
  %mul_comm(x, Nat.double(a)) : {_ == Nat.double(Nat.mul(a, x)) : Nat}
  %mul_comm(x, a) : {Nat.mul(x, Nat.double(a)) == Nat.double(_) : Nat}
  mul_dbl_r(x, a)

law dbl_inj:
  for +x: Nat
  for +y: Nat
  for e: {Nat.double(x) == Nat.double(y) : Nat}
  {x == y : Nat}

def dbl_inj(x, y, e):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, zero_ne_succ(1n+Nat.double(q), e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, succ_ne_zero(1n+Nat.double(p), e))
    case 1n+p 1n+q:
      %dbl_inj(p, q, succ_inj(Nat.double(p), Nat.double(q), succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e))) : {1n+p == 1n+_ : Nat}
      {==}

law dbl_ne_odd:
  for +x: Nat
  for +y: Nat
  for e: {Nat.double(x) == 1n+Nat.double(y) : Nat}
  Empty

def dbl_ne_odd(x, y, e):
  match x y:
    case 0n _:
      zero_ne_succ(Nat.double(y), e)
    case 1n+p 0n:
      succ_ne_zero(Nat.double(p), succ_inj(1n+Nat.double(p), 0n, e))
    case 1n+p 1n+q:
      dbl_ne_odd(p, q, succ_inj(Nat.double(p), 1n+Nat.double(q), succ_inj(1n+Nat.double(p), 2n+Nat.double(q), e)))

law dbl_zero:
  for +x: Nat
  for e: {Nat.double(x) == 0n : Nat}
  {x == 0n : Nat}

def dbl_zero(x, e):
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, succ_ne_zero(1n+Nat.double(p), e))

# Order
# =====

law lt_zero:
  for +i: Nat
  {Nat.is_lt(i, 0n) == False{} : Bool}

def lt_zero(i):
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}

law lt_irrefl:
  for +n: Nat
  {Nat.is_lt(n, n) == False{} : Bool}

def lt_irrefl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

law le_zero_l:
  for +n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}

def le_zero_l(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

def le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# a < 1 + b is a <= b.
law lt_succ_iff:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, 1n+b) == Nat.is_le(a, b) : Bool}

def lt_succ_iff(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      lt_zero(p)
    case 1n+p 1n+q:
      lt_succ_iff(p, q)

# 1 + a <= b is a < b.
law le_succ_lt:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}

def le_succ_lt(a, b):
  match b:
    case 0n:
      Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, lt_zero(a))
    case 1n+q:
      Equal.sym(Bool, Nat.is_lt(a, 1n+q), Nat.is_le(a, q), lt_succ_iff(a, q))

# not (a < b) is b <= a.
law not_lt_le:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_lt(a, b) == False{} : Bool}
  {Nat.is_le(b, a) == True{} : Bool}

def not_lt_le(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, true_ne_false(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_lt_le(p, q, e)

# not (a <= b) is b < a.
law not_le_lt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == False{} : Bool}
  {Nat.is_lt(b, a) == True{} : Bool}

def not_le_lt(a, b, e):
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_lt(b, 0n) == True{} : Bool}, true_ne_false(
        Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{}, Equal.sym(Bool, Nat.is_le(0n, b), True{}, le_zero_l(b)), e)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_le_lt(p, q, e)

law lt_to_le:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def lt_to_le(a, b, e):
  match a b:
    case 0n _:
      le_zero_l(b)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, false_ne_true(e))
    case 1n+p 1n+q:
      lt_to_le(p, q, e)

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      le_zero_l(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

law lt_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def lt_le_trans(a, b, c, ab, bc):
  %le_succ_lt(a, c) : {_ == True{} : Bool}
  le_trans(1n+a, b, c, %Equal.sym(Bool, Nat.is_le(1n+a, b), Nat.is_lt(a, b), le_succ_lt(a, b)) : {_ == True{} : Bool}; ab, bc)

law le_lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def le_lt_trans(a, b, c, ab, bc):
  %le_succ_lt(a, c) : {_ == True{} : Bool}
  le_trans(1n+a, 1n+b, c, ab, %Equal.sym(Bool, Nat.is_le(1n+b, c), Nat.is_lt(b, c), le_succ_lt(b, c)) : {_ == True{} : Bool}; bc)

law lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def lt_trans(a, b, c, ab, bc):
  lt_le_trans(a, b, c, ab, lt_to_le(b, c, bc))

# a <= a + k and a <= k + a.
law le_add_r:
  for +a: Nat
  for +k: Nat
  {Nat.is_le(a, Nat.add(a, k)) == True{} : Bool}

def le_add_r(a, k):
  match a:
    case 0n:
      le_zero_l(k)
    case 1n+p:
      le_add_r(p, k)

law le_add_l:
  for +a: Nat
  for +k: Nat
  {Nat.is_le(a, Nat.add(k, a)) == True{} : Bool}

def le_add_l(a, k):
  %add_comm(a, k) : {Nat.is_le(a, _) == True{} : Bool}
  le_add_r(a, k)

# b + x is never below b.
law lt_add_self:
  for +b: Nat
  for +x: Nat
  {Nat.is_lt(Nat.add(b, x), b) == False{} : Bool}

def lt_add_self(b, x):
  match b:
    case 0n:
      lt_zero(x)
    case 1n+p:
      lt_add_self(p, x)

law lt_pos:
  for +r: Nat
  for +b: Nat
  for h: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.is_lt(0n, b) == True{} : Bool}

def lt_pos(r, b, h):
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, false_ne_true(
        Equal.trans(Bool, False{}, Nat.is_lt(r, 0n), True{}, Equal.sym(Bool, Nat.is_lt(r, 0n), False{}, lt_zero(r)), h)))
    case 1n+q:
      {==}

law pos_add_l:
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_lt(0n, x) == True{} : Bool}
  {Nat.is_lt(0n, Nat.add(x, y)) == True{} : Bool}

def pos_add_l(x, y, h):
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, y) == True{} : Bool}, false_ne_true(h))
    case 1n+p:
      {==}

# c + a < c + b from a < b (and the same for <=).
law lt_add_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}

def lt_add_l(c, a, b, h):
  match c:
    case 0n:
      h
    case 1n+p:
      lt_add_l(p, a, b, h)

law le_add_mono_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}

def le_add_mono_l(c, a, b, h):
  match c:
    case 0n:
      h
    case 1n+p:
      le_add_mono_l(p, a, b, h)

law le_add_mono_r:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}

def le_add_mono_r(c, a, b, h):
  %add_comm(c, a) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %add_comm(c, b) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  le_add_mono_l(c, a, b, h)

law lt_add_mono_r:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}

def lt_add_mono_r(c, a, b, h):
  %add_comm(c, a) : {Nat.is_lt(_, Nat.add(b, c)) == True{} : Bool}
  %add_comm(c, b) : {Nat.is_lt(Nat.add(c, a), _) == True{} : Bool}
  lt_add_l(c, a, b, h)

# a <= b gives a * c <= b * c.
law le_mul_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}

def le_mul_r(a, b, c, e):
  match a b:
    case 0n _:
      le_zero_l(Nat.mul(b, c))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+p, c), 0n) == True{} : Bool}, false_ne_true(e))
    case 1n+p 1n+q:
      le_add_mono_l(c, Nat.mul(p, c), Nat.mul(q, c), le_mul_r(p, q, c, e))

law le_mul_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(c, a), Nat.mul(c, b)) == True{} : Bool}

def le_mul_l(c, a, b, e):
  %mul_comm(a, c) : {Nat.is_le(_, Nat.mul(c, b)) == True{} : Bool}
  %mul_comm(b, c) : {Nat.is_le(Nat.mul(a, c), _) == True{} : Bool}
  le_mul_r(a, b, c, e)

# k <= m gives k + (m - k) = m.
law le_sub_add:
  for +k: Nat
  for +m: Nat
  for h: {Nat.is_le(k, m) == True{} : Bool}
  {Nat.add(k, Nat.sub(m, k)) == m : Nat}

def le_sub_add(k, m, h):
  match k m:
    case 0n _:
      sub_zero(m)
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, false_ne_true(h))
    case 1n+p 1n+q:
      %le_sub_add(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# Division and remainder
# ======================

# The loop of Nat.divmod keeps d * b + r + n, with b = 1 + bp and m + r = bp.
law go_eq:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +bp: Nat
  for +h: {Nat.add(m, r) == bp : Nat}
  {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)))
    == Nat.add(Nat.mul(d, 1n+bp), Nat.add(r, n)) : Nat}

def go_eq(n, m, d, r, bp, h):
  match n:
    case 0n:
      %Equal.sym(Nat, Nat.add(r, 0n), r, add_zero(r)) : {Nat.add(Nat.mul(d, 1n+bp), r) == Nat.add(Nat.mul(d, 1n+bp), _) : Nat}
      {==}
    case 1n+np:
      match m:
        case 0n:
          -g = Nat.divmod.go(np, r, 1n+d, 0n)
          +db = Nat.mul(d, 1n+bp)
          Equal.trans(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, g), 1n+bp), Pair.snd(Nat, Nat, g)),
            Nat.add(Nat.mul(1n+d, 1n+bp), Nat.add(0n, np)), Nat.add(db, Nat.add(r, 1n+np)),
            go_eq(np, r, 1n+d, 0n, bp, %Equal.sym(Nat, Nat.add(r, 0n), r, add_zero(r)) : {_ == bp : Nat}; h),
            %Equal.sym(Nat, r, bp, h) : {Nat.add(Nat.add(1n+bp, db), np) == Nat.add(db, Nat.add(_, 1n+np)) : Nat}
            %Equal.sym(Nat, Nat.add(bp, 1n+np), 1n+Nat.add(bp, np), add_succ(bp, np)) :
              {Nat.add(Nat.add(1n+bp, db), np) == Nat.add(db, _) : Nat}
            %Equal.sym(Nat, Nat.add(db, 1n+Nat.add(bp, np)), 1n+Nat.add(db, Nat.add(bp, np)), add_succ(db, Nat.add(bp, np))) :
              {Nat.add(Nat.add(1n+bp, db), np) == _ : Nat}
            %Equal.sym(Nat, Nat.add(Nat.add(bp, db), np), Nat.add(bp, Nat.add(db, np)), add_assoc(bp, db, np)) :
              {1n+_ == 1n+Nat.add(db, Nat.add(bp, np)) : Nat}
            %add_left_comm(bp, db, np) : {1n+Nat.add(bp, Nat.add(db, np)) == 1n+_ : Nat}
            {==})
        case 1n+mp:
          -g = Nat.divmod.go(np, mp, d, 1n+r)
          +db = Nat.mul(d, 1n+bp)
          Equal.trans(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, g), 1n+bp), Pair.snd(Nat, Nat, g)),
            Nat.add(db, Nat.add(1n+r, np)), Nat.add(db, Nat.add(r, 1n+np)),
            go_eq(np, mp, d, 1n+r, bp, %Equal.sym(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), add_succ(mp, r)) : {_ == bp : Nat}; h),
            %Equal.sym(Nat, Nat.add(r, 1n+np), 1n+Nat.add(r, np), add_succ(r, np)) : {Nat.add(db, 1n+Nat.add(r, np)) == Nat.add(db, _) : Nat}
            {==})

law go_lt:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +bp: Nat
  for +h: {Nat.add(m, r) == bp : Nat}
  {Nat.is_lt(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp) == True{} : Bool}

def go_lt(n, m, d, r, bp, h):
  match n:
    case 0n:
      %h : {Nat.is_lt(r, 1n+_) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_lt(r, 1n+Nat.add(m, r)), Nat.is_le(r, Nat.add(m, r)), lt_succ_iff(r, Nat.add(m, r))) : {_ == True{} : Bool}
      le_add_l(r, m)
    case 1n+np:
      match m:
        case 0n:
          go_lt(np, r, 1n+d, 0n, bp, %Equal.sym(Nat, Nat.add(r, 0n), r, add_zero(r)) : {_ == bp : Nat}; h)
        case 1n+mp:
          go_lt(np, mp, d, 1n+r, bp, %Equal.sym(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), add_succ(mp, r)) : {_ == bp : Nat}; h)

# a = (a / b) * b + a % b.
law div_mod:
  for +a: Nat
  for +b: Nat
  {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat}

def div_mod(a, b):
  match b:
    case 0n:
      {==}
    case 1n+bp:
      go_eq(a, bp, 0n, 0n, bp, add_zero(bp))

law mod_lt:
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}

def mod_lt(a, b, h):
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mod(a, 0n), 0n) == True{} : Bool}, false_ne_true(h))
    case 1n+bp:
      go_lt(a, bp, 0n, 0n, bp, add_zero(bp))

# q1 * b + r1 = q2 * b + r2 with r1, r2 < b gives q1 = q2.
law div_uniq:
  for +q1: Nat
  for +q2: Nat
  for +b: Nat
  for +r1: Nat
  for +r2: Nat
  for h1: {Nat.is_lt(r1, b) == True{} : Bool}
  for h2: {Nat.is_lt(r2, b) == True{} : Bool}
  for e: {Nat.add(Nat.mul(q1, b), r1) == Nat.add(Nat.mul(q2, b), r2) : Nat}
  {q1 == q2 : Nat}

def div_uniq(q1, q2, b, r1, r2, h1, h2, e):
  match q1 q2:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      +x = Nat.mul(q, b)
      Empty.absurd({0n == 1n+q : Nat}, false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(b, Nat.add(x, r2)), b), True{},
        Equal.sym(Bool, Nat.is_lt(Nat.add(b, Nat.add(x, r2)), b), False{}, lt_add_self(b, Nat.add(x, r2))),
        %add_assoc(b, x, r2) : {Nat.is_lt(_, b) == True{} : Bool}
        %e : {Nat.is_lt(_, b) == True{} : Bool}
        h1)))
    case 1n+p 0n:
      +x = Nat.mul(p, b)
      Empty.absurd({1n+p == 0n : Nat}, false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(b, Nat.add(x, r1)), b), True{},
        Equal.sym(Bool, Nat.is_lt(Nat.add(b, Nat.add(x, r1)), b), False{}, lt_add_self(b, Nat.add(x, r1))),
        %add_assoc(b, x, r1) : {Nat.is_lt(_, b) == True{} : Bool}
        %Equal.sym(Nat, Nat.add(Nat.add(b, x), r1), r2, e) : {Nat.is_lt(_, b) == True{} : Bool}
        h2)))
    case 1n+p 1n+q:
      +x = Nat.mul(p, b)
      +y = Nat.mul(q, b)
      %div_uniq(p, q, b, r1, r2, h1, h2, add_cancel_l(b, Nat.add(x, r1), Nat.add(y, r2),
        %add_assoc(b, x, r1) : {_ == Nat.add(b, Nat.add(y, r2)) : Nat}
        %add_assoc(b, y, r2) : {Nat.add(Nat.add(b, x), r1) == _ : Nat}
        e)) : {1n+p == 1n+_ : Nat}
      {==}

law div_mul_add:
  for +q: Nat
  for +b: Nat
  for +r: Nat
  for +h: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat}

def div_mul_add(q, b, r, h):
  +n = Nat.add(Nat.mul(q, b), r)
  div_uniq(Nat.div(n, b), q, b, Nat.mod(n, b), r, mod_lt(n, b, lt_pos(r, b, h)), h, div_mod(n, b))

law mod_mul_add:
  for +q: Nat
  for +b: Nat
  for +r: Nat
  for +h: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}

def mod_mul_add(q, b, r, h):
  +n = Nat.add(Nat.mul(q, b), r)
  add_cancel_l(Nat.mul(q, b), Nat.mod(n, b), r,
    %div_mul_add(q, b, r, h) : {Nat.add(Nat.mul(_, b), Nat.mod(n, b)) == n : Nat}
    div_mod(n, b))

law mod_small:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.mod(a, b) == a : Nat}

def mod_small(a, b, h):
  mod_mul_add(0n, b, a, h)

law div_small:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.div(a, b) == 0n : Nat}

def div_small(a, b, h):
  div_mul_add(0n, b, a, h)

law mul_mod:
  for +a: Nat
  for +b: Nat
  {Nat.mod(Nat.mul(a, b), b) == 0n : Nat}

def mul_mod(a, b):
  match b:
    case 0n:
      mul_zero_r(a)
    case 1n+bp:
      %add_zero(Nat.mul(a, 1n+bp)) : {Nat.mod(_, 1n+bp) == 0n : Nat}
      mod_mul_add(a, 1n+bp, 0n, {==})

law div_mul:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.div(Nat.mul(a, b), b) == a : Nat}

def div_mul(a, b, h):
  %add_zero(Nat.mul(a, b)) : {Nat.div(_, b) == a : Nat}
  div_mul_add(a, b, 0n, h)

law mod_one:
  for +a: Nat
  {Nat.mod(a, 1n) == 0n : Nat}

def mod_one(a):
  %mul_one(a) : {Nat.mod(_, 1n) == 0n : Nat}
  mul_mod(a, 1n)

law div_one:
  for +a: Nat
  {Nat.div(a, 1n) == a : Nat}

def div_one(a):
  %mul_one(a) : {Nat.div(_, 1n) == a : Nat}
  div_mul(a, 1n, {==})

law mod_zero_l:
  for +b: Nat
  {Nat.mod(0n, b) == 0n : Nat}

def mod_zero_l(b):
  match b:
    case 0n:
      {==}
    case 1n+bp:
      {==}

law div_zero_l:
  for +b: Nat
  {Nat.div(0n, b) == 0n : Nat}

def div_zero_l(b):
  match b:
    case 0n:
      {==}
    case 1n+bp:
      {==}

# Adding a multiple of x does not change the remainder by x.
law mod_add_mul:
  for +j: Nat
  for +x: Nat
  for +z: Nat
  {Nat.mod(Nat.add(Nat.mul(j, x), z), x) == Nat.mod(z, x) : Nat}

def mod_add_mul(j, x, z):
  match x:
    case 0n:
      %Equal.sym(Nat, Nat.mul(j, 0n), 0n, mul_zero_r(j)) : {Nat.add(_, z) == z : Nat}
      {==}
    case 1n+xp:
      +q = Nat.div(z, 1n+xp)
      +r = Nat.mod(z, 1n+xp)
      %div_mod(z, 1n+xp) : {Nat.mod(Nat.add(Nat.mul(j, 1n+xp), _), 1n+xp) == r : Nat}
      %Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(j, q), 1n+xp), r), Nat.add(Nat.add(Nat.mul(j, 1n+xp), Nat.mul(q, 1n+xp)), r),
          Nat.add(Nat.mul(j, 1n+xp), Nat.add(Nat.mul(q, 1n+xp), r)),
          Equal.cong(Nat, Nat, t => Nat.add(t, r), Nat.mul(Nat.add(j, q), 1n+xp), Nat.add(Nat.mul(j, 1n+xp), Nat.mul(q, 1n+xp)), mul_add_r(j, q, 1n+xp)),
          add_assoc(Nat.mul(j, 1n+xp), Nat.mul(q, 1n+xp), r)) :
        {Nat.mod(_, 1n+xp) == r : Nat}
      mod_mul_add(Nat.add(j, q), 1n+xp, r, mod_lt(z, 1n+xp, {==}))

law div_add_mul:
  for +j: Nat
  for +x: Nat
  for +z: Nat
  for +h: {Nat.is_lt(0n, x) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(j, x), z), x) == Nat.add(j, Nat.div(z, x)) : Nat}

def div_add_mul(j, x, z, h):
  +q = Nat.div(z, x)
  +r = Nat.mod(z, x)
  %div_mod(z, x) : {Nat.div(Nat.add(Nat.mul(j, x), _), x) == Nat.add(j, q) : Nat}
  %Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(j, q), x), r), Nat.add(Nat.add(Nat.mul(j, x), Nat.mul(q, x)), r),
      Nat.add(Nat.mul(j, x), Nat.add(Nat.mul(q, x), r)),
      Equal.cong(Nat, Nat, t => Nat.add(t, r), Nat.mul(Nat.add(j, q), x), Nat.add(Nat.mul(j, x), Nat.mul(q, x)), mul_add_r(j, q, x)),
      add_assoc(Nat.mul(j, x), Nat.mul(q, x), r)) :
    {Nat.div(_, x) == Nat.add(j, q) : Nat}
  div_mul_add(Nat.add(j, q), x, r, mod_lt(z, x, h))

# Remainders inside sums and products.
law mod_add_mod_l:
  for +u: Nat
  for +v: Nat
  for +m: Nat
  {Nat.mod(Nat.add(Nat.mod(u, m), v), m) == Nat.mod(Nat.add(u, v), m) : Nat}

def mod_add_mod_l(u, v, m):
  +q = Nat.div(u, m)
  +r = Nat.mod(u, m)
  %div_mod(u, m) : {Nat.mod(Nat.add(r, v), m) == Nat.mod(Nat.add(_, v), m) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(q, m), r), v), Nat.add(Nat.mul(q, m), Nat.add(r, v)), add_assoc(Nat.mul(q, m), r, v)) :
    {Nat.mod(Nat.add(r, v), m) == Nat.mod(_, m) : Nat}
  Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(q, m), Nat.add(r, v)), m), Nat.mod(Nat.add(r, v), m), mod_add_mul(q, m, Nat.add(r, v)))

law mod_add_mod_r:
  for +v: Nat
  for +u: Nat
  for +m: Nat
  {Nat.mod(Nat.add(v, Nat.mod(u, m)), m) == Nat.mod(Nat.add(v, u), m) : Nat}

def mod_add_mod_r(v, u, m):
  %add_comm(Nat.mod(u, m), v) : {Nat.mod(_, m) == Nat.mod(Nat.add(v, u), m) : Nat}
  %add_comm(u, v) : {Nat.mod(Nat.add(Nat.mod(u, m), v), m) == Nat.mod(_, m) : Nat}
  mod_add_mod_l(u, v, m)

law mod_mul_mod_l:
  for +u: Nat
  for +y: Nat
  for +m: Nat
  {Nat.mod(Nat.mul(Nat.mod(u, m), y), m) == Nat.mod(Nat.mul(u, y), m) : Nat}

def mod_mul_mod_l(u, y, m):
  +q = Nat.div(u, m)
  +r = Nat.mod(u, m)
  %div_mod(u, m) : {Nat.mod(Nat.mul(r, y), m) == Nat.mod(Nat.mul(_, y), m) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, m), r), y), Nat.add(Nat.mul(Nat.mul(q, m), y), Nat.mul(r, y)), mul_add_r(Nat.mul(q, m), r, y)) :
    {Nat.mod(Nat.mul(r, y), m) == Nat.mod(_, m) : Nat}
  %Equal.trans(Nat, Nat.mul(Nat.mul(q, y), m), Nat.mul(q, Nat.mul(y, m)), Nat.mul(Nat.mul(q, m), y),
      mul_assoc(q, y, m),
      %mul_comm(m, y) : {Nat.mul(q, _) == Nat.mul(Nat.mul(q, m), y) : Nat}
      Equal.sym(Nat, Nat.mul(Nat.mul(q, m), y), Nat.mul(q, Nat.mul(m, y)), mul_assoc(q, m, y))) :
    {Nat.mod(Nat.mul(r, y), m) == Nat.mod(Nat.add(_, Nat.mul(r, y)), m) : Nat}
  Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(Nat.mul(q, y), m), Nat.mul(r, y)), m), Nat.mod(Nat.mul(r, y), m), mod_add_mul(Nat.mul(q, y), m, Nat.mul(r, y)))

law mod_mul_mod_r:
  for +y: Nat
  for +u: Nat
  for +m: Nat
  {Nat.mod(Nat.mul(y, Nat.mod(u, m)), m) == Nat.mod(Nat.mul(y, u), m) : Nat}

def mod_mul_mod_r(y, u, m):
  %mul_comm(Nat.mod(u, m), y) : {Nat.mod(_, m) == Nat.mod(Nat.mul(y, u), m) : Nat}
  %mul_comm(u, y) : {Nat.mod(Nat.mul(Nat.mod(u, m), y), m) == Nat.mod(_, m) : Nat}
  mod_mul_mod_l(u, y, m)

law mod_mod:
  for +u: Nat
  for +m: Nat
  {Nat.mod(Nat.mod(u, m), m) == Nat.mod(u, m) : Nat}

def mod_mod(u, m):
  %add_zero(Nat.mod(u, m)) : {Nat.mod(_, m) == Nat.mod(u, m) : Nat}
  %add_zero(u) : {Nat.mod(Nat.add(Nat.mod(u, m), 0n), m) == Nat.mod(_, m) : Nat}
  mod_add_mod_l(u, 0n, m)

# (a % (x * y)) % x = a % x.
law mod_mod_mul:
  for +a: Nat
  for +x: Nat
  for +y: Nat
  {Nat.mod(Nat.mod(a, Nat.mul(x, y)), x) == Nat.mod(a, x) : Nat}

def mod_mod_mul(a, x, y):
  +q = Nat.div(a, Nat.mul(x, y))
  +r = Nat.mod(a, Nat.mul(x, y))
  %div_mod(a, Nat.mul(x, y)) : {Nat.mod(r, x) == Nat.mod(_, x) : Nat}
  %Equal.trans(Nat, Nat.mul(Nat.mul(q, y), x), Nat.mul(q, Nat.mul(y, x)), Nat.mul(q, Nat.mul(x, y)),
      mul_assoc(q, y, x), %mul_comm(x, y) : {Nat.mul(q, _) == Nat.mul(q, Nat.mul(x, y)) : Nat}; {==}) :
    {Nat.mod(r, x) == Nat.mod(Nat.add(_, r), x) : Nat}
  Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(Nat.mul(q, y), x), r), x), Nat.mod(r, x), mod_add_mul(Nat.mul(q, y), x, r))

# (a / x) / y = a / (x * y).
law div_div:
  for +a: Nat
  for +x: Nat
  for +y: Nat
  {Nat.div(Nat.div(a, x), y) == Nat.div(a, Nat.mul(x, y)) : Nat}

def div_div(a, x, y):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      {==}
    case 1n+xp 0n:
      %Equal.sym(Nat, Nat.mul(1n+xp, 0n), 0n, mul_zero_r(1n+xp)) : {0n == Nat.div(a, _) : Nat}
      {==}
    case 1n+xp 1n+yp:
      +x1 = {1n+xp : Nat}
      +y1 = {1n+yp : Nat}
      +q1 = Nat.div(a, x1)
      +r1 = Nat.mod(a, x1)
      +q2 = Nat.div(q1, y1)
      +r2 = Nat.mod(q1, y1)
      +xy = Nat.mul(x1, y1)
      +s = Nat.add(Nat.mul(r2, x1), r1)
      # a = q2 * (x * y) + (r2 * x + r1)
      +ea = Equal.trans(Nat, Nat.add(Nat.mul(q2, xy), s), Nat.add(Nat.mul(q1, x1), r1), a,
        %div_mod(q1, y1) : {Nat.add(Nat.mul(q2, xy), s) == Nat.add(Nat.mul(_, x1), r1) : Nat}
        %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q2, y1), r2), x1), Nat.add(Nat.mul(Nat.mul(q2, y1), x1), Nat.mul(r2, x1)), mul_add_r(Nat.mul(q2, y1), r2, x1)) :
          {Nat.add(Nat.mul(q2, xy), s) == Nat.add(_, r1) : Nat}
        %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(q2, y1), x1), Nat.mul(r2, x1)), r1), Nat.add(Nat.mul(Nat.mul(q2, y1), x1), s),
            add_assoc(Nat.mul(Nat.mul(q2, y1), x1), Nat.mul(r2, x1), r1)) : {Nat.add(Nat.mul(q2, xy), s) == _ : Nat}
        %Equal.trans(Nat, Nat.mul(q2, xy), Nat.mul(q2, Nat.mul(y1, x1)), Nat.mul(Nat.mul(q2, y1), x1),
            %mul_comm(x1, y1) : {Nat.mul(q2, xy) == Nat.mul(q2, _) : Nat}; {==},
            Equal.sym(Nat, Nat.mul(Nat.mul(q2, y1), x1), Nat.mul(q2, Nat.mul(y1, x1)), mul_assoc(q2, y1, x1))) :
          {Nat.add(Nat.mul(q2, xy), s) == Nat.add(_, s) : Nat}
        {==},
        div_mod(a, x1))
      # r2 * x + r1 < x * y
      +hs = lt_le_trans(s, Nat.add(Nat.mul(r2, x1), x1), xy,
        lt_add_l(Nat.mul(r2, x1), r1, x1, mod_lt(a, x1, {==})),
        %add_comm(x1, Nat.mul(r2, x1)) : {Nat.is_le(_, xy) == True{} : Bool}
        %mul_comm(y1, x1) : {Nat.is_le(Nat.mul(1n+r2, x1), _) == True{} : Bool}
        le_mul_r(1n+r2, y1, x1, %Equal.sym(Bool, Nat.is_le(1n+r2, y1), Nat.is_lt(r2, y1), le_succ_lt(r2, y1)) : {_ == True{} : Bool}; mod_lt(q1, y1, {==})))
      %ea : {q2 == Nat.div(_, xy) : Nat}
      Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(q2, xy), s), xy), q2, div_mul_add(q2, xy, s, hs))

# a < b * c with b > 0 gives a / b < c.
def div_lt.go(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_lt(a, Nat.mul(b, c)) == True{} : Bool},
  t: Bool, et: {Nat.is_lt(Nat.div(a, b), c) == t : Bool}) -> {Nat.is_lt(Nat.div(a, b), c) == True{} : Bool}:
  match t:
    case True{}:
      et
    case False{}:
      +q = Nat.div(a, b)
      +hcq = not_lt_le(q, c, et)
      +hle = le_trans(Nat.mul(c, b), Nat.mul(q, b), a, le_mul_r(c, q, b, hcq),
        %div_mod(a, b) : {Nat.is_le(Nat.mul(q, b), _) == True{} : Bool}
        le_add_r(Nat.mul(q, b), Nat.mod(a, b)))
      +hlt = lt_le_trans(a, Nat.mul(b, c), a, h, %mul_comm(c, b) : {Nat.is_le(_, a) == True{} : Bool}; hle)
      Empty.absurd({Nat.is_lt(q, c) == True{} : Bool}, false_ne_true(
        Equal.trans(Bool, False{}, Nat.is_lt(a, a), True{}, Equal.sym(Bool, Nat.is_lt(a, a), False{}, lt_irrefl(a)), hlt)))

law div_lt:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +hb: {Nat.is_lt(0n, b) == True{} : Bool}
  for +h: {Nat.is_lt(a, Nat.mul(b, c)) == True{} : Bool}
  {Nat.is_lt(Nat.div(a, b), c) == True{} : Bool}

def div_lt(a, b, c, hb, h):
  div_lt.go(a, b, c, h, Nat.is_lt(Nat.div(a, b), c), {==})

# Powers
# ======

law pow_add:
  for +b: Nat
  for +j: Nat
  for +k: Nat
  {Nat.pow(b, Nat.add(j, k)) == Nat.mul(Nat.pow(b, j), Nat.pow(b, k)) : Nat}

def pow_add(b, j, k):
  match j:
    case 0n:
      Equal.sym(Nat, Nat.add(Nat.pow(b, k), 0n), Nat.pow(b, k), add_zero(Nat.pow(b, k)))
    case 1n+p:
      %Equal.sym(Nat, Nat.pow(b, Nat.add(p, k)), Nat.mul(Nat.pow(b, p), Nat.pow(b, k)), pow_add(b, p, k)) :
        {Nat.mul(b, _) == Nat.mul(Nat.mul(b, Nat.pow(b, p)), Nat.pow(b, k)) : Nat}
      Equal.sym(Nat, Nat.mul(Nat.mul(b, Nat.pow(b, p)), Nat.pow(b, k)), Nat.mul(b, Nat.mul(Nat.pow(b, p), Nat.pow(b, k))),
        mul_assoc(b, Nat.pow(b, p), Nat.pow(b, k)))

law pow_pos:
  for +k: Nat
  {Nat.is_lt(0n, Nat.pow(2n, k)) == True{} : Bool}

def pow_pos(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      pos_add_l(Nat.pow(2n, j), Nat.mul(1n, Nat.pow(2n, j)), pow_pos(j))

law pow2s:
  for +p: Nat
  {Nat.pow(2n, 1n+p) == Nat.double(Nat.pow(2n, p)) : Nat}

def pow2s(p):
  mul2(Nat.pow(2n, p))

# 2^(1+j) - 1 = 1 + 2 (2^j - 1).
law pow_sub1:
  for +j: Nat
  {Nat.sub(Nat.pow(2n, 1n+j), 1n) == 1n+Nat.double(Nat.sub(Nat.pow(2n, j), 1n)) : Nat}

def pow_sub1.go(+u: Nat) -> {Nat.sub(Nat.double(1n+u), 1n) == 1n+Nat.double(Nat.sub(1n+u, 1n)) : Nat}:
  %Equal.sym(Nat, Nat.sub(u, 0n), u, sub_zero(u)) : {Nat.sub(Nat.double(1n+u), 1n) == 1n+Nat.double(_) : Nat}
  {==}

law pow_one_plus:
  for +k: Nat
  {1n+Nat.sub(Nat.pow(2n, k), 1n) == Nat.pow(2n, k) : Nat}

def pow_one_plus(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Nat, Nat.mul(2n, Nat.pow(2n, j)), Nat.double(Nat.pow(2n, j)), mul2(Nat.pow(2n, j))) :
        {1n+Nat.sub(_, 1n) == _ : Nat}
      %pow_one_plus(j) : {1n+Nat.sub(Nat.double(_), 1n) == Nat.double(_) : Nat}
      {==}

def pow_sub1(j):
  %Equal.sym(Nat, Nat.mul(2n, Nat.pow(2n, j)), Nat.double(Nat.pow(2n, j)), mul2(Nat.pow(2n, j))) :
    {Nat.sub(_, 1n) == 1n+Nat.double(Nat.sub(Nat.pow(2n, j), 1n)) : Nat}
  %pow_one_plus(j) : {Nat.sub(Nat.double(_), 1n) == 1n+Nat.double(Nat.sub(_, 1n)) : Nat}
  pow_sub1.go(Nat.sub(Nat.pow(2n, j), 1n))

# 2^m <= 2^k for m <= k.
law pow_le:
  for +m: Nat
  for +k: Nat
  for +h: {Nat.is_le(m, k) == True{} : Bool}
  {Nat.is_le(Nat.pow(2n, m), Nat.pow(2n, k)) == True{} : Bool}

def pow_le(m, k, h):
  %le_sub_add(m, k, h) : {Nat.is_le(Nat.pow(2n, m), Nat.pow(2n, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.pow(2n, Nat.add(m, Nat.sub(k, m))), Nat.mul(Nat.pow(2n, m), Nat.pow(2n, Nat.sub(k, m))), pow_add(2n, m, Nat.sub(k, m))) :
    {Nat.is_le(Nat.pow(2n, m), _) == True{} : Bool}
  %mul_one(Nat.pow(2n, m)) :
    {Nat.is_le(_, Nat.mul(Nat.pow(2n, m), Nat.pow(2n, Nat.sub(k, m)))) == True{} : Bool}
  le_mul_l(Nat.pow(2n, m), 1n, Nat.pow(2n, Nat.sub(k, m)),
    %Equal.sym(Bool, Nat.is_le(1n, Nat.pow(2n, Nat.sub(k, m))), Nat.is_lt(0n, Nat.pow(2n, Nat.sub(k, m))), le_succ_lt(0n, Nat.pow(2n, Nat.sub(k, m)))) : {_ == True{} : Bool}
    pow_pos(Nat.sub(k, m)))

# (a % 2^m) % 2^k = a % 2^k for k <= m.
law mod_mod_pow:
  for +a: Nat
  for +k: Nat
  for +m: Nat
  for +h: {Nat.is_le(k, m) == True{} : Bool}
  {Nat.mod(Nat.mod(a, Nat.pow(2n, m)), Nat.pow(2n, k)) == Nat.mod(a, Nat.pow(2n, k)) : Nat}

def mod_mod_pow(a, k, m, h):
  %le_sub_add(k, m, h) : {Nat.mod(Nat.mod(a, Nat.pow(2n, _)), Nat.pow(2n, k)) == Nat.mod(a, Nat.pow(2n, k)) : Nat}
  %Equal.sym(Nat, Nat.pow(2n, Nat.add(k, Nat.sub(m, k))), Nat.mul(Nat.pow(2n, k), Nat.pow(2n, Nat.sub(m, k))), pow_add(2n, k, Nat.sub(m, k))) :
    {Nat.mod(Nat.mod(a, _), Nat.pow(2n, k)) == Nat.mod(a, Nat.pow(2n, k)) : Nat}
  mod_mod_mul(a, Nat.pow(2n, k), Nat.pow(2n, Nat.sub(m, k)))

# m <= k + (m - k).
law le_add_sub:
  for +m: Nat
  for +k: Nat
  {Nat.is_le(m, Nat.add(k, Nat.sub(m, k))) == True{} : Bool}

def le_add_sub(m, k):
  match m k:
    case 0n _:
      le_zero_l(Nat.add(k, Nat.sub(0n, k)))
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n+p 1n+q:
      le_add_sub(p, q)

law eq_comm:
  for +a: Nat
  for +b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}

def eq_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      eq_comm(p, q)

# a <= b and a != b give a + 1 <= b.
law le_ne:
  for +a: Nat
  for +b: Nat
  for +le: {Nat.is_le(a, b) == True{} : Bool}
  for +ne: {Nat.is_eq(a, b) == False{} : Bool}
  {Nat.is_le(1n+a, b) == True{} : Bool}

def le_ne(a, b, le, ne):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, true_ne_false(ne))
    case 0n 1n+q:
      le_zero_l(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, false_ne_true(le))
    case 1n+p 1n+q:
      le_ne(p, q, le, ne)

# a <= b gives not (b < a).
law le_not_lt:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_lt(b, a) == False{} : Bool}

def le_not_lt(a, b, h):
  match a b:
    case 0n _:
      lt_zero(b)
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, false_ne_true(h))
    case 1n+p 1n+q:
      le_not_lt(p, q, h)

# a + c <= x gives c <= x - a.
law le_sub_r:
  for +a: Nat
  for +c: Nat
  for +x: Nat
  for +h: {Nat.is_le(Nat.add(a, c), x) == True{} : Bool}
  {Nat.is_le(c, Nat.sub(x, a)) == True{} : Bool}

def le_sub_r(a, c, x, h):
  match a x:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(x, 0n), x, sub_zero(x)) : {Nat.is_le(c, _) == True{} : Bool}
      h
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(c, Nat.sub(0n, 1n+p)) == True{} : Bool}, false_ne_true(h))
    case 1n+p 1n+y:
      le_sub_r(p, c, y, h)

# 8a < 8b gives a < b.
def lt_mul_cancel.go(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(Nat.mul(c, a), Nat.mul(c, b)) == True{} : Bool},
  t: Bool, et: {Nat.is_lt(a, b) == t : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match t:
    case True{}:
      et
    case False{}:
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, false_ne_true(
        Equal.trans(Bool, False{}, Nat.is_lt(Nat.mul(c, a), Nat.mul(c, a)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.mul(c, a), Nat.mul(c, a)), False{}, lt_irrefl(Nat.mul(c, a))),
          lt_le_trans(Nat.mul(c, a), Nat.mul(c, b), Nat.mul(c, a), h, le_mul_l(c, b, a, not_lt_le(a, b, et))))))

law lt_mul_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(Nat.mul(c, a), Nat.mul(c, b)) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

def lt_mul_cancel(c, a, b, h):
  lt_mul_cancel.go(c, a, b, h, Nat.is_lt(a, b), {==})
