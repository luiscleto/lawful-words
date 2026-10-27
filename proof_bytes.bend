import Base
import ./defs.bend as D
import ./proof_nat.bend as N
import ./proof_word.bend as W
import ./proof_u32.bend as U

# Bytes in a word. Most laws compare two words bit by bit (U.bit_ext), with
# the bits of D.byte, shifts and 255 below.

# Bool facts
# ==========

law and_comm:
  for +a: Bool
  for +b: Bool
  {Bool.and(a, b) == Bool.and(b, a) : Bool}

def and_comm(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# and(a, and(b, and(c, d))) = and(b, and(a, d)) when a implies c.
law band_perm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for imp: {a == True{} : Bool} -> {c == True{} : Bool}
  {Bool.and(a, Bool.and(b, Bool.and(c, d))) == Bool.and(b, Bool.and(a, d)) : Bool}

def band_perm(a, b, c, d, imp):
  match a:
    case False{}:
      Equal.sym(Bool, Bool.and(b, False{}), False{}, N.and_false_r(b))
    case True{}:
      %Equal.sym(Bool, c, True{}, imp({==})) : {Bool.and(b, Bool.and(_, d)) == Bool.and(b, d) : Bool}
      {==}

# and(l, and(i, x)) = and(l, x) when l implies i.
law bimp:
  for +l: Bool
  for +i: Bool
  for +x: Bool
  for imp: {l == True{} : Bool} -> {i == True{} : Bool}
  {Bool.and(l, Bool.and(i, x)) == Bool.and(l, x) : Bool}

def bimp(l, i, x, imp):
  match l:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Bool, i, True{}, imp({==})) : {Bool.and(_, x) == x : Bool}
      {==}

# Bits of numbers
# ===============

law lt_succ_self:
  for +j: Nat
  {Nat.is_lt(j, 1n+j) == True{} : Bool}

def lt_succ_self(j):
  %Equal.sym(Bool, Nat.is_lt(j, 1n+j), Nat.is_le(j, j), N.lt_succ_iff(j, j)) : {_ == True{} : Bool}
  N.le_refl(j)

# A word below 2^k has bit k clear.
law bit_zero_div:
  for +b: U32
  for +k: Nat
  for +h: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, k)) == True{} : Bool}
  {D.bit(b, k) == False{} : Bool}

def bit_zero_div(b, k, h):
  %Equal.sym(Nat, Nat.div(U32.to_nat(b), Nat.pow(2n, k)), 0n, N.div_small(U32.to_nat(b), Nat.pow(2n, k), h)) :
    {Nat.is_eq(Nat.mod(_, 2n), 1n) == False{} : Bool}
  {==}

law bit_lt_pow:
  for +b: U32
  for +n: Nat
  for +k: Nat
  for +hb: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, n)) == True{} : Bool}
  for +hk: {Nat.is_le(n, k) == True{} : Bool}
  {D.bit(b, k) == False{} : Bool}

def bit_lt_pow(b, n, k, hb, hk):
  bit_zero_div(b, k, N.lt_le_trans(U32.to_nat(b), Nat.pow(2n, n), Nat.pow(2n, k), hb, N.pow_le(n, k, hk)))

law bit_ge32:
  for +a: U32
  for +k: Nat
  for +hk: {Nat.is_le(32n, k) == True{} : Bool}
  {D.bit(a, k) == False{} : Bool}

def bit_ge32(a, k, hk):
  bit_lt_pow(a, 32n, k, U.to_nat_lt_p(a), hk)

def bit_lt32.go(+a: U32, +k: Nat, z: Bool, +ez: {Nat.is_lt(k, 32n) == z : Bool}) -> {D.bit(a, k) == Bool.and(z, D.bit(a, k)) : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      bit_ge32(a, k, N.not_lt_le(k, 32n, ez))

# Bits from 32 up are clear.
law bit_lt32:
  for +a: U32
  for +k: Nat
  {D.bit(a, k) == Bool.and(Nat.is_lt(k, 32n), D.bit(a, k)) : Bool}

def bit_lt32(a, k):
  bit_lt32.go(a, k, Nat.is_lt(k, 32n), {==})

law bit_zero:
  for +k: Nat
  {D.bit(0, k) == False{} : Bool}

def bit_zero(k):
  bit_zero_div(0, k, N.pow_pos(k))

law bit_shrn:
  for +a: U32
  for +s: Nat
  for +k: Nat
  {D.bit(U32.shrn(a, s), k) == D.bit(a, Nat.add(k, s)) : Bool}

def bit_shrn(a, s, k):
  +x = U32.to_nat(a)
  +ps = Nat.pow(2n, s)
  +pk = Nat.pow(2n, k)
  %Equal.sym(Nat, U32.to_nat(U32.shrn(a, s)), Nat.div(x, ps), U.to_nat_shrn(a, s)) :
    {Nat.is_eq(Nat.mod(Nat.div(_, pk), 2n), 1n) == D.bit(a, Nat.add(k, s)) : Bool}
  %Equal.sym(Nat, Nat.div(Nat.div(x, ps), pk), Nat.div(x, Nat.mul(ps, pk)), N.div_div(x, ps, pk)) :
    {Nat.is_eq(Nat.mod(_, 2n), 1n) == D.bit(a, Nat.add(k, s)) : Bool}
  %N.mul_comm(pk, ps) : {Nat.is_eq(Nat.mod(Nat.div(x, _), 2n), 1n) == D.bit(a, Nat.add(k, s)) : Bool}
  %N.pow_add(2n, k, s) : {Nat.is_eq(Nat.mod(Nat.div(x, _), 2n), 1n) == D.bit(a, Nat.add(k, s)) : Bool}
  {==}

# Bits of a left shift
# ====================

law wbit_put:
  for +p: Nat
  for +c: Bool
  for +t: Word(p)
  for +j: Nat
  {W.wbit(p, Word.shl.put(p, c, t), j) == Bool.and(Nat.is_lt(j, p), W.wbit(1n+p, WCon{c, t}, j)) : Bool}

def wbit_put(p, c, t, j):
  match p:
    case 0n:
      match t j:
        case WNil{} 0n:
          {==}
        case WNil{} 1n+i:
          {==}
    case 1n+q:
      match t j:
        case WCon{+b, +u} 0n:
          {==}
        case WCon{+b, +u} 1n+i:
          wbit_put(q, b, u, i)

law bit_shl0:
  for +a: U32
  {D.bit(U32.shl(a), 0n) == False{} : Bool}

def bit_shl0(a):
  match a:
    case U32{+x}:
      match x:
        case WCon{+b, +t}:
          U.bitw(Word.shl(32n, WCon{b, t}), 0n)

law bit_shl1:
  for +a: U32
  for +j: Nat
  {D.bit(U32.shl(a), 1n+j) == Bool.and(Nat.is_lt(1n+j, 32n), D.bit(a, j)) : Bool}

def bit_shl1(a, j):
  match a:
    case U32{+x}:
      match x:
        case WCon{+b, +t}:
          %Equal.sym(Bool, D.bit(U32{Word.shl(32n, WCon{b, t})}, 1n+j), W.wbit(32n, Word.shl(32n, WCon{b, t}), 1n+j), U.bitw(Word.shl(32n, WCon{b, t}), 1n+j)) :
            {_ == Bool.and(Nat.is_lt(1n+j, 32n), D.bit(U32{WCon{b, t}}, j)) : Bool}
          %Equal.sym(Bool, D.bit(U32{WCon{b, t}}, j), W.wbit(32n, WCon{b, t}, j), U.bitw(WCon{b, t}, j)) :
            {W.wbit(32n, Word.shl(32n, WCon{b, t}), 1n+j) == Bool.and(Nat.is_lt(1n+j, 32n), _) : Bool}
          wbit_put(31n, b, t, j)

law bit_shln:
  for +a: U32
  for +s: Nat
  for +k: Nat
  {D.bit(U32.shln(a, s), k) == Bool.and(Nat.is_le(s, k), Bool.and(Nat.is_lt(k, 32n), D.bit(a, Nat.sub(k, s)))) : Bool}

def bit_shln(a, s, k):
  match s:
    case 0n:
      %Equal.sym(Bool, Nat.is_le(0n, k), True{}, N.le_zero_l(k)) :
        {D.bit(a, k) == Bool.and(_, Bool.and(Nat.is_lt(k, 32n), D.bit(a, Nat.sub(k, 0n)))) : Bool}
      %Equal.sym(Nat, Nat.sub(k, 0n), k, N.sub_zero(k)) :
        {D.bit(a, k) == Bool.and(True{}, Bool.and(Nat.is_lt(k, 32n), D.bit(a, _))) : Bool}
      bit_lt32(a, k)
    case 1n+t:
      match k:
        case 0n:
          bit_shl0(U32.shln(a, t))
        case 1n+j:
          %Equal.sym(Bool, D.bit(U32.shl(U32.shln(a, t)), 1n+j), Bool.and(Nat.is_lt(1n+j, 32n), D.bit(U32.shln(a, t), j)), bit_shl1(U32.shln(a, t), j)) :
            {_ == Bool.and(Nat.is_le(t, j), Bool.and(Nat.is_lt(1n+j, 32n), D.bit(a, Nat.sub(j, t)))) : Bool}
          %Equal.sym(Bool, D.bit(U32.shln(a, t), j), Bool.and(Nat.is_le(t, j), Bool.and(Nat.is_lt(j, 32n), D.bit(a, Nat.sub(j, t)))), bit_shln(a, t, j)) :
            {Bool.and(Nat.is_lt(1n+j, 32n), _) == Bool.and(Nat.is_le(t, j), Bool.and(Nat.is_lt(1n+j, 32n), D.bit(a, Nat.sub(j, t)))) : Bool}
          band_perm(Nat.is_lt(1n+j, 32n), Nat.is_le(t, j), Nat.is_lt(j, 32n), D.bit(a, Nat.sub(j, t)),
            h => N.lt_trans(j, 1n+j, 32n, lt_succ_self(j), h))

# 255 and bytes
# =============

law bit_255:
  for +k: Nat
  {D.bit(255, k) == Nat.is_lt(k, 8n) : Bool}

def bit_255(k):
  match k:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  Equal.trans(Bool, D.bit(255, 8n+k8), False{}, Nat.is_lt(8n+k8, 8n),
                                    bit_lt_pow(255, 8n, 8n+k8, {==}, N.le_zero_l(k8)),
                                    Equal.sym(Bool, Nat.is_lt(k8, 0n), False{}, N.lt_zero(k8)))

# Bit k of byte j of w is bit 8j + k of w (and 0 from k = 8 up).
law bit_byte:
  for +w: U32
  for +j: Nat
  for +k: Nat
  {D.bit(D.byte(w, j), k) == Bool.and(Nat.is_lt(k, 8n), D.bit(w, Nat.add(Nat.mul(8n, j), k))) : Bool}

def bit_byte(w, j, k):
  +s = Nat.mul(8n, j)
  %Equal.sym(Bool, D.bit(U32.and(U32.shrn(w, s), 255), k), Bool.and(D.bit(U32.shrn(w, s), k), D.bit(255, k)), U.bit_and(U32.shrn(w, s), 255, k)) :
    {_ == Bool.and(Nat.is_lt(k, 8n), D.bit(w, Nat.add(s, k))) : Bool}
  %Equal.sym(Bool, D.bit(U32.shrn(w, s), k), D.bit(w, Nat.add(k, s)), bit_shrn(w, s, k)) :
    {Bool.and(_, D.bit(255, k)) == Bool.and(Nat.is_lt(k, 8n), D.bit(w, Nat.add(s, k))) : Bool}
  %Equal.sym(Bool, D.bit(255, k), Nat.is_lt(k, 8n), bit_255(k)) :
    {Bool.and(D.bit(w, Nat.add(k, s)), _) == Bool.and(Nat.is_lt(k, 8n), D.bit(w, Nat.add(s, k))) : Bool}
  %N.add_comm(s, k) : {Bool.and(D.bit(w, _), Nat.is_lt(k, 8n)) == Bool.and(Nat.is_lt(k, 8n), D.bit(w, Nat.add(s, k))) : Bool}
  and_comm(D.bit(w, Nat.add(s, k)), Nat.is_lt(k, 8n))

# More Bool facts
# ===============

law band_dist:
  for +l: Bool
  for +x: Bool
  for +y: Bool
  {Bool.and(l, Bool.and(x, y)) == Bool.and(Bool.and(l, x), Bool.and(l, y)) : Bool}

def band_dist(l, x, y):
  match l:
    case False{}:
      {==}
    case True{}:
      {==}

law bor_dist:
  for +l: Bool
  for +x: Bool
  for +y: Bool
  {Bool.and(l, Bool.or(x, y)) == Bool.or(Bool.and(l, x), Bool.and(l, y)) : Bool}

def bor_dist(l, x, y):
  match l:
    case False{}:
      {==}
    case True{}:
      {==}

law bxor_dist:
  for +l: Bool
  for +x: Bool
  for +y: Bool
  {Bool.and(l, Bool.xor(x, y)) == Bool.xor(Bool.and(l, x), Bool.and(l, y)) : Bool}

def bxor_dist(l, x, y):
  match l:
    case False{}:
      {==}
    case True{}:
      {==}

law bnot_byte:
  for +l: Bool
  for +i: Bool
  for +x: Bool
  for imp: {l == True{} : Bool} -> {i == True{} : Bool}
  {Bool.and(l, Bool.and(i, Bool.not(x))) == Bool.xor(Bool.and(l, x), l) : Bool}

def bnot_byte(l, i, x, imp):
  match l x:
    case False{} _:
      {==}
    case True{} False{}:
      %Equal.sym(Bool, i, True{}, imp({==})) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case True{} True{}:
      %Equal.sym(Bool, i, True{}, imp({==})) : {Bool.and(_, False{}) == False{} : Bool}
      {==}

law blow:
  for +l: Bool
  for +g: Bool
  for +y: Bool
  for imp: {l == True{} : Bool} -> {g == False{} : Bool}
  {Bool.and(l, Bool.and(g, y)) == False{} : Bool}

def blow(l, g, y, imp):
  match l:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Bool, g, False{}, imp({==})) : {Bool.and(_, y) == False{} : Bool}
      {==}

law bor_low:
  for +l: Bool
  for +x: Bool
  for +g: Bool
  for +y: Bool
  for imp: {l == True{} : Bool} -> {g == False{} : Bool}
  {Bool.and(l, Bool.or(x, Bool.and(g, y))) == Bool.and(l, x) : Bool}

def bor_low(l, x, g, y, imp):
  match l:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Bool, g, False{}, imp({==})) : {Bool.or(x, Bool.and(_, y)) == x : Bool}
      N.or_false_r(x)

law put_bits:
  for +l: Bool
  for +i: Bool
  for +x: Bool
  for +y: Bool
  for imp1: {l == True{} : Bool} -> {i == True{} : Bool}
  for imp2: {l == False{} : Bool} -> {y == False{} : Bool}
  {Bool.and(l, Bool.or(Bool.and(x, Bool.and(i, Bool.not(Bool.and(i, l)))), Bool.and(i, y))) == y : Bool}

def put_bits(l, i, x, y, imp1, imp2):
  match l:
    case False{}:
      Equal.sym(Bool, y, False{}, imp2({==}))
    case True{}:
      %Equal.sym(Bool, i, True{}, imp1({==})) : {Bool.or(Bool.and(x, Bool.and(_, Bool.not(Bool.and(_, True{})))), Bool.and(_, y)) == y : Bool}
      %Equal.sym(Bool, Bool.and(x, False{}), False{}, N.and_false_r(x)) : {Bool.or(_, y) == y : Bool}
      {==}

# Index arithmetic: byte j, bit k is bit 8j + k
# =============================================

law lt_not_le:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.is_le(y, x) == False{} : Bool}

def lt_not_le(x, y, h):
  match x y:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, x) == False{} : Bool}, N.false_ne_true(
        Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, N.lt_zero(x)), h)))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_not_le(p, q, h)

law idx32:
  for +j: Nat
  for +k: Nat
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +hk: {Nat.is_lt(k, 8n) == True{} : Bool}
  {Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n) == True{} : Bool}

def idx32(j, k, hj, hk):
  match j:
    case 0n:
      N.lt_trans(k, 8n, 32n, hk, {==})
    case 1n+j1:
      match j1:
        case 0n:
          N.lt_trans(k, 8n, 24n, hk, {==})
        case 1n+j2:
          match j2:
            case 0n:
              N.lt_trans(k, 8n, 16n, hk, {==})
            case 1n+j3:
              match j3:
                case 0n:
                  hk
                case 1n+j4:
                  Empty.absurd({Nat.is_lt(Nat.add(Nat.mul(8n, 4n+j4), k), 32n) == True{} : Bool}, N.false_ne_true(
                    Equal.trans(Bool, False{}, Nat.is_lt(j4, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j4, 0n), False{}, N.lt_zero(j4)), hj)))

# 8j + k < 8 (j + 1) for k < 8.
law lt_mul8:
  for +j: Nat
  for +k: Nat
  for +hk: {Nat.is_lt(k, 8n) == True{} : Bool}
  {Nat.is_lt(Nat.add(Nat.mul(8n, j), k), Nat.mul(8n, 1n+j)) == True{} : Bool}

def lt_mul8(j, k, hk):
  %Equal.sym(Nat, Nat.mul(8n, 1n+j), Nat.add(8n, Nat.mul(8n, j)), N.mul_succ_r(8n, j)) :
    {Nat.is_lt(Nat.add(Nat.mul(8n, j), k), _) == True{} : Bool}
  %N.add_comm(Nat.mul(8n, j), 8n) : {Nat.is_lt(Nat.add(Nat.mul(8n, j), k), _) == True{} : Bool}
  N.lt_add_l(Nat.mul(8n, j), k, 8n, hk)

law idx_add:
  for +j: Nat
  for +s: Nat
  for +k: Nat
  {Nat.add(Nat.add(Nat.mul(8n, j), k), Nat.mul(8n, s)) == Nat.add(Nat.mul(8n, Nat.add(j, s)), k) : Nat}

def idx_add(j, s, k):
  +a = Nat.mul(8n, j)
  +b = Nat.mul(8n, s)
  %Equal.sym(Nat, Nat.mul(8n, Nat.add(j, s)), Nat.add(a, b), N.mul_add(8n, j, s)) : {Nat.add(Nat.add(a, k), b) == Nat.add(_, k) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, k), b), Nat.add(a, Nat.add(k, b)), N.add_assoc(a, k, b)) : {_ == Nat.add(Nat.add(a, b), k) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), k), Nat.add(a, Nat.add(b, k)), N.add_assoc(a, b, k)) : {Nat.add(a, Nat.add(k, b)) == _ : Nat}
  %N.add_comm(k, b) : {Nat.add(a, Nat.add(k, b)) == Nat.add(a, _) : Nat}
  {==}

law idx_sub:
  for +s: Nat
  for +j: Nat
  for +k: Nat
  for +hs: {Nat.is_le(s, j) == True{} : Bool}
  {Nat.sub(Nat.add(Nat.mul(8n, j), k), Nat.mul(8n, s)) == Nat.add(Nat.mul(8n, Nat.sub(j, s)), k) : Nat}

def idx_sub(s, j, k, hs):
  +t = Nat.sub(j, s)
  %N.le_sub_add(s, j, hs) : {Nat.sub(Nat.add(Nat.mul(8n, _), k), Nat.mul(8n, s)) == Nat.add(Nat.mul(8n, t), k) : Nat}
  %Equal.sym(Nat, Nat.mul(8n, Nat.add(s, t)), Nat.add(Nat.mul(8n, s), Nat.mul(8n, t)), N.mul_add(8n, s, t)) :
    {Nat.sub(Nat.add(_, k), Nat.mul(8n, s)) == Nat.add(Nat.mul(8n, t), k) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(8n, s), Nat.mul(8n, t)), k), Nat.add(Nat.mul(8n, s), Nat.add(Nat.mul(8n, t), k)),
      N.add_assoc(Nat.mul(8n, s), Nat.mul(8n, t), k)) :
    {Nat.sub(_, Nat.mul(8n, s)) == Nat.add(Nat.mul(8n, t), k) : Nat}
  N.sub_add_l(Nat.mul(8n, s), Nat.add(Nat.mul(8n, t), k))

law lt_sub:
  for +j: Nat
  for +r: Nat
  for +n: Nat
  for +h: {Nat.is_lt(Nat.add(j, r), n) == True{} : Bool}
  {Nat.is_lt(j, Nat.sub(n, r)) == True{} : Bool}

def lt_sub(j, r, n, h):
  match r n:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) : {Nat.is_lt(j, _) == True{} : Bool}
      %N.add_zero(j) : {Nat.is_lt(_, n) == True{} : Bool}
      h
    case 1n+q 0n:
      Empty.absurd({Nat.is_lt(j, Nat.sub(0n, 1n+q)) == True{} : Bool}, N.false_ne_true(
        Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(j, 1n+q), 0n), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(j, 1n+q), 0n), False{}, N.lt_zero(Nat.add(j, 1n+q))), h)))
    case 1n+q 1n+m:
      lt_sub(j, q, m, %N.add_succ(j, q) : {Nat.is_lt(_, 1n+m) == True{} : Bool}; h)

law le_sub_l:
  for +n: Nat
  for +r: Nat
  for +j: Nat
  for +h: {Nat.is_le(n, Nat.add(j, r)) == True{} : Bool}
  {Nat.is_le(Nat.sub(n, r), j) == True{} : Bool}

def le_sub_l(n, r, j, h):
  match n r:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) : {Nat.is_le(_, j) == True{} : Bool}
      %N.add_zero(j) : {Nat.is_le(n, _) == True{} : Bool}
      h
    case 0n 1n+q:
      N.le_zero_l(j)
    case 1n+m 1n+q:
      le_sub_l(m, q, j, %N.add_succ(j, q) : {Nat.is_le(1n+m, _) == True{} : Bool}; h)

law sub_sub_eq:
  for +j: Nat
  for +r: Nat
  for +n: Nat
  for +hr: {Nat.is_le(r, n) == True{} : Bool}
  {Nat.sub(j, Nat.sub(n, r)) == Nat.sub(Nat.add(j, r), n) : Nat}

def sub_sub_eq(j, r, n, hr):
  match r n:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) : {Nat.sub(j, _) == Nat.sub(Nat.add(j, 0n), n) : Nat}
      %Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)) : {Nat.sub(j, n) == Nat.sub(_, n) : Nat}
      {==}
    case 1n+q 0n:
      Empty.absurd({Nat.sub(j, Nat.sub(0n, 1n+q)) == Nat.sub(Nat.add(j, 1n+q), 0n) : Nat}, N.false_ne_true(hr))
    case 1n+q 1n+m:
      %Equal.sym(Nat, Nat.add(j, 1n+q), 1n+Nat.add(j, q), N.add_succ(j, q)) : {Nat.sub(j, Nat.sub(m, q)) == Nat.sub(_, 1n+m) : Nat}
      sub_sub_eq(j, q, m, hr)

# The byte laws
# =============

law to_nat_byte:
  for +w: U32
  for +j: Nat
  {U32.to_nat(D.byte(w, j)) == Nat.mod(Nat.div(U32.to_nat(w), Nat.pow(2n, Nat.mul(8n, j))), Nat.pow(2n, 8n)) : Nat}

def to_nat_byte(w, j):
  +s = Nat.mul(8n, j)
  %Equal.sym(Nat, U32.to_nat(U32.and(U32.shrn(w, s), 255)), Nat.mod(U32.to_nat(U32.shrn(w, s)), Nat.pow(2n, 8n)),
      U.to_nat_and_mask(U32.shrn(w, s), 255, 8n, {==})) :
    {_ == Nat.mod(Nat.div(U32.to_nat(w), Nat.pow(2n, s)), Nat.pow(2n, 8n)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.shrn(w, s)), Nat.div(U32.to_nat(w), Nat.pow(2n, s)), U.to_nat_shrn(w, s)) :
    {Nat.mod(_, Nat.pow(2n, 8n)) == Nat.mod(Nat.div(U32.to_nat(w), Nat.pow(2n, s)), Nat.pow(2n, 8n)) : Nat}
  {==}

law byte_lt:
  for +w: U32
  for +j: Nat
  {U32.is_lt(D.byte(w, j), 256) == True{} : Bool}

def byte_lt(w, j):
  +x = Nat.div(U32.to_nat(w), Nat.pow(2n, Nat.mul(8n, j)))
  %Equal.sym(Bool, U32.is_lt(D.byte(w, j), 256), Nat.is_lt(U32.to_nat(D.byte(w, j)), U32.to_nat(256)), U.is_lt_to_nat(D.byte(w, j), 256)) :
    {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(D.byte(w, j)), Nat.mod(x, Nat.pow(2n, 8n)), to_nat_byte(w, j)) :
    {Nat.is_lt(_, Nat.pow(2n, 8n)) == True{} : Bool}
  N.mod_lt(x, Nat.pow(2n, 8n), N.pow_pos(8n))

def byte_and.k(+a: U32, +b: U32, +j: Nat, +k: Nat) -> {D.bit(D.byte(U32.and(a, b), j), k) == D.bit(U32.and(D.byte(a, j), D.byte(b, j)), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  %Equal.sym(Bool, D.bit(D.byte(U32.and(a, b), j), k), Bool.and(l, D.bit(U32.and(a, b), i)), bit_byte(U32.and(a, b), j, k)) :
    {_ == D.bit(U32.and(D.byte(a, j), D.byte(b, j)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.and(a, b), i), Bool.and(D.bit(a, i), D.bit(b, i)), U.bit_and(a, b, i)) :
    {Bool.and(l, _) == D.bit(U32.and(D.byte(a, j), D.byte(b, j)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.and(D.byte(a, j), D.byte(b, j)), k), Bool.and(D.bit(D.byte(a, j), k), D.bit(D.byte(b, j), k)), U.bit_and(D.byte(a, j), D.byte(b, j), k)) :
    {Bool.and(l, Bool.and(D.bit(a, i), D.bit(b, i))) == _ : Bool}
  %Equal.sym(Bool, D.bit(D.byte(a, j), k), Bool.and(l, D.bit(a, i)), bit_byte(a, j, k)) :
    {Bool.and(l, Bool.and(D.bit(a, i), D.bit(b, i))) == Bool.and(_, D.bit(D.byte(b, j), k)) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(b, j), k), Bool.and(l, D.bit(b, i)), bit_byte(b, j, k)) :
    {Bool.and(l, Bool.and(D.bit(a, i), D.bit(b, i))) == Bool.and(Bool.and(l, D.bit(a, i)), _) : Bool}
  band_dist(l, D.bit(a, i), D.bit(b, i))

law byte_and:
  for +a: U32
  for +b: U32
  for +j: Nat
  {D.byte(U32.and(a, b), j) == U32.and(D.byte(a, j), D.byte(b, j)) : U32}

def byte_and(a, b, j):
  U.bit_ext(D.byte(U32.and(a, b), j), U32.and(D.byte(a, j), D.byte(b, j)), k => byte_and.k(a, b, j, k))

def byte_or.k(+a: U32, +b: U32, +j: Nat, +k: Nat) -> {D.bit(D.byte(U32.or(a, b), j), k) == D.bit(U32.or(D.byte(a, j), D.byte(b, j)), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  %Equal.sym(Bool, D.bit(D.byte(U32.or(a, b), j), k), Bool.and(l, D.bit(U32.or(a, b), i)), bit_byte(U32.or(a, b), j, k)) :
    {_ == D.bit(U32.or(D.byte(a, j), D.byte(b, j)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.or(a, b), i), Bool.or(D.bit(a, i), D.bit(b, i)), U.bit_or(a, b, i)) :
    {Bool.and(l, _) == D.bit(U32.or(D.byte(a, j), D.byte(b, j)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.or(D.byte(a, j), D.byte(b, j)), k), Bool.or(D.bit(D.byte(a, j), k), D.bit(D.byte(b, j), k)), U.bit_or(D.byte(a, j), D.byte(b, j), k)) :
    {Bool.and(l, Bool.or(D.bit(a, i), D.bit(b, i))) == _ : Bool}
  %Equal.sym(Bool, D.bit(D.byte(a, j), k), Bool.and(l, D.bit(a, i)), bit_byte(a, j, k)) :
    {Bool.and(l, Bool.or(D.bit(a, i), D.bit(b, i))) == Bool.or(_, D.bit(D.byte(b, j), k)) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(b, j), k), Bool.and(l, D.bit(b, i)), bit_byte(b, j, k)) :
    {Bool.and(l, Bool.or(D.bit(a, i), D.bit(b, i))) == Bool.or(Bool.and(l, D.bit(a, i)), _) : Bool}
  bor_dist(l, D.bit(a, i), D.bit(b, i))

law byte_or:
  for +a: U32
  for +b: U32
  for +j: Nat
  {D.byte(U32.or(a, b), j) == U32.or(D.byte(a, j), D.byte(b, j)) : U32}

def byte_or(a, b, j):
  U.bit_ext(D.byte(U32.or(a, b), j), U32.or(D.byte(a, j), D.byte(b, j)), k => byte_or.k(a, b, j, k))

def byte_xor.k(+a: U32, +b: U32, +j: Nat, +k: Nat) -> {D.bit(D.byte(U32.xor(a, b), j), k) == D.bit(U32.xor(D.byte(a, j), D.byte(b, j)), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  %Equal.sym(Bool, D.bit(D.byte(U32.xor(a, b), j), k), Bool.and(l, D.bit(U32.xor(a, b), i)), bit_byte(U32.xor(a, b), j, k)) :
    {_ == D.bit(U32.xor(D.byte(a, j), D.byte(b, j)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.xor(a, b), i), Bool.xor(D.bit(a, i), D.bit(b, i)), U.bit_xor(a, b, i)) :
    {Bool.and(l, _) == D.bit(U32.xor(D.byte(a, j), D.byte(b, j)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.xor(D.byte(a, j), D.byte(b, j)), k), Bool.xor(D.bit(D.byte(a, j), k), D.bit(D.byte(b, j), k)), U.bit_xor(D.byte(a, j), D.byte(b, j), k)) :
    {Bool.and(l, Bool.xor(D.bit(a, i), D.bit(b, i))) == _ : Bool}
  %Equal.sym(Bool, D.bit(D.byte(a, j), k), Bool.and(l, D.bit(a, i)), bit_byte(a, j, k)) :
    {Bool.and(l, Bool.xor(D.bit(a, i), D.bit(b, i))) == Bool.xor(_, D.bit(D.byte(b, j), k)) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(b, j), k), Bool.and(l, D.bit(b, i)), bit_byte(b, j, k)) :
    {Bool.and(l, Bool.xor(D.bit(a, i), D.bit(b, i))) == Bool.xor(Bool.and(l, D.bit(a, i)), _) : Bool}
  bxor_dist(l, D.bit(a, i), D.bit(b, i))

law byte_xor:
  for +a: U32
  for +b: U32
  for +j: Nat
  {D.byte(U32.xor(a, b), j) == U32.xor(D.byte(a, j), D.byte(b, j)) : U32}

def byte_xor(a, b, j):
  U.bit_ext(D.byte(U32.xor(a, b), j), U32.xor(D.byte(a, j), D.byte(b, j)), k => byte_xor.k(a, b, j, k))

def byte_not.k(+a: U32, +j: Nat, +hj: {Nat.is_lt(j, 4n) == True{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(U32.not(a), j), k) == D.bit(U32.xor(D.byte(a, j), 255), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  %Equal.sym(Bool, D.bit(D.byte(U32.not(a), j), k), Bool.and(l, D.bit(U32.not(a), i)), bit_byte(U32.not(a), j, k)) :
    {_ == D.bit(U32.xor(D.byte(a, j), 255), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.not(a), i), Bool.and(Nat.is_lt(i, 32n), Bool.not(D.bit(a, i))), U.bit_not(a, i)) :
    {Bool.and(l, _) == D.bit(U32.xor(D.byte(a, j), 255), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.xor(D.byte(a, j), 255), k), Bool.xor(D.bit(D.byte(a, j), k), D.bit(255, k)), U.bit_xor(D.byte(a, j), 255, k)) :
    {Bool.and(l, Bool.and(Nat.is_lt(i, 32n), Bool.not(D.bit(a, i)))) == _ : Bool}
  %Equal.sym(Bool, D.bit(D.byte(a, j), k), Bool.and(l, D.bit(a, i)), bit_byte(a, j, k)) :
    {Bool.and(l, Bool.and(Nat.is_lt(i, 32n), Bool.not(D.bit(a, i)))) == Bool.xor(_, D.bit(255, k)) : Bool}
  %Equal.sym(Bool, D.bit(255, k), l, bit_255(k)) :
    {Bool.and(l, Bool.and(Nat.is_lt(i, 32n), Bool.not(D.bit(a, i)))) == Bool.xor(Bool.and(l, D.bit(a, i)), _) : Bool}
  bnot_byte(l, Nat.is_lt(i, 32n), D.bit(a, i), hk => idx32(j, k, hj, hk))

law byte_not:
  for +a: U32
  for +j: Nat
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {D.byte(U32.not(a), j) == U32.xor(D.byte(a, j), 255) : U32}

def byte_not(a, j, hj):
  U.bit_ext(D.byte(U32.not(a), j), U32.xor(D.byte(a, j), 255), k => byte_not.k(a, j, hj, k))

def byte_shrn.k(+w: U32, +s: Nat, +j: Nat, +k: Nat) ->
  {D.bit(D.byte(U32.shrn(w, Nat.mul(8n, s)), j), k) == D.bit(D.byte(w, Nat.add(j, s)), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  %Equal.sym(Bool, D.bit(D.byte(U32.shrn(w, Nat.mul(8n, s)), j), k), Bool.and(l, D.bit(U32.shrn(w, Nat.mul(8n, s)), i)), bit_byte(U32.shrn(w, Nat.mul(8n, s)), j, k)) :
    {_ == D.bit(D.byte(w, Nat.add(j, s)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.shrn(w, Nat.mul(8n, s)), i), D.bit(w, Nat.add(i, Nat.mul(8n, s))), bit_shrn(w, Nat.mul(8n, s), i)) :
    {Bool.and(l, _) == D.bit(D.byte(w, Nat.add(j, s)), k) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(w, Nat.add(j, s)), k), Bool.and(l, D.bit(w, Nat.add(Nat.mul(8n, Nat.add(j, s)), k))), bit_byte(w, Nat.add(j, s), k)) :
    {Bool.and(l, D.bit(w, Nat.add(i, Nat.mul(8n, s)))) == _ : Bool}
  %idx_add(j, s, k) : {Bool.and(l, D.bit(w, Nat.add(i, Nat.mul(8n, s)))) == Bool.and(l, D.bit(w, _)) : Bool}
  {==}

law byte_shrn:
  for +w: U32
  for +s: Nat
  for +j: Nat
  {D.byte(U32.shrn(w, Nat.mul(8n, s)), j) == D.byte(w, Nat.add(j, s)) : U32}

def byte_shrn(w, s, j):
  U.bit_ext(D.byte(U32.shrn(w, Nat.mul(8n, s)), j), D.byte(w, Nat.add(j, s)), k => byte_shrn.k(w, s, j, k))

def byte_shln_low.k(+w: U32, +s: Nat, +j: Nat, +hj: {Nat.is_lt(j, s) == True{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(U32.shln(w, Nat.mul(8n, s)), j), k) == D.bit(0, k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  +s8 = Nat.mul(8n, s)
  %Equal.sym(Bool, D.bit(D.byte(U32.shln(w, s8), j), k), Bool.and(l, D.bit(U32.shln(w, s8), i)), bit_byte(U32.shln(w, s8), j, k)) :
    {_ == D.bit(0, k) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(w, s8), i), Bool.and(Nat.is_le(s8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(w, Nat.sub(i, s8)))), bit_shln(w, s8, i)) :
    {Bool.and(l, _) == D.bit(0, k) : Bool}
  %Equal.sym(Bool, D.bit(0, k), False{}, bit_zero(k)) :
    {Bool.and(l, Bool.and(Nat.is_le(s8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(w, Nat.sub(i, s8))))) == _ : Bool}
  blow(l, Nat.is_le(s8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(w, Nat.sub(i, s8))),
    hk => lt_not_le(i, s8, N.lt_le_trans(i, Nat.mul(8n, 1n+j), s8, lt_mul8(j, k, hk),
      N.le_mul_l(8n, 1n+j, s, %Equal.sym(Bool, Nat.is_le(1n+j, s), Nat.is_lt(j, s), N.le_succ_lt(j, s)) : {_ == True{} : Bool}; hj))))

law byte_shln_low:
  for +w: U32
  for +s: Nat
  for +j: Nat
  for +hj: {Nat.is_lt(j, s) == True{} : Bool}
  {D.byte(U32.shln(w, Nat.mul(8n, s)), j) == 0 : U32}

def byte_shln_low(w, s, j, hj):
  U.bit_ext(D.byte(U32.shln(w, Nat.mul(8n, s)), j), 0, k => byte_shln_low.k(w, s, j, hj, k))

def byte_shln_high.k(+w: U32, +s: Nat, +j: Nat, +hs: {Nat.is_le(s, j) == True{} : Bool}, +hj: {Nat.is_lt(j, 4n) == True{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(U32.shln(w, Nat.mul(8n, s)), j), k) == D.bit(D.byte(w, Nat.sub(j, s)), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  +s8 = Nat.mul(8n, s)
  +x = D.bit(w, Nat.add(Nat.mul(8n, Nat.sub(j, s)), k))
  %Equal.sym(Bool, D.bit(D.byte(U32.shln(w, s8), j), k), Bool.and(l, D.bit(U32.shln(w, s8), i)), bit_byte(U32.shln(w, s8), j, k)) :
    {_ == D.bit(D.byte(w, Nat.sub(j, s)), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(w, s8), i), Bool.and(Nat.is_le(s8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(w, Nat.sub(i, s8)))), bit_shln(w, s8, i)) :
    {Bool.and(l, _) == D.bit(D.byte(w, Nat.sub(j, s)), k) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(w, Nat.sub(j, s)), k), Bool.and(l, x), bit_byte(w, Nat.sub(j, s), k)) :
    {Bool.and(l, Bool.and(Nat.is_le(s8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(w, Nat.sub(i, s8))))) == _ : Bool}
  %Equal.sym(Bool, Nat.is_le(s8, i), True{}, N.le_trans(s8, Nat.mul(8n, j), i, N.le_mul_l(8n, s, j, hs), N.le_add_r(Nat.mul(8n, j), k))) :
    {Bool.and(l, Bool.and(_, Bool.and(Nat.is_lt(i, 32n), D.bit(w, Nat.sub(i, s8))))) == Bool.and(l, x) : Bool}
  %Equal.sym(Nat, Nat.sub(i, s8), Nat.add(Nat.mul(8n, Nat.sub(j, s)), k), idx_sub(s, j, k, hs)) :
    {Bool.and(l, Bool.and(True{}, Bool.and(Nat.is_lt(i, 32n), D.bit(w, _)))) == Bool.and(l, x) : Bool}
  bimp(l, Nat.is_lt(i, 32n), x, hk => idx32(j, k, hj, hk))

law byte_shln_high:
  for +w: U32
  for +s: Nat
  for +j: Nat
  for +hs: {Nat.is_le(s, j) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {D.byte(U32.shln(w, Nat.mul(8n, s)), j) == D.byte(w, Nat.sub(j, s)) : U32}

def byte_shln_high(w, s, j, hs, hj):
  U.bit_ext(D.byte(U32.shln(w, Nat.mul(8n, s)), j), D.byte(w, Nat.sub(j, s)), k => byte_shln_high.k(w, s, j, hs, hj, k))

# The bits of a merged word, at byte j, bit k.
law bit_merge:
  for +lo: U32
  for +hi: U32
  for +r: Nat
  for +j: Nat
  for +k: Nat
  {D.bit(D.byte(D.merge(lo, hi, r), j), k) == Bool.and(Nat.is_lt(k, 8n), Bool.or(D.bit(lo, Nat.add(Nat.add(Nat.mul(8n, j), k), Nat.mul(8n, r))),
    Bool.and(Nat.is_le(Nat.mul(8n, Nat.sub(4n, r)), Nat.add(Nat.mul(8n, j), k)), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n),
      D.bit(hi, Nat.sub(Nat.add(Nat.mul(8n, j), k), Nat.mul(8n, Nat.sub(4n, r)))))))) : Bool}

def bit_merge(lo, hi, r, j, k):
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  +r8 = Nat.mul(8n, r)
  +u8 = Nat.mul(8n, Nat.sub(4n, r))
  %Equal.sym(Bool, D.bit(D.byte(D.merge(lo, hi, r), j), k), Bool.and(l, D.bit(D.merge(lo, hi, r), i)), bit_byte(D.merge(lo, hi, r), j, k)) :
    {_ == Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))) : Bool}
  %Equal.sym(Bool, D.bit(U32.or(U32.shrn(lo, r8), U32.shln(hi, u8)), i), Bool.or(D.bit(U32.shrn(lo, r8), i), D.bit(U32.shln(hi, u8), i)), U.bit_or(U32.shrn(lo, r8), U32.shln(hi, u8), i)) :
    {Bool.and(l, _) == Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))) : Bool}
  %Equal.sym(Bool, D.bit(U32.shrn(lo, r8), i), D.bit(lo, Nat.add(i, r8)), bit_shrn(lo, r8, i)) :
    {Bool.and(l, Bool.or(_, D.bit(U32.shln(hi, u8), i))) == Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(hi, u8), i), Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))), bit_shln(hi, u8, i)) :
    {Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), _)) == Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))) : Bool}
  {==}

def byte_merge_lo.k(+lo: U32, +hi: U32, +r: Nat, +j: Nat, +h: {Nat.is_lt(Nat.add(j, r), 4n) == True{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(D.merge(lo, hi, r), j), k) == D.bit(D.byte(lo, Nat.add(j, r)), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  +r8 = Nat.mul(8n, r)
  +u8 = Nat.mul(8n, Nat.sub(4n, r))
  +y = Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))
  %Equal.sym(Bool, D.bit(D.byte(D.merge(lo, hi, r), j), k), Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), y))), bit_merge(lo, hi, r, j, k)) :
    {_ == D.bit(D.byte(lo, Nat.add(j, r)), k) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(lo, Nat.add(j, r)), k), Bool.and(l, D.bit(lo, Nat.add(Nat.mul(8n, Nat.add(j, r)), k))), bit_byte(lo, Nat.add(j, r), k)) :
    {Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), y))) == _ : Bool}
  %idx_add(j, r, k) : {Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), y))) == Bool.and(l, D.bit(lo, _)) : Bool}
  bor_low(l, D.bit(lo, Nat.add(i, r8)), Nat.is_le(u8, i), y,
    hk => lt_not_le(i, u8, N.lt_le_trans(i, Nat.mul(8n, 1n+j), u8, lt_mul8(j, k, hk),
      N.le_mul_l(8n, 1n+j, Nat.sub(4n, r), %Equal.sym(Bool, Nat.is_le(1n+j, Nat.sub(4n, r)), Nat.is_lt(j, Nat.sub(4n, r)), N.le_succ_lt(j, Nat.sub(4n, r))) : {_ == True{} : Bool};
        lt_sub(j, r, 4n, h)))))

law byte_merge_lo:
  for +lo: U32
  for +hi: U32
  for +r: Nat
  for +j: Nat
  for +h: {Nat.is_lt(Nat.add(j, r), 4n) == True{} : Bool}
  {D.byte(D.merge(lo, hi, r), j) == D.byte(lo, Nat.add(j, r)) : U32}

def byte_merge_lo(lo, hi, r, j, h):
  U.bit_ext(D.byte(D.merge(lo, hi, r), j), D.byte(lo, Nat.add(j, r)), k => byte_merge_lo.k(lo, hi, r, j, h, k))

def byte_merge_hi.k(+lo: U32, +hi: U32, +r: Nat, +j: Nat, +hr: {Nat.is_le(r, 4n) == True{} : Bool}, +hj: {Nat.is_lt(j, 4n) == True{} : Bool},
  +h: {Nat.is_le(4n, Nat.add(j, r)) == True{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(D.merge(lo, hi, r), j), k) == D.bit(D.byte(hi, Nat.sub(Nat.add(j, r), 4n)), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +i = Nat.add(Nat.mul(8n, j), k)
  +r8 = Nat.mul(8n, r)
  +u = Nat.sub(4n, r)
  +u8 = Nat.mul(8n, u)
  +hu = le_sub_l(4n, r, j, h)
  +x = D.bit(hi, Nat.add(Nat.mul(8n, Nat.sub(Nat.add(j, r), 4n)), k))
  %Equal.sym(Bool, D.bit(D.byte(D.merge(lo, hi, r), j), k),
      Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))), bit_merge(lo, hi, r, j, k)) :
    {_ == D.bit(D.byte(hi, Nat.sub(Nat.add(j, r), 4n)), k) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(hi, Nat.sub(Nat.add(j, r), 4n)), k), Bool.and(l, x), bit_byte(hi, Nat.sub(Nat.add(j, r), 4n), k)) :
    {Bool.and(l, Bool.or(D.bit(lo, Nat.add(i, r8)), Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))) == _ : Bool}
  %Equal.sym(Bool, D.bit(lo, Nat.add(i, r8)), False{}, bit_ge32(lo, Nat.add(i, r8),
      %Equal.sym(Nat, Nat.add(i, r8), Nat.add(Nat.mul(8n, Nat.add(j, r)), k), idx_add(j, r, k)) : {Nat.is_le(32n, _) == True{} : Bool}
      N.le_trans(32n, Nat.mul(8n, Nat.add(j, r)), Nat.add(Nat.mul(8n, Nat.add(j, r)), k), N.le_mul_l(8n, 4n, Nat.add(j, r), h), N.le_add_r(Nat.mul(8n, Nat.add(j, r)), k)))) :
    {Bool.and(l, Bool.or(_, Bool.and(Nat.is_le(u8, i), Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))) == Bool.and(l, x) : Bool}
  %Equal.sym(Bool, Nat.is_le(u8, i), True{}, N.le_trans(u8, Nat.mul(8n, j), i, N.le_mul_l(8n, u, j, hu), N.le_add_r(Nat.mul(8n, j), k))) :
    {Bool.and(l, Bool.or(False{}, Bool.and(_, Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.sub(i, u8)))))) == Bool.and(l, x) : Bool}
  %Equal.sym(Nat, Nat.sub(i, u8), Nat.add(Nat.mul(8n, Nat.sub(j, u)), k), idx_sub(u, j, k, hu)) :
    {Bool.and(l, Bool.or(False{}, Bool.and(True{}, Bool.and(Nat.is_lt(i, 32n), D.bit(hi, _))))) == Bool.and(l, x) : Bool}
  %Equal.sym(Nat, Nat.sub(j, u), Nat.sub(Nat.add(j, r), 4n), sub_sub_eq(j, r, 4n, hr)) :
    {Bool.and(l, Bool.or(False{}, Bool.and(True{}, Bool.and(Nat.is_lt(i, 32n), D.bit(hi, Nat.add(Nat.mul(8n, _), k)))))) == Bool.and(l, x) : Bool}
  bimp(l, Nat.is_lt(i, 32n), x, hk => idx32(j, k, hj, hk))

law byte_merge_hi:
  for +lo: U32
  for +hi: U32
  for +r: Nat
  for +j: Nat
  for +hr: {Nat.is_le(r, 4n) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +h: {Nat.is_le(4n, Nat.add(j, r)) == True{} : Bool}
  {D.byte(D.merge(lo, hi, r), j) == D.byte(hi, Nat.sub(Nat.add(j, r), 4n)) : U32}

def byte_merge_hi(lo, hi, r, j, hr, hj, h):
  U.bit_ext(D.byte(D.merge(lo, hi, r), j), D.byte(hi, Nat.sub(Nat.add(j, r), 4n)), k => byte_merge_hi.k(lo, hi, r, j, hr, hj, h, k))

# The bits of put_byte(w, j, b) at byte j, bit k.
def byte_put_same.k(+w: U32, +j: Nat, +b: U32, +hj: {Nat.is_lt(j, 4n) == True{} : Bool}, +hb: {U32.is_lt(b, 256) == True{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(D.put_byte(w, j, b), j), k) == D.bit(b, k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +s = Nat.mul(8n, j)
  +i = Nat.add(s, k)
  +m = U32.shln(255, s)
  +ii = Nat.is_lt(i, 32n)
  %Equal.sym(Bool, D.bit(D.byte(D.put_byte(w, j, b), j), k), Bool.and(l, D.bit(D.put_byte(w, j, b), i)), bit_byte(D.put_byte(w, j, b), j, k)) :
    {_ == D.bit(b, k) : Bool}
  %Equal.sym(Bool, D.bit(U32.or(U32.and(w, U32.not(m)), U32.shln(b, s)), i), Bool.or(D.bit(U32.and(w, U32.not(m)), i), D.bit(U32.shln(b, s), i)),
      U.bit_or(U32.and(w, U32.not(m)), U32.shln(b, s), i)) :
    {Bool.and(l, _) == D.bit(b, k) : Bool}
  %Equal.sym(Bool, D.bit(U32.and(w, U32.not(m)), i), Bool.and(D.bit(w, i), D.bit(U32.not(m), i)), U.bit_and(w, U32.not(m), i)) :
    {Bool.and(l, Bool.or(_, D.bit(U32.shln(b, s), i))) == D.bit(b, k) : Bool}
  %Equal.sym(Bool, D.bit(U32.not(m), i), Bool.and(ii, Bool.not(D.bit(m, i))), U.bit_not(m, i)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, i), _), D.bit(U32.shln(b, s), i))) == D.bit(b, k) : Bool}
  %Equal.sym(Bool, D.bit(m, i), Bool.and(Nat.is_le(s, i), Bool.and(ii, D.bit(255, Nat.sub(i, s)))), bit_shln(255, s, i)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, i), Bool.and(ii, Bool.not(_))), D.bit(U32.shln(b, s), i))) == D.bit(b, k) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(b, s), i), Bool.and(Nat.is_le(s, i), Bool.and(ii, D.bit(b, Nat.sub(i, s)))), bit_shln(b, s, i)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, i), Bool.and(ii, Bool.not(Bool.and(Nat.is_le(s, i), Bool.and(ii, D.bit(255, Nat.sub(i, s))))))), _)) == D.bit(b, k) : Bool}
  %Equal.sym(Bool, Nat.is_le(s, i), True{}, N.le_add_r(s, k)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, i), Bool.and(ii, Bool.not(Bool.and(_, Bool.and(ii, D.bit(255, Nat.sub(i, s))))))),
      Bool.and(_, Bool.and(ii, D.bit(b, Nat.sub(i, s)))))) == D.bit(b, k) : Bool}
  %Equal.sym(Nat, Nat.sub(i, s), k, N.sub_add_l(s, k)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, i), Bool.and(ii, Bool.not(Bool.and(True{}, Bool.and(ii, D.bit(255, _)))))),
      Bool.and(True{}, Bool.and(ii, D.bit(b, _))))) == D.bit(b, k) : Bool}
  %Equal.sym(Bool, D.bit(255, k), l, bit_255(k)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, i), Bool.and(ii, Bool.not(Bool.and(True{}, Bool.and(ii, _))))),
      Bool.and(True{}, Bool.and(ii, D.bit(b, k))))) == D.bit(b, k) : Bool}
  put_bits(l, ii, D.bit(w, i), D.bit(b, k), hk => idx32(j, k, hj, hk),
    e => bit_lt_pow(b, 8n, k, %U.is_lt_to_nat(b, 256) : {_ == True{} : Bool}; hb, N.not_lt_le(k, 8n, e)))

law byte_put_same:
  for +w: U32
  for +j: Nat
  for +b: U32
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +hb: {U32.is_lt(b, 256) == True{} : Bool}
  {D.byte(D.put_byte(w, j, b), j) == b : U32}

def byte_put_same(w, j, b, hj, hb):
  U.bit_ext(D.byte(D.put_byte(w, j, b), j), b, k => byte_put_same.k(w, j, b, hj, hb, k))

law other_bits:
  for +l: Bool
  for +g: Bool
  for +ii: Bool
  for +w: Bool
  for +z1: Bool
  for +z2: Bool
  for imp1: {l == True{} : Bool} -> {g == True{} : Bool} -> {z1 == False{} : Bool}
  for imp2: {l == True{} : Bool} -> {g == True{} : Bool} -> {z2 == False{} : Bool}
  {Bool.and(l, Bool.or(Bool.and(w, Bool.and(ii, Bool.not(Bool.and(g, Bool.and(ii, z1))))), Bool.and(g, Bool.and(ii, z2)))) == Bool.and(l, Bool.and(ii, w)) : Bool}

def other_bits(l, g, ii, w, z1, z2, imp1, imp2):
  match l g ii w:
    case False{} _ _ _:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{}:
      %Equal.sym(Bool, z1, False{}, imp1({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(True{}, Bool.and(True{}, Bool.not(Bool.and(True{}, Bool.and(True{}, _))))), Bool.and(True{}, Bool.and(True{}, z2)))) == Bool.and(True{}, Bool.and(True{}, True{})) : Bool}
      %Equal.sym(Bool, z2, False{}, imp2({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(True{}, Bool.and(True{}, Bool.not(Bool.and(True{}, Bool.and(True{}, False{}))))), Bool.and(True{}, Bool.and(True{}, _)))) == Bool.and(True{}, Bool.and(True{}, True{})) : Bool}
      {==}
    case True{} True{} True{} False{}:
      %Equal.sym(Bool, z1, False{}, imp1({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(False{}, Bool.and(True{}, Bool.not(Bool.and(True{}, Bool.and(True{}, _))))), Bool.and(True{}, Bool.and(True{}, z2)))) == Bool.and(True{}, Bool.and(True{}, False{})) : Bool}
      %Equal.sym(Bool, z2, False{}, imp2({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(False{}, Bool.and(True{}, Bool.not(Bool.and(True{}, Bool.and(True{}, False{}))))), Bool.and(True{}, Bool.and(True{}, _)))) == Bool.and(True{}, Bool.and(True{}, False{})) : Bool}
      {==}
    case True{} True{} False{} True{}:
      %Equal.sym(Bool, z1, False{}, imp1({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(True{}, Bool.and(False{}, Bool.not(Bool.and(True{}, Bool.and(False{}, _))))), Bool.and(True{}, Bool.and(False{}, z2)))) == Bool.and(True{}, Bool.and(False{}, True{})) : Bool}
      %Equal.sym(Bool, z2, False{}, imp2({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(True{}, Bool.and(False{}, Bool.not(Bool.and(True{}, Bool.and(False{}, False{}))))), Bool.and(True{}, Bool.and(False{}, _)))) == Bool.and(True{}, Bool.and(False{}, True{})) : Bool}
      {==}
    case True{} True{} False{} False{}:
      %Equal.sym(Bool, z1, False{}, imp1({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(False{}, Bool.and(False{}, Bool.not(Bool.and(True{}, Bool.and(False{}, _))))), Bool.and(True{}, Bool.and(False{}, z2)))) == Bool.and(True{}, Bool.and(False{}, False{})) : Bool}
      %Equal.sym(Bool, z2, False{}, imp2({==})({==})) :
        {Bool.and(True{}, Bool.or(Bool.and(False{}, Bool.and(False{}, Bool.not(Bool.and(True{}, Bool.and(False{}, False{}))))), Bool.and(True{}, Bool.and(False{}, _)))) == Bool.and(True{}, Bool.and(False{}, False{})) : Bool}
      {==}

# Byte i of a word whose byte j (j != i) was set: bit k < 8 is beyond byte j.
law other_idx:
  for +i: Nat
  for +j: Nat
  for +k: Nat
  for +hk: {Nat.is_lt(k, 8n) == True{} : Bool}
  for +hg: {Nat.is_le(Nat.mul(8n, j), Nat.add(Nat.mul(8n, i), k)) == True{} : Bool}
  for +hne: {Nat.is_eq(i, j) == False{} : Bool}
  {Nat.is_le(8n, Nat.sub(Nat.add(Nat.mul(8n, i), k), Nat.mul(8n, j))) == True{} : Bool}

def other_idx(i, j, k, hk, hg, hne):
  +p = Nat.add(Nat.mul(8n, i), k)
  +hb = N.lt_mul_cancel(8n, j, 1n+i, N.le_lt_trans(Nat.mul(8n, j), p, Nat.mul(8n, 1n+i), hg, lt_mul8(i, k, hk)))
  +hc = {%N.lt_succ_iff(j, i) : {_ == True{} : Bool}; hb : {Nat.is_le(j, i) == True{} : Bool}}
  +hd = N.le_ne(j, i, hc, %N.eq_comm(i, j) : {_ == False{} : Bool}; hne)
  N.le_sub_r(Nat.mul(8n, j), 8n, p,
    %Equal.trans(Nat, Nat.mul(8n, 1n+j), Nat.add(8n, Nat.mul(8n, j)), Nat.add(Nat.mul(8n, j), 8n), N.mul_succ_r(8n, j), N.add_comm(8n, Nat.mul(8n, j))) :
      {Nat.is_le(_, p) == True{} : Bool}
    N.le_trans(Nat.mul(8n, 1n+j), Nat.mul(8n, i), p, N.le_mul_l(8n, 1n+j, i, hd), N.le_add_r(Nat.mul(8n, i), k)))

def byte_put_other.k(+w: U32, +i: Nat, +j: Nat, +b: U32, +hb: {U32.is_lt(b, 256) == True{} : Bool}, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(D.put_byte(w, j, b), i), k) == D.bit(D.byte(w, i), k) : Bool}:
  +l = Nat.is_lt(k, 8n)
  +s = Nat.mul(8n, j)
  +p = Nat.add(Nat.mul(8n, i), k)
  +m = U32.shln(255, s)
  +ii = Nat.is_lt(p, 32n)
  +g = Nat.is_le(s, p)
  %Equal.sym(Bool, D.bit(D.byte(D.put_byte(w, j, b), i), k), Bool.and(l, D.bit(D.put_byte(w, j, b), p)), bit_byte(D.put_byte(w, j, b), i, k)) :
    {_ == D.bit(D.byte(w, i), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.or(U32.and(w, U32.not(m)), U32.shln(b, s)), p), Bool.or(D.bit(U32.and(w, U32.not(m)), p), D.bit(U32.shln(b, s), p)),
      U.bit_or(U32.and(w, U32.not(m)), U32.shln(b, s), p)) :
    {Bool.and(l, _) == D.bit(D.byte(w, i), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.and(w, U32.not(m)), p), Bool.and(D.bit(w, p), D.bit(U32.not(m), p)), U.bit_and(w, U32.not(m), p)) :
    {Bool.and(l, Bool.or(_, D.bit(U32.shln(b, s), p))) == D.bit(D.byte(w, i), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.not(m), p), Bool.and(ii, Bool.not(D.bit(m, p))), U.bit_not(m, p)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, p), _), D.bit(U32.shln(b, s), p))) == D.bit(D.byte(w, i), k) : Bool}
  %Equal.sym(Bool, D.bit(m, p), Bool.and(g, Bool.and(ii, D.bit(255, Nat.sub(p, s)))), bit_shln(255, s, p)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, p), Bool.and(ii, Bool.not(_))), D.bit(U32.shln(b, s), p))) == D.bit(D.byte(w, i), k) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(b, s), p), Bool.and(g, Bool.and(ii, D.bit(b, Nat.sub(p, s)))), bit_shln(b, s, p)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, p), Bool.and(ii, Bool.not(Bool.and(g, Bool.and(ii, D.bit(255, Nat.sub(p, s))))))), _)) == D.bit(D.byte(w, i), k) : Bool}
  %Equal.sym(Bool, D.bit(255, Nat.sub(p, s)), Nat.is_lt(Nat.sub(p, s), 8n), bit_255(Nat.sub(p, s))) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, p), Bool.and(ii, Bool.not(Bool.and(g, Bool.and(ii, _))))), Bool.and(g, Bool.and(ii, D.bit(b, Nat.sub(p, s)))))) == D.bit(D.byte(w, i), k) : Bool}
  %Equal.sym(Bool, D.bit(D.byte(w, i), k), Bool.and(l, D.bit(w, p)), bit_byte(w, i, k)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, p), Bool.and(ii, Bool.not(Bool.and(g, Bool.and(ii, Nat.is_lt(Nat.sub(p, s), 8n)))))), Bool.and(g, Bool.and(ii, D.bit(b, Nat.sub(p, s)))))) == _ : Bool}
  %Equal.sym(Bool, D.bit(w, p), Bool.and(ii, D.bit(w, p)), bit_lt32(w, p)) :
    {Bool.and(l, Bool.or(Bool.and(D.bit(w, p), Bool.and(ii, Bool.not(Bool.and(g, Bool.and(ii, Nat.is_lt(Nat.sub(p, s), 8n)))))), Bool.and(g, Bool.and(ii, D.bit(b, Nat.sub(p, s)))))) == Bool.and(l, _) : Bool}
  other_bits(l, g, ii, D.bit(w, p), Nat.is_lt(Nat.sub(p, s), 8n), D.bit(b, Nat.sub(p, s)),
    hl => hg => N.le_not_lt(8n, Nat.sub(p, s), other_idx(i, j, k, hl, hg, hij)),
    hl => hg => bit_lt_pow(b, 8n, Nat.sub(p, s), %U.is_lt_to_nat(b, 256) : {_ == True{} : Bool}; hb, other_idx(i, j, k, hl, hg, hij)))

law byte_put_other:
  for +w: U32
  for +i: Nat
  for +j: Nat
  for +b: U32
  for +hb: {U32.is_lt(b, 256) == True{} : Bool}
  for +hij: {Nat.is_eq(i, j) == False{} : Bool}
  {D.byte(D.put_byte(w, j, b), i) == D.byte(w, i) : U32}

def byte_put_other(w, i, j, b, hb, hij):
  U.bit_ext(D.byte(D.put_byte(w, j, b), i), D.byte(w, i), k => byte_put_other.k(w, i, j, b, hb, hij, k))

# Packing
# =======

def Cmp.disc_gt(c: Cmp) -> Type:
  match c:
    case GT{}:
      Empty
    case o:
      Unit

def lt_ne_gt(e: {LT{} == GT{} : Cmp}) -> Empty:
  %e : Cmp.disc_gt(_)
  Unit{}

law gt_flip:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.is_lt(b, a) == True{} : Bool}

def gt_flip(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, W.gt_ne_eq(Equal.sym(Cmp, EQ{}, GT{}, h)))
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, lt_ne_gt(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gt_flip(p, q, h)

# Bit k of byte J of b << 8X, for b < 256 and k < 8: bit k of b when J = X.
def bsel.go(+b: U32, +x: Nat, +j: Nat, +k: Nat, +hb: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, 8n)) == True{} : Bool},
  +hk: {Nat.is_lt(k, 8n) == True{} : Bool}, c: Cmp, +ec: {Nat.cmp(j, x) == c : Cmp}) ->
  {Bool.and(Nat.is_le(Nat.mul(8n, x), Nat.add(Nat.mul(8n, j), k)), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n),
     D.bit(b, Nat.sub(Nat.add(Nat.mul(8n, j), k), Nat.mul(8n, x)))))
   == Bool.and(Nat.is_eq(j, x), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n), D.bit(b, k))) : Bool}:
  match c:
    case LT{}:
      +p = Nat.add(Nat.mul(8n, j), k)
      +ii = Nat.is_lt(p, 32n)
      +hlt = {%Equal.sym(Cmp, Nat.cmp(j, x), LT{}, ec) : {Cmp.is_lt(_) == True{} : Bool}; {==} : {Nat.is_lt(j, x) == True{} : Bool}}
      %Equal.sym(Bool, Nat.is_le(Nat.mul(8n, x), p), False{}, lt_not_le(p, Nat.mul(8n, x), N.lt_le_trans(p, Nat.mul(8n, 1n+j), Nat.mul(8n, x), lt_mul8(j, k, hk),
          N.le_mul_l(8n, 1n+j, x, %Equal.sym(Bool, Nat.is_le(1n+j, x), Nat.is_lt(j, x), N.le_succ_lt(j, x)) : {_ == True{} : Bool}; hlt)))) :
        {Bool.and(_, Bool.and(ii, D.bit(b, Nat.sub(p, Nat.mul(8n, x))))) == Bool.and(Nat.is_eq(j, x), Bool.and(ii, D.bit(b, k))) : Bool}
      %Equal.sym(Cmp, Nat.cmp(j, x), LT{}, ec) : {False{} == Bool.and(Cmp.is_eq(_), Bool.and(ii, D.bit(b, k))) : Bool}
      {==}
    case EQ{}:
      +hjx = N.eq_sound(j, x, %Equal.sym(Cmp, Nat.cmp(j, x), EQ{}, ec) : {Cmp.is_eq(_) == True{} : Bool}; {==})
      +p = Nat.add(Nat.mul(8n, j), k)
      +ii = Nat.is_lt(p, 32n)
      %hjx : {Bool.and(Nat.is_le(Nat.mul(8n, _), p), Bool.and(ii, D.bit(b, Nat.sub(p, Nat.mul(8n, _))))) == Bool.and(Nat.is_eq(j, _), Bool.and(ii, D.bit(b, k))) : Bool}
      %Equal.sym(Bool, Nat.is_le(Nat.mul(8n, j), p), True{}, N.le_add_r(Nat.mul(8n, j), k)) :
        {Bool.and(_, Bool.and(ii, D.bit(b, Nat.sub(p, Nat.mul(8n, j))))) == Bool.and(Nat.is_eq(j, j), Bool.and(ii, D.bit(b, k))) : Bool}
      %Equal.sym(Nat, Nat.sub(p, Nat.mul(8n, j)), k, N.sub_add_l(Nat.mul(8n, j), k)) :
        {Bool.and(True{}, Bool.and(ii, D.bit(b, _))) == Bool.and(Nat.is_eq(j, j), Bool.and(ii, D.bit(b, k))) : Bool}
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, N.eq_refl(j)) :
        {Bool.and(True{}, Bool.and(ii, D.bit(b, k))) == Bool.and(_, Bool.and(ii, D.bit(b, k))) : Bool}
      {==}
    case GT{}:
      +p = Nat.add(Nat.mul(8n, j), k)
      +ii = Nat.is_lt(p, 32n)
      +hxj = gt_flip(j, x, ec)
      +hle = N.lt_to_le(x, j, hxj)
      +q = Nat.add(Nat.mul(8n, Nat.sub(j, x)), k)
      %Equal.sym(Bool, Nat.is_le(Nat.mul(8n, x), p), True{}, N.le_trans(Nat.mul(8n, x), Nat.mul(8n, j), p, N.le_mul_l(8n, x, j, hle), N.le_add_r(Nat.mul(8n, j), k))) :
        {Bool.and(_, Bool.and(ii, D.bit(b, Nat.sub(p, Nat.mul(8n, x))))) == Bool.and(Nat.is_eq(j, x), Bool.and(ii, D.bit(b, k))) : Bool}
      %Equal.sym(Nat, Nat.sub(p, Nat.mul(8n, x)), q, idx_sub(x, j, k, hle)) :
        {Bool.and(True{}, Bool.and(ii, D.bit(b, _))) == Bool.and(Nat.is_eq(j, x), Bool.and(ii, D.bit(b, k))) : Bool}
      %Equal.sym(Bool, D.bit(b, q), False{}, bit_lt_pow(b, 8n, q, hb,
          N.le_trans(8n, Nat.mul(8n, Nat.sub(j, x)), q,
            N.le_mul_l(8n, 1n, Nat.sub(j, x), %Equal.sym(Bool, Nat.is_le(1n, Nat.sub(j, x)), Nat.is_lt(0n, Nat.sub(j, x)), N.le_succ_lt(0n, Nat.sub(j, x))) : {_ == True{} : Bool};
              lt_sub(0n, x, j, hxj)),
            N.le_add_r(Nat.mul(8n, Nat.sub(j, x)), k)))) :
        {Bool.and(True{}, Bool.and(ii, _)) == Bool.and(Nat.is_eq(j, x), Bool.and(ii, D.bit(b, k))) : Bool}
      %Equal.sym(Cmp, Nat.cmp(j, x), GT{}, ec) : {Bool.and(ii, False{}) == Bool.and(Cmp.is_eq(_), Bool.and(ii, D.bit(b, k))) : Bool}
      N.and_false_r(ii)

law bsel:
  for +b: U32
  for +x: Nat
  for +j: Nat
  for +k: Nat
  for +hb: {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, 8n)) == True{} : Bool}
  for +hk: {Nat.is_lt(k, 8n) == True{} : Bool}
  {D.bit(U32.shln(b, Nat.mul(8n, x)), Nat.add(Nat.mul(8n, j), k))
    == Bool.and(Nat.is_eq(j, x), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n), D.bit(b, k))) : Bool}

def bsel(b, x, j, k, hb, hk):
  +p = Nat.add(Nat.mul(8n, j), k)
  %Equal.sym(Bool, D.bit(U32.shln(b, Nat.mul(8n, x)), p), Bool.and(Nat.is_le(Nat.mul(8n, x), p), Bool.and(Nat.is_lt(p, 32n), D.bit(b, Nat.sub(p, Nat.mul(8n, x))))),
      bit_shln(b, Nat.mul(8n, x), p)) :
    {_ == Bool.and(Nat.is_eq(j, x), Bool.and(Nat.is_lt(p, 32n), D.bit(b, k))) : Bool}
  bsel.go(b, x, j, k, hb, hk, Nat.cmp(j, x), {==})

# A U32 test b < 256 as numbers.
law lt256:
  for +b: U32
  for +h: {U32.is_lt(b, 256) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(b), Nat.pow(2n, 8n)) == True{} : Bool}

def lt256(b, h):
  %U.is_lt_to_nat(b, 256) : {_ == True{} : Bool}
  h

# Bit k (k < 8) of byte j of pack4(b0, b1, b2, b3).
law pack_bits:
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +j: Nat
  for +k: Nat
  for +h0: {Nat.is_lt(U32.to_nat(b0), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h1: {Nat.is_lt(U32.to_nat(b1), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h2: {Nat.is_lt(U32.to_nat(b2), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h3: {Nat.is_lt(U32.to_nat(b3), Nat.pow(2n, 8n)) == True{} : Bool}
  for +hk: {Nat.is_lt(k, 8n) == True{} : Bool}
  {D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, j), k)) ==
    Bool.or(Bool.and(Nat.is_eq(j, 0n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n), D.bit(b0, k))),
    Bool.or(Bool.and(Nat.is_eq(j, 1n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n), D.bit(b1, k))),
    Bool.or(Bool.and(Nat.is_eq(j, 2n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n), D.bit(b2, k))),
            Bool.and(Nat.is_eq(j, 3n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, j), k), 32n), D.bit(b3, k)))))) : Bool}

def pack_bits(b0, b1, b2, b3, j, k, h0, h1, h2, h3, hk):
  +p = Nat.add(Nat.mul(8n, j), k)
  +ii = Nat.is_lt(p, 32n)
  +a0 = Bool.and(Nat.is_eq(j, 0n), Bool.and(ii, D.bit(b0, k)))
  +a1 = Bool.and(Nat.is_eq(j, 1n), Bool.and(ii, D.bit(b1, k)))
  +a2 = Bool.and(Nat.is_eq(j, 2n), Bool.and(ii, D.bit(b2, k)))
  +a3 = Bool.and(Nat.is_eq(j, 3n), Bool.and(ii, D.bit(b3, k)))
  +r2 = U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n))
  +r1 = U32.or(U32.shln(b1, 8n), r2)
  %Equal.sym(Bool, D.bit(U32.or(b0, r1), p), Bool.or(D.bit(b0, p), D.bit(r1, p)), U.bit_or(b0, r1, p)) :
    {_ == Bool.or(a0, Bool.or(a1, Bool.or(a2, a3))) : Bool}
  %Equal.sym(Bool, D.bit(r1, p), Bool.or(D.bit(U32.shln(b1, 8n), p), D.bit(r2, p)), U.bit_or(U32.shln(b1, 8n), r2, p)) :
    {Bool.or(D.bit(b0, p), _) == Bool.or(a0, Bool.or(a1, Bool.or(a2, a3))) : Bool}
  %Equal.sym(Bool, D.bit(r2, p), Bool.or(D.bit(U32.shln(b2, 16n), p), D.bit(U32.shln(b3, 24n), p)), U.bit_or(U32.shln(b2, 16n), U32.shln(b3, 24n), p)) :
    {Bool.or(D.bit(b0, p), Bool.or(D.bit(U32.shln(b1, 8n), p), _)) == Bool.or(a0, Bool.or(a1, Bool.or(a2, a3))) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(b0, Nat.mul(8n, 0n)), p), a0, bsel(b0, 0n, j, k, h0, hk)) :
    {Bool.or(_, Bool.or(D.bit(U32.shln(b1, 8n), p), Bool.or(D.bit(U32.shln(b2, 16n), p), D.bit(U32.shln(b3, 24n), p)))) == Bool.or(a0, Bool.or(a1, Bool.or(a2, a3))) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(b1, Nat.mul(8n, 1n)), p), a1, bsel(b1, 1n, j, k, h1, hk)) :
    {Bool.or(a0, Bool.or(_, Bool.or(D.bit(U32.shln(b2, 16n), p), D.bit(U32.shln(b3, 24n), p)))) == Bool.or(a0, Bool.or(a1, Bool.or(a2, a3))) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(b2, Nat.mul(8n, 2n)), p), a2, bsel(b2, 2n, j, k, h2, hk)) :
    {Bool.or(a0, Bool.or(a1, Bool.or(_, D.bit(U32.shln(b3, 24n), p)))) == Bool.or(a0, Bool.or(a1, Bool.or(a2, a3))) : Bool}
  %Equal.sym(Bool, D.bit(U32.shln(b3, Nat.mul(8n, 3n)), p), a3, bsel(b3, 3n, j, k, h3, hk)) :
    {Bool.or(a0, Bool.or(a1, Bool.or(a2, _))) == Bool.or(a0, Bool.or(a1, Bool.or(a2, a3))) : Bool}
  {==}

law nth4_lt:
  for +j: Nat
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +h0: {Nat.is_lt(U32.to_nat(b0), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h1: {Nat.is_lt(U32.to_nat(b1), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h2: {Nat.is_lt(U32.to_nat(b2), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h3: {Nat.is_lt(U32.to_nat(b3), Nat.pow(2n, 8n)) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(D.nth4(j, b0, b1, b2, b3)), Nat.pow(2n, 8n)) == True{} : Bool}

def nth4_lt(j, b0, b1, b2, b3, h0, h1, h2, h3):
  match j:
    case 0n:
      h0
    case 1n+p:
      match p:
        case 0n:
          h1
        case 1n+q:
          match q:
            case 0n:
              h2
            case 1n+t:
              h3

# Bit k (k < 8) of byte j (j < 4) of a packed word is bit k of the j-th value.
law pack_byte:
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +j: Nat
  for +k: Nat
  for +h0: {Nat.is_lt(U32.to_nat(b0), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h1: {Nat.is_lt(U32.to_nat(b1), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h2: {Nat.is_lt(U32.to_nat(b2), Nat.pow(2n, 8n)) == True{} : Bool}
  for +h3: {Nat.is_lt(U32.to_nat(b3), Nat.pow(2n, 8n)) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +hk: {Nat.is_lt(k, 8n) == True{} : Bool}
  {D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, j), k)) == D.bit(D.nth4(j, b0, b1, b2, b3), k) : Bool}

def pack_byte(b0, b1, b2, b3, j, k, h0, h1, h2, h3, hj, hk):
  match j:
    case 0n:
      %Equal.sym(Bool, D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, 0n), k)), Bool.or(Bool.and(Nat.is_eq(0n, 0n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 0n), k), 32n), D.bit(b0, k))),
          Bool.or(Bool.and(Nat.is_eq(0n, 1n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 0n), k), 32n), D.bit(b1, k))),
          Bool.or(Bool.and(Nat.is_eq(0n, 2n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 0n), k), 32n), D.bit(b2, k))),
                  Bool.and(Nat.is_eq(0n, 3n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 0n), k), 32n), D.bit(b3, k)))))),
          pack_bits(b0, b1, b2, b3, 0n, k, h0, h1, h2, h3, hk)) :
        {_ == D.bit(b0, k) : Bool}
      %Equal.sym(Bool, Bool.or(Bool.and(Nat.is_lt(k, 32n), D.bit(b0, k)), False{}), Bool.and(Nat.is_lt(k, 32n), D.bit(b0, k)), N.or_false_r(Bool.and(Nat.is_lt(k, 32n), D.bit(b0, k)))) :
        {_ == D.bit(b0, k) : Bool}
      %Equal.sym(Bool, Nat.is_lt(k, 32n), True{}, idx32(0n, k, {==}, hk)) : {Bool.and(_, D.bit(b0, k)) == D.bit(b0, k) : Bool}
      {==}
    case 1n+j1:
      match j1:
        case 0n:
          %Equal.sym(Bool, D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, 1n), k)), Bool.or(Bool.and(Nat.is_eq(1n, 0n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 1n), k), 32n), D.bit(b0, k))),
              Bool.or(Bool.and(Nat.is_eq(1n, 1n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 1n), k), 32n), D.bit(b1, k))),
              Bool.or(Bool.and(Nat.is_eq(1n, 2n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 1n), k), 32n), D.bit(b2, k))),
                      Bool.and(Nat.is_eq(1n, 3n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 1n), k), 32n), D.bit(b3, k)))))),
              pack_bits(b0, b1, b2, b3, 1n, k, h0, h1, h2, h3, hk)) :
            {_ == D.bit(b1, k) : Bool}
          %Equal.sym(Bool, Bool.or(Bool.and(Nat.is_lt(8n+k, 32n), D.bit(b1, k)), False{}), Bool.and(Nat.is_lt(8n+k, 32n), D.bit(b1, k)), N.or_false_r(Bool.and(Nat.is_lt(8n+k, 32n), D.bit(b1, k)))) :
            {_ == D.bit(b1, k) : Bool}
          %Equal.sym(Bool, Nat.is_lt(8n+k, 32n), True{}, idx32(1n, k, {==}, hk)) : {Bool.and(_, D.bit(b1, k)) == D.bit(b1, k) : Bool}
          {==}
        case 1n+j2:
          match j2:
            case 0n:
              %Equal.sym(Bool, D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, 2n), k)), Bool.or(Bool.and(Nat.is_eq(2n, 0n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 2n), k), 32n), D.bit(b0, k))),
                  Bool.or(Bool.and(Nat.is_eq(2n, 1n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 2n), k), 32n), D.bit(b1, k))),
                  Bool.or(Bool.and(Nat.is_eq(2n, 2n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 2n), k), 32n), D.bit(b2, k))),
                          Bool.and(Nat.is_eq(2n, 3n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 2n), k), 32n), D.bit(b3, k)))))),
                  pack_bits(b0, b1, b2, b3, 2n, k, h0, h1, h2, h3, hk)) :
                {_ == D.bit(b2, k) : Bool}
              %Equal.sym(Bool, Bool.or(Bool.and(Nat.is_lt(16n+k, 32n), D.bit(b2, k)), False{}), Bool.and(Nat.is_lt(16n+k, 32n), D.bit(b2, k)), N.or_false_r(Bool.and(Nat.is_lt(16n+k, 32n), D.bit(b2, k)))) :
                {_ == D.bit(b2, k) : Bool}
              %Equal.sym(Bool, Nat.is_lt(16n+k, 32n), True{}, idx32(2n, k, {==}, hk)) : {Bool.and(_, D.bit(b2, k)) == D.bit(b2, k) : Bool}
              {==}
            case 1n+j3:
              match j3:
                case 0n:
                  %Equal.sym(Bool, D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, 3n), k)), Bool.or(Bool.and(Nat.is_eq(3n, 0n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 3n), k), 32n), D.bit(b0, k))),
                      Bool.or(Bool.and(Nat.is_eq(3n, 1n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 3n), k), 32n), D.bit(b1, k))),
                      Bool.or(Bool.and(Nat.is_eq(3n, 2n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 3n), k), 32n), D.bit(b2, k))),
                              Bool.and(Nat.is_eq(3n, 3n), Bool.and(Nat.is_lt(Nat.add(Nat.mul(8n, 3n), k), 32n), D.bit(b3, k)))))),
                      pack_bits(b0, b1, b2, b3, 3n, k, h0, h1, h2, h3, hk)) :
                    {_ == D.bit(b3, k) : Bool}
                  %Equal.sym(Bool, Nat.is_lt(24n+k, 32n), True{}, idx32(3n, k, {==}, hk)) : {Bool.and(_, D.bit(b3, k)) == D.bit(b3, k) : Bool}
                  {==}
                case 1n+j4:
                  Empty.absurd({D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, 4n+j4), k)) == D.bit(D.nth4(4n+j4, b0, b1, b2, b3), k) : Bool}, N.false_ne_true(
                    Equal.trans(Bool, False{}, Nat.is_lt(j4, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j4, 0n), False{}, N.lt_zero(j4)), hj)))

def byte_pack4.l(+b0: U32, +b1: U32, +b2: U32, +b3: U32, +j: Nat, +k: Nat,
  +h0: {Nat.is_lt(U32.to_nat(b0), Nat.pow(2n, 8n)) == True{} : Bool},
  +h1: {Nat.is_lt(U32.to_nat(b1), Nat.pow(2n, 8n)) == True{} : Bool},
  +h2: {Nat.is_lt(U32.to_nat(b2), Nat.pow(2n, 8n)) == True{} : Bool},
  +h3: {Nat.is_lt(U32.to_nat(b3), Nat.pow(2n, 8n)) == True{} : Bool},
  +hj: {Nat.is_lt(j, 4n) == True{} : Bool}, z: Bool, +ez: {Nat.is_lt(k, 8n) == z : Bool}) ->
  {Bool.and(z, D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, j), k))) == D.bit(D.nth4(j, b0, b1, b2, b3), k) : Bool}:
  match z:
    case True{}:
      pack_byte(b0, b1, b2, b3, j, k, h0, h1, h2, h3, hj, ez)
    case False{}:
      Equal.sym(Bool, D.bit(D.nth4(j, b0, b1, b2, b3), k), False{},
        bit_lt_pow(D.nth4(j, b0, b1, b2, b3), 8n, k, nth4_lt(j, b0, b1, b2, b3, h0, h1, h2, h3), N.not_lt_le(k, 8n, ez)))

def byte_pack4.k(+b0: U32, +b1: U32, +b2: U32, +b3: U32, +j: Nat,
  +h0: {Nat.is_lt(U32.to_nat(b0), Nat.pow(2n, 8n)) == True{} : Bool},
  +h1: {Nat.is_lt(U32.to_nat(b1), Nat.pow(2n, 8n)) == True{} : Bool},
  +h2: {Nat.is_lt(U32.to_nat(b2), Nat.pow(2n, 8n)) == True{} : Bool},
  +h3: {Nat.is_lt(U32.to_nat(b3), Nat.pow(2n, 8n)) == True{} : Bool},
  +hj: {Nat.is_lt(j, 4n) == True{} : Bool}, +k: Nat) ->
  {D.bit(D.byte(D.pack4(b0, b1, b2, b3), j), k) == D.bit(D.nth4(j, b0, b1, b2, b3), k) : Bool}:
  %Equal.sym(Bool, D.bit(D.byte(D.pack4(b0, b1, b2, b3), j), k), Bool.and(Nat.is_lt(k, 8n), D.bit(D.pack4(b0, b1, b2, b3), Nat.add(Nat.mul(8n, j), k))),
      bit_byte(D.pack4(b0, b1, b2, b3), j, k)) :
    {_ == D.bit(D.nth4(j, b0, b1, b2, b3), k) : Bool}
  byte_pack4.l(b0, b1, b2, b3, j, k, h0, h1, h2, h3, hj, Nat.is_lt(k, 8n), {==})

law byte_pack4:
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +j: Nat
  for +h0: {U32.is_lt(b0, 256) == True{} : Bool}
  for +h1: {U32.is_lt(b1, 256) == True{} : Bool}
  for +h2: {U32.is_lt(b2, 256) == True{} : Bool}
  for +h3: {U32.is_lt(b3, 256) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {D.byte(D.pack4(b0, b1, b2, b3), j) == D.nth4(j, b0, b1, b2, b3) : U32}

def byte_pack4(b0, b1, b2, b3, j, h0, h1, h2, h3, hj):
  U.bit_ext(D.byte(D.pack4(b0, b1, b2, b3), j), D.nth4(j, b0, b1, b2, b3),
    k => byte_pack4.k(b0, b1, b2, b3, j, lt256(b0, h0), lt256(b1, h1), lt256(b2, h2), lt256(b3, h3), hj, k))

law nth4_byte:
  for +w: U32
  for +j: Nat
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {D.nth4(j, D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)) == D.byte(w, j) : U32}

def nth4_byte(w, j, hj):
  match j:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+t:
              match t:
                case 0n:
                  {==}
                case 1n+u:
                  Empty.absurd({D.nth4(4n+u, D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)) == D.byte(w, 4n+u) : U32}, N.false_ne_true(
                    Equal.trans(Bool, False{}, Nat.is_lt(u, 0n), True{}, Equal.sym(Bool, Nat.is_lt(u, 0n), False{}, N.lt_zero(u)), hj)))

def pack4_bytes.go(+w: U32, +j: Nat, +k: Nat, +hk: {Nat.is_lt(k, 8n) == True{} : Bool}, z: Bool, +ez: {Nat.is_lt(j, 4n) == z : Bool}) ->
  {D.bit(D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), Nat.add(Nat.mul(8n, j), k)) == D.bit(w, Nat.add(Nat.mul(8n, j), k)) : Bool}:
  match z:
    case True{}:
      +p = Nat.add(Nat.mul(8n, j), k)
      %Equal.sym(Bool, D.bit(D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), p),
          D.bit(D.nth4(j, D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), k),
          pack_byte(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n), j, k,
            lt256(D.byte(w, 0n), byte_lt(w, 0n)), lt256(D.byte(w, 1n), byte_lt(w, 1n)), lt256(D.byte(w, 2n), byte_lt(w, 2n)), lt256(D.byte(w, 3n), byte_lt(w, 3n)), ez, hk)) :
        {_ == D.bit(w, p) : Bool}
      %Equal.sym(U32, D.nth4(j, D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), D.byte(w, j), nth4_byte(w, j, ez)) : {D.bit(_, k) == D.bit(w, p) : Bool}
      %Equal.sym(Bool, D.bit(D.byte(w, j), k), Bool.and(Nat.is_lt(k, 8n), D.bit(w, p)), bit_byte(w, j, k)) : {_ == D.bit(w, p) : Bool}
      %Equal.sym(Bool, Nat.is_lt(k, 8n), True{}, hk) : {Bool.and(_, D.bit(w, p)) == D.bit(w, p) : Bool}
      {==}
    case False{}:
      +p = Nat.add(Nat.mul(8n, j), k)
      +h32 = N.le_trans(32n, Nat.mul(8n, j), p, N.le_mul_l(8n, 4n, j, N.not_lt_le(j, 4n, ez)), N.le_add_r(Nat.mul(8n, j), k))
      Equal.trans(Bool, D.bit(D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), p), False{}, D.bit(w, p),
        bit_ge32(D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), p, h32),
        Equal.sym(Bool, D.bit(w, p), False{}, bit_ge32(w, p, h32)))

def pack4_bytes.k(+w: U32, +k: Nat) -> {D.bit(D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), k) == D.bit(w, k) : Bool}:
  +j = Nat.div(k, 8n)
  +r = Nat.mod(k, 8n)
  %Equal.trans(Nat, Nat.add(Nat.mul(8n, j), r), Nat.add(Nat.mul(j, 8n), r), k,
      Equal.cong(Nat, Nat, t => Nat.add(t, r), Nat.mul(8n, j), Nat.mul(j, 8n), N.mul_comm(8n, j)), N.div_mod(k, 8n)) :
    {D.bit(D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), _) == D.bit(w, _) : Bool}
  pack4_bytes.go(w, j, r, N.mod_lt(k, 8n, {==}), Nat.is_lt(j, 4n), {==})

law pack4_bytes:
  for +w: U32
  {D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)) == w : U32}

def pack4_bytes(w):
  U.bit_ext(D.pack4(D.byte(w, 0n), D.byte(w, 1n), D.byte(w, 2n), D.byte(w, 3n)), w, k => pack4_bytes.k(w, k))

law byte_ext:
  for +a: U32
  for +b: U32
  for +h0: {D.byte(a, 0n) == D.byte(b, 0n) : U32}
  for +h1: {D.byte(a, 1n) == D.byte(b, 1n) : U32}
  for +h2: {D.byte(a, 2n) == D.byte(b, 2n) : U32}
  for +h3: {D.byte(a, 3n) == D.byte(b, 3n) : U32}
  {a == b : U32}

def byte_ext(a, b, h0, h1, h2, h3):
  Equal.trans(U32, a, D.pack4(D.byte(a, 0n), D.byte(a, 1n), D.byte(a, 2n), D.byte(a, 3n)), b,
    Equal.sym(U32, D.pack4(D.byte(a, 0n), D.byte(a, 1n), D.byte(a, 2n), D.byte(a, 3n)), a, pack4_bytes(a)),
    %Equal.sym(U32, D.byte(a, 0n), D.byte(b, 0n), h0) : {D.pack4(_, D.byte(a, 1n), D.byte(a, 2n), D.byte(a, 3n)) == b : U32}
    %Equal.sym(U32, D.byte(a, 1n), D.byte(b, 1n), h1) : {D.pack4(D.byte(b, 0n), _, D.byte(a, 2n), D.byte(a, 3n)) == b : U32}
    %Equal.sym(U32, D.byte(a, 2n), D.byte(b, 2n), h2) : {D.pack4(D.byte(b, 0n), D.byte(b, 1n), _, D.byte(a, 3n)) == b : U32}
    %Equal.sym(U32, D.byte(a, 3n), D.byte(b, 3n), h3) : {D.pack4(D.byte(b, 0n), D.byte(b, 1n), D.byte(b, 2n), _) == b : U32}
    pack4_bytes(b))

# The number a packed word stands for
# ===================================

law bor_comm:
  for +x: Bool
  for +y: Bool
  {Bool.or(x, y) == Bool.or(y, x) : Bool}

def bor_comm(x, y):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law wor_comm:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.or(n, a, b) == Word.or(n, b, a) : Word(n)}

def wor_comm(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %bor_comm(x, y) : {WCon{Bool.or(x, y), Word.or(p, at, bt)} == WCon{_, Word.or(p, bt, at)} : Word(1n+p)}
          %wor_comm(p, at, bt) : {WCon{Bool.or(x, y), Word.or(p, at, bt)} == WCon{Bool.or(x, y), _} : Word(1n+p)}
          {==}

law or_comm:
  for +a: U32
  for +b: U32
  {U32.or(a, b) == U32.or(b, a) : U32}

def or_comm(a, b):
  match a b:
    case U32{+x} U32{+y}:
      %wor_comm(32n, x, y) : {U32{Word.or(32n, x, y)} == U32{_} : U32}
      {==}

law lt_mul_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  for +hc: {Nat.is_lt(0n, c) == True{} : Bool}
  {Nat.is_lt(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}

def lt_mul_r(a, b, c, h, hc):
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.mul(a, c), 0n) == True{} : Bool}, N.false_ne_true(
        Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, N.lt_zero(a)), h)))
    case 0n 1n+q:
      N.pos_add_l(c, Nat.mul(q, c), hc)
    case 1n+p 1n+q:
      N.lt_add_l(c, Nat.mul(p, c), Nat.mul(q, c), lt_mul_r(p, q, c, h, hc))

# 2^16, 2^24 and 2^32 in terms of a = 2^8.
law p16:
  for +a: Nat
  for +ha: {Nat.pow(2n, 8n) == a : Nat}
  {Nat.pow(2n, 16n) == Nat.mul(a, a) : Nat}

def p16(a, ha):
  %ha : {Nat.pow(2n, 16n) == Nat.mul(_, _) : Nat}
  %{{==} : {Nat.add(8n, 8n) == 16n : Nat}} : {Nat.pow(2n, _) == Nat.mul(Nat.pow(2n, 8n), Nat.pow(2n, 8n)) : Nat}
  N.pow_add(2n, 8n, 8n)

law p24:
  for +a: Nat
  for +ha: {Nat.pow(2n, 8n) == a : Nat}
  {Nat.pow(2n, 24n) == Nat.mul(Nat.mul(a, a), a) : Nat}

def p24(a, ha):
  %p16(a, ha) : {Nat.pow(2n, 24n) == Nat.mul(_, a) : Nat}
  %ha : {Nat.pow(2n, 24n) == Nat.mul(Nat.pow(2n, 16n), _) : Nat}
  %{{==} : {Nat.add(16n, 8n) == 24n : Nat}} : {Nat.pow(2n, _) == Nat.mul(Nat.pow(2n, 16n), Nat.pow(2n, 8n)) : Nat}
  N.pow_add(2n, 16n, 8n)

law p32:
  for +a: Nat
  for +m: Nat
  for +ha: {Nat.pow(2n, 8n) == a : Nat}
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  {m == Nat.mul(Nat.mul(Nat.mul(a, a), a), a) : Nat}

def p32(a, m, ha, hm):
  %hm : {_ == Nat.mul(Nat.mul(Nat.mul(a, a), a), a) : Nat}
  %p24(a, ha) : {Nat.pow(2n, 32n) == Nat.mul(_, a) : Nat}
  %ha : {Nat.pow(2n, 32n) == Nat.mul(Nat.pow(2n, 24n), _) : Nat}
  %{{==} : {Nat.add(24n, 8n) == 32n : Nat}} : {Nat.pow(2n, _) == Nat.mul(Nat.pow(2n, 24n), Nat.pow(2n, 8n)) : Nat}
  N.pow_add(2n, 24n, 8n)

law le_mul_pos:
  for +x: Nat
  for +c: Nat
  for +hc: {Nat.is_lt(0n, c) == True{} : Bool}
  {Nat.is_le(x, Nat.mul(x, c)) == True{} : Bool}

def le_mul_pos(x, c, hc):
  %N.mul_one(x) : {Nat.is_le(_, Nat.mul(x, c)) == True{} : Bool}
  N.le_mul_l(x, 1n, c, %Equal.sym(Bool, Nat.is_le(1n, c), Nat.is_lt(0n, c), N.le_succ_lt(0n, c)) : {_ == True{} : Bool}; hc)

# The value of b << 8s, 16 or 24, with a = 2^8 and m = 2^32 abstract.
law shv:
  for +b: U32
  for +s: Nat
  for +p: Nat
  for +a: Nat
  for +m: Nat
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  for +hp: {Nat.pow(2n, s) == p : Nat}
  for +hb: {Nat.is_lt(U32.to_nat(b), a) == True{} : Bool}
  for +hpm: {Nat.is_le(Nat.mul(a, p), m) == True{} : Bool}
  for +hp0: {Nat.is_lt(0n, p) == True{} : Bool}
  {U32.to_nat(U32.shln(b, s)) == Nat.mul(U32.to_nat(b), p) : Nat}

def shv(b, s, p, a, m, hm, hp, hb, hpm, hp0):
  Equal.trans(Nat, U32.to_nat(U32.shln(b, s)), Nat.mod(Nat.mul(U32.to_nat(b), Nat.pow(2n, s)), m), Nat.mul(U32.to_nat(b), p),
    U.to_nat_shln.m(b, s, m, hm),
    %Equal.sym(Nat, Nat.pow(2n, s), p, hp) : {Nat.mod(Nat.mul(U32.to_nat(b), _), m) == Nat.mul(U32.to_nat(b), p) : Nat}
    N.mod_small(Nat.mul(U32.to_nat(b), p), m, N.lt_le_trans(Nat.mul(U32.to_nat(b), p), Nat.mul(a, p), m, lt_mul_r(U32.to_nat(b), a, p, hb, hp0), hpm)))

law pk.m:
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +a: Nat
  for +m: Nat
  for +ha: {Nat.pow(2n, 8n) == a : Nat}
  for +hm: {Nat.pow(2n, 32n) == m : Nat}
  for +h0: {Nat.is_lt(U32.to_nat(b0), a) == True{} : Bool}
  for +h1: {Nat.is_lt(U32.to_nat(b1), a) == True{} : Bool}
  for +h2: {Nat.is_lt(U32.to_nat(b2), a) == True{} : Bool}
  for +h3: {Nat.is_lt(U32.to_nat(b3), a) == True{} : Bool}
  {U32.to_nat(D.pack4(b0, b1, b2, b3)) == Nat.add(U32.to_nat(b0), Nat.add(Nat.mul(U32.to_nat(b1), a),
    Nat.add(Nat.mul(U32.to_nat(b2), Nat.mul(a, a)), Nat.mul(U32.to_nat(b3), Nat.mul(Nat.mul(a, a), a))))) : Nat}

def pk.m(b0, b1, b2, b3, a, m, ha, hm, h0, h1, h2, h3):
  +x0 = U32.to_nat(b0)
  +x1 = U32.to_nat(b1)
  +x2 = U32.to_nat(b2)
  +x3 = U32.to_nat(b3)
  +a2 = Nat.mul(a, a)
  +a3 = Nat.mul(a2, a)
  +ap = {%ha : {Nat.is_lt(0n, _) == True{} : Bool}; N.pow_pos(8n) : {Nat.is_lt(0n, a) == True{} : Bool}}
  +a2p = lt_mul_r(0n, a, a, ap, ap)
  +a3p = lt_mul_r(0n, a2, a, a2p, ap)
  +em = {%Equal.sym(Nat, m, Nat.mul(a3, a), p32(a, m, ha, hm)) : {Nat.is_le(Nat.mul(a, a3), _) == True{} : Bool}; %N.mul_comm(a3, a) : {Nat.is_le(_, Nat.mul(a3, a)) == True{} : Bool}; N.le_refl(Nat.mul(a3, a)) :
    {Nat.is_le(Nat.mul(a, a3), m) == True{} : Bool}}
  +la3 = {%Equal.sym(Nat, m, Nat.mul(a3, a), p32(a, m, ha, hm)) : {Nat.is_le(a3, _) == True{} : Bool}; le_mul_pos(a3, a, ap) : {Nat.is_le(a3, m) == True{} : Bool}}
  +la2 = N.le_trans(a2, a3, m, le_mul_pos(a2, a, ap), la3)
  +s1 = U32.shln(b1, 8n)
  +s2 = U32.shln(b2, 16n)
  +s3 = U32.shln(b3, 24n)
  +v1 = shv(b1, 8n, a, a, m, hm, ha, h1, N.le_trans(Nat.mul(a, a), a3, m, le_mul_pos(a2, a, ap), la3), ap)
  +v2 = shv(b2, 16n, a2, a, m, hm, p16(a, ha), h2,
    %N.mul_comm(a2, a) : {Nat.is_le(_, m) == True{} : Bool}; la3, a2p)
  +v3 = shv(b3, 24n, a3, a, m, hm, p24(a, ha), h3, em, a3p)
  # y = s2 | s3 = x3 a3 + x2 a2
  +yv = Nat.add(Nat.mul(x3, a3), Nat.mul(x2, a2))
  +ey = Equal.trans(Nat, U32.to_nat(U32.or(s2, s3)), U32.to_nat(U32.or(s3, s2)), yv,
    %or_comm(s2, s3) : {U32.to_nat(U32.or(s2, s3)) == U32.to_nat(_) : Nat}; {==},
    %Equal.sym(Nat, U32.to_nat(U32.or(s3, s2)), Nat.add(U32.to_nat(s3), U32.to_nat(s2)),
        U.to_nat_or_split(s3, s2, 24n,
          %Equal.sym(Nat, Nat.pow(2n, 24n), Nat.mul(Nat.mul(a, a), a), p24(a, ha)) : {Nat.mod(U32.to_nat(s3), _) == 0n : Nat}
          %Equal.sym(Nat, U32.to_nat(s3), Nat.mul(x3, a3), v3) : {Nat.mod(_, a3) == 0n : Nat}
          N.mul_mod(x3, a3),
          %Equal.sym(Nat, Nat.pow(2n, 24n), Nat.mul(Nat.mul(a, a), a), p24(a, ha)) : {Nat.is_lt(U32.to_nat(s2), _) == True{} : Bool}
          %Equal.sym(Nat, U32.to_nat(s2), Nat.mul(x2, a2), v2) : {Nat.is_lt(_, a3) == True{} : Bool}
          %N.mul_comm(a, a2) : {Nat.is_lt(Nat.mul(x2, a2), _) == True{} : Bool}
          lt_mul_r(x2, a, a2, h2, a2p))) :
      {_ == yv : Nat}
    %Equal.sym(Nat, U32.to_nat(s3), Nat.mul(x3, a3), v3) : {Nat.add(_, U32.to_nat(s2)) == yv : Nat}
    %Equal.sym(Nat, U32.to_nat(s2), Nat.mul(x2, a2), v2) : {Nat.add(Nat.mul(x3, a3), _) == yv : Nat}
    {==})
  # x = s1 | y = y + x1 a
  +yw = U32.or(s2, s3)
  +xv = Nat.add(yv, Nat.mul(x1, a))
  +eq2 = Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(x3, a), x2), a2), Nat.add(Nat.mul(Nat.mul(x3, a), a2), Nat.mul(x2, a2)), yv,
      N.mul_add_r(Nat.mul(x3, a), x2, a2),
      Equal.cong(Nat, Nat, t => Nat.add(t, Nat.mul(x2, a2)), Nat.mul(Nat.mul(x3, a), a2), Nat.mul(x3, a3),
        %N.mul_comm(a, a2) : {Nat.mul(Nat.mul(x3, a), a2) == Nat.mul(x3, _) : Nat}; N.mul_assoc(x3, a, a2)))
  +ymul = {%eq2 : {Nat.mod(_, a2) == 0n : Nat}; N.mul_mod(Nat.add(Nat.mul(x3, a), x2), a2) : {Nat.mod(yv, a2) == 0n : Nat}}
  +ex = Equal.trans(Nat, U32.to_nat(U32.or(s1, yw)), U32.to_nat(U32.or(yw, s1)), xv,
    %or_comm(s1, yw) : {U32.to_nat(U32.or(s1, yw)) == U32.to_nat(_) : Nat}; {==},
    %Equal.sym(Nat, U32.to_nat(U32.or(yw, s1)), Nat.add(U32.to_nat(yw), U32.to_nat(s1)),
        U.to_nat_or_split(yw, s1, 16n,
          %Equal.sym(Nat, Nat.pow(2n, 16n), Nat.mul(a, a), p16(a, ha)) : {Nat.mod(U32.to_nat(yw), _) == 0n : Nat}
          %Equal.sym(Nat, U32.to_nat(yw), yv, ey) : {Nat.mod(_, a2) == 0n : Nat}
          ymul,
          %Equal.sym(Nat, Nat.pow(2n, 16n), Nat.mul(a, a), p16(a, ha)) : {Nat.is_lt(U32.to_nat(s1), _) == True{} : Bool}
          %Equal.sym(Nat, U32.to_nat(s1), Nat.mul(x1, a), v1) : {Nat.is_lt(_, a2) == True{} : Bool}
          lt_mul_r(x1, a, a, h1, ap))) :
      {_ == xv : Nat}
    %Equal.sym(Nat, U32.to_nat(yw), yv, ey) : {Nat.add(_, U32.to_nat(s1)) == xv : Nat}
    %Equal.sym(Nat, U32.to_nat(s1), Nat.mul(x1, a), v1) : {Nat.add(yv, _) == xv : Nat}
    {==})
  # pack = b0 | x = x + x0
  +xw = U32.or(s1, yw)
  +q = Nat.add(Nat.mul(Nat.add(Nat.mul(x3, a), x2), a), x1)
  +xmul = {%Equal.trans(Nat, Nat.mul(q, a), Nat.add(Nat.mul(Nat.mul(Nat.add(Nat.mul(x3, a), x2), a), a), Nat.mul(x1, a)), xv,
      N.mul_add_r(Nat.mul(Nat.add(Nat.mul(x3, a), x2), a), x1, a),
      Equal.cong(Nat, Nat, t => Nat.add(t, Nat.mul(x1, a)), Nat.mul(Nat.mul(Nat.add(Nat.mul(x3, a), x2), a), a), yv,
        Equal.trans(Nat, Nat.mul(Nat.mul(Nat.add(Nat.mul(x3, a), x2), a), a), Nat.mul(Nat.add(Nat.mul(x3, a), x2), a2), yv,
          N.mul_assoc(Nat.add(Nat.mul(x3, a), x2), a, a), eq2))) :
      {Nat.mod(_, a) == 0n : Nat}; N.mul_mod(q, a) : {Nat.mod(xv, a) == 0n : Nat}}
  %or_comm(xw, b0) : {U32.to_nat(_) == Nat.add(x0, Nat.add(Nat.mul(x1, a), Nat.add(Nat.mul(x2, a2), Nat.mul(x3, a3)))) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.or(xw, b0)), Nat.add(U32.to_nat(xw), x0),
      U.to_nat_or_split(xw, b0, 8n,
        %Equal.sym(Nat, Nat.pow(2n, 8n), a, ha) : {Nat.mod(U32.to_nat(xw), _) == 0n : Nat}
        %Equal.sym(Nat, U32.to_nat(xw), xv, ex) : {Nat.mod(_, a) == 0n : Nat}
        xmul,
        %Equal.sym(Nat, Nat.pow(2n, 8n), a, ha) : {Nat.is_lt(x0, _) == True{} : Bool}; h0)) :
    {_ == Nat.add(x0, Nat.add(Nat.mul(x1, a), Nat.add(Nat.mul(x2, a2), Nat.mul(x3, a3)))) : Nat}
  %Equal.sym(Nat, U32.to_nat(xw), xv, ex) : {Nat.add(_, x0) == Nat.add(x0, Nat.add(Nat.mul(x1, a), Nat.add(Nat.mul(x2, a2), Nat.mul(x3, a3)))) : Nat}
  %N.add_comm(x0, xv) : {_ == Nat.add(x0, Nat.add(Nat.mul(x1, a), Nat.add(Nat.mul(x2, a2), Nat.mul(x3, a3)))) : Nat}
  %N.add_comm(Nat.mul(x1, a), yv) : {Nat.add(x0, _) == Nat.add(x0, Nat.add(Nat.mul(x1, a), Nat.add(Nat.mul(x2, a2), Nat.mul(x3, a3)))) : Nat}
  %N.add_comm(Nat.mul(x2, a2), Nat.mul(x3, a3)) : {Nat.add(x0, Nat.add(Nat.mul(x1, a), _)) == Nat.add(x0, Nat.add(Nat.mul(x1, a), Nat.add(Nat.mul(x2, a2), Nat.mul(x3, a3)))) : Nat}
  {==}

law to_nat_pack4:
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +h0: {U32.is_lt(b0, 256) == True{} : Bool}
  for +h1: {U32.is_lt(b1, 256) == True{} : Bool}
  for +h2: {U32.is_lt(b2, 256) == True{} : Bool}
  for +h3: {U32.is_lt(b3, 256) == True{} : Bool}
  {U32.to_nat(D.pack4(b0, b1, b2, b3)) == Nat.add(U32.to_nat(b0), Nat.add(Nat.mul(U32.to_nat(b1), Nat.pow(2n, 8n)), Nat.add(Nat.mul(U32.to_nat(b2), Nat.pow(2n, 16n)), Nat.mul(U32.to_nat(b3), Nat.pow(2n, 24n))))) : Nat}

def to_nat_pack4(b0, b1, b2, b3, h0, h1, h2, h3):
  %Equal.sym(Nat, Nat.pow(2n, 24n), Nat.mul(Nat.mul(Nat.pow(2n, 8n), Nat.pow(2n, 8n)), Nat.pow(2n, 8n)), p24(Nat.pow(2n, 8n), {==})) :
    {U32.to_nat(D.pack4(b0, b1, b2, b3)) == Nat.add(U32.to_nat(b0), Nat.add(Nat.mul(U32.to_nat(b1), Nat.pow(2n, 8n)), Nat.add(Nat.mul(U32.to_nat(b2), Nat.pow(2n, 16n)), Nat.mul(U32.to_nat(b3), _)))) : Nat}
  %Equal.sym(Nat, Nat.pow(2n, 16n), Nat.mul(Nat.pow(2n, 8n), Nat.pow(2n, 8n)), p16(Nat.pow(2n, 8n), {==})) :
    {U32.to_nat(D.pack4(b0, b1, b2, b3)) == Nat.add(U32.to_nat(b0), Nat.add(Nat.mul(U32.to_nat(b1), Nat.pow(2n, 8n)), Nat.add(Nat.mul(U32.to_nat(b2), _),
      Nat.mul(U32.to_nat(b3), Nat.mul(Nat.mul(Nat.pow(2n, 8n), Nat.pow(2n, 8n)), Nat.pow(2n, 8n)))))) : Nat}
  pk.m(b0, b1, b2, b3, Nat.pow(2n, 8n), Nat.pow(2n, 32n), {==}, {==}, lt256(b0, h0), lt256(b1, h1), lt256(b2, h2), lt256(b3, h3))
