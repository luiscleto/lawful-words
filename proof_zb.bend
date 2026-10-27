import Base
import ./defs.bend as D
import ./proof_nat.bend as N
import ./proof_u32.bend as U

# The zero-byte test (law zb_zero), byte by byte. A word is split into four
# 8-bit words (app8), and the subtraction v - 0x01010101 is followed one byte
# at a time: with no borrow into a byte x, the byte's flag is set and a borrow
# goes out exactly when x is zero (zb_byte, checked on all 256 bytes).

# All bits clear.
def allz(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Bool.and(Bool.not(b), allz(p, t))

# Eight bits x in front of r.
def app8(-n: Nat, x: Word(8n), r: Word(n)) -> Word(Nat.add(8n, n)):
  match x:
    case WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}:
      WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, r}}}}}}}}

def one8() -> Word(8n):
  WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}

def h8() -> Word(8n):
  WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}

def ones8() -> Word(8n):
  WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}

# The zero-byte flags of v with subtrahend k, flag mask h and carry in c.
def zf(+n: Nat, +v: Word(n), k: Word(n), h: Word(n), c: Bool) -> Word(n):
  Word.and(n, Word.and(n, Word.adc(n, v, k, True{}, c), Word.not(n, v)), h)

law allz_cmp:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_eq(Word.cmp(n, w, Word.zero(n))) == allz(n, w) : Bool}

def allz_cmp(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, Word.zero(p)))), Bool.and(Cmp.is_eq(Word.cmp(p, t, Word.zero(p))), True{}),
              U.fin_eq(False{}, False{}, Word.cmp(p, t, Word.zero(p)))) :
            {_ == allz(p, t) : Bool}
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, t, Word.zero(p))), True{}), Cmp.is_eq(Word.cmp(p, t, Word.zero(p))), N.and_true_r_id(Cmp.is_eq(Word.cmp(p, t, Word.zero(p))))) :
            {_ == allz(p, t) : Bool}
          allz_cmp(p, t)
        case WCon{True{}, +t}:
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.zero(p)))), Bool.and(Cmp.is_eq(Word.cmp(p, t, Word.zero(p))), False{}),
              U.fin_eq(True{}, False{}, Word.cmp(p, t, Word.zero(p)))) :
            {_ == False{} : Bool}
          N.and_false_r(Cmp.is_eq(Word.cmp(p, t, Word.zero(p))))

law allz_andz:
  for +n: Nat
  for +r: Word(n)
  {allz(n, Word.and(n, r, Word.zero(n))) == True{} : Bool}

def allz_andz(n, r):
  match n:
    case 0n:
      match r:
        case WNil{}:
          {==}
    case 1n+p:
      match r:
        case WCon{False{}, +t}:
          allz_andz(p, t)
        case WCon{True{}, +t}:
          allz_andz(p, t)

# One byte of the zero-byte test, with no borrow in.
law zb_byte:
  for +n: Nat
  for +x: Word(8n)
  for +r: Word(n)
  for +kr: Word(n)
  for +hr: Word(n)
  {allz(Nat.add(8n, n), zf(Nat.add(8n, n), app8(n, x, r), app8(n, one8(), kr), app8(n, h8(), hr), True{}))
    == Bool.and(Bool.not(allz(8n, x)), allz(n, zf(n, r, kr, hr, True{}))) : Bool}

def zb_byte(n, x, r, kr, hr):
  match x:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}

# A byte masked with 255.
law allz_mask:
  for +n: Nat
  for +x: Word(8n)
  for +r: Word(n)
  {allz(Nat.add(8n, n), Word.and(Nat.add(8n, n), app8(n, x, r), app8(n, ones8(), Word.zero(n))))
    == Bool.and(allz(8n, x), allz(n, Word.and(n, r, Word.zero(n)))) : Bool}

def allz_mask(n, x, r):
  match x:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}

law zb_zero:
  for +v: U32
  {U32.is_zero(D.zb(v)) == (U32.is_ne(D.byte(v, 0n), 0) && (U32.is_ne(D.byte(v, 1n), 0) && (U32.is_ne(D.byte(v, 2n), 0) && U32.is_ne(D.byte(v, 3n), 0)))) : Bool}

def zb_ne0(+c0: Bool, +c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, +c10: Bool, +c11: Bool, +c12: Bool, +c13: Bool, +c14: Bool, +c15: Bool, +c16: Bool, +c17: Bool, +c18: Bool, +c19: Bool, +c20: Bool, +c21: Bool, +c22: Bool, +c23: Bool, +c24: Bool, +c25: Bool, +c26: Bool, +c27: Bool, +c28: Bool, +c29: Bool, +c30: Bool, +c31: Bool) ->
  {U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0) == Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})) : Bool}:
  Equal.cong(Bool, Bool, t => Bool.not(t), Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}),
    Equal.trans(Bool, Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}),
      allz_cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))),
      Equal.trans(Bool, allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), Bool.and(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}), allz(24n, Word.and(24n, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n)))), allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}),
        allz_mask(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))),
        %Equal.sym(Bool, allz(24n, Word.and(24n, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n))), True{}, allz_andz(24n, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}))))) : {Bool.and(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}), _) == allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}) : Bool}
        N.and_true_r_id(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})))))

def zb_ne1(+c0: Bool, +c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, +c10: Bool, +c11: Bool, +c12: Bool, +c13: Bool, +c14: Bool, +c15: Bool, +c16: Bool, +c17: Bool, +c18: Bool, +c19: Bool, +c20: Bool, +c21: Bool, +c22: Bool, +c23: Bool, +c24: Bool, +c25: Bool, +c26: Bool, +c27: Bool, +c28: Bool, +c29: Bool, +c30: Bool, +c31: Bool) ->
  {U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0) == Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})) : Bool}:
  Equal.cong(Bool, Bool, t => Bool.not(t), Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}),
    Equal.trans(Bool, Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}),
      allz_cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))),
      Equal.trans(Bool, allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), Bool.and(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}), allz(24n, Word.and(24n, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n)))), allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}),
        allz_mask(24n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))),
        %Equal.sym(Bool, allz(24n, Word.and(24n, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n))), True{}, allz_andz(24n, app8(16n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))))) : {Bool.and(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}), _) == allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}) : Bool}
        N.and_true_r_id(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})))))

def zb_ne2(+c0: Bool, +c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, +c10: Bool, +c11: Bool, +c12: Bool, +c13: Bool, +c14: Bool, +c15: Bool, +c16: Bool, +c17: Bool, +c18: Bool, +c19: Bool, +c20: Bool, +c21: Bool, +c22: Bool, +c23: Bool, +c24: Bool, +c25: Bool, +c26: Bool, +c27: Bool, +c28: Bool, +c29: Bool, +c30: Bool, +c31: Bool) ->
  {U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0) == Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})) : Bool}:
  Equal.cong(Bool, Bool, t => Bool.not(t), Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}),
    Equal.trans(Bool, Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}),
      allz_cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))),
      Equal.trans(Bool, allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), Bool.and(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}), allz(24n, Word.and(24n, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n)))), allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}),
        allz_mask(24n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))),
        %Equal.sym(Bool, allz(24n, Word.and(24n, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n))), True{}, allz_andz(24n, app8(16n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))))) : {Bool.and(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}), _) == allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}) : Bool}
        N.and_true_r_id(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})))))

def zb_ne3(+c0: Bool, +c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, +c10: Bool, +c11: Bool, +c12: Bool, +c13: Bool, +c14: Bool, +c15: Bool, +c16: Bool, +c17: Bool, +c18: Bool, +c19: Bool, +c20: Bool, +c21: Bool, +c22: Bool, +c23: Bool, +c24: Bool, +c25: Bool, +c26: Bool, +c27: Bool, +c28: Bool, +c29: Bool, +c30: Bool, +c31: Bool) ->
  {U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0) == Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}})) : Bool}:
  Equal.cong(Bool, Bool, t => Bool.not(t), Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}),
    Equal.trans(Bool, Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n))), Word.zero(Nat.add(8n, 24n)))), allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}),
      allz_cmp(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))),
      Equal.trans(Bool, allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), app8(24n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))), app8(24n, ones8(), Word.zero(24n)))), Bool.and(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}), allz(24n, Word.and(24n, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n)))), allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}),
        allz_mask(24n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{})))),
        %Equal.sym(Bool, allz(24n, Word.and(24n, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))), Word.zero(24n))), True{}, allz_andz(24n, app8(16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(8n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, app8(0n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}, WNil{}))))) : {Bool.and(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}), _) == allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}) : Bool}
        N.and_true_r_id(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}})))))

def zb_zero(v):
  match v:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(Nat.add(8n, 24n), zf(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, one8(), app8(16n, one8(), app8(8n, one8(), app8(0n, one8(), WNil{})))), app8(24n, h8(), app8(16n, h8(), app8(8n, h8(), app8(0n, h8(), WNil{})))), True{}), Word.zero(Nat.add(8n, 24n)))), allz(Nat.add(8n, 24n), zf(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, one8(), app8(16n, one8(), app8(8n, one8(), app8(0n, one8(), WNil{})))), app8(24n, h8(), app8(16n, h8(), app8(8n, h8(), app8(0n, h8(), WNil{})))), True{})), allz_cmp(Nat.add(8n, 24n), zf(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, one8(), app8(16n, one8(), app8(8n, one8(), app8(0n, one8(), WNil{})))), app8(24n, h8(), app8(16n, h8(), app8(8n, h8(), app8(0n, h8(), WNil{})))), True{}))) :
        {_ == Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, allz(Nat.add(8n, 24n), zf(Nat.add(8n, 24n), app8(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})))), app8(24n, one8(), app8(16n, one8(), app8(8n, one8(), app8(0n, one8(), WNil{})))), app8(24n, h8(), app8(16n, h8(), app8(8n, h8(), app8(0n, h8(), WNil{})))), True{})), Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), allz(24n, zf(24n, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}))), app8(16n, one8(), app8(8n, one8(), app8(0n, one8(), WNil{}))), app8(16n, h8(), app8(8n, h8(), app8(0n, h8(), WNil{}))), True{}))), zb_byte(24n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}, app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}))), app8(16n, one8(), app8(8n, one8(), app8(0n, one8(), WNil{}))), app8(16n, h8(), app8(8n, h8(), app8(0n, h8(), WNil{}))))) :
        {_ == Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, allz(Nat.add(8n, 16n), zf(Nat.add(8n, 16n), app8(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}))), app8(16n, one8(), app8(8n, one8(), app8(0n, one8(), WNil{}))), app8(16n, h8(), app8(8n, h8(), app8(0n, h8(), WNil{}))), True{})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), allz(16n, zf(16n, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})), app8(8n, one8(), app8(0n, one8(), WNil{})), app8(8n, h8(), app8(0n, h8(), WNil{})), True{}))), zb_byte(16n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}}, app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})), app8(8n, one8(), app8(0n, one8(), WNil{})), app8(8n, h8(), app8(0n, h8(), WNil{})))) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), _) == Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, allz(Nat.add(8n, 8n), zf(Nat.add(8n, 8n), app8(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{})), app8(8n, one8(), app8(0n, one8(), WNil{})), app8(8n, h8(), app8(0n, h8(), WNil{})), True{})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), allz(8n, zf(8n, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}), app8(0n, one8(), WNil{}), app8(0n, h8(), WNil{}), True{}))), zb_byte(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}}, app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}), app8(0n, one8(), WNil{}), app8(0n, h8(), WNil{}))) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), _)) == Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, allz(Nat.add(8n, 0n), zf(Nat.add(8n, 0n), app8(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}), app8(0n, one8(), WNil{}), app8(0n, h8(), WNil{}), True{})), Bool.and(Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}})), allz(0n, zf(0n, WNil{}, WNil{}, WNil{}, True{}))), zb_byte(0n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}, WNil{}, WNil{}, WNil{})) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), _))) == Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}})), True{}), Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}})), N.and_true_r_id(Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}})))) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), _))) == Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), zb_ne0(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}))))) == Bool.and(_, Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), zb_ne1(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}))))) == Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(_, Bool.and(U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), zb_ne2(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}))))) == Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(_, U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0)))) : Bool}
      %Equal.sym(Bool, U32.is_ne(D.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}})), zb_ne3(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), Bool.not(allz(8n, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}))))) == Bool.and(Bool.not(allz(8n, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}})), Bool.and(Bool.not(allz(8n, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}})), _))) : Bool}
      {==}
