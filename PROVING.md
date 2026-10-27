# Proving lawful-words: brief for the proof agent

## Goal

Prove every law in `LAWS.bend` (83 laws about Base's `U32` operations, bytes inside a word, and
Nat facts). Three reviewers from different model families accepted the statements, so they are
frozen: never edit `LAWS.bend` or `defs.bend`. If a law looks false or unprovable as stated, stop
and report it with the reason; do not work around it.

The package will be published on BendHub, and `lawful-bytes` (packed byte buffers) will import it.
Proofs go in new files: `PROOF.bend` (imports `LAWS.bend` and fills every law, as
`def name(...) -> {...}: ...` with the law's name) plus helper files `proof_*.bend` as you need.
Gate:

```
timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend PROOF.bend --check-only
timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend PROOF.bend --verdict
```

Both must print ALL PROOFS CHECK, with no `@unsafe` and no foreign code anywhere in the import
graph. Write a `check.sh` that runs both, and `test/spot.bend` (`bend test/spot.bend`: 59 checks,
all True).

## Strategy (suggested; yours to judge)

- **Generalize over the width.** `U32` is `U32{Word(32n)}`, and `Word(n)` is n bits, lowest first
  (`WCon{head, tail}`). Most U32 laws are instances of a `Word(n)` lemma proven by induction on n:
  `Word.to_nat(n, w) < 2^n`, `Word.add` as addition modulo 2^n, `Word.cmp` as Nat.cmp, the shifts,
  the bitwise ops. Prove those once, then specialize to 32.
- **Nat facts first.** The Nat section at the end of `LAWS.bend` (add/mul commutativity and
  associativity, distributivity, div/mod identities, powers) is what everything else uses. Base
  has no Nat arithmetic laws at all.
- **Bytes via the numbers.** `D.byte(w, j)` is `(n(w) / 2^(8j)) mod 256` (`to_nat_byte`); most
  byte laws follow from Nat div/mod facts and `to_nat_inj`. `byte_ext` and `zb_zero` are the
  hardest: `zb_zero` is a borrow argument over the four bytes of `v - 0x01010101`; working per
  byte through `Word(8)` lemmas may be easier than numbers.
- **Testing first.** Nat is unary, so numbers near 2^32 cannot be evaluated. Small cases can, and
  `Word(n)` lemmas can be spot-checked at n = 8 instantly.

## Bend proof notes (from the framebender and minebender proofs)

- `%e : G` rewrites with `e : {new == old}`: `G` is the goal with `_` where `old` is; the rest of the
  def proves `G` with `new` there. Use `Equal.sym` to turn an equation around. `Equal.trans`,
  `Equal.cong` are in Base. Rewrite direction was the most frequent error in every earlier proof.
- `match` only inspects parameters or pattern-bound variables; a computed value needs a helper def
  that takes it as a parameter. Matches follow parameter order (`match a b:` for both). No match
  after a let.
- No mutual recursion, no forward references (define helpers first). Termination: the first argument
  that changes must shrink structurally; put it first. Eliminators take the induction hypothesis
  as a function argument.
- Unfilled laws are dead claims: a proof cannot call an open law. Prove in dependency order.
- A law's `for x` without `+` cannot be reused in its proof: restate with `+` where needed (same
  statement otherwise). Every equation used twice needs `+`. Function-typed hypotheses are affine.
- Refuting `{True{} == False{}}` or `{1n+n == 0n}`: rewrite through a `disc` motive that sends one
  constructor to `Empty` and the other to `Unit`, answer `Unit{}`.
- `Bool.pick`, `&&`, `||` evaluate both sides; to reason about them, case-split.
- Recursive defs do not unfold on variables: a lemma about `f(x)` for variable `x` needs a case
  split on `x` first.
- `?name` prints the goal at that point; `?TODO` leaves a hole. Errors print expected/observed terms.
- Every operator needs its type: `(a + b : U32)`. Bare constructors in a let need an annotation.
- `../framebender/proof_base.bend` and `../framebender/proof_machine_nat.bend` have proven Nat and
  Word facts you may copy (same author; MIT). `String.eq` soundness down to `Word.cmp` was proven
  there twice.

## Rules

- Use `nice -n 19` and a `timeout` for every check. No benchmarks needed.
- No git commits; the lead commits.
- Keep `notes/proof.md`: what is proven, the plan for the rest, and short bullets on where the proofs
  got hard and why (research data: rewrite direction, affinity, a missing lemma...).
- Stop when every law is proven and both gate commands pass, or after about four hours, and report:
  - what is proven;
  - what is left, and why;
  - any law you believe is false or unusable as stated.
