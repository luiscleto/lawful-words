You are reviewing a draft specification for `lawful-words`, a small Bend 2 package that will be
published on BendHub. It states, as laws, what Base's `U32` operations compute: each law says what
an operation does to the number a word stands for (`U32.to_nat`). The laws will be proven by a proof
checker, then used by other packages: first `lawful-bytes`, bytes packed four to a `U32` in an
`Array<U32>`, where every index computation, shift and mask needs these facts. A wrong law means a
false proof somewhere downstream; a missing law means a downstream proof cannot be done.

Read these files in the current directory (read-only; do not modify anything):
- `LAWS.bend`: the laws (the main object of review).
- `defs.bend`: the definitions the laws use (`W.n`, `W.wrap`, `W.bit`, `W.two32`).
- Base, for how `U32`, `Word`, `Nat` and `Bool` operations are defined: run `bend base` (the whole
  library) or `bend base <name>` (one definition, e.g. `bend base U32.sub`, `bend base Word.shr`).
You may run `bend LAWS.bend --check-only` (it reports 20 unproven laws, which is expected). Do not
evaluate expressions on large numbers: Base's `Nat` arithmetic is too slow for values near 2^32.

Bend notes: `law name:` followed by `for x: T` lines is a claim for every x; `for h: {a == b : T}` is a
hypothesis; `{a == b : T}` is equality; `+x` only marks a variable as reusable; `&&`, `||` are
boolean and, or; `Nat.sub` is truncated subtraction (never below 0); `Nat.div`/`Nat.mod` are
floor division and remainder. A `Word(n)` is n bits, lowest bit first; `U32` wraps a `Word(32n)`.

For each definition and law, answer:
(a) Does the Bend mean exactly what its English comment says?
(b) Is it true of Base's definitions as written? If not, give a concrete counterexample (values of
    the variables), worked out by hand from Base's definitions.
(c) Edge cases: 0, 2^32 - 1, shifting by 0, 32 or more bits, masks of 0 or 32 bits, `Nat.div` and
    `Nat.mod` by zero, bit positions of 32 or more.
(d) Missing laws: which facts will a packed-bytes library need that these laws do not give, or give
    only through a long chain? Think of: extracting byte j of a word (`(w >> 8j) & 255`), building a
    word from four bytes, word index `i >> 2` and byte offset `i & 3`, comparisons and counters,
    `U32.from_nat` of a sum, `U32.min`/`max`, `U32.div`/`mod`, `U32.to_nat` of a loop counter.
(e) For a published package: are the names and the shape of the laws convenient to use in proofs
    (rewriting with them, combining them)? Would a different form be easier to use?

Report a numbered list of findings. For each: the law or definition; severity (blocker / should fix
/ minor); the problem; a concrete example where possible; a suggested fix. Be concrete and brief. If
something is correct, you do not need to say so. End with the full report as your final message.
