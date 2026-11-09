# Partial harmonic sums are never integers: a proof and its Lean 4 formalization

**Result.** For every integer `n ≥ 2`, the sum

```
S_n = 1/2 + 1/3 + … + 1/n
```

is not an integer. (Equivalently, the harmonic number `H_n = 1 + S_n` is not an
integer for `n ≥ 2`. This is a classical fact; Mathlib already contains it as
`harmonic_not_int`. The point of this repository is a different, self-contained
argument and its machine-checked formalization.)

**Idea of the proof.** Assume `S_{k+1} = a` is an integer. Then
`S_k = (a(k+1) − 1)/(k+1)`, a fraction in lowest terms. Let
`L_k = lcm(2, …, k)`.

* If `(k+1) ∤ L_k`, the denominator of `S_k` (which divides `L_k`) is `k+1`,
  a contradiction.
* If `(k+1) ∣ L_k`, write `L_k = m(k+1)`. Then `L_k · S_k = m[a(k+1) − 1]`.
  The left side is odd (exactly one term `L_k / i` is odd, namely `i = 2^α`),
  while `m` is even, so the right side is even. Contradiction.

## Contents

| File | What it is |
|---|---|
| `paper/harmonic_paper.pdf` | The paper (source: `paper/harmonic_paper.tex`) |
| `HarmonicNonInteger.lean` | The Lean 4 formalization |

The main theorem is `HarmonicNonInteger.paper_theorem`:

```lean
theorem paper_theorem {n : ℕ} (hn : 2 ≤ n) : ¬ ∃ a : ℤ, S n = (a : ℚ)
```

The file follows the structure of the paper. Part I is a short cross-check via
Mathlib; Part II is the paper's argument (Equation (1), Case 1, Case 2(a)/(b)).

## Building

The exact Lean and Mathlib versions are pinned in `lean-toolchain` and
`lake-manifest.json`.

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

The main theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); this can be checked by running
`#print axioms HarmonicNonInteger.paper_theorem`.

## License

MIT, see `LICENSE`.