/-
  HarmonicNonInteger.lean

  Lean 4 + Mathlib formalization of
    "A Proof by Contradiction on the Non-Integer Property of
     Partial Harmonic Sums"  (Srivatsan Sriram, 2026).

  Main result (`paper_theorem`): for every integer n ≥ 2,
  S_n = 1/2 + 1/3 + … + 1/n is not an integer.

  Part 0   Definitions.  `S n = ∑_{i=2}^{n} 1/i`, and the step
           S_{k+1} = S_k + 1/(k+1)                              (`S_succ`).

  Part I   A short proof through Mathlib's `harmonic_not_int`, kept as an
           independent cross-check.  Part II does not use it.

  Part II  The proof from the paper.
             * Helpers: the 2-adic valuation `v₂`, L_k = LCM(2,…,k),
               α = max_{2≤i≤k} v₂(i), and Lemma 1
               (`unique_max`, `two_pow_alpha_mem`, `L_form`, `v2_L`).
             * Equation (1) and gcd(a(k+1)−1, k+1) = 1       (`eq1`, `gcd_eq_one`).
             * Case 1, (k+1) ∤ L_k                  (`den_S_dvd_L`, `dvd_den_of_mul`).
             * Case 2, (k+1) ∣ L_k: ∆ is odd (`odd_Delta`), m is even (`even_m`),
               and the two contradict each other                  (`paper_core`).
             * `paper_theorem`: the main theorem.
-/

import Mathlib

open Finset

namespace HarmonicNonInteger

/-! ## Part 0 — definitions and the transition S_{k+1} = S_k + 1/(k+1) -/

/-- `S n = ∑_{i=2}^{n} 1/i`. -/
noncomputable def S (n : ℕ) : ℚ := ∑ i ∈ Icc 2 n, (i : ℚ)⁻¹

lemma S_one : S 1 = 0 := by
  unfold S
  rw [Finset.Icc_eq_empty (show ¬ (2 : ℕ) ≤ 1 by norm_num)]
  simp

lemma S_succ {k : ℕ} (hk : 1 ≤ k) : S (k + 1) = S k + ((k : ℚ) + 1)⁻¹ := by
  unfold S
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1)]
  push_cast
  ring

/-! ## Part I — cross-check through Mathlib -/

lemma S_eq_harmonic_sub_one : ∀ n : ℕ, S (n + 1) = harmonic (n + 1) - 1 := by
  intro n
  induction n with
  | zero =>
    rw [zero_add, S_one]
    simp [harmonic]
  | succ n ih =>
    rw [S_succ (by omega), ih, harmonic_succ (n + 1)]
    push_cast
    ring

theorem S_not_int_mathlib {n : ℕ} (hn : 2 ≤ n) : ¬ ∃ a : ℤ, S n = (a : ℚ) := by
  rintro ⟨a, ha⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := S_eq_harmonic_sub_one m
  obtain ⟨b, hb⟩ : ∃ b : ℤ, harmonic (m + 1) = (b : ℚ) :=
    ⟨a + 1, by rw [ha] at h; push_cast; linarith⟩
  exact harmonic_not_int hn (by rw [hb]; simp [Rat.isInt])

/-! ## Part II — the paper's proof -/

section Paper

/-! ### Elementary helpers -/

/-- Every positive `n` is `2^e * b` with `b` odd. -/
lemma two_pow_mul_odd (n : ℕ) (hn : 1 ≤ n) : ∃ e b : ℕ, Odd b ∧ n = 2 ^ e * b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with ⟨c, hc⟩ | hodd
    · obtain ⟨e, b, hb, h⟩ := ih c (by omega) (by omega)
      exact ⟨e + 1, b, hb, by rw [hc, h]; ring⟩
    · exact ⟨0, n, hodd, by simp⟩

/-- Product of the odd numbers `≤ k`. -/
def Qn (k : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 k).filter (fun j => Odd j), j

lemma Qn_odd (k : ℕ) : Odd (Qn k) := by
  unfold Qn
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro j hj
  exact (Finset.mem_filter.mp hj).2

/-! ### 2-adic valuations

  `v2 n` is defined directly from the decomposition `n = 2^e * b` (b odd),
  so nothing here depends on Mathlib's `padicValNat` / `multiplicity` API. -/

/-- The exponent of 2 in a decomposition is unique. -/
lemma two_pow_mul_odd_unique {e e' b b' : ℕ} (hb : Odd b) (hb' : Odd b')
    (h : 2 ^ e * b = 2 ^ e' * b') : e = e' := by
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, e' = e + d + 1 := ⟨e' - e - 1, by omega⟩
    have h2e : 0 < 2 ^ e := by positivity
    have hbb : b = 2 * (2 ^ d * b') := by
      apply Nat.eq_of_mul_eq_mul_left h2e
      calc 2 ^ e * b = 2 ^ (e + d + 1) * b' := h
        _ = 2 ^ e * (2 * (2 ^ d * b')) := by ring
    obtain ⟨r, hr⟩ := hb
    omega
  · exact heq
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, e = e' + d + 1 := ⟨e - e' - 1, by omega⟩
    have h2e : 0 < 2 ^ e' := by positivity
    have hbb : b' = 2 * (2 ^ d * b) := by
      apply Nat.eq_of_mul_eq_mul_left h2e
      calc 2 ^ e' * b' = 2 ^ (e' + d + 1) * b := h.symm
        _ = 2 ^ e' * (2 * (2 ^ d * b)) := by ring
    obtain ⟨r, hr⟩ := hb'
    omega

/-- `v2 n` = the exponent of 2 in `n` (0 for `n = 0`). -/
noncomputable def v2 (n : ℕ) : ℕ :=
  if h : 1 ≤ n then (two_pow_mul_odd n h).choose else 0

local notation "v₂" => v2

lemma v2_decomp {e b : ℕ} (hb : Odd b) : v₂ (2 ^ e * b) = e := by
  have h0 : 0 < 2 ^ e * b := Nat.mul_pos (by positivity) hb.pos
  have h1 : 1 ≤ 2 ^ e * b := by omega
  have key : v2 (2 ^ e * b) = (two_pow_mul_odd (2 ^ e * b) h1).choose := by
    simp [v2, h1]
  rw [key]
  obtain ⟨b', hb', h'⟩ := (two_pow_mul_odd (2 ^ e * b) h1).choose_spec
  exact two_pow_mul_odd_unique hb' hb h'.symm

lemma v2_odd {b : ℕ} (hb : Odd b) : v₂ b = 0 := by
  have := v2_decomp (e := 0) hb
  simpa using this

lemma v2_pow (n : ℕ) : v₂ (2 ^ n) = n := by
  have := v2_decomp (e := n) (b := 1) odd_one
  simpa using this

lemma v2_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : v₂ (a * b) = v₂ a + v₂ b := by
  obtain ⟨e1, b1, hb1, rfl⟩ := two_pow_mul_odd a (Nat.pos_of_ne_zero ha)
  obtain ⟨e2, b2, hb2, rfl⟩ := two_pow_mul_odd b (Nat.pos_of_ne_zero hb)
  have h : 2 ^ e1 * b1 * (2 ^ e2 * b2) = 2 ^ (e1 + e2) * (b1 * b2) := by ring
  rw [h, v2_decomp (hb1.mul hb2), v2_decomp hb1, v2_decomp hb2]

/-- `v₂ n ≥ 1  ⇒  n` even. -/
lemma even_of_v2_pos {n : ℕ} (hn : n ≠ 0) (h : 1 ≤ v₂ n) : Even n := by
  obtain ⟨e, b, hb, rfl⟩ := two_pow_mul_odd n (Nat.pos_of_ne_zero hn)
  rw [v2_decomp hb] at h
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  exact ⟨2 ^ e' * b, by ring⟩

/-! ### L_k = LCM(2,…,k) -/

/-- `L k = LCM(2, 3, …, k)`. -/
def L (k : ℕ) : ℕ := (Finset.Icc 2 k).lcm id

lemma dvd_L {k i : ℕ} (hi : i ∈ Finset.Icc 2 k) : i ∣ L k := Finset.dvd_lcm hi

lemma L_dvd {k T : ℕ} (h : ∀ i ∈ Finset.Icc 2 k, i ∣ T) : L k ∣ T := Finset.lcm_dvd h

lemma L_one : L 1 = 1 := by
  unfold L
  rw [Finset.Icc_eq_empty (show ¬ (2 : ℕ) ≤ 1 by norm_num)]
  simp

/-! ### α = max_{2 ≤ i ≤ k} v₂(i), and the uniqueness of 2^α -/

/-- `α = max_{2≤i≤k} v₂(i)`. -/
noncomputable def alpha (k : ℕ) : ℕ := (Finset.Icc 2 k).sup (fun i => v₂ i)

lemma v2_le_alpha {k i : ℕ} (hi : i ∈ Finset.Icc 2 k) : v₂ i ≤ alpha k := by
  unfold alpha
  exact Finset.le_sup (f := fun i => v₂ i) hi

lemma exists_attain {k : ℕ} (hk : 2 ≤ k) : ∃ i ∈ Finset.Icc 2 k, v₂ i = alpha k := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup (Finset.Icc 2 k)
    ⟨2, Finset.mem_Icc.mpr ⟨le_refl 2, hk⟩⟩ (fun i => v₂ i)
  exact ⟨i, hi, h.symm⟩

/-- "Within `{2,…,k}` the element `2^α` is strictly unique in achieving this
    maximum valuation."  (the uniqueness half) -/
lemma unique_max {k i : ℕ} (hi : i ∈ Finset.Icc 2 k) (hv : v₂ i = alpha k) :
    i = 2 ^ alpha k := by
  obtain ⟨hi2, hik⟩ := Finset.mem_Icc.mp hi
  obtain ⟨e, b, hb, hib⟩ := two_pow_mul_odd i (by omega)
  have he : e = alpha k := by
    rw [hib, v2_decomp hb] at hv
    exact hv
  subst he
  by_contra hne
  have hb1 : b ≠ 1 := by
    intro h
    apply hne
    rw [hib, h, mul_one]
  have hb3 : 3 ≤ b := by
    obtain ⟨r, hr⟩ := hb
    omega
  have h3 : 2 ^ alpha k * 3 ≤ 2 ^ alpha k * b := Nat.mul_le_mul_left _ hb3
  have hpos : 0 < 2 ^ alpha k := by positivity
  have hp : 2 ^ (alpha k + 1) = 2 ^ alpha k * 2 := by ring
  have hmem2 : 2 ^ (alpha k + 1) ∈ Finset.Icc 2 k :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have := v2_le_alpha hmem2
  rw [v2_pow] at this
  omega

/-- "…the element `2^α` …": it does lie in `{2,…,k}` (existence half). -/
lemma two_pow_alpha_mem {k : ℕ} (hk : 2 ≤ k) : 2 ^ alpha k ∈ Finset.Icc 2 k := by
  obtain ⟨i, hi, hv⟩ := exists_attain hk
  have := unique_max hi hv
  rw [← this]
  exact hi

lemma one_le_alpha {k : ℕ} (hk : 2 ≤ k) : 1 ≤ alpha k := by
  by_contra hlt
  have h0 : alpha k = 0 := by omega
  have h2 := (Finset.mem_Icc.mp (two_pow_alpha_mem hk)).1
  rw [h0] at h2
  norm_num at h2

/-! ### v₂(L_k) = α : write `L_k = 2^α · o` with `o` odd -/

/-- Every `i ∈ [2,k]` divides `2^α · Qn k`  (hence so does `L_k`). -/
lemma dvd_pow_Qn {k i : ℕ} (hi : i ∈ Finset.Icc 2 k) : i ∣ 2 ^ alpha k * Qn k := by
  obtain ⟨hi2, hik⟩ := Finset.mem_Icc.mp hi
  obtain ⟨e, b, hb, hib⟩ := two_pow_mul_odd i (by omega)
  have hb1 : 1 ≤ b := hb.pos
  have h2e : 0 < 2 ^ e := by positivity
  have hbi : b ≤ i := by nlinarith [hib, hb1, h2e]
  have heα : e ≤ alpha k := by
    have := v2_le_alpha hi
    rwa [hib, v2_decomp hb] at this
  have hbQ : b ∣ Qn k := by
    unfold Qn
    apply Finset.dvd_prod_of_mem (fun j : ℕ => j)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb1, by omega⟩, hb⟩
  rw [hib]
  exact mul_dvd_mul (pow_dvd_pow 2 heα) hbQ

lemma L_form {k : ℕ} (hk : 2 ≤ k) : ∃ o, Odd o ∧ L k = 2 ^ alpha k * o := by
  have hmem := two_pow_alpha_mem hk
  obtain ⟨o, ho⟩ := dvd_L hmem
  refine ⟨o, ?_, ho⟩
  have hLd : L k ∣ 2 ^ alpha k * Qn k := L_dvd (fun i hi => dvd_pow_Qn hi)
  rw [ho] at hLd
  have hpos : 0 < 2 ^ alpha k := by positivity
  have : o ∣ Qn k := Nat.dvd_of_mul_dvd_mul_left hpos hLd
  exact (Qn_odd k).of_dvd_nat this

lemma L_pos {k : ℕ} (hk : 2 ≤ k) : 0 < L k := by
  obtain ⟨o, ho, h⟩ := L_form hk
  rw [h]
  exact Nat.mul_pos (by positivity) ho.pos

/-- `v₂(L_k) = α`. -/
lemma v2_L {k : ℕ} (hk : 2 ≤ k) : v₂ (L k) = alpha k := by
  obtain ⟨o, ho, h⟩ := L_form hk
  have h2 : (2 : ℕ) ^ alpha k ≠ 0 := by positivity
  rw [h, v2_mul h2 ho.pos.ne', v2_pow, v2_odd ho, add_zero]

/-! ### Equation (1) and gcd(a(k+1)−1, k+1) = 1 -/

/-- Equation (1):  `S_k = a − 1/(k+1) = (a(k+1) − 1)/(k+1)`. -/
lemma eq1 {k : ℕ} {a : ℤ} (hk1 : 1 ≤ k) (ha : S (k + 1) = (a : ℚ)) :
    S k = ((a * ((k : ℤ) + 1) - 1 : ℤ) : ℚ) / ((k : ℚ) + 1) := by
  have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hne]
  have h := S_succ hk1
  rw [ha] at h
  have hx : ((k : ℚ) + 1)⁻¹ * ((k : ℚ) + 1) = 1 := by field_simp
  have hS : S k = (a : ℚ) - ((k : ℚ) + 1)⁻¹ := by linarith
  rw [hS]
  push_cast
  linear_combination (-1 : ℚ) * hx

/-- "gcd(a(k+1) − 1, k+1) = gcd(−1, k+1) = 1". -/
lemma gcd_eq_one (a : ℤ) (k : ℕ) : Int.gcd (a * ((k : ℤ) + 1) - 1) ((k : ℤ) + 1) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp ⟨-1, a, by ring⟩

lemma isCoprime_succ (a : ℤ) (k : ℕ) :
    IsCoprime ((k : ℤ) + 1) (a * ((k : ℤ) + 1) - 1) := ⟨a, -1, by ring⟩

/-! ### Case 1 : denominators -/

/-- Clearing denominators: `L * S k = ∑ L / i`  (a natural number). -/
lemma mul_S_eq (k L : ℕ) (hdiv : ∀ i, 2 ≤ i → i ≤ k → i ∣ L) :
    (L : ℚ) * S k = ((∑ i ∈ Icc 2 k, L / i : ℕ) : ℚ) := by
  unfold S
  rw [Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hd := hdiv i hi.1 hi.2
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_div hd hi0, div_eq_mul_inv]

/-- If `m * q` is an integer then the reduced denominator of `q` divides `m`. -/
lemma den_dvd_of_mul_int (q : ℚ) (m : ℕ) (n : ℤ) (h : (m : ℚ) * q = n) : q.den ∣ m := by
  have h2 : ((m : ℤ) * q.num : ℤ) = n * q.den := by
    have : (((m : ℤ) * q.num : ℤ) : ℚ) = ((n * q.den : ℤ) : ℚ) := by
      push_cast
      rw [← Rat.mul_den_eq_num, ← h]
      ring
    exact_mod_cast this
  have h3 : q.den ∣ m * q.num.natAbs := by
    have h4 : (q.den : ℤ) ∣ (m : ℤ) * q.num := ⟨n, by rw [h2]; ring⟩
    have h5 := Int.natAbs_dvd_natAbs.mpr h4
    simpa [Int.natAbs_mul] using h5
  exact Nat.Coprime.dvd_of_dvd_mul_right q.reduced.symm h3

/-- If `q * d = X` with `gcd(d, X) = 1`, then `d` divides the reduced denominator of `q`. -/
lemma dvd_den_of_mul {q : ℚ} {d : ℕ} {X : ℤ} (h : q * d = X)
    (hcop : IsCoprime (d : ℤ) X) : d ∣ q.den := by
  have h2 : q.num * (d : ℤ) = X * q.den := by
    have : ((q.num * (d : ℤ) : ℤ) : ℚ) = ((X * q.den : ℤ) : ℚ) := by
      push_cast
      rw [← Rat.mul_den_eq_num, ← h]
      ring
    exact_mod_cast this
  have h3 : (d : ℤ) ∣ X * q.den := ⟨q.num, by rw [← h2]; ring⟩
  have h4 : (d : ℤ) ∣ (q.den : ℤ) := hcop.dvd_of_dvd_mul_left h3
  exact_mod_cast h4

/-- "The denominator of `S_k`, in lowest terms, must divide `L_k`." -/
lemma den_S_dvd_L (k : ℕ) : (S k).den ∣ L k := by
  have h := mul_S_eq k (L k) (fun i hi hik => dvd_L (Finset.mem_Icc.mpr ⟨hi, hik⟩))
  exact den_dvd_of_mul_int (S k) (L k) ((∑ i ∈ Finset.Icc 2 k, L k / i : ℕ) : ℤ)
    (by exact_mod_cast h)

/-! ### Case 2 : parity -/

/-- "The sum of an arbitrary number of even integers and exactly one odd integer
    is strictly odd.  Therefore ∆ is odd." -/
lemma odd_Delta {k : ℕ} (hk : 2 ≤ k) : Odd (∑ i ∈ Finset.Icc 2 k, L k / i) := by
  obtain ⟨o, ho, hLo⟩ := L_form hk
  have hmem := two_pow_alpha_mem hk
  have h2pos : 0 < 2 ^ alpha k := by positivity
  rw [← Finset.add_sum_erase _ _ hmem]
  apply Odd.add_even
  · -- the unique term i = 2^α :  L_k / 2^α = o  is odd
    have : L k / 2 ^ alpha k = o := by
      rw [hLo]
      exact Nat.mul_div_cancel_left o h2pos
    rw [this]
    exact ho
  · -- every other term is even :  v₂(L_k) = α > v₂(i)
    apply Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) ⟨0, rfl⟩
    intro i hi
    show Even (L k / i)
    obtain ⟨hne, hi'⟩ := Finset.mem_erase.mp hi
    obtain ⟨hi2, hik⟩ := Finset.mem_Icc.mp hi'
    have hle := v2_le_alpha hi'
    have hlt : v₂ i < alpha k :=
      lt_of_le_of_ne hle (fun h => hne (unique_max hi' h))
    obtain ⟨q, hq⟩ := dvd_L hi'
    have hi0 : i ≠ 0 := by omega
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq
      exact (L_pos hk).ne' hq
    have hqd : L k / i = q := by
      rw [hq]
      exact Nat.mul_div_cancel_left q (by omega)
    rw [hqd]
    apply even_of_v2_pos hq0
    have := v2_L hk
    rw [hq, v2_mul hi0 hq0] at this
    omega

/-- Cases 2(a) and 2(b): if `L_k = m (k+1)` then `m` is even. -/
lemma even_m {k m : ℕ} (hk : 2 ≤ k) (hm : L k = (k + 1) * m) : Even m := by
  have hLpos := L_pos hk
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm
    exact hLpos.ne' hm
  have hv : v₂ (L k) = v₂ (k + 1) + v₂ m := by
    rw [hm]
    exact v2_mul (by omega) hm0
  have hvL := v2_L hk
  apply even_of_v2_pos hm0
  rcases Nat.even_or_odd (k + 1) with _hev | hodd
  · -- Case 2(b): (k+1) is even
    obtain ⟨β, b, hb, hkb⟩ := two_pow_mul_odd (k + 1) (by omega)
    have hvk : v₂ (k + 1) = β := by
      rw [hkb, v2_decomp hb]
    have hβα : β ≤ alpha k := by omega
    -- (k+1) is not a pure power of 2
    have hb1 : b ≠ 1 := by
      intro hb1
      subst hb1
      have h1 := (Finset.mem_Icc.mp (two_pow_alpha_mem hk)).2
      have h2 : 2 ^ β ≤ 2 ^ alpha k := Nat.pow_le_pow_right (by norm_num) hβα
      omega
    -- so b > 1 (odd), i.e. b ≥ 3
    have hb3 : 3 ≤ b := by
      obtain ⟨r, hr⟩ := hb
      omega
    -- and β < α
    have hβlt : β < alpha k := by
      rcases Nat.lt_or_ge β (alpha k) with h | h
      · exact h
      · exfalso
        have hβeq : β = alpha k := le_antisymm hβα h
        rw [hβeq] at hkb
        have h3 : 2 ^ alpha k * 3 ≤ 2 ^ alpha k * b := Nat.mul_le_mul_left _ hb3
        have hpos : 0 < 2 ^ alpha k := by positivity
        have hp : 2 ^ (alpha k + 1) = 2 ^ alpha k * 2 := by ring
        have hmem2 : 2 ^ (alpha k + 1) ∈ Finset.Icc 2 k :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have := v2_le_alpha hmem2
        rw [v2_pow] at this
        omega
    -- α = v₂(m) + β  with β < α  ⇒  v₂(m) ≥ 1
    omega
  · -- Case 2(a): (k+1) is odd, so v₂(m) = v₂(L_k) = α ≥ 1
    have h0 := v2_odd hodd
    have h1 := one_le_alpha hk
    omega

/-! ### The core of the proof -/

/-- Suppose `S_{k+1} = a ∈ ℤ`, `k ≥ 1`.  Contradiction. -/
theorem paper_core {k : ℕ} {a : ℤ} (hk1 : 1 ≤ k) (ha : S (k + 1) = (a : ℚ)) : False := by
  -- Equation (1)
  have e1 := eq1 hk1 ha
  have e1' : S k * ((k : ℚ) + 1) = (a : ℚ) * ((k : ℚ) + 1) - 1 := by
    have := (eq_div_iff (by positivity : ((k : ℚ) + 1) ≠ 0)).mp e1
    push_cast at this
    exact this
  by_cases hcase : (k + 1) ∣ L k
  · ---------------------------------------------------------------- Case 2
    have hk : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this
      rw [L_one] at hcase
      omega
    -- Equation (2):  L_k = m (k+1)
    obtain ⟨m, hm⟩ := hcase
    -- ∆ = L_k · S_k = ∑ L_k / i
    obtain ⟨Δ, hΔdef⟩ : ∃ Δ, Δ = ∑ i ∈ Finset.Icc 2 k, L k / i := ⟨_, rfl⟩
    have hodd : Odd Δ := by
      rw [hΔdef]
      exact odd_Delta hk
    have hmul : (L k : ℚ) * S k = (Δ : ℚ) := by
      rw [hΔdef]
      exact mul_S_eq k (L k) (fun i hi hik => dvd_L (Finset.mem_Icc.mpr ⟨hi, hik⟩))
    -- Equation (3):  L_k · S_k = m [a(k+1) − 1]
    have hΔ : (Δ : ℤ) = (m : ℤ) * (a * ((k : ℤ) + 1) - 1) := by
      have hq : (Δ : ℚ) = (m : ℚ) * ((a : ℚ) * ((k : ℚ) + 1) - 1) := by
        rw [← hmul, hm]
        push_cast
        linear_combination (m : ℚ) * e1'
      exact_mod_cast hq
    -- m is even (Cases 2(a), 2(b))
    obtain ⟨s, hs⟩ := even_m hk hm
    -- ∆ is odd, but ∆ = m [ … ] is even
    obtain ⟨r, hr⟩ := hodd
    have h3 : (Δ : ℤ) = 2 * ((s : ℤ) * (a * ((k : ℤ) + 1) - 1)) := by
      rw [hΔ, hs]
      push_cast
      ring
    have hr' : (Δ : ℤ) = 2 * (r : ℤ) + 1 := by exact_mod_cast hr
    omega
  · ---------------------------------------------------------------- Case 1
    -- (k+1) ∣ den(S_k) : S_k = (a(k+1) − 1)/(k+1) is already in lowest terms
    have hd1 : (k + 1) ∣ (S k).den := by
      apply dvd_den_of_mul (X := a * ((k : ℤ) + 1) - 1)
      · push_cast
        exact e1'
      · push_cast
        exact isCoprime_succ a k
    -- den(S_k) ∣ L_k
    exact hcase (dvd_trans hd1 (den_S_dvd_L k))

/-- **Theorem 1.**  For all integers `n ≥ 2`, `S_n` is not an integer. -/
theorem paper_theorem {n : ℕ} (hn : 2 ≤ n) : ¬ ∃ a : ℤ, S n = (a : ℚ) := by
  rintro ⟨a, ha⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact paper_core (by omega) ha

end Paper

end HarmonicNonInteger

-- To list the axioms the main theorem depends on, uncomment:
-- #print axioms HarmonicNonInteger.paper_theorem
