import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A first formal leaf for Ford's Hurwitz-zeta estimate

The target is Theorem 1 of Kevin Ford, *Vinogradov's integral and bounds for the
Riemann zeta function*, Proc. London Math. Soc. 85 (2002), 565--633.  The
finite weighted-block estimate below is the Abel transformation used in the
proof of Lemma 7.3, immediately before the cubic exponent `g(j)` is introduced.

Khale uses the Hurwitz part of Ford's theorem in equation (1.2) of
arXiv:2210.06457.  The first theorem records exactly how Khale's removed
initial term is represented by Mathlib's periodic `HurwitzZeta.hurwitzZeta` in
the half-plane of absolute convergence.
-/

open scoped BigOperators
open Complex Finset Set

namespace FordHurwitz

/-- Ford's explicit exponential-sum constants from Theorem 2. -/
def exponentialSumC : ℝ := 9.463

def exponentialSumD : ℝ := 133.66

/-- The exponent generated from `D` in Ford's Lemma 7.3. -/
noncomputable def zetaExponentB : ℝ :=
  (2 / 9) * Real.sqrt (3 * exponentialSumD)

/-- Theorem 2's value `D = 133.66` yields the advertised exponent `B = 4.45`
after rounding upward. -/
theorem zetaExponentB_pos : 0 < zetaExponentB := by
  dsimp [zetaExponentB, exponentialSumD]
  positivity

theorem zetaExponentB_le : zetaExponentB ≤ 4.45 := by
  have hnon : (0 : ℝ) ≤ 3 * 133.66 := by norm_num
  have hs := Real.sq_sqrt hnon
  have hp := Real.sqrt_nonneg (3 * 133.66)
  dsimp [zetaExponentB, exponentialSumD]
  norm_num at hs ⊢
  nlinarith

/-- The oscillatory factor `(n + u) ^ (-it)` written with a real logarithm. -/
noncomputable def phase (u t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-Complex.I * ((t * Real.log (n + u) : ℝ) : ℂ))

/-- Ford's oscillatory factor has modulus one when `n + u` is positive. -/
theorem norm_phase (u t : ℝ) (n : ℕ) : ‖phase u t n‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

/-- The exponential definition agrees with Mathlib's complex power on a
positive real base. -/
theorem cpow_neg_imag_eq_phase {u t : ℝ} {n : ℕ} (hnu : 0 < n + u) :
    ((n + u : ℂ) ^ (-(Complex.I * (t : ℂ)))) = phase u t n := by
  have hbase : (n : ℂ) + (u : ℂ) = (((n : ℝ) + u : ℝ) : ℂ) := by push_cast; rfl
  rw [hbase]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hnu.ne')]
  rw [← Complex.ofReal_log hnu.le]
  congr 1
  push_cast
  ring

/-- Splitting the real decay from the oscillatory part of a Hurwitz-zeta
summand. -/
theorem cpow_neg_real_add_imag_eq_weight_phase
    {u σ t : ℝ} {n : ℕ} (hnu : 0 < n + u) :
    ((n + u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))) =
      (n + u : ℝ) ^ (-σ) • phase u t n := by
  have hbase : (n : ℂ) + (u : ℂ) = (((n : ℝ) + u : ℝ) : ℂ) := by push_cast; rfl
  rw [hbase]
  have hne : ((((n : ℝ) + u : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hnu.ne'
  have hexp : -((σ : ℂ) + Complex.I * (t : ℂ)) =
      ((-σ : ℝ) : ℂ) + (-(Complex.I * (t : ℂ))) := by
    push_cast
    ring
  rw [hexp, Complex.cpow_add _ _ hne, ← Complex.ofReal_cpow hnu.le]
  have hphase := cpow_neg_imag_eq_phase (u := u) (t := t) (n := n) hnu
  rw [hbase] at hphase
  rw [hphase]
  rfl

/-- Khale's notation `u⁻ˢ` is the reciprocal form used by Mathlib's
Dirichlet-series theorem. -/
theorem cpow_neg_eq_one_div_cpow (u : ℝ) (s : ℂ) :
    (u : ℂ) ^ (-s) = 1 / (u : ℂ) ^ s := by
  rw [Complex.cpow_neg, one_div]

/-- In the half-plane of convergence, subtracting Khale's initial term from
Mathlib's Hurwitz zeta leaves precisely the series beginning with `n = 1`.
This also checks the endpoint `u = 1`, which Mathlib represents in the
periodic type `UnitAddCircle`. -/
theorem hasSum_hurwitzZeta_sub_initial
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ 1 / ((n + 1 + u : ℝ) : ℂ) ^ s)
      (HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s - 1 / (u : ℂ) ^ s) := by
  have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re hu hs
  have htail := (hasSum_nat_add_iff' (f := fun n : ℕ ↦ 1 / (n + u : ℂ) ^ s) 1).mpr h
  simpa [add_assoc, add_comm, add_left_comm] using htail

/-- Finite summation by parts in exactly the form used for Ford's weighted
dyadic blocks. -/
theorem weighted_range_by_parts (w : ℕ → ℝ) (z : ℕ → ℂ) (r : ℕ) :
    ∑ i ∈ Finset.range r, w i • z i =
      w (r - 1) • (∑ i ∈ Finset.range r, z i) -
        ∑ i ∈ Finset.range (r - 1),
          (w (i + 1) - w i) • (∑ q ∈ Finset.range (i + 1), z q) := by
  exact Finset.sum_range_by_parts w z r

/-- Abel's transformation with its sharp constant: a nonnegative decreasing
weight costs only its first value times the maximal norm of a prefix sum.
This is the deterministic inequality behind the second line in Ford's proof
of Lemma 7.3. -/
theorem norm_weighted_range_le_first
    {w : ℕ → ℝ} {z : ℕ → ℂ} {r : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (hprefix : ∀ q, q ≤ r → ‖∑ i ∈ Finset.range q, z i‖ ≤ M) :
    ‖∑ i ∈ Finset.range r, w i • z i‖ ≤ w 0 * M := by
  by_cases hr : r = 0
  · subst r
    simp [mul_nonneg (hw0 0) hM]
  rw [weighted_range_by_parts]
  calc
    ‖w (r - 1) • (∑ i ∈ Finset.range r, z i) -
        ∑ i ∈ Finset.range (r - 1),
          (w (i + 1) - w i) • (∑ q ∈ Finset.range (i + 1), z q)‖
        ≤ ‖w (r - 1) • (∑ i ∈ Finset.range r, z i)‖ +
          ‖∑ i ∈ Finset.range (r - 1),
            (w (i + 1) - w i) • (∑ q ∈ Finset.range (i + 1), z q)‖ :=
      norm_sub_le _ _
    _ ≤ w (r - 1) * M +
          ∑ i ∈ Finset.range (r - 1), (w i - w (i + 1)) * M := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
        exact mul_le_mul_of_nonneg_left (hprefix r le_rfl) (hw0 _)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ i))),
          neg_sub]
        apply mul_le_mul_of_nonneg_left
        · apply hprefix
          simp only [Finset.mem_range] at hi
          omega
        · exact sub_nonneg.mpr (hw (Nat.le_succ i))
    _ = w 0 * M := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

/-- The phase prefix sum on the integer interval `N < n ≤ N + q`. -/
noncomputable def phasePrefix (u t : ℝ) (N q : ℕ) : ℂ :=
  ∑ i ∈ Finset.range q, phase u t (N + i + 1)

/-- The weighted block on `N < n ≤ R` appearing in Ford's Lemma 7.3. -/
noncomputable def weightedBlock (u σ t : ℝ) (N R : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (R - N),
    ((N + i + 1 : ℝ) + u) ^ (-σ) • phase u t (N + i + 1)

/-- The weighted phase block is literally Ford's complex-power block. -/
theorem weightedBlock_eq_sum_cpow
    {u σ t : ℝ} {N R : ℕ} (hu : 0 < u) :
    weightedBlock u σ t N R =
      ∑ i ∈ Finset.range (R - N),
        ((N + i + 1 + u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))) := by
  rw [weightedBlock]
  apply Finset.sum_congr rfl
  intro i hi
  have hpos : 0 < (N + i + 1 : ℕ) + u := by
    push_cast
    positivity
  have hterm := (cpow_neg_real_add_imag_eq_weight_phase
    (u := u) (σ := σ) (t := t) (n := N + i + 1) hpos).symm
  simpa only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add] using hterm

/-- The exact partial-summation bound used by Ford before the exponential-sum
estimate is inserted.  It proves the factor `N ^ (-σ)` with no extra constant.
The prefix hypothesis is the finite content of Ford's `S(N,t)` bound on this
particular block. -/
theorem norm_weightedBlock_le
    {u σ t M : ℝ} {N R : ℕ}
    (hu : 0 < u) (hσ : 0 ≤ σ) (hN : 1 ≤ N) (_hNR : N ≤ R) (hM : 0 ≤ M)
    (hprefix : ∀ q, q ≤ R - N → ‖phasePrefix u t N q‖ ≤ M) :
    ‖weightedBlock u σ t N R‖ ≤ (N : ℝ) ^ (-σ) * M := by
  let w : ℕ → ℝ := fun i ↦ ((N + i + 1 : ℝ) + u) ^ (-σ)
  let z : ℕ → ℂ := fun i ↦ phase u t (N + i + 1)
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ Real.rpow_nonneg (by positivity) _
  have hw : Antitone w := by
    intro i j hij
    have hi : w i = ((N + i + 1 : ℝ) + u) ^ (-σ) := rfl
    have hj : w j = ((N + j + 1 : ℝ) + u) ^ (-σ) := rfl
    rw [hi, hj]
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · have hnat : N + i + 1 ≤ N + j + 1 := by omega
      have hcast : (N + i + 1 : ℕ) ≤ N + j + 1 := hnat
      have hreal : ((N + i + 1 : ℕ) : ℝ) ≤ ((N + j + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcast
      push_cast at hreal
      linarith
    · linarith
  have hcore : ‖∑ i ∈ Finset.range (R - N), w i • z i‖ ≤ w 0 * M := by
    apply norm_weighted_range_le_first hM hw0 hw
    intro q hq
    simpa [phasePrefix, z] using hprefix q hq
  rw [weightedBlock]
  change ‖∑ i ∈ Finset.range (R - N), w i • z i‖ ≤ _
  refine hcore.trans ?_
  apply mul_le_mul_of_nonneg_right _ hM
  apply Real.rpow_le_rpow_of_nonpos
  · exact_mod_cast (show 0 < N from Nat.zero_lt_of_lt hN)
  · have : (N : ℝ) ≤ (N : ℝ) + (0 : ℕ) + 1 + u := by
      push_cast
      linarith
    exact this
  · linarith

/-- Source-shaped version of `norm_weightedBlock_le`, with the summand written
as `(n + u) ^ (-σ-it)`. -/
theorem norm_sum_cpow_block_le
    {u σ t M : ℝ} {N R : ℕ}
    (hu : 0 < u) (hσ : 0 ≤ σ) (hN : 1 ≤ N) (hNR : N ≤ R) (hM : 0 ≤ M)
    (hprefix : ∀ q, q ≤ R - N → ‖phasePrefix u t N q‖ ≤ M) :
    ‖∑ i ∈ Finset.range (R - N),
        ((N + i + 1 + u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ))))‖
      ≤ (N : ℝ) ^ (-σ) * M := by
  rw [← weightedBlock_eq_sum_cpow hu]
  exact norm_weightedBlock_le hu hσ hN hNR hM hprefix

end FordHurwitz
