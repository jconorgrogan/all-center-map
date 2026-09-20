import MellinDetectorLeaf
import Mathlib.Analysis.Complex.JensenFormula

/-!
# A literal Jensen envelope for the local Dirichlet-zero count

This file formalizes the divisor, multiplicity, interval convention, and
Jensen geometry behind Appendix (A.5).  It does not assume or declare an
`O(log(q(|t|+2)))` zero-count theorem.  The sole local premise in the final
Jensen estimate is an upper bound for the L-function on one explicit outer
circle; the center is proved nonzero from Mathlib's Euler-product
nonvanishing theorem.
-/

namespace MAPLocalZeroWindow

open Set Metric
open scoped BigOperators Interval
open DirichletZeros MAPMellinDetectorLeaf

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Symmetric height large enough to contain the closed unit interval
`[t,t+1]`, for positive or negative `t`. -/
def windowHeight (t : ℝ) : ℝ := |t| + 1

/-- The exact closed-interval convention printed in Appendix (A.5). -/
def closedUnitWindowSupport (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : Finset ℂ :=
  (zeroSupport χ σ (windowHeight t)).filter fun ρ =>
    t ≤ ρ.im ∧ ρ.im ≤ t + 1

/-- A half-open version, convenient for disjoint interval partitions. -/
def halfOpenUnitWindowSupport (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : Finset ℂ :=
  (zeroSupport χ σ (windowHeight t)).filter fun ρ =>
    t ≤ ρ.im ∧ ρ.im < t + 1

/-- A centered closed unit window `[t-1/2,t+1/2]`. -/
def centeredUnitWindowSupport (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : Finset ℂ :=
  closedUnitWindowSupport χ σ (t - 1 / 2)

def closedUnitWindowCount (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℕ :=
  ∑ ρ ∈ closedUnitWindowSupport χ σ t,
    zeroMultiplicity χ σ (windowHeight t) ρ

def halfOpenUnitWindowCount (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℕ :=
  ∑ ρ ∈ halfOpenUnitWindowSupport χ σ t,
    zeroMultiplicity χ σ (windowHeight t) ρ

/-- The multiplicity count in the centered closed interval
`[t - 1/2, t + 1/2]`. -/
def centeredUnitWindowCount (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℕ :=
  closedUnitWindowCount χ σ (t - 1 / 2)

/-- The half-open convention is pointwise contained in the manuscript's
closed convention. -/
theorem halfOpenUnitWindowSupport_subset_closed
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) :
    halfOpenUnitWindowSupport χ σ t ⊆
      closedUnitWindowSupport χ σ t := by
  intro ρ hρ
  rw [halfOpenUnitWindowSupport, Finset.mem_filter] at hρ
  rw [closedUnitWindowSupport, Finset.mem_filter]
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.le⟩

theorem halfOpenUnitWindowCount_le_closed
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) :
    halfOpenUnitWindowCount χ σ t ≤
      closedUnitWindowCount χ σ t := by
  unfold halfOpenUnitWindowCount closedUnitWindowCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (halfOpenUnitWindowSupport_subset_closed χ σ t)
    (fun _ _ _ => Nat.zero_le _)

/-- Every ordinate in the closed unit interval lies in the symmetric compact
rectangle used to define its analytic multiplicity. -/
theorem closedUnitWindowSupport_mem_rectangle
    (χ : DirichletCharacter ℂ q) {σ t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ closedUnitWindowSupport χ σ t) :
    ρ ∈ zeroRectangle σ (windowHeight t) := by
  have hsupp : ρ ∈ zeroSupport χ σ (windowHeight t) :=
    (Finset.mem_filter.mp hρ).1
  exact (zeroDivisor χ σ (windowHeight t)).supportWithinDomain
    ((zeroSupport_mem_iff χ σ (windowHeight t) ρ).mp hsupp)

/-- The center and radii used for the Jensen disk.  On the zero-density range
`Re ρ ≥ 1/2`, the true Euclidean corner distance is `sqrt(5/2) < 8/5`.
The outer radius `17/10` leaves the fixed Jensen denominator `log(17/16)`
while keeping the whole circle in `3/10 ≤ Re z ≤ 37/10`. -/
def jensenCenter (t : ℝ) : ℂ :=
  (2 : ℝ) + (t + 1 / 2) * Complex.I

def jensenInnerRadius : ℝ := 8 / 5

def jensenOuterRadius : ℝ := 17 / 10

/-- The arithmetic scale occurring in the intended local zero estimate. -/
def arithmeticScale (q : ℕ) (t : ℝ) : ℝ :=
  q * (|t| + 2)

@[simp] theorem jensenCenter_re (t : ℝ) : (jensenCenter t).re = 2 := by
  simp [jensenCenter]

@[simp] theorem jensenCenter_im (t : ℝ) :
    (jensenCenter t).im = t + 1 / 2 := by
  simp [jensenCenter]

/-- Literal rectangle-to-disk geometry, including both endpoints of the
closed ordinate interval. -/
theorem closedUnitWindowSupport_mem_jensenDisk
    (χ : DirichletCharacter ℂ q) {σ t : ℝ} (hσ : 1 / 2 ≤ σ) {ρ : ℂ}
    (hρ : ρ ∈ closedUnitWindowSupport χ σ t) :
    ρ ∈ closedBall (jensenCenter t) jensenInnerRadius := by
  have hrect := closedUnitWindowSupport_mem_rectangle χ hρ
  have hre := (Complex.mem_reProdIm.mp hrect).1
  have him := (Finset.mem_filter.mp hρ).2
  have hrehalf : 1 / 2 ≤ ρ.re := hσ.trans hre.1
  have hre1 : ρ.re ≤ 1 := hre.2
  rw [mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num [jensenInnerRadius])).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, jensenCenter_re, Complex.sub_im,
    jensenCenter_im]
  norm_num [jensenInnerRadius]
  nlinarith [sq_nonneg (ρ.re - 1 / 2), sq_nonneg (1 - ρ.re),
    sq_nonneg (ρ.im - t), sq_nonneg (t + 1 - ρ.im)]

/-- The regularized L-function is entire, hence analytic on every Jensen
disk. -/
theorem analyticOnNhd_regularizedLFunction_closedBall
    (χ : DirichletCharacter ℂ q) (t R : ℝ) :
    AnalyticOnNhd ℂ (regularizedLFunction χ)
      (closedBall (jensenCenter t) |R|) := by
  intro z _hz
  exact (differentiable_regularizedLFunction χ).analyticAt z

/-- The chosen Jensen center is zero-free.  This is already available from
Mathlib's nonvanishing theorem in `Re s ≥ 1`; no lower modulus estimate is
claimed here. -/
theorem regularizedLFunction_jensenCenter_ne_zero
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    regularizedLFunction χ (jensenCenter t) ≠ 0 := by
  apply regularizedLFunction_ne_zero_of_one_le_re χ
  simp [jensenCenter]

/-- On a point belonging to both the rectangle and the inner Jensen disk,
the two divisors record the same analytic order. -/
theorem zeroDivisor_eq_jensenDivisor
    (χ : DirichletCharacter ℂ q) {σ t : ℝ} {ρ : ℂ}
    (hrect : ρ ∈ zeroRectangle σ (windowHeight t))
    (hball : ρ ∈ closedBall (jensenCenter t) |jensenInnerRadius|) :
    zeroDivisor χ σ (windowHeight t) ρ =
      MeromorphicOn.divisor (regularizedLFunction χ)
        (closedBall (jensenCenter t) |jensenInnerRadius|) ρ := by
  rw [zeroDivisor_apply_of_mem χ σ (windowHeight t) hrect]
  rw [MeromorphicOn.divisor_apply
    ((analyticOnNhd_regularizedLFunction_closedBall χ t
      jensenInnerRadius).meromorphicOn) hball]

/-- The multiplicity-aware count in the manuscript's closed unit window is
bounded by the full divisor mass in the explicit Jensen disk. -/
theorem closedUnitWindowCount_le_jensenDivisor
    (χ : DirichletCharacter ℂ q) {σ t : ℝ} (hσ : 1 / 2 ≤ σ) :
    (closedUnitWindowCount χ σ t : ℤ) ≤
      ∑ᶠ ρ : ℂ,
        MeromorphicOn.divisor (regularizedLFunction χ)
          (closedBall (jensenCenter t) |jensenInnerRadius|) ρ := by
  let D := MeromorphicOn.divisor (regularizedLFunction χ)
    (closedBall (jensenCenter t) |jensenInnerRadius|)
  have hA := analyticOnNhd_regularizedLFunction_closedBall χ t
    jensenInnerRadius
  have hDfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall (jensenCenter t)
      |jensenInnerRadius|)
  have hsubset : closedUnitWindowSupport χ σ t ⊆ hDfinite.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset]
    change D ρ ≠ 0
    have hrect := closedUnitWindowSupport_mem_rectangle χ hρ
    have hball0 := closedUnitWindowSupport_mem_jensenDisk χ hσ hρ
    have hball : ρ ∈ closedBall (jensenCenter t) |jensenInnerRadius| := by
      have hr : 0 < jensenInnerRadius := by norm_num [jensenInnerRadius]
      rw [abs_of_pos hr]
      exact hball0
    rw [← zeroDivisor_eq_jensenDivisor χ hrect hball]
    exact (zeroSupport_mem_iff χ σ (windowHeight t) ρ).mp
      (Finset.mem_filter.mp hρ).1
  have hmult (ρ : ℂ) (hρ : ρ ∈ closedUnitWindowSupport χ σ t) :
      (zeroMultiplicity χ σ (windowHeight t) ρ : ℤ) = D ρ := by
    have hrect := closedUnitWindowSupport_mem_rectangle χ hρ
    have hball0 := closedUnitWindowSupport_mem_jensenDisk χ hσ hρ
    have hball : ρ ∈ closedBall (jensenCenter t) |jensenInnerRadius| := by
      have hr : 0 < jensenInnerRadius := by norm_num [jensenInnerRadius]
      rw [abs_of_pos hr]
      exact hball0
    have hnonneg : 0 ≤ zeroDivisor χ σ (windowHeight t) ρ :=
      zeroDivisor_nonneg_of_mem χ σ (windowHeight t) hrect
    rw [zeroMultiplicity, Int.toNat_of_nonneg hnonneg]
    exact zeroDivisor_eq_jensenDivisor χ hrect hball
  calc
    (closedUnitWindowCount χ σ t : ℤ) =
        ∑ ρ ∈ closedUnitWindowSupport χ σ t, D ρ := by
      unfold closedUnitWindowCount
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact hmult ρ hρ
    _ ≤ ∑ ρ ∈ hDfinite.toFinset, D ρ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun ρ _hD _hnot =>
          MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA ρ)
    _ = ∑ᶠ ρ : ℂ, D ρ := by
      symm
      rw [finsum_eq_sum_of_support_subset D]
      intro ρ hρ
      exact (Set.Finite.mem_toFinset hDfinite).mpr hρ

/-- Jensen's inequality now gives a literal multiplicity-aware local count.
The remaining analytic input is only the stated outer-circle bound. -/
theorem closedUnitWindowCount_le_jensen
    (χ : DirichletCharacter ℂ q) {σ t M : ℝ}
    (hσ : 1 / 2 ≤ σ) (hM : 1 ≤ M)
    (hcircle : ∀ z ∈ sphere (jensenCenter t) |jensenOuterRadius|,
      ‖regularizedLFunction χ z‖ ≤ M) :
    (closedUnitWindowCount χ σ t : ℝ) ≤
      Real.log (M / ‖regularizedLFunction χ (jensenCenter t)‖) /
        Real.log (jensenOuterRadius / jensenInnerRadius) := by
  have hcompare := closedUnitWindowCount_le_jensenDivisor χ (t := t) hσ
  have hcompareR :
      (closedUnitWindowCount χ σ t : ℝ) ≤
        (∑ᶠ ρ : ℂ,
          MeromorphicOn.divisor (regularizedLFunction χ)
            (closedBall (jensenCenter t) |jensenInnerRadius|) ρ : ℤ) := by
    exact_mod_cast hcompare
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := regularizedLFunction χ)
    (c := jensenCenter t) (r := jensenInnerRadius)
    (R := jensenOuterRadius) (M := M)
    (by norm_num [jensenInnerRadius])
    (by norm_num [jensenInnerRadius, jensenOuterRadius]) hM
    (analyticOnNhd_regularizedLFunction_closedBall χ t jensenOuterRadius)
    (regularizedLFunction_jensenCenter_ne_zero χ t) hcircle
  exact hcompareR.trans hJensen

/-- The fixed Jensen denominator is strictly positive. -/
theorem jensenDenominator_pos :
    0 < Real.log (jensenOuterRadius / jensenInnerRadius) := by
  apply Real.log_pos
  norm_num [jensenOuterRadius, jensenInnerRadius]

/-- A growth-ratio estimate on the explicit fixed Jensen disk is the exact
remaining analytic input for a logarithmic local zero count.  This theorem
does not postulate a zero-count estimate: it exposes the quantitative
L-function bound which Jensen needs. -/
theorem closedUnitWindowCount_le_of_fixedDisk_growth
    (χ : DirichletCharacter ℂ q) {σ t M C : ℝ}
    (hσ : 1 / 2 ≤ σ) (hM : 1 ≤ M)
    (hcircle : ∀ z ∈ sphere (jensenCenter t) |jensenOuterRadius|,
      ‖regularizedLFunction χ z‖ ≤ M)
    (hgrowth :
      Real.log (M / ‖regularizedLFunction χ (jensenCenter t)‖) ≤
        C * Real.log (arithmeticScale q t)) :
    (closedUnitWindowCount χ σ t : ℝ) ≤
      C * Real.log (arithmeticScale q t) /
        Real.log (jensenOuterRadius / jensenInnerRadius) := by
  exact (closedUnitWindowCount_le_jensen χ hσ hM hcircle).trans
    (div_le_div_of_nonneg_right hgrowth jensenDenominator_pos.le)

end

end MAPLocalZeroWindow
