import Mathlib

/-!
# Full MAP and prime-pair endpoint: exact declarations and finite bridges

This file has two deliberately separate jobs.

* `PrimePairEndpoints` gives the literal, unconditional propositions that a
  complete formalization must prove.  In particular, the polylogarithmic mask
  exponents are chosen *after* the requested saving `A` and aperture reserve
  `ε`, and remain fixed for every later `X`, `H`, and Fourier center.
* `FiniteBridges` proves the exact finite square expansion behind the
  variance/Q4+ conversion and the finite Chebyshev counting inequality behind
  the density-one consequence.

No theorem in this file assumes MAP, Shiu, a zero-density theorem, a zero-free
region, Perron's formula, or the MRT transfer.  The final endpoint below is a
`Prop` to be proved, not an axiom and not a theorem with hidden hypotheses.
-/

namespace PrimePairEndpoints

open MeasureTheory Metric Set
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The exact finite von Mangoldt polynomial on `X < n ≤ 2X`. -/
def primeExponentialSum (X : ℝ) (α : UnitAddCircle) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * fourier (n : ℤ) α

/-- Polylogarithmic major arcs, using reduced representatives `0 ≤ a < q`. -/
def majorArcs (X : ℝ) (B B' : ℕ) : Set UnitAddCircle :=
  {α | ∃ q a : ℕ,
    1 ≤ q ∧
    (q : ℝ) ≤ (Real.log X) ^ B ∧
    a < q ∧
    a.Coprime q ∧
    dist α ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle)) ≤
      (Real.log X) ^ B' / X}

def minorArcs (X : ℝ) (B B' : ℕ) : Set UnitAddCircle :=
  (majorArcs X B B')ᶜ

/-- A circle arc of radius `1/(2H)`, hence length `1/H` in the legal range. -/
def centeredArc (H : ℝ) (center : UnitAddCircle) : Set UnitAddCircle :=
  closedBall center ((2 * H)⁻¹)

/--
The all-center local MAP family, with normalized Haar measure.

The quantifier order is part of the declaration: `B` and `B'` may depend on
`A, ε`, but cannot depend on `X`, `H`, or `center`.
-/
def AllCenterLocalMAP : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ B B' : ℕ, ∃ C X₀ : ℝ,
      0 < C ∧ 2 ≤ X₀ ∧
      ∀ X H : ℝ, X₀ ≤ X →
        Real.rpow X (2 / 15 + ε) ≤ H →
        ∀ center : UnitAddCircle,
          (∫ α in centeredArc H center ∩ minorArcs X B B',
              ‖primeExponentialSum X α‖ ^ 2
                ∂AddCircle.haarAddCircle) ≤
            C * X * Real.rpow (Real.log X) (-A)

/-- Von Mangoldt on integers, extended by zero off the positive integers. -/
def integerVonMangoldt (m : ℤ) : ℝ :=
  if 0 < m then ArithmeticFunction.vonMangoldt m.toNat else 0

/-- `R_X(h)`, retaining all prime powers. -/
def primePairCorrelation (X : ℝ) (h : ℤ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    ArithmeticFunction.vonMangoldt n *
      integerVonMangoldt ((n : ℤ) + h)

/-- The twin-prime Euler product. -/
def twinPrimeConstant : ℝ :=
  ∏' p : ℕ,
    if p.Prime ∧ 2 < p then
      ((p : ℝ) * ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ 2
    else 1

/-- Hardy--Littlewood singular series. Its domain deliberately excludes zero. -/
def singularSeries (h : {z : ℤ // z ≠ 0}) : ℝ :=
  if (2 : ℤ) ∣ h.1 then
    2 * twinPrimeConstant *
      ∏' p : ℕ,
        if p.Prime ∧ 2 < p ∧ (p : ℤ) ∣ h.1 then
          ((p : ℝ) - 1) / ((p : ℝ) - 2)
        else 1
  else 0

/-- Exact translated integer window, before deleting zero. -/
def translatedWindow (H h₀ : ℝ) : Finset ℤ :=
  Finset.Icc ⌈h₀ - H⌉ ⌊h₀ + H⌋

/-- Technical totalization used only in sums; the mathematical series remains undefined at zero. -/
def singularSeriesTotal (h : ℤ) : ℝ :=
  if hh : h ≠ 0 then singularSeries ⟨h, hh⟩ else 0

/-- The prime-pair signal with the forbidden zero shift deleted. -/
def primePairSignal (X : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 0 else primePairCorrelation X h

/-- The pointwise Hardy--Littlewood error, with zero shift deleted. -/
def primePairError (X : ℝ) (h : ℤ) : ℝ :=
  primePairSignal X h - X * singularSeriesTotal h

/-- Exact translated-window variance. -/
def primePairVariance (X H h₀ : ℝ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀, |primePairError X h| ^ 2

/-- Exact fourth-correlation quantity in Q4+. -/
def q4Quantity (X H h₀ : ℝ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀, (primePairSignal X h) ^ 2

/-- Exact singular-series-square main term in Q4+. -/
def singularSquareMain (H h₀ : ℝ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀, (singularSeriesTotal h) ^ 2

/-- The first projection used to weld Q4+ to the variance. -/
def firstProjection (X H h₀ : ℝ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    singularSeriesTotal h * primePairSignal X h

def LegalParameters (ε X H h₀ : ℝ) : Prop :=
  Real.rpow X (2 / 15 + ε) ≤ H ∧
  H ≤ Real.rpow X (1 - ε) ∧
  0 ≤ h₀ ∧
  h₀ ≤ Real.rpow X (1 - ε)

/-- Full translated-window variance family. -/
def VarianceFamily : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X H h₀ : ℝ, X₀ ≤ X →
        LegalParameters ε X H h₀ →
        primePairVariance X H h₀ ≤
          C * H * X ^ 2 * Real.rpow (Real.log X) (-A)

/-- Q4+ with the exact singular-square sum as its main term. -/
def Q4PlusFamily : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X H h₀ : ℝ, X₀ ≤ X →
        LegalParameters ε X H h₀ →
        q4Quantity X H h₀ ≤
          X ^ 2 * singularSquareMain H h₀ +
            C * H * X ^ 2 * Real.rpow (Real.log X) (-A)

/-- Shifts failing `X (log X)^(-A)` Hardy--Littlewood accuracy. -/
def exceptionalShifts (A X H h₀ : ℝ) : Finset ℤ :=
  (translatedWindow H h₀).filter fun h =>
    X * Real.rpow (Real.log X) (-A) < |primePairError X h|

/-- Density-one Hardy--Littlewood consequence in every translated window. -/
def DensityOnePrimePairFamily : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X H h₀ : ℝ, X₀ ≤ X →
        LegalParameters ε X H h₀ →
        ((exceptionalShifts A X H h₀).card : ℝ) ≤
          C * H * Real.rpow (Real.log X) (-A)

/-- The single unconditional endpoint that the complete project must prove. -/
def FullUnconditionalMAPEndpoint : Prop :=
  AllCenterLocalMAP ∧ VarianceFamily ∧ Q4PlusFamily ∧ DensityOnePrimePairFamily

end
end PrimePairEndpoints

namespace FiniteBridges

open scoped BigOperators

section Q4Variance

variable {ι : Type*}

def variance (s : Finset ι) (R S : ι → ℝ) (X : ℝ) : ℝ :=
  ∑ h ∈ s, (R h - X * S h) ^ 2

def q4 (s : Finset ι) (R : ι → ℝ) : ℝ :=
  ∑ h ∈ s, (R h) ^ 2

def projection (s : Finset ι) (R S : ι → ℝ) : ℝ :=
  ∑ h ∈ s, S h * R h

def singularMain (s : Finset ι) (S : ι → ℝ) : ℝ :=
  ∑ h ∈ s, (S h) ^ 2

/-- Exact finite identity relating the variance, Q4, and first projection. -/
theorem variance_eq_q4_sub_projection_add_main
    (s : Finset ι) (R S : ι → ℝ) (X : ℝ) :
    variance s R S X =
      q4 s R - 2 * X * projection s R S + X ^ 2 * singularMain s S := by
  classical
  simp only [variance, q4, projection, singularMain]
  calc
    (∑ h ∈ s, (R h - X * S h) ^ 2) =
        ∑ h ∈ s, ((R h) ^ 2 - 2 * X * (S h * R h) + X ^ 2 * (S h) ^ 2) := by
          apply Finset.sum_congr rfl
          intro h hh
          ring
    _ = (∑ h ∈ s, (R h) ^ 2) -
          2 * X * (∑ h ∈ s, S h * R h) +
          X ^ 2 * (∑ h ∈ s, (S h) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.mul_sum]

/-- Variance plus an accurate first projection implies Q4+. -/
theorem q4_le_of_variance_le_of_projection_close
    (s : Finset ι) (R S : ι → ℝ) {X V E : ℝ}
    (hX : 0 ≤ X) (hvar : variance s R S X ≤ V)
    (hproj : |projection s R S - X * singularMain s S| ≤ E) :
    q4 s R ≤ X ^ 2 * singularMain s S + V + 2 * X * E := by
  have hp : projection s R S ≤ X * singularMain s S + E := by
    linarith [abs_le.mp hproj |>.2]
  have hmul : 2 * X * projection s R S ≤
      2 * X * (X * singularMain s S + E) :=
    mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hX)
  have hid := variance_eq_q4_sub_projection_add_main s R S X
  nlinarith

/-- Q4+ plus the same first projection implies the variance bound. -/
theorem variance_le_of_q4_le_of_projection_close
    (s : Finset ι) (R S : ι → ℝ) {X V E : ℝ}
    (hX : 0 ≤ X)
    (hq4 : q4 s R ≤ X ^ 2 * singularMain s S + V)
    (hproj : |projection s R S - X * singularMain s S| ≤ E) :
    variance s R S X ≤ V + 2 * X * E := by
  have hp : X * singularMain s S - E ≤ projection s R S := by
    linarith [abs_le.mp hproj |>.1]
  have hmul : 2 * X * (X * singularMain s S - E) ≤
      2 * X * projection s R S :=
    mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hX)
  have hid := variance_eq_q4_sub_projection_add_main s R S X
  nlinarith

end Q4Variance

section DensityOne

variable {ι : Type*}

/--
Finite Chebyshev counting in the exact form needed for the density-one
prime-pair consequence.  The strict exceptional threshold permits a weak
square lower bound for every exceptional index.
-/
theorem exceptional_card_mul_sq_le_sum_sq
    (s : Finset ι) (e : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (((s.filter fun i => t < |e i|).card : ℝ) * t ^ 2) ≤
      ∑ i ∈ s, |e i| ^ 2 := by
  classical
  let bad := s.filter fun i => t < |e i|
  have hpoint : ∀ i ∈ bad, t ^ 2 ≤ |e i| ^ 2 := by
    intro i hi
    have hi' : t < |e i| := (Finset.mem_filter.mp hi).2
    nlinarith [abs_nonneg (e i)]
  have hcard : (bad.card : ℝ) * t ^ 2 ≤ ∑ i ∈ bad, |e i| ^ 2 := by
    simpa [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum bad (fun i => |e i| ^ 2) (t ^ 2) hpoint)
  have hsubset : bad ⊆ s := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hsum : (∑ i ∈ bad, |e i| ^ 2) ≤ ∑ i ∈ s, |e i| ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i hiS hiBad => sq_nonneg |e i|)
  exact hcard.trans hsum

end DensityOne

end FiniteBridges

namespace PrimePairEndpoints

open scoped BigOperators

/-- The generic finite square identity specialized to the actual prime-pair objects. -/
theorem primePairVariance_exact_identity (X H h₀ : ℝ) :
    primePairVariance X H h₀ =
      q4Quantity X H h₀ - 2 * X * firstProjection X H h₀ +
        X ^ 2 * singularSquareMain H h₀ := by
  simpa [primePairVariance, primePairError, q4Quantity, firstProjection,
    singularSquareMain, FiniteBridges.variance, FiniteBridges.q4,
    FiniteBridges.projection, FiniteBridges.singularMain, sq_abs] using
    FiniteBridges.variance_eq_q4_sub_projection_add_main
      (translatedWindow H h₀) (primePairSignal X) singularSeriesTotal X

/-- The finite exceptional-set count is controlled by the exact variance. -/
theorem exceptionalShifts_card_mul_threshold_sq_le_variance
    (A X H h₀ : ℝ) (hX : 1 ≤ X) :
    ((exceptionalShifts A X H h₀).card : ℝ) *
        (X * Real.rpow (Real.log X) (-A)) ^ 2 ≤
      primePairVariance X H h₀ := by
  have ht : 0 ≤ X * Real.rpow (Real.log X) (-A) :=
    mul_nonneg (zero_le_one.trans hX)
      (Real.rpow_nonneg (Real.log_nonneg hX) _)
  simpa [exceptionalShifts, primePairVariance] using
    FiniteBridges.exceptional_card_mul_sq_le_sum_sq
      (translatedWindow H h₀) (primePairError X) ht

/--
The complete rate-relabeling step from the variance family to the advertised
density-one prime-pair family.  A requested exceptional-set saving `A` uses
the variance theorem with saving `3*A`, exactly as in the paper audit.
-/
theorem varianceFamily_implies_densityOne :
    VarianceFamily → DensityOnePrimePairFamily := by
  intro hvar A ε hA hε
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    hvar (3 * A) ε (by positivity) hε
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXtwo : 2 ≤ X := hX₀.trans hXX₀
  have hXone : 1 ≤ X := one_le_two.trans hXtwo
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hLpos : 0 < Real.log X := Real.log_pos (one_lt_two.trans_le hXtwo)
  have hv := hbound X H h₀ hXX₀ hlegal
  have hc := exceptionalShifts_card_mul_threshold_sq_le_variance A X H h₀ hXone
  have hpow2 :
      Real.rpow (Real.log X) (-A) ^ 2 =
        Real.rpow (Real.log X) ((-A) * (2 : ℝ)) := by
    exact (Real.rpow_mul_natCast hLpos.le (-A) 2).symm
  have hpow :
      Real.rpow (Real.log X) (-A) * Real.rpow (Real.log X) (-A) ^ 2 =
        Real.rpow (Real.log X) (-(3 * A)) := by
    rw [hpow2]
    calc
      Real.rpow (Real.log X) (-A) * Real.rpow (Real.log X) ((-A) * (2 : ℝ)) =
          Real.rpow (Real.log X) ((-A) + (-A) * (2 : ℝ)) :=
        (Real.rpow_add hLpos (-A) ((-A) * (2 : ℝ))).symm
      _ = Real.rpow (Real.log X) (-(3 * A)) := by
        congr 1
        ring
  have hscale :
      (C * H * Real.rpow (Real.log X) (-A)) *
          (X * Real.rpow (Real.log X) (-A)) ^ 2 =
        C * H * X ^ 2 * Real.rpow (Real.log X) (-(3 * A)) := by
    rw [mul_pow, ← hpow]
    ring
  have hmul :
      ((exceptionalShifts A X H h₀).card : ℝ) *
          (X * Real.rpow (Real.log X) (-A)) ^ 2 ≤
        (C * H * Real.rpow (Real.log X) (-A)) *
          (X * Real.rpow (Real.log X) (-A)) ^ 2 := by
    exact hc.trans (hv.trans_eq hscale.symm)
  exact le_of_mul_le_mul_right hmul
    (sq_pos_of_pos (mul_pos hXpos (Real.rpow_pos_of_pos hLpos _)))

end PrimePairEndpoints
