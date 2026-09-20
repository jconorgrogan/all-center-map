import MRTProposition51ProjectionHighGeometry
import MRTProposition51HardBranch

/-!
# The final low/high coefficient weld in MRT Proposition 5.1

The analytic projection arguments on pp. 46--47 have two ordinary-error
scales: `η / H` for the high-frequency piece and
`1 / (|β| * H) / H` for the low-frequency piece.  This file records the
shortest source-faithful final step: their squared contributions add to at
most the square of their sum, which is exactly `ordinaryError`.

No estimate of either projection is postulated here.  The theorem accepts only
the two explicit intermediate majorants that the high- and low-frequency
arguments must prove.
-/

namespace MAPFinishP51Projection

open MeasureTheory
open MAPMRTCorollary53Source

noncomputable section

/-- The two squared projection coefficients fit simultaneously, with no
factor `2`, into the literal coefficient of `ordinaryError`. -/
theorem low_high_coefficients_le_ordinaryError
    {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hH : 0 < H) (hbeta : beta ≠ 0) (heta : 0 ≤ eta) :
    ((1 / (|beta| * H)) ^ 2 / H ^ 2 + eta ^ 2 / H ^ 2) *
        ordinarySlidingMass X H f ≤
      ordinaryError X H f beta eta := by
  have hinv : 0 ≤ 1 / (|beta| * H) := by positivity
  have hHsq : 0 < H ^ 2 := sq_pos_of_pos hH
  have hmass : 0 ≤ ordinarySlidingMass X H f := by
    unfold ordinarySlidingMass
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hcoeff :
      (1 / (|beta| * H)) ^ 2 / H ^ 2 + eta ^ 2 / H ^ 2 ≤
        (eta + 1 / (|beta| * H)) ^ 2 / H ^ 2 := by
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hHsq).2
    nlinarith
  unfold ordinaryError
  exact mul_le_mul_of_nonneg_right hcoeff hmass

/-- Final projection bookkeeping: once the literal low and high pieces have
been bounded at their respective source scales, their sum is absorbed by the
single published `ordinaryError` term. -/
theorem low_add_high_projection_term_le_ordinaryError
    {X H beta eta lowTerm highTerm : ℝ} {f : ℕ → ℂ}
    (hH : 0 < H) (hbeta : beta ≠ 0) (heta : 0 ≤ eta)
    (hlow : lowTerm ≤
      (1 / (|beta| * H)) ^ 2 / H ^ 2 * ordinarySlidingMass X H f)
    (hhigh : highTerm ≤
      eta ^ 2 / H ^ 2 * ordinarySlidingMass X H f) :
    lowTerm + highTerm ≤ ordinaryError X H f beta eta := by
  calc
    lowTerm + highTerm ≤
        (1 / (|beta| * H)) ^ 2 / H ^ 2 * ordinarySlidingMass X H f +
          eta ^ 2 / H ^ 2 * ordinarySlidingMass X H f :=
      add_le_add hlow hhigh
    _ = ((1 / (|beta| * H)) ^ 2 / H ^ 2 + eta ^ 2 / H ^ 2) *
          ordinarySlidingMass X H f := by ring
    _ ≤ ordinaryError X H f beta eta :=
      low_high_coefficients_le_ordinaryError hH hbeta heta

/-! ## The first still-missing analytic contract

The preceding theorem is purely algebraic.  The following definitions expose
the earliest source-facing statement which is not supplied by the current
`LowIBP`/`HighDifferentiation`/`HighGeometry` modules.  They use the literal
Dirichlet sums from the Littlewood--Paley decomposition (76), specialized to
the source logarithmic dual function.
-/

def lowProjectionEnergy
    (X H beta eta : ℝ) (cutoff : ℝ → ℝ) (g : ℝ → ℂ)
    (f : ℕ → ℂ) : ℝ :=
  ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      f n * (Real.sqrt n : ℂ)⁻¹ *
        MAPMRTProposition51HardBranch.lowFrequencyProjection
          X beta eta cutoff
          (MAPMRTProposition51HardBranch.logarithmicDualFunction
            X H beta cutoff g)
          (Real.log n - Real.log X)‖ ^ 2

def highProjectionEnergy
    (X H beta eta : ℝ) (cutoff : ℝ → ℝ) (g : ℝ → ℂ)
    (f : ℕ → ℂ) : ℝ :=
  ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      f n * (Real.sqrt n : ℂ)⁻¹ *
        MAPMRTProposition51HardBranch.highFrequencyProjection
          X beta eta cutoff
          (MAPMRTProposition51HardBranch.logarithmicDualFunction
            X H beta cutoff g)
          (Real.log n - Real.log X)‖ ^ 2

/-- Source-faithful target left after the current local calculus and window
geometry lemmas.  The page-47 low projection carries the *combined* source
coefficient `η + 1 / (|β|H)`; it is not valid to assign only its inverse
part to the low projection.  The high projection retains its `η` scale.
`C` records the absolute constants suppressed in the paper. -/
def LowHighProjectionOrdinaryMajorants
    (C X H beta eta : ℝ) (cutoff : ℝ → ℝ) (f : ℕ → ℂ) : Prop :=
  ∀ g : ℝ → ℂ,
    Integrable g →
    Integrable (fun x ↦ ‖g x‖ ^ 2) →
    (∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) →
    (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1 →
      lowProjectionEnergy X H beta eta cutoff g f ≤
          C * ordinaryError X H f beta eta ∧
      highProjectionEnergy X H beta eta cutoff g f ≤
          C * (eta ^ 2 / H ^ 2 * ordinarySlidingMass X H f)

/-- Deterministic consumer of the precise missing low/high analytic contract.
It closes the ordinary-error bookkeeping for the actual projection sums, but
does not address the medium/stationary projection or the duality reduction to
`sourceEnergy`. -/
theorem actual_low_add_high_projection_energy_le
    {C X H beta eta : ℝ} {cutoff : ℝ → ℝ} {f : ℕ → ℂ}
    (hC : 0 ≤ C) (hH : 0 < H) (hbeta : beta ≠ 0) (heta : 0 ≤ eta)
    (hproj : LowHighProjectionOrdinaryMajorants
      C X H beta eta cutoff f)
    (g : ℝ → ℂ) (hgL1 : Integrable g)
    (hg : Integrable (fun x ↦ ‖g x‖ ^ 2))
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1) :
    lowProjectionEnergy X H beta eta cutoff g f +
        highProjectionEnergy X H beta eta cutoff g f ≤
      (2 * C) * ordinaryError X H f beta eta := by
  obtain ⟨hlow, hhigh⟩ := hproj g hgL1 hg hgSupport hgOne
  have hhigh' :
      C * (eta ^ 2 / H ^ 2 * ordinarySlidingMass X H f) ≤
        C * ordinaryError X H f beta eta := by
    apply mul_le_mul_of_nonneg_left _ hC
    have hmass : 0 ≤ ordinarySlidingMass X H f := by
      unfold ordinarySlidingMass
      exact integral_nonneg fun _ ↦ sq_nonneg _
    unfold ordinaryError
    apply mul_le_mul_of_nonneg_right _ hmass
    have hinv : 0 ≤ 1 / (|beta| * H) := by positivity
    have hcoef : eta ^ 2 ≤ (eta + 1 / (|beta| * H)) ^ 2 := by
      nlinarith
    exact div_le_div_of_nonneg_right hcoef (sq_nonneg H)
  calc
    lowProjectionEnergy X H beta eta cutoff g f +
        highProjectionEnergy X H beta eta cutoff g f ≤
      C * ordinaryError X H f beta eta +
        C * (eta ^ 2 / H ^ 2 * ordinarySlidingMass X H f) :=
      add_le_add hlow hhigh
    _ ≤ C * ordinaryError X H f beta eta +
          C * ordinaryError X H f beta eta := add_le_add le_rfl hhigh'
    _ = (2 * C) * ordinaryError X H f beta eta := by ring

/-- The finite-sum/integral passage needed after either the low change of
variables or equation (77).  Thus this measure-theoretic step is not part of
the remaining analytic gap: once each projected coefficient has an integrable
source integrand, the finite Dirichlet sum moves through the integral exactly.
-/
theorem finite_projection_sum_integral_passage
    {ι : Type*} (s : Finset ι) (coefficient : ι → ℂ)
    (integrand : ι → ℝ → ℂ)
    (hint : ∀ i ∈ s, Integrable (integrand i)) :
    (∑ i ∈ s, coefficient i * ∫ x : ℝ, integrand i x) =
      ∫ x : ℝ, ∑ i ∈ s, coefficient i * integrand i x := by
  rw [integral_finset_sum s]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
  · intro i hi
    exact (hint i hi).const_mul (coefficient i)

/-- The completed part of the actual high-frequency route: once equation
(77) and Cauchy--Schwarz reduce the high projection to the displayed scaled
centered-window energy with coefficient `η² / (32 H²)`, the existing p.46
geometry theorem puts that term inside `ordinaryError`. -/
theorem high_scaled_window_energy_le_ordinaryError
    {X H beta eta lambda : ℝ} {f : ℕ → ℂ}
    (hH : 0 < H) (hbeta : beta ≠ 0) (heta : 0 ≤ eta)
    (hlambdaLower : 1 / 2 ≤ lambda) (hlambdaUpper : lambda ≤ 2) :
    eta ^ 2 / (32 * H ^ 2) *
        (∫ x : ℝ,
          MAPMRTProposition51ProjectionHighGeometry.scaledCenteredWindowSum
            X H lambda f x ^ 2) ≤
      ordinaryError X H f beta eta := by
  have hgeometry :=
    MAPMRTProposition51ProjectionHighGeometry.integral_sq_scaledCenteredWindowSum_le_ordinarySlidingMass
        (X := X) (H := H) (lambda := lambda) (f := f)
        hH.le hlambdaLower hlambdaUpper
  have hscale : 0 ≤ eta ^ 2 / (32 * H ^ 2) := by positivity
  have hmass : 0 ≤ ordinarySlidingMass X H f := by
    unfold ordinarySlidingMass
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hinv : 0 ≤ 1 / (|beta| * H) := by positivity
  calc
    eta ^ 2 / (32 * H ^ 2) *
        (∫ x : ℝ,
          MAPMRTProposition51ProjectionHighGeometry.scaledCenteredWindowSum
            X H lambda f x ^ 2) ≤
      eta ^ 2 / (32 * H ^ 2) *
        (32 * ordinarySlidingMass X H f) :=
      mul_le_mul_of_nonneg_left hgeometry hscale
    _ = eta ^ 2 / H ^ 2 * ordinarySlidingMass X H f := by
      field_simp [hH.ne']
      <;> ring
    _ ≤ ordinaryError X H f beta eta := by
      unfold ordinaryError
      apply mul_le_mul_of_nonneg_right _ hmass
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hH)).2
      nlinarith

end
end MAPFinishP51Projection

#print axioms MAPFinishP51Projection.low_high_coefficients_le_ordinaryError
#print axioms MAPFinishP51Projection.low_add_high_projection_term_le_ordinaryError
#print axioms MAPFinishP51Projection.actual_low_add_high_projection_energy_le
#print axioms MAPFinishP51Projection.finite_projection_sum_integral_passage
#print axioms MAPFinishP51Projection.high_scaled_window_energy_le_ordinaryError
