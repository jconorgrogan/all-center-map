import JutilaCollarMeshCutoff

/-!
# Huxley's fixed-modulus density bound across the compact-to-collar gap

The source density exponent is

`3 * (1 - sigma) / (3 * sigma - 1)`

from Huxley's Halasz--Montgomery estimate, as recorded in equation
`zeeshmh` of the Chen--Gupta--Li source.  This module proves only the exact
MAP exponent conversion and endpoint weld.  The source density theorem
itself remains an analytic input and is not declared here.
-/

namespace MAPHuxleyCompactGapExponent

open MAPRelativeNearOneMesh27 MAPJutilaCollarMeshCutoff MAPGuthMaynard

noncomputable section

/-- Literal exponent of the fixed-modulus Huxley density estimate. -/
def huxleyDensityExponent (sigma : ℝ) : ℝ :=
  3 * (1 - sigma) / (3 * sigma - 1)

/-- One fixed subpower exponent selected from Huxley's `o(1)`. -/
def huxleySourceEta : ℝ := 31 / 658560

/-- Final fixed power saving after the relative-cell width and source loss. -/
def huxleyCompactSaving : ℝ := 31 / 329280

theorem huxleySourceEta_pos : 0 < huxleySourceEta := by
  norm_num [huxleySourceEta]

theorem huxleyCompactSaving_pos : 0 < huxleyCompactSaving := by
  norm_num [huxleyCompactSaving]

/-- The Huxley denominator is uniformly positive on the closed MAP gap. -/
theorem huxley_denominator_lower {sigma : ℝ}
    (hsigma : 4 / 5 ≤ sigma) :
    (7 / 5 : ℝ) ≤ 3 * sigma - 1 := by
  linarith

/-- At the MAP height, including the full `u≤1/315` polylog conductor
allowance, Huxley's density coefficient is at most `274/147`. -/
theorem huxley_height_coefficient_le
    {epsilon u sigma : ℝ}
    (hepsilon : 0 ≤ epsilon) (hu : u ≤ 1 / 315)
    (hsigma : 4 / 5 ≤ sigma) :
    3 * (tau epsilon + u) / (3 * sigma - 1) ≤ 274 / 147 := by
  have hden : 0 < 3 * sigma - 1 :=
    lt_of_lt_of_le (by norm_num) (huxley_denominator_lower hsigma)
  rw [div_le_iff₀ hden]
  have htau : tau epsilon + u ≤ 274 / 315 := by
    unfold tau
    linarith
  have hdenLower := huxley_denominator_lower hsigma
  nlinarith

/-- The source exponent is nonnegative on the closed gap. -/
theorem huxleyDensityExponent_nonneg {sigma : ℝ}
    (hsigmaLow : 4 / 5 ≤ sigma) (hsigmaHigh : sigma ≤ 1) :
    0 ≤ huxleyDensityExponent sigma := by
  unfold huxleyDensityExponent
  exact div_nonneg (mul_nonneg (by norm_num) (by linarith))
    (by linarith [huxley_denominator_lower hsigmaLow])

/-- The literal weighted exponent calculation on
`4/5 ≤ sigma ≤ 279/280`.  A relative cell has width at most
`(1-sigma)/24`; Huxley's source `o(1)` is specialized so that its height
cost is at most `31/329280`. -/
theorem huxley_compact_gap_exponent_bound
    {epsilon u eta sigma Delta : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hu : u ≤ 1 / 315)
    (hsigmaLow : 4 / 5 ≤ sigma)
    (hsigmaHigh : sigma ≤ 279 / 280)
    (hDelta : Delta ≤ (1 - sigma) / 24)
    (hetaLoss : (tau epsilon + u) * eta ≤ huxleyCompactSaving) :
    (tau epsilon + u) * (huxleyDensityExponent sigma + eta) +
        2 * (sigma + Delta - 1) ≤ -huxleyCompactSaving := by
  have hden : 0 < 3 * sigma - 1 :=
    lt_of_lt_of_le (by norm_num) (huxley_denominator_lower hsigmaLow)
  have hd : 0 ≤ 1 - sigma := by linarith
  have hdmin : (1 / 280 : ℝ) ≤ 1 - sigma := by linarith
  have hcoef := huxley_height_coefficient_le hepsilon hu hsigmaLow
  have hmul := mul_le_mul_of_nonneg_right hcoef hd
  have hrearrange :
      (tau epsilon + u) * huxleyDensityExponent sigma =
        (3 * (tau epsilon + u) / (3 * sigma - 1)) * (1 - sigma) := by
    unfold huxleyDensityExponent
    field_simp [hden.ne']
  rw [mul_add, hrearrange]
  unfold huxleyCompactSaving at hetaLoss ⊢
  nlinarith

/-- The fixed source choice really fits the explicit loss slot; no
asymptotic notation remains in the exponent arithmetic. -/
theorem huxleySourceEta_fits
    {epsilon u : ℝ} (hepsilon : 0 ≤ epsilon)
    (hu : u ≤ 1 / 315) :
    (tau epsilon + u) * huxleySourceEta ≤ huxleyCompactSaving := by
  have htau : tau epsilon + u ≤ 274 / 315 := by
    unfold tau
    linarith
  have heta : 0 < huxleySourceEta := huxleySourceEta_pos
  unfold huxleySourceEta huxleyCompactSaving
  nlinarith

/-- Pointwise density-to-cell-mass conversion at the literal source base
`R=qT`.  The only analytic premise is `hdensity`; all base conversion,
source loss, and weight arithmetic are discharged. -/
theorem huxley_density_mul_weight_le
    {epsilon u sigma Delta X C R zeroCount : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hu : u ≤ 1 / 315)
    (hsigmaLow : 4 / 5 ≤ sigma)
    (hsigmaHigh : sigma ≤ 279 / 280)
    (hDelta : Delta ≤ (1 - sigma) / 24)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRtoX : R ≤ Real.rpow X (tau epsilon + u))
    (hdensity : zeroCount ≤ C * Real.rpow R
      (huxleyDensityExponent sigma + huxleySourceEta)) :
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
      C * Real.rpow X (-huxleyCompactSaving) := by
  have heta0 : 0 ≤ huxleySourceEta := huxleySourceEta_pos.le
  have hexp0 : 0 ≤ huxleyDensityExponent sigma + huxleySourceEta :=
    add_nonneg (huxleyDensityExponent_nonneg hsigmaLow (by linarith)) heta0
  have hbase : Real.rpow R
      (huxleyDensityExponent sigma + huxleySourceEta) ≤
      Real.rpow (Real.rpow X (tau epsilon + u))
        (huxleyDensityExponent sigma + huxleySourceEta) :=
    Real.rpow_le_rpow hR hRtoX hexp0
  have hcollapse : Real.rpow (Real.rpow X (tau epsilon + u))
      (huxleyDensityExponent sigma + huxleySourceEta) =
      Real.rpow X ((tau epsilon + u) *
        (huxleyDensityExponent sigma + huxleySourceEta)) :=
    (Real.rpow_mul (zero_le_one.trans hX) _ _).symm
  have hdensityX : zeroCount ≤ C * Real.rpow X
      ((tau epsilon + u) *
        (huxleyDensityExponent sigma + huxleySourceEta)) := by
    calc
      zeroCount ≤ C * Real.rpow R
          (huxleyDensityExponent sigma + huxleySourceEta) := hdensity
      _ ≤ C * Real.rpow (Real.rpow X (tau epsilon + u))
          (huxleyDensityExponent sigma + huxleySourceEta) :=
        mul_le_mul_of_nonneg_left hbase hC
      _ = _ := by rw [hcollapse]
  have hweight : 0 ≤ Real.rpow X (2 * (sigma + Delta - 1)) :=
    Real.rpow_nonneg (zero_le_one.trans hX) _
  calc
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
        (C * Real.rpow X ((tau epsilon + u) *
          (huxleyDensityExponent sigma + huxleySourceEta))) *
          Real.rpow X (2 * (sigma + Delta - 1)) :=
      mul_le_mul_of_nonneg_right hdensityX hweight
    _ = C * Real.rpow X ((tau epsilon + u) *
          (huxleyDensityExponent sigma + huxleySourceEta) +
        2 * (sigma + Delta - 1)) := by
      rw [mul_assoc]
      congr 1
      exact (Real.rpow_add (zero_lt_one.trans_le hX) _ _).symm
    _ ≤ C * Real.rpow X (-huxleyCompactSaving) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hX
      apply huxley_compact_gap_exponent_bound hepsilon hu
        hsigmaLow hsigmaHigh hDelta
      exact huxleySourceEta_fits hepsilon hu

/-- Every relative-mesh left endpoint assigned to the Huxley branch lies in
the exact source range. -/
theorem huxley_mesh_endpoint_range {j : ℕ} (hj : j < collarIndex) :
    4 / 5 ≤ relativePoint j ∧ relativePoint j < 279 / 280 := by
  constructor
  · exact (relativePoint_mono (Nat.zero_le j)) |>.trans' (by
      rw [relativePoint_zero])
  · by_contra hnot
    have hge : (279 / 280 : ℝ) ≤ relativePoint j := le_of_not_gt hnot
    have hjle : j ≤ collarIndex - 1 := by
      unfold collarIndex at hj ⊢
      omega
    have hupper := relativePoint_mono hjle
    have hbefore := relativePoint_before_collarIndex
    linarith

/-- Literal relative-cell mass bound for every mesh index assigned to the
Huxley branch.  This connects the exact cumulative-count source exponent to
the half-open multiplicity-weighted cells consumed by the splice theorem. -/
theorem huxley_relativeCellMass_le
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon u X C R : ℝ} {j : ℕ}
    (hj : j < collarIndex)
    (hepsilon : 0 ≤ epsilon) (hu : u ≤ 1 / 315)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRtoX : R ≤ Real.rpow X (tau epsilon + u))
    (hdensity :
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow R
          (huxleyDensityExponent (relativePoint j) + huxleySourceEta)) :
    (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      C * Real.rpow X (-huxleyCompactSaving) := by
  have hrange := huxley_mesh_endpoint_range hj
  have hmass := relativeCellMass_le_count_mul_upperWeight
    S multiplicity beta j hX
  have hlocal := huxley_density_mul_weight_le
    (epsilon := epsilon) (u := u)
    (sigma := relativePoint j) (Delta := relativeWidth j)
    hepsilon hu hrange.1 hrange.2.le
    (by rw [relativeWidth_eq_one_sub_point_div])
    hX hC hR hRtoX hdensity
  calc
    (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) *
        Real.rpow X (2 * (relativePoint (j + 1) - 1)) := hmass
    _ = ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) *
        Real.rpow X
          (2 * (relativePoint j + relativeWidth j - 1)) := by
      rw [relativePoint_succ]
    _ ≤ C * Real.rpow X (-huxleyCompactSaving) := hlocal

end

end MAPHuxleyCompactGapExponent

#print axioms MAPHuxleyCompactGapExponent.huxley_height_coefficient_le
#print axioms MAPHuxleyCompactGapExponent.huxley_compact_gap_exponent_bound
#print axioms MAPHuxleyCompactGapExponent.huxleySourceEta_fits
#print axioms MAPHuxleyCompactGapExponent.huxley_density_mul_weight_le
#print axioms MAPHuxleyCompactGapExponent.huxley_mesh_endpoint_range
#print axioms MAPHuxleyCompactGapExponent.huxley_relativeCellMass_le
