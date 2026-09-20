import HarmonicInterfaces
import SingularSeriesFiniteFactors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Prime-pair major-arc weld

This file formalizes the exact, MAP-owned algebra in manuscript (4.3), before
the genuinely analytic estimates are applied.  In particular it fixes:

* the reduced representatives `0 ≤ a < q` used by the rational mask;
* the normalized-Haar Fourier sign `fourier (-h)`;
* the square of the Möbius/totient coefficient;
* the separation of the rational Ramanujan coefficient from the continuous
  dyadic autocorrelation kernel;
* the exact major/minor/support boundary decomposition.

No theorem called `MajorArc` is assumed here.  The pointwise prime-polynomial
approximation, the continuous-kernel tail, and the Ramanujan-series tail remain
separate analytic obligations.
-/

namespace MAPMajorArcWeld

open AddCircle MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

noncomputable section

/-- Reduced representatives modulo `q`, matching `majorArcs`. -/
def reducedResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a => a.Coprime q

theorem mem_reducedResidues {q a : ℕ} :
    a ∈ reducedResidues q ↔ a < q ∧ a.Coprime q := by
  simp [reducedResidues]

/-- The rational point `a/q` on the normalized circle `ℝ/ℤ`. -/
def rationalCenter (q a : ℕ) : UnitAddCircle :=
  (↑((a : ℝ) / (q : ℝ)) : UnitAddCircle)

/-- Ramanujan coefficient with exactly the paper's Fourier sign. -/
def ramanujanCoefficient (q : ℕ) (h : ℤ) : ℂ :=
  ∑ a ∈ reducedResidues q, fourier (-h) (rationalCenter q a)

/-- The coefficient in the prime-polynomial major-arc approximation. -/
def primeMajorCoefficient (q : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (q.totient : ℂ)

/-- Its square-norm, kept as a complex scalar for the Fourier formula. -/
def primeMajorSquareCoefficient (q : ℕ) : ℂ :=
  ((‖primeMajorCoefficient q‖ ^ 2 : ℝ) : ℂ)

/-- Truncated Ramanujan series produced by denominators `1 ≤ q ≤ Q`. -/
def truncatedSingularCoefficient (Q : ℕ) (h : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q,
    primeMajorSquareCoefficient q * ramanujanCoefficient q h

/-- A generic continuous Fourier kernel.  The major-arc factorization is
proved for arbitrary `V`, so its algebra is independent of the analytic
construction of the dyadic integral. -/
def truncatedContinuousKernel
    (V : ℝ → ℂ) (R : ℝ) (h : ℤ) : ℂ :=
  ∫ β in -R..R,
    ((‖V β‖ ^ 2 : ℝ) : ℂ) * fourier (-h) (β : UnitAddCircle)

/-- Contribution of one modeled rational arc in lifted `β` coordinates. -/
def modeledRationalArc
    (V : ℝ → ℂ) (R : ℝ) (q a : ℕ) (h : ℤ) : ℂ :=
  ∫ β in -R..R,
    ((‖primeMajorCoefficient q * V β‖ ^ 2 : ℝ) : ℂ) *
      fourier (-h) (rationalCenter q a + (β : UnitAddCircle))

theorem primeMajorSquareCoefficient_eq_mul_conj (q : ℕ) :
    primeMajorSquareCoefficient q =
      primeMajorCoefficient q * conj (primeMajorCoefficient q) := by
  rw [primeMajorSquareCoefficient, ← Complex.normSq_eq_norm_sq]
  exact (Complex.mul_conj _).symm

theorem primeMajorSquareCoefficient_eq_arithmetic (q : ℕ) :
    primeMajorSquareCoefficient q =
      (((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2) /
        ((q.totient : ℂ) ^ 2) := by
  rw [primeMajorSquareCoefficient_eq_mul_conj]
  unfold primeMajorCoefficient
  simp only [map_intCast, map_natCast, map_div₀]
  ring

theorem modeledRationalArc_factor
    (V : ℝ → ℂ) (R : ℝ) (q a : ℕ) (h : ℤ) :
    modeledRationalArc V R q a h =
      fourier (-h) (rationalCenter q a) *
        primeMajorSquareCoefficient q * truncatedContinuousKernel V R h := by
  unfold modeledRationalArc truncatedContinuousKernel
  calc
    (∫ β in -R..R,
        ((‖primeMajorCoefficient q * V β‖ ^ 2 : ℝ) : ℂ) *
          fourier (-h) (rationalCenter q a + (β : UnitAddCircle))) =
      ∫ β in -R..R,
        (fourier (-h) (rationalCenter q a) *
          primeMajorSquareCoefficient q) *
          (((‖V β‖ ^ 2 : ℝ) : ℂ) * fourier (-h) (β : UnitAddCircle)) := by
        apply intervalIntegral.integral_congr
        intro β hβ
        simp only
        rw [norm_mul, mul_pow]
        unfold primeMajorSquareCoefficient
        push_cast
        simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
        ring
    _ = (fourier (-h) (rationalCenter q a) *
          primeMajorSquareCoefficient q) *
        ∫ β in -R..R,
          (((‖V β‖ ^ 2 : ℝ) : ℂ) * fourier (-h) (β : UnitAddCircle)) := by
        exact intervalIntegral.integral_const_mul _ _
    _ = _ := by ring

/-- Exact reduced-residue factorization at a fixed denominator. -/
theorem sum_modeledRationalArc_reducedResidues
    (V : ℝ → ℂ) (R : ℝ) (q : ℕ) (h : ℤ) :
    (∑ a ∈ reducedResidues q, modeledRationalArc V R q a h) =
      primeMajorSquareCoefficient q * ramanujanCoefficient q h *
        truncatedContinuousKernel V R h := by
  simp_rw [modeledRationalArc_factor]
  unfold ramanujanCoefficient
  rw [← Finset.sum_mul]
  simp_rw [mul_assoc]
  rw [← Finset.sum_mul]
  ring

/-- Exact denominator/residue factorization.  This is the finite algebra at
the heart of the manuscript's reduced-residue sum. -/
theorem sum_modeledRationalArc_all
    (V : ℝ → ℂ) (R : ℝ) (Q : ℕ) (h : ℤ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ a ∈ reducedResidues q, modeledRationalArc V R q a h) =
        truncatedSingularCoefficient Q h *
          truncatedContinuousKernel V R h := by
  simp_rw [sum_modeledRationalArc_reducedResidues]
  unfold truncatedSingularCoefficient
  rw [← Finset.sum_mul]

/-! ## Literal rational-mask geometry -/

/-- A lifted point in the paper's `β`-range belongs to the literal major-arc
mask.  The harmless half-period hypothesis is automatic once the
polylogarithmic width is less than `1/2`. -/
theorem lifted_point_mem_majorArcs
    {X : ℝ} {B D q a : ℕ} {β : ℝ}
    (hq1 : 1 ≤ q)
    (hqQ : (q : ℝ) ≤ (Real.log X) ^ B)
    (ha : a ∈ reducedResidues q)
    (hβ : |β| ≤ (Real.log X) ^ D / X)
    (hhalf : |β| ≤ (1 : ℝ) / 2) :
    rationalCenter q a + (β : UnitAddCircle) ∈
      PrimePairEndpoints.majorArcs X B D := by
  rw [mem_reducedResidues] at ha
  refine ⟨q, a, hq1, hqQ, ha.1, ha.2, ?_⟩
  unfold rationalCenter
  rw [dist_eq_norm, add_sub_cancel_left,
    (norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2]
  · exact hβ
  · simpa using hhalf

/-! ## Pointwise approximation error propagation -/

/-- Squaring a pointwise major-arc approximation loses only the expected
`E(2|model|+E)` factor.  This is the exact error propagation used before
integrating the modeled rational arcs. -/
theorem abs_normSq_sub_normSq_le
    (actual model : ℂ) :
    |‖actual‖ ^ 2 - ‖model‖ ^ 2| ≤
      ‖actual - model‖ * (2 * ‖model‖ + ‖actual - model‖) := by
  have hdiff : |‖actual‖ - ‖model‖| ≤ ‖actual - model‖ :=
    abs_norm_sub_norm_le actual model
  have hsum : ‖actual‖ + ‖model‖ ≤
      2 * ‖model‖ + ‖actual - model‖ := by
    have htri : ‖actual‖ ≤ ‖actual - model‖ + ‖model‖ := by
      calc
        ‖actual‖ = ‖(actual - model) + model‖ := by ring_nf
        _ ≤ ‖actual - model‖ + ‖model‖ := norm_add_le _ _
    linarith
  calc
    |‖actual‖ ^ 2 - ‖model‖ ^ 2| =
        |‖actual‖ - ‖model‖| * (‖actual‖ + ‖model‖) := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity)]
          ring
    _ ≤ ‖actual - model‖ * (‖actual‖ + ‖model‖) :=
      mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ ≤ ‖actual - model‖ *
        (2 * ‖model‖ + ‖actual - model‖) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)

theorem abs_normSq_sub_normSq_le_of_error
    {actual model : ℂ} {E : ℝ}
    (hE : ‖actual - model‖ ≤ E) :
    |‖actual‖ ^ 2 - ‖model‖ ^ 2| ≤ E * (2 * ‖model‖ + E) := by
  have hEnonneg : 0 ≤ E := (norm_nonneg _).trans hE
  calc
    |‖actual‖ ^ 2 - ‖model‖ ^ 2| ≤
        ‖actual - model‖ * (2 * ‖model‖ + ‖actual - model‖) :=
      abs_normSq_sub_normSq_le actual model
    _ ≤ E * (2 * ‖model‖ + E) := by
      nlinarith [norm_nonneg (actual - model), norm_nonneg model]

/-! ## The manuscript's literal continuous dyadic model -/

/-- Continuous dyadic prime-polynomial model
`∫_X^{2X} e(βx) dx`, with `e(t)=exp(2πit)`. -/
def dyadicContinuousAmplitude (X β : ℝ) : ℂ :=
  ∫ x in X..2 * X,
    Complex.exp (2 * Real.pi * Complex.I * (β * x))

def modeledDyadicMajorContribution (X R : ℝ) (Q : ℕ) (h : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q,
    ∑ a ∈ reducedResidues q,
      modeledRationalArc (dyadicContinuousAmplitude X) R q a h

/-- Literal paper cutoffs `Q=(log X)^B`, `P=(log X)^D`, converted to the
finite denominator range and lifted `β` radius used by the model sum. -/
def paperDenominatorCutoff (X : ℝ) (B : ℕ) : ℕ :=
  ⌊(Real.log X) ^ B⌋₊

def paperArcRadius (X : ℝ) (D : ℕ) : ℝ :=
  (Real.log X) ^ D / X

def modeledPaperMajorContribution
    (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  modeledDyadicMajorContribution X (paperArcRadius X D)
    (paperDenominatorCutoff X B) h

theorem modeledDyadicMajorContribution_factor
    (X R : ℝ) (Q : ℕ) (h : ℤ) :
    modeledDyadicMajorContribution X R Q h =
      truncatedSingularCoefficient Q h *
        truncatedContinuousKernel (dyadicContinuousAmplitude X) R h := by
  exact sum_modeledRationalArc_all (dyadicContinuousAmplitude X) R Q h

theorem modeledPaperMajorContribution_factor
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    modeledPaperMajorContribution X B D h =
      truncatedSingularCoefficient (paperDenominatorCutoff X B) h *
        truncatedContinuousKernel (dyadicContinuousAmplitude X)
          (paperArcRadius X D) h := by
  exact modeledDyadicMajorContribution_factor X (paperArcRadius X D)
    (paperDenominatorCutoff X B) h

/-! ## Exact support/boundary weld -/

def dyadicNatSupport (X : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊

def dyadicIntSupport (X : ℝ) : Finset ℤ :=
  (dyadicNatSupport X).map Nat.castEmbedding

/-- One-sided correlation restricted to the twice-supported range. -/
def twiceSupportedOneSided (X : ℝ) (h : ℤ) : ℝ :=
  ∑ n ∈ dyadicNatSupport X,
    if (n : ℤ) + h ∈ dyadicIntSupport X then
      ArithmeticFunction.vonMangoldt n *
        PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h)
    else 0

/-- The exact overhang left when the shifted prime exits the dyadic support. -/
def explicitBoundaryOverhang (X : ℝ) (h : ℤ) : ℝ :=
  ∑ n ∈ dyadicNatSupport X,
    if (n : ℤ) + h ∉ dyadicIntSupport X then
      ArithmeticFunction.vonMangoldt n *
        PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h)
    else 0

theorem primePairCorrelation_eq_twiceSupported_add_overhang
    (X : ℝ) (h : ℤ) :
    PrimePairEndpoints.primePairCorrelation X h =
      twiceSupportedOneSided X h + explicitBoundaryOverhang X h := by
  classical
  unfold PrimePairEndpoints.primePairCorrelation twiceSupportedOneSided
    explicitBoundaryOverhang dyadicNatSupport
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : (n : ℤ) + h ∈ dyadicIntSupport X
  · simp [hs]
  · simp [hs]

theorem supportedCorrelation_eq_twiceSupportedOneSided
    (X : ℝ) (h : ℤ) :
    MAPHarmonicEndpoint.supportedCorrelation X h =
      twiceSupportedOneSided X h := by
  classical
  unfold MAPHarmonicEndpoint.supportedCorrelation twiceSupportedOneSided
    dyadicNatSupport
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hs : (m : ℤ) + h ∈ dyadicIntSupport X
  · rw [if_pos hs]
    unfold dyadicIntSupport at hs
    rw [Finset.mem_map] at hs
    obtain ⟨n, hn, hncast⟩ := hs
    change (n : ℤ) = (m : ℤ) + h at hncast
    have hnIoc : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := by
      simpa [dyadicNatSupport] using hn
    have htarget : (n : ℤ) - (m : ℤ) = h := by omega
    rw [Finset.sum_eq_single n]
    · rw [if_pos htarget]
      unfold PrimePairEndpoints.integerVonMangoldt
      have hnpos : 0 < (m : ℤ) + h := by
        rw [← hncast]
        exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hnIoc).1)
      rw [if_pos hnpos]
      have htoNat : ((m : ℤ) + h).toNat = n := by omega
      rw [htoNat]
      ring
    · intro b hb hbn
      have hne : (b : ℤ) - (m : ℤ) ≠ h := by
        intro heq
        have : b = n := by omega
        exact hbn this
      simp [hne]
    · intro hnot
      exact (hnot hnIoc).elim
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro n hn
    have hne : (n : ℤ) - (m : ℤ) ≠ h := by
      intro heq
      apply hs
      unfold dyadicIntSupport
      rw [Finset.mem_map]
      refine ⟨n, hn, ?_⟩
      change (n : ℤ) = (m : ℤ) + h
      omega
    simp [hne]

/-- Difference between the one-sided public correlation and the literal
twice-supported Fourier coefficient. -/
def supportBoundaryCorrection (X : ℝ) (h : ℤ) : ℝ :=
  PrimePairEndpoints.primePairCorrelation X h -
    MAPHarmonicEndpoint.supportedCorrelation X h

theorem supportBoundaryCorrection_eq_explicitBoundaryOverhang
    (X : ℝ) (h : ℤ) :
    supportBoundaryCorrection X h = explicitBoundaryOverhang X h := by
  rw [supportBoundaryCorrection,
    primePairCorrelation_eq_twiceSupported_add_overhang,
    supportedCorrelation_eq_twiceSupportedOneSided]
  ring

theorem primePairCorrelation_eq_supported_add_boundary (X : ℝ) (h : ℤ) :
    PrimePairEndpoints.primePairCorrelation X h =
      MAPHarmonicEndpoint.supportedCorrelation X h +
        supportBoundaryCorrection X h := by
  unfold supportBoundaryCorrection
  ring

/-- Exact major/minor/support-boundary decomposition with normalized Haar
measure and the manuscript's Fourier sign already fixed upstream. -/
theorem primePairCorrelation_eq_major_add_minor_add_boundary
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    (PrimePairEndpoints.primePairCorrelation X h : ℂ) =
      MAPHarmonicEndpoint.majorCoefficient X B D h +
        MAPHarmonicEndpoint.minorCoefficient X B D h +
          (supportBoundaryCorrection X h : ℂ) := by
  rw [primePairCorrelation_eq_supported_add_boundary]
  push_cast
  rw [MAPHarmonicEndpoint.supportedCorrelation_eq_major_add_minor]

/-- The literal Hardy--Littlewood overlap model in (4.3), totalized at zero. -/
def primePairMajorModel (X : ℝ) (h : ℤ) : ℂ :=
  (((X - |(h : ℝ)|) * PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)

/-- An exact final weld: once the major coefficient and the support boundary
are separately estimated, the only remaining Fourier error is the minor
coefficient.  This theorem contains no analytic assumption hidden in a
definition. -/
theorem primePair_error_decomposition
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    (PrimePairEndpoints.primePairCorrelation X h : ℂ) -
        primePairMajorModel X h =
      MAPHarmonicEndpoint.minorCoefficient X B D h +
        (MAPHarmonicEndpoint.majorCoefficient X B D h -
          primePairMajorModel X h) +
        (supportBoundaryCorrection X h : ℂ) := by
  rw [primePairCorrelation_eq_major_add_minor_add_boundary]
  ring

end

end MAPMajorArcWeld
