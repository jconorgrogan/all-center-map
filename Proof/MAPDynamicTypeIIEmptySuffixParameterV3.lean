import AllCenterApertureTransfer
import PostA5HighStripSplitReductionFromFourthMoment
import MRTLemma215DynamicTypeIIFiniteEnvelopeV3

/-! # Eventual parameter inequality killing the empty Type-II suffix -/

namespace MAPDynamicTypeIIEmptySuffixParameterV3

open Filter
open MAPAllCenterApertureTransfer
open PostA5HighStripSplitReductionFromFourthMoment
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3

noncomputable section

/-- For the manuscript choices `delta = rho/16` and
`H₀ = H X^{-delta}`, the fixed branch-length envelope is eventually below
the source scale.  This is the exact inequality required by the certified
empty-suffix support lemma. -/
theorem eventually_typeII_emptySuffix_parameter
    (epsilon : ℝ) (K : ℕ) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      (2 : ℝ) ^ (2 * K) *
          (2 * (baseAperture epsilon X *
            Real.rpow X (-(apertureReserve epsilon / 16)))) ≤ X := by
  let rho := apertureReserve epsilon
  let delta := rho / 16
  let e := 2 / 15 + rho - delta
  let gap := 1 - e
  have hrhoPos : 0 < rho := apertureReserve_pos hepsilon
  have hrhoUpper : rho ≤ 1 / 1200 := by
    dsimp [rho, apertureReserve]
    exact min_le_right _ _
  have hePos : 0 < e := by
    dsimp [e, delta]
    linarith
  have hgapPos : 0 < gap := by
    dsimp [gap, e, delta]
    linarith
  have hconst := eventually_const_mul_polylog_le_rpow
    ((2 : ℝ) ^ (2 * K)) 0 gap (by positivity) hgapPos
  filter_upwards [hconst, eventually_ge_atTop 1] with X hconstX hX
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hconstX' : (2 : ℝ) ^ (2 * K) ≤ Real.rpow X gap := by
    simpa [Real.rpow_zero] using hconstX
  have hH0 : baseAperture epsilon X *
      Real.rpow X (-(apertureReserve epsilon / 16)) =
      (1 / 2) * Real.rpow X e := by
    unfold baseAperture
    dsimp [e, delta, rho]
    calc
      (1 / 2) * Real.rpow X (2 / 15 + apertureReserve epsilon) *
          Real.rpow X (-(apertureReserve epsilon / 16)) =
        (1 / 2) * (Real.rpow X (2 / 15 + apertureReserve epsilon) *
          Real.rpow X (-(apertureReserve epsilon / 16))) := by ring
      _ = (1 / 2) * Real.rpow X
          ((2 / 15 + apertureReserve epsilon) +
            (-(apertureReserve epsilon / 16))) := by
        exact congrArg (fun z : ℝ => (1 / 2) * z)
          (Real.rpow_add hXpos _ _).symm
      _ = _ := by congr 2 <;> ring
  rw [hH0]
  have hmul := mul_le_mul_of_nonneg_right hconstX'
    (Real.rpow_nonneg (le_trans (by norm_num) hX) e)
  calc
    (2 : ℝ) ^ (2 * K) * (2 * ((1 / 2) * Real.rpow X e)) =
        (2 : ℝ) ^ (2 * K) * Real.rpow X e := by ring
    _ ≤ Real.rpow X gap * Real.rpow X e := hmul
    _ = Real.rpow X (gap + e) := (Real.rpow_add hXpos gap e).symm
    _ = X := by
      have hge : gap + e = 1 := by dsimp [gap]; ring
      rw [hge]
      simp

/-- Threshold form used by pointwise constructors. -/
theorem exists_typeII_emptySuffix_parameter_threshold
    (epsilon : ℝ) (K : ℕ) (hepsilon : 0 < epsilon) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (2 : ℝ) ^ (2 * K) *
          (2 * (baseAperture epsilon X *
            Real.rpow X (-(apertureReserve epsilon / 16)))) ≤ X := by
  simpa only [eventually_atTop] using
    eventually_typeII_emptySuffix_parameter epsilon K hepsilon

/-- The global fixed-order inequality specializes to every actual component
of every branch. -/
theorem component_emptySuffix_large_of_branchEnvelope
    {X H₀ : ℝ} {K : ℕ} (hH₀ : 0 ≤ H₀)
    (hglobal : (2 : ℝ) ^ (2 * K) * (2 * H₀) ≤ X)
    (branch : Fin K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
      (branch : ℕ))
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))
      ((branch : ℕ) + 1)) :
    (2 : ℝ) ^ (sortedComponentFactorList logIndex zbag mbag).length *
        (2 * H₀) ≤ X := by
  have hlen := sortedComponentFactorList_length_le logIndex zbag mbag
  have hlenK : (sortedComponentFactorList logIndex zbag mbag).length ≤
      2 * K := by
    have hbranch : (branch : ℕ) < K := branch.isLt
    omega
  have hpowNat : 2 ^ (sortedComponentFactorList logIndex zbag mbag).length ≤
      2 ^ (2 * K) := Nat.pow_le_pow_right (by omega) hlenK
  have hpow : (2 : ℝ) ^
      (sortedComponentFactorList logIndex zbag mbag).length ≤
      (2 : ℝ) ^ (2 * K) := by exact_mod_cast hpowNat
  exact (mul_le_mul_of_nonneg_right hpow (by positivity)).trans hglobal

end
end MAPDynamicTypeIIEmptySuffixParameterV3

#print axioms MAPDynamicTypeIIEmptySuffixParameterV3.eventually_typeII_emptySuffix_parameter
#print axioms MAPDynamicTypeIIEmptySuffixParameterV3.exists_typeII_emptySuffix_parameter_threshold
