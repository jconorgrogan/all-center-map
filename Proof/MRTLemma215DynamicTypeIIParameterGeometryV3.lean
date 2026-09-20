import MAPDynamicTypeIIEmptySuffixParameterV3

/-! # Uniform eventual geometry for the fixed Type-II classifier parameters -/

namespace MRTLemma215DynamicTypeIIParameterGeometryV3

open Filter
open PostA5HighStripSplitReductionFromFourthMoment
open MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicTypeIIFiniteEnvelopeV3

noncomputable section

/-- The eight-type classifier inequality is an equality for the chosen `H₀`. -/
theorem typeII_parameter_geometry_eq {X delta : ℝ} (hX : 0 < X) :
    Real.rpow X delta * (2 * Real.rpow X ((8 : ℝ)⁻¹)) =
      2 * Real.rpow X (delta + 1 / 8) := by
  calc
    _ = 2 * (Real.rpow X delta * Real.rpow X ((8 : ℝ)⁻¹)) := by ring
    _ = 2 * Real.rpow X (delta + (8 : ℝ)⁻¹) := by
      exact congrArg (fun t : ℝ => 2 * t) (Real.rpow_add hX delta ((8 : ℝ)⁻¹)).symm
    _ = _ := by norm_num

/-- The fixed factor `2^(2K+1)` is eventually absorbed by the strict
exponent reserve below one. `K` and `delta` are fixed before `X`. -/
theorem eventually_typeII_parameter_global
    (delta : ℝ) (K : ℕ) (hdelta : delta ≤ 1 / 240) :
    ∀ᶠ X : ℝ in atTop,
      (2 : ℝ) ^ (2 * K) * (2 * Real.rpow X (delta + 1 / 8)) ≤ X := by
  let gap : ℝ := 1 - (delta + 1 / 8)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hconst := eventually_const_mul_polylog_le_rpow
    (2 * (2 : ℝ) ^ (2 * K)) 0 gap (by positivity) hgap
  filter_upwards [hconst, eventually_ge_atTop 1] with X hc hX
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hc' : 2 * (2 : ℝ) ^ (2 * K) ≤ Real.rpow X gap := by
    have hz : Real.rpow (Real.log X) 0 = 1 := Real.rpow_zero _
    simpa only [hz, mul_one] using hc
  calc
    _ = (2 * (2 : ℝ) ^ (2 * K)) * Real.rpow X (delta + 1 / 8) := by ring
    _ ≤ Real.rpow X gap * Real.rpow X (delta + 1 / 8) :=
      mul_le_mul_of_nonneg_right hc' (Real.rpow_nonneg hXpos.le _)
    _ = Real.rpow X (gap + (delta + 1 / 8)) := (Real.rpow_add hXpos _ _).symm
    _ = X := by have he : gap + (delta + 1 / 8) = 1 := by dsimp [gap]; ring
                rw [he]
                exact Real.rpow_one X

/-- The global envelope controls the source list of every raw branch,
including all unit choices in both bags. -/
theorem actual_component_size_of_parameter_global
    {X delta : ℝ} {K : ℕ} (hX : 1 ≤ X)
    (hglobal : (2 : ℝ) ^ (2 * K) * (2 * Real.rpow X (delta + 1 / 8)) ≤ X)
    (branch : Fin K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1)) :
    (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
      Real.rpow X delta ≤ X := by
  have hlen := dynamicComponentFactorList_length_le logIndex zbag mbag
  have hbranch := branch.isLt
  have hpow : (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length ≤
      (2 : ℝ) ^ (2 * K) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hscale : Real.rpow X delta ≤ 2 * Real.rpow X (delta + 1 / 8) := by
    have he : Real.rpow X delta ≤ Real.rpow X (delta + 1 / 8) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hn : 0 ≤ Real.rpow X (delta + 1 / 8) := Real.rpow_nonneg (by linarith) _
    linarith
  exact (mul_le_mul hpow hscale (Real.rpow_nonneg (by linarith) _) (by positivity)).trans hglobal

/-- One eventual set supplies the literal HB safety cutoff, classifier
geometry, global empty-suffix envelope and all actual component sizes. -/
theorem eventually_actual_typeII_parameter_geometry
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∀ᶠ X : ℝ in atTop,
      3 ≤ X ∧
      1 ≤ hbOrder delta ∧
      dynamicHBCutoff X (hbOrder delta) ≤ Real.rpow X delta ∧
      Real.rpow X delta * (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤
        2 * Real.rpow X (delta + 1 / 8) ∧
      (2 : ℝ) ^ (2 * hbOrder delta) * (2 * Real.rpow X (delta + 1 / 8)) ≤ X ∧
      ∀ (branch : Fin (hbOrder delta))
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
        (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
        (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
          Real.rpow X delta ≤ X := by
  filter_upwards [eventually_typeII_parameter_global delta (hbOrder delta) hdeltaUpper,
    eventually_ge_atTop 3] with X hglobal hX
  refine ⟨hX, hbOrder_one hdelta,
    dynamicHBCutoff_hbOrder_le_rpow (by linarith) hdelta,
    (typeII_parameter_geometry_eq (by linarith)).le, hglobal, ?_⟩
  intro branch logIndex zbag mbag
  exact actual_component_size_of_parameter_global (by linarith) hglobal branch logIndex zbag mbag

/-- Threshold form: the threshold depends only on fixed `delta`, before
quantifying over `X` and over every literal source component. -/
theorem exists_actual_typeII_parameter_geometry_threshold
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      3 ≤ X ∧
      1 ≤ hbOrder delta ∧
      dynamicHBCutoff X (hbOrder delta) ≤ Real.rpow X delta ∧
      Real.rpow X delta * (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤
        2 * Real.rpow X (delta + 1 / 8) ∧
      (2 : ℝ) ^ (2 * hbOrder delta) * (2 * Real.rpow X (delta + 1 / 8)) ≤ X ∧
      ∀ (branch : Fin (hbOrder delta))
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
        (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
        (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
          Real.rpow X delta ≤ X := by
  simpa only [eventually_atTop] using
    eventually_actual_typeII_parameter_geometry delta hdelta hdeltaUpper

end
end MRTLemma215DynamicTypeIIParameterGeometryV3

#print axioms MRTLemma215DynamicTypeIIParameterGeometryV3.eventually_actual_typeII_parameter_geometry
#print axioms MRTLemma215DynamicTypeIIParameterGeometryV3.exists_actual_typeII_parameter_geometry_threshold
