import SiegelWalfiszCharacterReduction
import PrimitiveRemovableClosure
import SupportBoundaryQuantitative
import MAPVarianceTransferWeld

/-!
# Real-endpoint and imprimitive adapters for twisted Mangoldt prefixes

This file contains only deterministic consequences of the promoted explicit
formula.  It neither assumes nor asserts the Siegel--Walfisz target.
-/

namespace MAPPsiEndpointImprimitiveAdapters

open Set Filter
open scoped BigOperators ArithmeticFunction
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- The two independently introduced main-term definitions are identical. -/
theorem characterMain_eq_residueMain
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    MAPSiegelWalfiszCharacterReduction.characterMain χ t =
      residueMain χ t := by
  rfl

/-- Passing to the primitive inducer preserves the real-endpoint main term. -/
theorem characterMain_primitiveCharacter
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    MAPSiegelWalfiszCharacterReduction.characterMain
        χ.primitiveCharacter t =
      MAPSiegelWalfiszCharacterReduction.characterMain χ t := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [characterMain_eq_residueMain] using
    residueMain_primitiveCharacter χ t

/-- The half-integer Perron endpoint costs at most `1/2` in the main term. -/
theorem norm_residueMain_halfInteger_floor_sub_characterMain_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 0 ≤ t) :
    ‖residueMain χ (halfIntegerPoint ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤ 1 / 2 := by
  classical
  by_cases hχ : χ = 1
  · simp only [residueMain, MAPSiegelWalfiszCharacterReduction.characterMain,
      hχ, if_true]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_halfIntegerPoint_floor_sub_le t ht
  · simp [residueMain, MAPSiegelWalfiszCharacterReduction.characterMain, hχ]

/-- Exact real-endpoint summation of the six literal terms in the promoted
primitive rectangle formula.  This is the shortest adapter from the
half-integer Perron formula to the endpoint used by Siegel--Walfisz. -/
theorem norm_twistedMangoldtPrefix_sub_characterMain_le_explicitTerms
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 0 ≤ t)
    {σ c T : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      DirichletZeros.regularizedLFunction χ
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      DirichletZeros.regularizedLFunction χ
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      DirichletZeros.regularizedLFunction χ
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
      1 / 2 +
        ‖multiplicityWeightedPerronZeroSum χ σ T
          (halfIntegerPoint ⌊t⌋₊)‖ +
        ‖leftLineIntegral χ (halfIntegerPoint ⌊t⌋₊) σ T‖ +
        ‖horizontalBoundaryIntegral χ
          (halfIntegerPoint ⌊t⌋₊) σ c T‖ +
        ‖insideKernelError χ ⌊t⌋₊ c T‖ +
        ‖TruncatedTwistedPerron.coefficientTail χ
          (halfIntegerPoint ⌊t⌋₊) c T (Finset.Icc 1 ⌊t⌋₊)‖ := by
  rw [PrimitiveRemovableClosure.twistedMangoldtPrefix_eq_explicit_formula_decomposition
    χ ⌊t⌋₊ hσ0 hσ1 hc hT hleftNonzero hbottomNonzero htopNonzero]
  let z := multiplicityWeightedPerronZeroSum χ σ T
    (halfIntegerPoint ⌊t⌋₊)
  let l := leftLineIntegral χ (halfIntegerPoint ⌊t⌋₊) σ T
  let h := horizontalBoundaryIntegral χ
    (halfIntegerPoint ⌊t⌋₊) σ c T
  let i := insideKernelError χ ⌊t⌋₊ c T
  let e := TruncatedTwistedPerron.coefficientTail χ
    (halfIntegerPoint ⌊t⌋₊) c T (Finset.Icc 1 ⌊t⌋₊)
  let m := residueMain χ (halfIntegerPoint ⌊t⌋₊) -
    MAPSiegelWalfiszCharacterReduction.characterMain χ t
  have hm : ‖m‖ ≤ 1 / 2 := by
    simpa only [m] using
      norm_residueMain_halfInteger_floor_sub_characterMain_le χ ht
  have hrest : ‖-z + l - h + i - e‖ ≤
      ‖z‖ + ‖l‖ + ‖h‖ + ‖i‖ + ‖e‖ := by
    calc
      ‖-z + l - h + i - e‖ =
          ‖((((-z) + l) + (-h)) + i) + (-e)‖ := by
        congr 1
      _ ≤ ‖(((-z) + l) + (-h)) + i‖ + ‖-e‖ := norm_add_le _ _
      _ ≤ (‖((-z) + l) + (-h)‖ + ‖i‖) + ‖-e‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖(-z) + l‖ + ‖-h‖) + ‖i‖) + ‖-e‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (((‖-z‖ + ‖l‖) + ‖-h‖) + ‖i‖) + ‖-e‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖z‖ + ‖l‖ + ‖h‖ + ‖i‖ + ‖e‖ := by
        simp only [norm_neg]
  have hsplit :
      residueMain χ (halfIntegerPoint ⌊t⌋₊) - z + l - h + i - e -
          MAPSiegelWalfiszCharacterReduction.characterMain χ t =
        m + (-z + l - h + i - e) := by
    dsimp only [m]
    ring
  rw [hsplit]
  exact (norm_add_le _ _).trans <|
    (add_le_add hm hrest).trans_eq (by
      dsimp only [z, l, h, i, e]
      ring)

/-- Exact ambient-to-primitive endpoint inequality.  The only loss is the
literal missing-Euler-factor correction. -/
theorem norm_ambientPrefix_sub_characterMain_le_primitive_add_correction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 N) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
      ‖APFoundation.twistedMangoldtSum χ.primitiveCharacter
          (Finset.Icc 1 N) -
        MAPSiegelWalfiszCharacterReduction.characterMain
          χ.primitiveCharacter t‖ +
      ‖APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N)‖ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [APFoundation.twistedMangoldtSum_eq_primitive_sub_correction,
    characterMain_primitiveCharacter χ t]
  rw [show
    APFoundation.twistedMangoldtSum χ.primitiveCharacter (Finset.Icc 1 N) -
          APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N) -
          MAPSiegelWalfiszCharacterReduction.characterMain χ t =
        (APFoundation.twistedMangoldtSum χ.primitiveCharacter
            (Finset.Icc 1 N) -
          MAPSiegelWalfiszCharacterReduction.characterMain χ t) +
        (-APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N)) by ring]
  simpa only [norm_neg] using
    norm_add_le
      (APFoundation.twistedMangoldtSum χ.primitiveCharacter
        (Finset.Icc 1 N) -
          MAPSiegelWalfiszCharacterReduction.characterMain χ t)
      (-APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N))

/-- In a dyadic endpoint window, the bad-Euler-factor correction is bounded
by one explicit polylogarithm. -/
theorem norm_imprimitiveCorrection_floor_le_four_log_pow
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X t : ℝ} {B : ℕ} (hX : 2 ≤ X)
    (ht : t ∈ Set.Icc X (2 * X))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    ‖APFoundation.imprimitiveMangoldtCorrection χ
        (Finset.Icc 1 ⌊t⌋₊)‖ ≤
      4 * (Real.log X) ^ (B + 1) := by
  have hXpos : 0 < X := by linarith
  have htpos : 0 < t := hXpos.trans_le ht.1
  have hNposNat : 1 ≤ ⌊t⌋₊ :=
    (Nat.one_le_floor_iff t).2 (by linarith [ht.1])
  have hNpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast hNposNat
  have hNle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htpos.le
  have hNtwoX : (⌊t⌋₊ : ℝ) ≤ 2 * X := hNle.trans ht.2
  have hlogN : Real.log (⌊t⌋₊ : ℝ) ≤ 2 * Real.log X :=
    (Real.log_le_log hNpos hNtwoX).trans
      (MAPVarianceTransferWeld.log_two_mul_le_two_log hX)
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogN0 : 0 ≤ Real.log (⌊t⌋₊ : ℝ) :=
    Real.log_natCast_nonneg ⌊t⌋₊
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinvlog2 : (Real.log 2)⁻¹ ≤ 2 := by
    simpa using
      (inv_le_inv₀ hlog2 (by norm_num : (0 : ℝ) < 1 / 2)).2 hlog2half
  have hfloorFactor :
      (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤
        4 * Real.log X := by
    calc
      (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤
          Real.log (⌊t⌋₊ : ℝ) / Real.log 2 :=
        Nat.floor_le (div_nonneg hlogN0 hlog2.le)
      _ = Real.log (⌊t⌋₊ : ℝ) * (Real.log 2)⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ (2 * Real.log X) * 2 := by gcongr
      _ = 4 * Real.log X := by ring
  have hlogq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlogq : Real.log q ≤ (Real.log X) ^ B :=
    (Real.log_le_self (Nat.cast_nonneg q)).trans hq
  calc
    ‖APFoundation.imprimitiveMangoldtCorrection χ
        (Finset.Icc 1 ⌊t⌋₊)‖ ≤
        (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) *
          Real.log q :=
      norm_imprimitiveMangoldtCorrection_prefix_le χ ⌊t⌋₊
    _ ≤ (4 * Real.log X) * (Real.log X) ^ B := by
      exact mul_le_mul hfloorFactor hlogq hlogq0
        (by positivity)
    _ = 4 * (Real.log X) ^ (B + 1) := by
      rw [pow_succ]
      ring

/-- Every requested logarithmic saving eventually absorbs the complete
imprimitive correction, uniformly over the polylogarithmic modulus range and
the dyadic endpoint window. -/
theorem eventually_norm_imprimitiveCorrection_floor_le_logSaving
    (A B : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        (q : ℝ) ≤ (Real.log X) ^ B →
        ‖APFoundation.imprimitiveMangoldtCorrection χ
            (Finset.Icc 1 ⌊t⌋₊)‖ ≤
          X / (Real.log X) ^ A := by
  have hpoly := SupportBoundaryQuantitative.polylog_absorption
    (((A + B + 1 : ℕ) : ℝ)) (1 / 2 : ℝ) (by norm_num)
  filter_upwards [hpoly, Filter.eventually_ge_atTop (16 : ℝ)] with X hpolyX hX16
  intro q _ χ t ht hq
  have hX2 : 2 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hpolyPow : (Real.log X) ^ (A + B + 1) ≤ Real.sqrt X := by
    calc
      (Real.log X) ^ (A + B + 1) =
          Real.rpow (Real.log X) (((A + B + 1 : ℕ) : ℝ)) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ Real.rpow X (1 / 2 : ℝ) := hpolyX
      _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  have hsqrt : 4 * Real.sqrt X ≤ X := by
    have hsqrt0 := Real.sqrt_nonneg X
    have hsquare := Real.sq_sqrt hXpos.le
    nlinarith
  have hcorrection :=
    norm_imprimitiveCorrection_floor_le_four_log_pow χ hX2 ht hq
  apply hcorrection.trans
  apply (le_div_iff₀ (pow_pos hlogpos A)).2
  calc
    4 * (Real.log X) ^ (B + 1) * (Real.log X) ^ A =
        4 * (Real.log X) ^ (A + B + 1) := by
      rw [show A + B + 1 = (B + 1) + A by omega, pow_add, pow_succ]
      simp only [pow_zero]
      ring
    _ ≤ 4 * Real.sqrt X := by gcongr
    _ ≤ X := hsqrt

/-- Deterministic primitive-to-ambient and arbitrary-exponent collapse.  The
premise is restricted to primitive characters, while the conclusion is the
existing ambient-character contract. -/
theorem uniformTwistedMangoldtPsi_of_primitive
    (hprimitive :
      ∀ A B : ℕ, ∃ C X0 : ℝ,
        0 < C ∧ 2 ≤ X0 ∧
          ∀ X : ℝ, X0 ≤ X →
          ∀ q : ℕ, 1 ≤ q →
            (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
          ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
            ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
                MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
              C * X / (Real.log X) ^ A) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi := by
  intro A B
  obtain ⟨Cp, Xp, hCp, hXp, hp⟩ := hprimitive A B
  have hevent := eventually_norm_imprimitiveCorrection_floor_le_logSaving A B
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Xe, he⟩ := hevent
  let C : ℝ := Cp + 1
  let X0 : ℝ := max Xp Xe
  refine ⟨C, X0, by dsimp [C]; linarith, ?_, ?_⟩
  · exact hXp.trans (le_max_left Xp Xe)
  intro X hX q hq hqcap χ t ht
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hcondNat : χ.conductor ≤ q :=
    Nat.le_of_dvd q.pos_of_neZero χ.conductor_dvd_level
  have hcondCast : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hcondNat
  have hcond : (χ.conductor : ℝ) ≤ (Real.log X) ^ B :=
    hcondCast.trans hqcap
  have hcondOne : 1 ≤ χ.conductor :=
    Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hpBound := hp X ((le_max_left Xp Xe).trans hX)
    χ.conductor hcondOne hcond χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive t ht
  have heBound := he X ((le_max_right Xp Xe).trans hX)
    q χ t ht hqcap
  calc
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
          χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ =
      ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ := by rfl
    _ ≤ ‖APFoundation.twistedMangoldtSum χ.primitiveCharacter
          (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain
          χ.primitiveCharacter t‖ +
        ‖APFoundation.imprimitiveMangoldtCorrection χ
          (Finset.Icc 1 ⌊t⌋₊)‖ :=
      norm_ambientPrefix_sub_characterMain_le_primitive_add_correction
        χ ⌊t⌋₊ t
    _ ≤ Cp * X / (Real.log X) ^ A +
        X / (Real.log X) ^ A := add_le_add hpBound heBound
    _ = C * X / (Real.log X) ^ A := by
      dsimp only [C]
      ring

end

end MAPPsiEndpointImprimitiveAdapters

#print axioms MAPPsiEndpointImprimitiveAdapters.norm_twistedMangoldtPrefix_sub_characterMain_le_explicitTerms
#print axioms MAPPsiEndpointImprimitiveAdapters.norm_ambientPrefix_sub_characterMain_le_primitive_add_correction
#print axioms MAPPsiEndpointImprimitiveAdapters.eventually_norm_imprimitiveCorrection_floor_le_logSaving
#print axioms MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
