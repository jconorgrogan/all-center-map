import KoukExercise12TwoPointwiseLocalZeroSplit
import KoukExercise12TwoLocalPolylogScalars
import KoukExercise12TwoEndpointScalars
import SiegelExceptionalOnePower

/-!
# Nonprincipal Exercise 12.2 with the exceptional atom absorbed

This is the source-facing join between the selected local contour and the
proved Goldfeld--Siegel theorem.  The regular divisor keeps its explicit
weak-VK gap.  The possible real exceptional atom is already reduced to an
arbitrarily small logarithmic budget.
-/

namespace MAPNonprincipalKoukSiegelFormula

open Filter Set DirichletZeros
open PrimitiveExplicitFormulaSpine PrimitiveTruncatedExplicitFormulaBridge
open PaperEdgePrimitiveComponents MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoZeroSum
open MAPKoukExercise12TwoLocalHorizontalAperture

noncomputable section

private theorem halfInteger_ranges
    {X t : ℝ} (hX : 2 ≤ X) (ht : t ∈ Set.Icc X (2 * X)) :
    let N := ⌊t⌋₊
    let x := halfIntegerPoint N
    1 ≤ N ∧ X / 2 ≤ x ∧ x ≤ 3 * X := by
  have h := MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_floor_range hX ht
  exact ⟨h.1, h.2.1, h.2.2.1⟩

private theorem halfInteger_exceptional_base_compare
    {X x beta : ℝ} (hX : 2 ≤ X) (hxLower : X / 2 ≤ x)
    (hbetaLower : 1 / 2 < beta) (hbetaUpper : beta < 1) :
    Real.rpow x (beta - 1) ≤ 2 * Real.rpow X (beta - 1) := by
  have hXpos : 0 < X := by linarith
  have hhalfPos : 0 < X / 2 := by positivity
  have hxpos : 0 < x := hhalfPos.trans_le hxLower
  have hneg : beta - 1 ≤ 0 := by linarith
  have hbase := Real.rpow_le_rpow_of_nonpos hhalfPos hxLower hneg
  have htwo : Real.rpow (2 : ℝ) (1 - beta) ≤ 2 := by
    calc
      Real.rpow (2 : ℝ) (1 - beta) ≤ Real.rpow (2 : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hrewrite : Real.rpow (X / 2) (beta - 1) =
      Real.rpow X (beta - 1) * Real.rpow (2 : ℝ) (1 - beta) := by
    calc
      Real.rpow (X / 2) (beta - 1) =
          Real.rpow X (beta - 1) / Real.rpow (2 : ℝ) (beta - 1) :=
        Real.div_rpow hXpos.le (by norm_num : (0 : ℝ) ≤ 2) _
      _ = Real.rpow X (beta - 1) *
          (Real.rpow (2 : ℝ) (beta - 1))⁻¹ := by ring
      _ = Real.rpow X (beta - 1) *
          Real.rpow (2 : ℝ) (-(beta - 1)) := by
        congr 1
        exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (beta - 1)).symm
      _ = Real.rpow X (beta - 1) *
          Real.rpow (2 : ℝ) (1 - beta) := by ring_nf
  change Real.rpow x (beta - 1) ≤ Real.rpow (X / 2) (beta - 1) at hbase
  change Real.rpow x (beta - 1) ≤ 2 * Real.rpow X (beta - 1)
  calc
    Real.rpow x (beta - 1) ≤ Real.rpow (X / 2) (beta - 1) := hbase
    _ = Real.rpow X (beta - 1) * Real.rpow (2 : ℝ) (1 - beta) := hrewrite
    _ ≤ Real.rpow X (beta - 1) * 2 :=
      mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hXpos.le _)
    _ = 2 * Real.rpow X (beta - 1) := by ring

/-- At polylogarithmic height the nonprincipal local formula has its regular
weak-VK zero gap inserted, while the possible exceptional atom costs only an
arbitrarily prescribed inverse logarithm. -/
theorem exists_eventually_nonprincipal_formula
    (B D M : ℕ) :
    let p := B + 3 * D
    let c := 1 /
      (100000000000 * (((B + D : ℕ) : ℝ) + Real.log 4))
    ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ (Real.log X) ^ B →
      ∀ chi : DirichletCharacter ℂ q,
        chi.IsPrimitive → chi ≠ 1 →
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
          ∃ T ∈ Set.Ioo ((Real.log X) ^ D) ((Real.log X) ^ D + 1),
            let x := halfIntegerPoint ⌊t⌋₊
            let dLeft := exerciseRealClearance chi ((Real.log X) ^ D)
            let dHorizontal := exerciseHorizontalClearance chi ((Real.log X) ^ D)
            let dCorner := min dLeft dHorizontal
            let L := Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))
            let RLeft := 20 * (Real.log 21600 + 2 * L) +
              5520 * L + 5520 * L / dLeft
            let RHorizontal := 20 * (Real.log 21600 + 2 * L) +
              5520 * L + 5520 * L / dHorizontal
            let RCorner := 20 * (Real.log 21600 + 2 * L) +
              5520 * L + 5520 * L / dCorner
            dLeft ≤ sigma ∧
            c * Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤
              exercise12TwoGap q T ∧
            ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
                MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
              1 / 2 +
              ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
                x ^ (1 - exercise12TwoGap q T) +
              (6 * 40000016) * X *
                Real.rpow (Real.log X) (-(M : ℝ)) +
              T / Real.pi * (RLeft * x ^ sigma / sigma) +
              (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
                (RCorner * x ^ (1 / 2 : ℝ) / T +
                  RHorizontal * x ^ standardEdge ⌊t⌋₊ / T) +
              insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  classical
  dsimp only
  let p : ℕ := B + 3 * D
  let c : ℝ := 1 /
    (100000000000 * (((B + D : ℕ) : ℝ) + Real.log 4))
  have hweak :=
    MAPKoukExercise12TwoPolylogScalars.eventually_weakGap_le_exercise12TwoGap B D
  have hSiegel := MAPSiegelExceptionalOnePower.eventually_prefactor_mul_onePower_le
    (K := ((B + 1 : ℕ) : ℝ)) (A := ((M + 1 : ℕ) : ℝ)) (P := (p : ℝ))
    (by positivity) (by positivity) (by positivity)
  filter_upwards [hweak, hSiegel, eventually_ge_atTop (Real.exp 2),
      eventually_ge_atTop 4] with X hweakX hSiegelX hXexp hX4
  intro q _inst hq chi hprim hchi t ht
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hXexp
  have hlogTwo : 2 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp
  have hlogPos : 0 < Real.log X := by linarith
  have hHone : 1 ≤ (Real.log X) ^ D := one_le_pow₀ (by linarith)
  obtain ⟨hN, hxLower, hxUpper⟩ := halfInteger_ranges (by linarith) ht
  have ht0 : 0 ≤ t := hXpos.le.trans ht.1
  obtain ⟨sigma, hsigma, T, hT, hpoint⟩ :=
    MAPKoukExercise12TwoPointwiseLocalZeroSplit.exists_norm_primitivePrefix_sub_characterMain_le_local_regular_add_exceptional
      chi hprim hchi ht0 hN hHone
  refine ⟨sigma, hsigma, T, hT, ?_⟩
  dsimp only
  refine ⟨hpoint.1, ?_, ?_⟩
  · simpa only [c] using hweakX q T hq hT
  let E := (6 * 40000016) * X *
    Real.rpow (Real.log X) (-(M : ℝ))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hInv :=
    MAPKoukExercise12TwoLocalPolylogScalars.inv_exerciseRealClearance_polylogHeight_le
      B D hlogTwo chi hprim hq
  have hqPlus : (q : ℝ) ≤ Real.rpow (Real.log X) ((B + 1 : ℕ) : ℝ) := by
    calc
      (q : ℝ) ≤ (Real.log X) ^ B := hq
      _ ≤ (Real.log X) ^ (B + 1) :=
        pow_le_pow_right₀ (by linarith : 1 ≤ Real.log X) (by omega)
      _ = Real.rpow (Real.log X) ((B + 1 : ℕ) : ℝ) :=
        (Real.rpow_natCast (Real.log X) (B + 1)).symm
  have htargetPower : Real.rpow (Real.log X) (-((M + 1 : ℕ) : ℝ)) ≤
      Real.rpow (Real.log X) (-(M : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Real.log X)
    push_cast
    linarith
  apply hpoint.2 E hE
  · intro rho hrho
    have hrhoFilter := hrho
    rw [theorem12ThreeCollarSupport, Finset.mem_filter] at hrhoFilter
    have hrhoFull := hrhoFilter.1
    have hbetaLower := theorem12ThreeCollar_lt_half hrhoFilter.2
    have hbetaUpper := MAPMellinDetectorLeaf.re_lt_one_of_mem_zeroSupport chi hrhoFull
    obtain ⟨hreal, him, _hmult⟩ :=
      mem_collarSupport_exceptional chi hprim hchi hrho
    have hregzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
      chi sigma T hrhoFull
    have hzeroComplex : DirichletCharacter.LFunction chi rho = 0 := by
      simpa [regularizedLFunction, hchi] using hregzero
    have hrhoReal : rho = (rho.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hzero : DirichletCharacter.LFunction chi rho.re = 0 := by
      rw [hrhoReal] at hzeroComplex
      exact hzeroComplex
    have hSiegelTerm := hSiegelX q chi rho.re hqPlus hchi hreal hzero
    have hxpos : 0 < halfIntegerPoint ⌊t⌋₊ :=
      (halfIntegerPoint_pos ⌊t⌋₊)
    have hpowSplit :
        Real.rpow (halfIntegerPoint ⌊t⌋₊) rho.re =
          halfIntegerPoint ⌊t⌋₊ *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (rho.re - 1) := by
      calc
        _ = Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 + (rho.re - 1)) := by ring_nf
        _ = Real.rpow (halfIntegerPoint ⌊t⌋₊) 1 *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (rho.re - 1) :=
          Real.rpow_add hxpos 1 (rho.re - 1)
        _ = _ := by
          rw [show Real.rpow (halfIntegerPoint ⌊t⌋₊) 1 =
            halfIntegerPoint ⌊t⌋₊ from Real.rpow_one _]
    have hbaseCompare := halfInteger_exceptional_base_compare (by linarith) hxLower
      hbetaLower hbetaUpper
    have hpow : Real.rpow (halfIntegerPoint ⌊t⌋₊) rho.re ≤
        6 * X * Real.rpow X (rho.re - 1) := by
      rw [hpowSplit]
      have hxnonneg := (halfIntegerPoint_pos ⌊t⌋₊).le
      calc
        _ ≤ (3 * X) * (2 * Real.rpow X (rho.re - 1)) :=
          mul_le_mul hxUpper hbaseCompare
            (Real.rpow_nonneg hxpos.le _) (by positivity)
        _ = 6 * X * Real.rpow X (rho.re - 1) := by ring
    have hdPos := exerciseRealClearance_pos chi ((Real.log X) ^ D)
    have hInvSigma : sigma⁻¹ ≤
        40000016 * (Real.log X) ^ p := by
      have hds := hpoint.1
      have hinvds : sigma⁻¹ ≤
          (exerciseRealClearance chi ((Real.log X) ^ D))⁻¹ :=
        by
          simpa [one_div] using one_div_le_one_div_of_le hdPos hds
      exact hinvds.trans (by simpa only [p] using hInv)
    rw [div_eq_mul_inv]
    calc
      Real.rpow (halfIntegerPoint ⌊t⌋₊) rho.re * sigma⁻¹ ≤
          (6 * X * Real.rpow X (rho.re - 1)) *
            (40000016 * (Real.log X) ^ p) :=
        mul_le_mul hpow hInvSigma (inv_nonneg.mpr hsigma.1.le)
          (mul_nonneg (mul_nonneg (by norm_num) hXpos.le)
            (Real.rpow_nonneg hXpos.le _))
      _ = (6 * 40000016) * X *
          ((Real.log X) ^ p * Real.rpow X (rho.re - 1)) := by ring
      _ ≤ (6 * 40000016) * X *
          Real.rpow (Real.log X) (-((M + 1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [Real.rpow_natCast] using hSiegelTerm
      _ ≤ E := by
        dsimp [E]
        exact mul_le_mul_of_nonneg_left htargetPower (by positivity)

end
end MAPNonprincipalKoukSiegelFormula

#print axioms MAPNonprincipalKoukSiegelFormula.exists_eventually_nonprincipal_formula
