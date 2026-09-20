import KoukExercise12TwoPointwisePrincipalLocalGap
import KoukExercise12TwoPolylogScalars
import KoukExercise12TwoZeroSum
import PrincipalKoukTheorem12Three
import KoukTheorem12ThreeGlobal
import KhaleAppendixBSourceReduction
import SupportBoundaryQuantitative

/-!
# Principal local formula from the zeta `3-4-1` collar

The conductor-one branch does not need the Ford--Khale zero-free region.
The principal `3-4-1` argument supplies a reciprocal-logarithmic collar at
large ordinate; compactness supplies the bounded ordinate range.  At the
polylogarithmic contour height this yields the weak gap of exponent `1/4`
used below.
-/

namespace MAPPrincipalKoukLocalTheorem12ThreeFormula

open Filter Set DirichletZeros
open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture
open MAPKoukExercise12TwoZeroSum

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

theorem exists_eventually_principal_local_formula (D : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
            ∃ T ∈ Set.Ioo ((Real.log X) ^ D) ((Real.log X) ^ D + 1),
              let x := halfIntegerPoint ⌊t⌋₊
              let dLeft := exerciseRealClearance
                (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
              let dHorizontal := exerciseHorizontalClearance
                (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
              let dCorner := min dLeft dHorizontal
              let L := Real.log ((Real.log X) ^ D + 3)
              let RLeft := 2 + 20 * (Real.log 223948800 + 6 * L) +
                30300 * L + 30300 * L / dLeft
              let RHorizontal := 2 + 20 * (Real.log 223948800 + 6 * L) +
                30300 * L + 30300 * L / dHorizontal
              let RCorner := 2 + 20 * (Real.log 223948800 + 6 * L) +
                30300 * L + 30300 * L / dCorner
              dLeft ≤ sigma ∧
              ‖APFoundation.twistedMangoldtSum
                    (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 ⌊t⌋₊) -
                  MAPSiegelWalfiszCharacterReduction.characterMain
                    (1 : DirichletCharacter ℂ 1) t‖ ≤
                1 / 2 +
                ((dirichletZeroCount
                    (1 : DirichletCharacter ℂ 1) sigma T : ℝ) / sigma) *
                  x ^ (1 - c * Real.rpow (Real.log X) (-(1 / 4 : ℝ))) +
                T / Real.pi * (RLeft * x ^ sigma / sigma) +
                (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
                  (RCorner * x ^ (1 / 2 : ℝ) / T +
                    RHorizontal * x ^ standardEdge ⌊t⌋₊ / T) +
                insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  obtain ⟨cLow, hcLow, hLow⟩ :=
    MAPKhaleAppendixBSource.exists_primitive_principal_preKhale_gap
  let cWeak : ℝ :=
    1 / (100000000000 * (((D : ℕ) : ℝ) + Real.log 4))
  let c : ℝ := min (1 / 5) (min cLow cWeak)
  have hcWeak : 0 < cWeak := by
    dsimp only [cWeak]
    positivity
  have hc : 0 < c := lt_min (by norm_num) (lt_min hcLow hcWeak)
  have hweak :=
    MAPKoukExercise12TwoPolylogScalars.eventually_weakGap_le_exercise12TwoGap 0 D
  have hdecay : ∀ᶠ X : ℝ in atTop,
      c * Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤ c := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hlogOne : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hX
    have hp : Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlogOne (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hc.le
  refine ⟨c, hc, ?_⟩
  filter_upwards [hweak, hdecay,
      eventually_ge_atTop (Real.exp 2), eventually_ge_atTop 4] with
      X hweakX hdecayX hXexp hX4
  intro t ht
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hXexp
  have hlogOne : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hXexp
  have hHone : 1 ≤ (Real.log X) ^ D := one_le_pow₀ hlogOne
  have ht0 : 0 ≤ t := hXpos.le.trans ht.1
  have hfloor : 1 ≤ ⌊t⌋₊ := by
    have htOne : (1 : ℝ) ≤ t := (by linarith : (1 : ℝ) ≤ X).trans ht.1
    have : 0 < ⌊t⌋₊ := (Nat.floor_pos (R := ℝ)).2 htOne
    omega
  obtain ⟨sigma, hsigma, T, hT, hpoint⟩ :=
    MAPKoukExercise12TwoPointwisePrincipalLocalGap.exists_norm_principalPrefix_sub_main_le_of_gap
      ht0 hfloor hHone
  refine ⟨sigma, hsigma, T, hT, ?_⟩
  dsimp only
  refine ⟨hpoint.1, ?_⟩
  let omega : ℝ := c * Real.rpow (Real.log X) (-(1 / 4 : ℝ))
  apply hpoint.2 omega
  · dsimp only [omega]
    exact mul_nonneg hc.le
      (Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ X)) _)
  intro rho hrho
  have hrhoFull : rho ∈ zeroSupport
      (1 : DirichletCharacter ℂ 1) 0 T :=
    MAPMellinDetectorLeaf.zeroSupport_mono
      (1 : DirichletCharacter ℂ 1) hsigma.1.le le_rfl hrho
  by_cases hreHalf : 1 / 2 ≤ rho.re
  · have hcenter := MAPKoukTheorem12ThreeGlobal.mem_centered_of_mem_zeroSupport
        (1 : DirichletCharacter ℂ 1) hrho hreHalf
    by_cases hcollar : inTheorem12ThreeCollar (q := 1) rho
    · by_cases hheight : 1 / 4 < |rho.im|
      · exact False.elim
          (MAPPrincipalKoukTheorem12Three.high_principal_nearOne_zero_absent
            hcenter hheight (by simpa [inTheorem12ThreeCollar] using hcollar))
      · by_cases hbeta : 4 / 5 < rho.re
        · have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
            show (1 : DirichletCharacter ℂ 1).conductor = 1
            rw [DirichletCharacter.conductor_one]
          have hheightLow :
              |rho.im| < Real.exp (Real.exp (Real.exp 23)) := by
            have him : |rho.im| ≤ 1 / 4 := le_of_not_gt hheight
            have hexp : 1 < Real.exp (Real.exp (Real.exp 23)) :=
              Real.one_lt_exp_iff.mpr (by positivity)
            linarith
          have hgap := hLow 1 (1 : DirichletCharacter ℂ 1)
            hprim rfl T rho hrhoFull hbeta hheightLow
          have homegaGap : omega ≤ 1 - rho.re := by
            dsimp only [omega]
            exact hdecayX.trans
              ((min_le_right (1 / 5) (min cLow cWeak)).trans
                ((min_le_left cLow cWeak).trans hgap))
          linarith
        · have hgap : (1 / 5 : ℝ) ≤ 1 - rho.re := by linarith
          have homegaGap : omega ≤ 1 - rho.re := by
            dsimp only [omega]
            exact hdecayX.trans
              ((min_le_left (1 / 5) (min cLow cWeak)).trans hgap)
          linarith
    · have hT0 : 0 ≤ T := by
        exact (pow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ X)) D).trans hT.1.le
      have hregular :=
        exercise12TwoGap_le_one_sub_re_of_not_collar
          (1 : DirichletCharacter ℂ 1) hT0 hrho hcollar
      have hweakT := hweakX 1 T (by simp) hT
      have hcoef : c ≤ cWeak :=
        (min_le_right (1 / 5) (min cLow cWeak)).trans (min_le_right cLow cWeak)
      have hpow0 : 0 ≤ Real.rpow (Real.log X) (-(1 / 4 : ℝ)) :=
        Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ X)) _
      have homegaWeak : omega ≤ cWeak *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) := by
        dsimp only [omega]
        exact mul_le_mul_of_nonneg_right hcoef hpow0
      have hweakT' : cWeak * Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤
          exercise12TwoGap 1 T := by
        simpa only [cWeak, Nat.zero_add, Nat.cast_id] using hweakT
      have homegaGap := homegaWeak.trans (hweakT'.trans hregular)
      linarith
  · have hgap : (1 / 2 : ℝ) ≤ 1 - rho.re := by linarith
    have hcHalf : c ≤ 1 / 2 :=
      (min_le_left (1 / 5) (min cLow cWeak)).trans (by norm_num)
    have homegaGap : omega ≤ 1 - rho.re := by
      dsimp only [omega]
      exact hdecayX.trans (hcHalf.trans hgap)
    linarith

end
end MAPPrincipalKoukLocalTheorem12ThreeFormula

#print axioms MAPPrincipalKoukLocalTheorem12ThreeFormula.exists_eventually_principal_local_formula
