import KoukExercise12TwoPointwisePrincipalLocalGap
import PrincipalWeakVKZeroGapFromKhaleHigh
import SupportBoundaryQuantitative

/-!
# Principal local-horizontal formula from Appendix B

This is the source-facing principal formula used by the Siegel--Walfisz
collapse.  Appendix B enters only through the conductor-one high-zero gap.
-/

namespace MAPPrincipalKoukLocalKhaleHighFormula

open Filter Set DirichletZeros
open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture MAPKhaleAppendixBSource

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

theorem exists_eventually_principal_local_formula_of_ford_raw
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw : MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (D : ℕ) :
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
                  x ^ (1 - c * Real.rpow (Real.log X) (-(3 / 4 : ℝ))) +
                T / Real.pi * (RLeft * x ^ sigma / sigma) +
                (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
                  (RCorner * x ^ (1 / 2 : ℝ) / T +
                    RHorizontal * x ^ standardEdge ⌊t⌋₊ / T) +
                insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  obtain ⟨c, hc, hgap⟩ :=
    MAPPrincipalWeakVKZeroGapFromKhaleHigh.exists_eventually_principal_weakVK_gap_of_ford_raw
      hFord hRaw
  refine ⟨c, hc, ?_⟩
  have hpoly := SupportBoundaryQuantitative.polylog_absorption
    (D : ℝ) (1 / 2 : ℝ) (by norm_num)
  filter_upwards [hgap, hpoly,
      eventually_ge_atTop (Real.exp 2), eventually_ge_atTop 4] with
      X hgapX hpolyX hXexp hX4
  intro t ht
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hXexp
  have hHone : 1 ≤ (Real.log X) ^ D := by
    have hlog : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hXexp
    exact one_le_pow₀ hlog
  have ht0 : 0 ≤ t := hXpos.le.trans ht.1
  have hfloor : 1 ≤ ⌊t⌋₊ := by
    have htOne : (1 : ℝ) ≤ t := (by linarith : (1 : ℝ) ≤ X).trans ht.1
    have : 0 < ⌊t⌋₊ := (Nat.floor_pos (R := ℝ)).2 htOne
    omega
  have hHX : (Real.log X) ^ D + 1 ≤ X := by
    have hpow : (Real.log X) ^ D ≤ Real.sqrt X := by
      calc
        (Real.log X) ^ D = Real.rpow (Real.log X) (D : ℝ) :=
          (Real.rpow_natCast _ _).symm
        _ ≤ Real.rpow X (1 / 2 : ℝ) := hpolyX
        _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
    have hsqrt : Real.sqrt X + 1 ≤ X := by
      have hsqrtNonneg := Real.sqrt_nonneg X
      nlinarith [Real.sq_sqrt hXpos.le]
    linarith
  obtain ⟨sigma, hsigma, T, hT, hpoint⟩ :=
    MAPKoukExercise12TwoPointwisePrincipalLocalGap.exists_norm_principalPrefix_sub_main_le_of_gap
      ht0 hfloor hHone
  refine ⟨sigma, hsigma, T, hT, ?_⟩
  dsimp only
  refine ⟨hpoint.1, ?_⟩
  apply hpoint.2 (c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)))
  · exact mul_nonneg hc.le
      (Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ X)) _)
  intro rho hrho
  have hrhoFull : rho ∈ zeroSupport
      (1 : DirichletCharacter ℂ 1) 0 T :=
    MAPMellinDetectorLeaf.zeroSupport_mono
      (1 : DirichletCharacter ℂ 1) hsigma.1.le le_rfl hrho
  have hsource := hgapX T (hT.2.le.trans hHX) rho hrhoFull
  linarith

end
end MAPPrincipalKoukLocalKhaleHighFormula

#print axioms MAPPrincipalKoukLocalKhaleHighFormula.exists_eventually_principal_local_formula_of_ford_raw
