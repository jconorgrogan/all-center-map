import BHPFixedCharacterFromDyadicAFE

/-!
# Principal zeta fourth moment from the shared Ramachandra dyadic AFE

The live structured-density route already assumes Ramachandra's all-character
dyadic AFE object for the nonprincipal Type-II branch.  That object also
contains the unique primitive character of conductor one.  This file applies
the same certified blockwise discrete mean-square argument at `q = 1`, so the
principal high-strip branch needs no independent zeta-density premise and no
arbitrary-coefficient Guth--Maynard theorem.
-/

namespace MAPPrincipalZetaFourthMomentFromDyadicAFE

open Filter
open CGLProofDAG
open BHPRamachandraMeanValueFromDyadicAFE
open BHPFixedCharacterFromDyadicAFE
open BHPAllCharacterDyadicBudget MAPMRTLemma211AllCharacterSource

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- The all-character Ramachandra dyadic AFE already carried by the live
nonprincipal route supplies the exact conductor-one discrete fourth moment.
No primitivity or nonprincipality hypothesis is used by the finite AFE data. -/
theorem principalZetaDiscreteFourthMoment_of_dyadicAFE_raw
    (hAFE : RamachandraLemma3To6AllCharacterDyadicAFE) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T : ℝ) (W : Finset ℝ),
          T₀ ≤ T → OneSeparated W →
          (∀ t ∈ W, |t| ≤ T) →
          (∑ t ∈ W, ‖DirichletCharacter.LFunction chiOne
            (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
            C * Real.rpow T (1 + epsilon) := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 4
  let theta : ℝ := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; linarith
  have htheta : 0 < theta := by dsimp [theta]; linarith
  have hmean : DiscreteMeanValueSourceLeaf.DiscreteDirichletMeanSquare :=
    RecenteredSampling.discreteDirichletMeanSquare_of_hilbert
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  obtain ⟨Cmv, Tmv, hCmv, hTmv, hmv⟩ := hmean eta heta
  obtain ⟨C₀, hC₀, B, hsource⟩ := hAFE
  have hpoly := ZeroDensityArithmetic.polylog_absorption (B : ℝ) theta htheta
  obtain ⟨Xlog, hXlog⟩ := Filter.eventually_atTop.1 hpoly
  let C : ℝ := Cmv * C₀ * Real.rpow 2 eta
  let T₀ : ℝ := max Tmv (max 2 Xlog)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hT₀ : 2 ≤ T₀ := by
    dsimp [T₀]
    exact (le_max_left 2 Xlog).trans (le_max_right Tmv (max 2 Xlog))
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T W hT hsep hheight
  have hTmv' : Tmv ≤ T :=
    (le_max_left Tmv (max 2 Xlog)).trans hT
  have hTtwo : 2 ≤ T :=
    (le_max_left 2 Xlog).trans
      ((le_max_right Tmv (max 2 Xlog)).trans hT)
  have hXlogT : Xlog ≤ T :=
    (le_max_right 2 Xlog).trans
      ((le_max_right Tmv (max 2 Xlog)).trans hT)
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
  have hTone : 1 ≤ T := by linarith
  obtain ⟨data⟩ := hsource 1 T T hTtwo (by simpa using hTone) le_rfl
  have hmean' : 0 < Cmv ∧ 2 ≤ Tmv ∧
      ∀ (S : ℝ) (N : ℕ) (b : ℕ → ℂ) (W' : Finset ℝ),
        Tmv ≤ S → 1 ≤ N → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S) →
        (∑ u ∈ W', ‖dirichletPolynomial b N u‖ ^ 2) ≤
          Cmv * Real.rpow S eta * ((N : ℝ) + S) *
            DiscreteMeanValueSourceLeaf.coefficientEnergy b N :=
    ⟨hCmv, hTmv, hmv⟩
  have hraw := selected_fourth_mass_le_dyadicFamilyCost
    data chiOne W hmean' hTpos.le (by linarith) hsep hheight
  have hlogAbs : Real.rpow (Real.log T) (B : ℝ) ≤
      Real.rpow T theta := hXlog T hXlogT
  have hlogPow : Real.log T ^ B ≤ Real.rpow T theta := by
    rw [← Real.rpow_natCast]
    exact hlogAbs
  have haggregate :
      data.A * ramachandraDyadicFamilyCost 1 T data.N data.b ≤
        C₀ * Real.rpow T (1 + theta) := by
    calc
      data.A * ramachandraDyadicFamilyCost 1 T data.N data.b ≤
          C₀ * (1 : ℝ) * T * Real.log T ^ B := by
        simpa only [Nat.cast_one] using data.aggregate_budget
      _ ≤ C₀ * T * Real.rpow T theta := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hlogPow
            (mul_nonneg hC₀.le hTpos.le)
      _ = C₀ * Real.rpow T (1 + theta) := by
        calc
          C₀ * T * Real.rpow T theta =
              C₀ * (Real.rpow T 1 * Real.rpow T theta) := by
                have honeRpow : Real.rpow T (1 : ℝ) = T := Real.rpow_one T
                rw [honeRpow]
                ring
          _ = C₀ * Real.rpow T (1 + theta) :=
            congrArg (fun y : ℝ => C₀ * y)
              (Real.rpow_add hTpos 1 theta).symm
  have hscale0 : 0 ≤ Cmv * Real.rpow (2 * T) eta :=
    mul_nonneg hCmv.le (Real.rpow_nonneg (by positivity) _)
  have hcombined :
      Cmv * Real.rpow (2 * T) eta *
          (data.A * ramachandraDyadicFamilyCost 1 T data.N data.b) ≤
        Cmv * Real.rpow (2 * T) eta *
          (C₀ * Real.rpow T (1 + theta)) :=
    mul_le_mul_of_nonneg_left haggregate hscale0
  have hmulTwo : Real.rpow (2 * T) eta =
      Real.rpow 2 eta * Real.rpow T eta :=
    Real.mul_rpow (by norm_num) hTpos.le
  have hpowCombine : Real.rpow T eta * Real.rpow T (1 + theta) =
      Real.rpow T (1 + eta + theta) := by
    calc
      Real.rpow T eta * Real.rpow T (1 + theta) =
          Real.rpow T (eta + (1 + theta)) :=
        (Real.rpow_add hTpos eta (1 + theta)).symm
      _ = Real.rpow T (1 + eta + theta) := by congr 1 <;> ring
  have hexponent : 1 + eta + theta ≤ 1 + epsilon := by
    dsimp [eta, theta]
    linarith
  have hpowMono : Real.rpow T (1 + eta + theta) ≤
      Real.rpow T (1 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hTone hexponent
  calc
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chiOne
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) =
        ∑ t ∈ W, criticalLineLFourth chiOne t := by rfl
    _ ≤ Cmv * Real.rpow (2 * T) eta *
          (data.A * ramachandraDyadicFamilyCost 1 T data.N data.b) := hraw
    _ ≤ Cmv * Real.rpow (2 * T) eta *
          (C₀ * Real.rpow T (1 + theta)) := hcombined
    _ = C * Real.rpow T (1 + eta + theta) := by
      rw [hmulTwo]
      calc
        Cmv * (Real.rpow 2 eta * Real.rpow T eta) *
            (C₀ * Real.rpow T (1 + theta)) =
            C * (Real.rpow T eta * Real.rpow T (1 + theta)) := by
              dsimp [C]
              ring
        _ = C * Real.rpow T (1 + eta + theta) := by rw [hpowCombine]
    _ ≤ C * Real.rpow T (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hpowMono hC.le

end
end MAPPrincipalZetaFourthMomentFromDyadicAFE

#print axioms MAPPrincipalZetaFourthMomentFromDyadicAFE.principalZetaDiscreteFourthMoment_of_dyadicAFE_raw
