import PrincipalZetaHuxley1972TerminalProofReduction

/-!
# Corrected Huxley terminal collar with the `(5.2)` log factors retained

`PrincipalZetaHuxley1972Equation58LogAudit` shows that the printed Jutila
breaks add positive logarithmic powers omitted in the second line of `(5.8)`.
On the MAP collar, the exact variable powers are bounded by one additional
integral log power.  Thus the source-faithful fixed-power envelope is

* first term: `log^22`;
* middle term: `log^45`;
* third term: `log^76`.

The difference between the third and middle losses remains exactly `31`, so
Huxley's already-certified power-gap absorption is unchanged.  This module
provides the corrected deterministic route to the principal selected-system
interface, with final explicit loss `P=45` rather than the unproved `P=44`.
-/

namespace MAPPrincipalZetaHuxley1972CorrectedLog45Terminal

open DirichletZeros
open MAPHuxleyCompactGapExponent
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPJutilaCollarMeshCutoff MAPJutilaCollarA5Budget
open MAPPrincipalZetaHuxley1972TerminalProofReduction

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- The repaired `(6.10)` constant required by the printed use of `Y_300`. -/
def correctedEquation610ConstantLog45 : ℝ := 3240000

private theorem weak_equation610_complement_of_corrected
    {T sigma : ℝ} (hT : Real.exp (Real.exp 1) ≤ T)
    (hcorrected : correctedEquation610ConstantLog45 *
      Real.log (Real.log T) / Real.log T ≤ 1 - sigma) :
    32400 * Real.log (Real.log T) / Real.log T ≤ 1 - sigma := by
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT
  have hlogPos : 0 < Real.log T := (Real.exp_pos 1).trans_le hlogLower
  have hloglog0 : 0 ≤ Real.log (Real.log T) :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hlogLower)
  have hfrac0 : 0 ≤ Real.log (Real.log T) / Real.log T :=
    div_nonneg hloglog0 hlogPos.le
  have hconst : (32400 : ℝ) ≤ correctedEquation610ConstantLog45 := by
    norm_num [correctedEquation610ConstantLog45]
  calc
    32400 * Real.log (Real.log T) / Real.log T =
        32400 * (Real.log (Real.log T) / Real.log T) := by ring
    _ ≤ correctedEquation610ConstantLog45 *
        (Real.log (Real.log T) / Real.log T) :=
      mul_le_mul_of_nonneg_right hconst hfrac0
    _ = correctedEquation610ConstantLog45 *
        Real.log (Real.log T) / Real.log T := by ring
    _ ≤ 1 - sigma := hcorrected

/-- The repaired third term still spends exactly `31` log powers: `76-45`.
The stronger factor-100 complement implies the weaker inequality used by the
existing power-gap theorem. -/
theorem correctedEquation58_thirdTerm_le_log45_target
    {T sigma : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hsigmaLow : 279 / 280 ≤ sigma) (hsigmaHigh : sigma ≤ 1)
    (hnotZeroFree : correctedEquation610ConstantLog45 *
      Real.log (Real.log T) / Real.log T ≤ 1 - sigma) :
    Real.rpow T (equation58ThirdExponent sigma) *
        Real.rpow (Real.log T) 76 ≤
      Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 45 := by
  have hweak := weak_equation610_complement_of_corrected hT hnotZeroFree
  have h75 := equation58_thirdTerm_le_target
    hT hsigmaLow hsigmaHigh hweak
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT
  have hlogPos : 0 < Real.log T := (Real.exp_pos 1).trans_le hlogLower
  have hsplit76 : Real.rpow (Real.log T) 76 =
      Real.rpow (Real.log T) 75 * Real.log T := by
    calc
      Real.rpow (Real.log T) 76 =
          Real.rpow (Real.log T) ((75 : ℝ) + 1) := by norm_num
      _ = Real.rpow (Real.log T) 75 *
          Real.rpow (Real.log T) 1 := Real.rpow_add hlogPos 75 1
      _ = Real.rpow (Real.log T) 75 * Real.log T := by
        congr 1
        exact Real.rpow_one _
  have hsplit45 : Real.rpow (Real.log T) 45 =
      Real.rpow (Real.log T) 44 * Real.log T := by
    calc
      Real.rpow (Real.log T) 45 =
          Real.rpow (Real.log T) ((44 : ℝ) + 1) := by norm_num
      _ = Real.rpow (Real.log T) 44 *
          Real.rpow (Real.log T) 1 := Real.rpow_add hlogPos 44 1
      _ = Real.rpow (Real.log T) 44 * Real.log T := by
        congr 1
        exact Real.rpow_one _
  rw [hsplit76, hsplit45]
  calc
    Real.rpow T (equation58ThirdExponent sigma) *
        (Real.rpow (Real.log T) 75 * Real.log T) =
      (Real.rpow T (equation58ThirdExponent sigma) *
        Real.rpow (Real.log T) 75) * Real.log T := by ring
    _ ≤ (Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 44) * Real.log T :=
      mul_le_mul_of_nonneg_right h75 hlogPos.le
    _ = Real.rpow T (huxleyDensityExponent sigma) *
        (Real.rpow (Real.log T) 44 * Real.log T) := by ring

/-- The first term is trivially below the corrected `log^45` target. -/
theorem correctedEquation58_firstTerm_le_log45_target
    {T sigma : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) :
    Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 22 ≤
      Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 45 := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT
  have hlogOne : 1 ≤ Real.log T :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hlogLower
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num))
    (Real.rpow_nonneg hTpos.le _)

/-- Pure deterministic collapse of the corrected `22,45,76` envelope. -/
theorem correctedEquation58_threeTerms_le_three_log45_target
    {T sigma : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hsigmaLow : 279 / 280 ≤ sigma) (hsigmaHigh : sigma ≤ 1)
    (hnotZeroFree : correctedEquation610ConstantLog45 *
      Real.log (Real.log T) / Real.log T ≤ 1 - sigma) :
    Real.rpow T (huxleyDensityExponent sigma) *
          Real.rpow (Real.log T) 22 +
        Real.rpow T (huxleyDensityExponent sigma) *
          Real.rpow (Real.log T) 45 +
        Real.rpow T (equation58ThirdExponent sigma) *
          Real.rpow (Real.log T) 76 ≤
      3 * (Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 45) := by
  have hfirst := correctedEquation58_firstTerm_le_log45_target
    (sigma := sigma) hT
  have hthird := correctedEquation58_thirdTerm_le_log45_target
    hT hsigmaLow hsigmaHigh hnotZeroFree
  linarith

/-- Corrected terminal source surface after both printed repairs: the
factor-100 zero-free constant and the omitted break-log factors. -/
def Huxley1972CorrectedTerminalThreeTermDichotomyLog45 : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ Real.exp (Real.exp 1) ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      (zeroSupport chiOne sigma T).card = 0 ∨
        (correctedEquation610ConstantLog45 *
            Real.log (Real.log T) / Real.log T ≤ 1 - sigma ∧
          ((zeroSupport chiOne sigma T).card : ℝ) ≤
            C * (Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 22 +
                Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 45 +
                Real.rpow T (equation58ThirdExponent sigma) *
                  Real.rpow (Real.log T) 76))

/-- Corrected exact-log collar consequence. -/
def Huxley1972CorrectedTerminalCollarExactLog45 : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      ((zeroSupport chiOne sigma T).card : ℝ) ≤
        C * Real.rpow (Real.log T) 45 *
          Real.rpow T (huxleyDensityExponent sigma)

theorem correctedTerminalCollarExactLog45_of_threeTermDichotomy
    (hsource : Huxley1972CorrectedTerminalThreeTermDichotomyLog45) :
    Huxley1972CorrectedTerminalCollarExactLog45 := by
  obtain ⟨C, T₀, hC, hT₀, hsource⟩ := hsource
  have htwoT₀ : 2 ≤ T₀ := by
    have htwoExpOne : (2 : ℝ) ≤ Real.exp 1 :=
      (show (2 : ℝ) ≤ 2.7182818283 by norm_num).trans Real.exp_one_gt_d9.le
    have hExpMono : Real.exp 1 ≤ Real.exp (Real.exp 1) :=
      Real.exp_le_exp.mpr (Real.one_le_exp zero_le_one)
    exact (htwoExpOne.trans hExpMono).trans hT₀
  refine ⟨3 * C, T₀, by positivity, htwoT₀, ?_⟩
  intro T sigma hT hsigmaLow hsigmaHigh
  have hTlarge : Real.exp (Real.exp 1) ≤ T := hT₀.trans hT
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hTlarge
  have hlogPos : 0 < Real.log T := by
    have : Real.exp 1 ≤ Real.log T := by
      calc
        Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
        _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hTlarge
    exact (Real.exp_pos 1).trans_le this
  rcases hsource T sigma hT hsigmaLow hsigmaHigh with hzero | hthree
  · have hnonneg : 0 ≤ (3 * C) * Real.rpow (Real.log T) 45 *
        Real.rpow T (huxleyDensityExponent sigma) :=
      mul_nonneg
        (mul_nonneg (by positivity) (Real.rpow_nonneg hlogPos.le _))
        (Real.rpow_nonneg hTpos.le _)
    simpa [hzero] using hnonneg
  · have hcollapse := correctedEquation58_threeTerms_le_three_log45_target
      hTlarge hsigmaLow hsigmaHigh hthree.1
    calc
      ((zeroSupport chiOne sigma T).card : ℝ) ≤
          C * (Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 22 +
              Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 45 +
              Real.rpow T (equation58ThirdExponent sigma) *
                Real.rpow (Real.log T) 76) := hthree.2
      _ ≤ C * (3 * (Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 45)) :=
        mul_le_mul_of_nonneg_left hcollapse hC.le
      _ = (3 * C) * Real.rpow (Real.log T) 45 *
          Real.rpow T (huxleyDensityExponent sigma) := by ring

/-- The corrected terminal collar inhabits MAP's principal selected-system
surface with the honest fixed loss `P=45`. -/
theorem principalSelectedP53_of_correctedTerminalCollarExactLog45
    (hsource : Huxley1972CorrectedTerminalCollarExactLog45) :
    JutilaGappedSelectedPrincipalP53Eventually := by
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hsource
  let R₀ : ℝ := max T₀ 6
  refine ⟨C, R₀, 45, hC, le_max_right _ _, by norm_num, ?_⟩
  intro q _inst chi T sigma omega W hprim hchi hT hsigmaLow hsigmaHigh
    _homega _hgap hscale _hregularGap hWsub _hWsep _hWcard
  have hq : q = 1 := by
    have hcond : chi.conductor = q := hprim
    rw [hchi, DirichletCharacter.conductor_one] at hcond
    exact hcond.symm
  subst q
  have hchiOne : chi = (1 : DirichletCharacter ℂ 1) := hchi
  subst chi
  simp only [Nat.cast_one, one_mul] at hscale ⊢
  have hTzero : T₀ ≤ T := (le_max_left T₀ 6).trans hscale
  have hTone : 1 ≤ T := by linarith
  have hWsupport : W ⊆ zeroSupport chiOne sigma T := by
    intro rho hrho
    exact (Finset.mem_filter.mp (hWsub hrho)).1
  have hcard : (W.card : ℝ) ≤ ((zeroSupport chiOne sigma T).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hWsupport
  have hsourceBound := hbound T sigma hTzero hsigmaLow hsigmaHigh
  have hden : 0 < 3 * sigma - 1 := by linarith
  have hgap0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigmaHigh
  have hcoeff : 3 / (3 * sigma - 1) ≤
      2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget := by
    apply (div_le_iff₀ hden).2
    norm_num [collarDelta, detectorLogBudget]
    nlinarith
  have hexp : huxleyDensityExponent sigma ≤
      (2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
        (1 - sigma) := by
    rw [show huxleyDensityExponent sigma =
      (3 / (3 * sigma - 1)) * (1 - sigma) by
        unfold huxleyDensityExponent
        field_simp]
    exact mul_le_mul_of_nonneg_right hcoeff hgap0
  have hpower := Real.rpow_le_rpow_of_exponent_le hTone hexp
  have hlog0 : 0 ≤ Real.rpow (Real.log T) (45 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg hTone) _
  calc
    (W.card : ℝ) ≤ ((zeroSupport chiOne sigma T).card : ℝ) := hcard
    _ ≤ C * Real.rpow (Real.log T) 45 *
          Real.rpow T (huxleyDensityExponent sigma) := hsourceBound
    _ ≤ C * Real.rpow (Real.log T) 45 *
          Real.rpow T
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma)) :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg hC.le hlog0)

theorem principalSelectedP53_of_correctedThreeTermDichotomyLog45
    (hsource : Huxley1972CorrectedTerminalThreeTermDichotomyLog45) :
    JutilaGappedSelectedPrincipalP53Eventually :=
  principalSelectedP53_of_correctedTerminalCollarExactLog45
    (correctedTerminalCollarExactLog45_of_threeTermDichotomy hsource)

end
end MAPPrincipalZetaHuxley1972CorrectedLog45Terminal

#print axioms MAPPrincipalZetaHuxley1972CorrectedLog45Terminal.correctedEquation58_thirdTerm_le_log45_target
#print axioms MAPPrincipalZetaHuxley1972CorrectedLog45Terminal.correctedEquation58_threeTerms_le_three_log45_target
#print axioms MAPPrincipalZetaHuxley1972CorrectedLog45Terminal.correctedTerminalCollarExactLog45_of_threeTermDichotomy
#print axioms MAPPrincipalZetaHuxley1972CorrectedLog45Terminal.principalSelectedP53_of_correctedThreeTermDichotomyLog45
