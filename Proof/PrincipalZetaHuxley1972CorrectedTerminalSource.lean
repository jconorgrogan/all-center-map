import PrincipalZetaHuxley1972TerminalProofReduction
import PrincipalZetaHuxley1972CorrectedLog45Terminal
import PrincipalWeakVKZeroGap
import PrincipalZetaHuxley1972Equation39Exceptions
import PrincipalZetaHuxley1972Equation35Identity
import PrincipalZetaHuxley1972Equation314GammaNormalizer
import PrincipalZetaHuxley1972Equation315ClassifierArithmetic
import PrincipalZetaHuxley1972LiteralClassCover
import PostA5TypeIIFourthMoment
import PrincipalZetaContourTails
import PostA5HighStripSplitReductionFromFourthMoment

/-!
# Huxley 1972 terminal source: printed-constant audit and repaired weld

On printed p.168, (5.5) permits the Jutila-break index `A` only when

`A <= (1/6) * sqrt ((1-alpha) log T / log log T)`.

On printed p.169, (6.9) requires `X > Y_300`, and the next sentence sums
(4.7) for `a = 2, ..., 300`.  The complement of the printed (6.10), whose
constant is `32400`, only forces the right side of (5.5) past `30`, because
`32400 = (6*30)^2`.  It does not force it past `300`.  The constant which
makes those three printed lines fit is

`3240000 = (6*300)^2`.

This file does two things.

* It certifies that exact factor-100 mismatch, including a literal numerical
  counterexample to the missing implication.
* It exposes a repaired source surface at the actual intermediate equations:
  (3.9)--(3.15) classification and exceptions, the class-I estimate (5.8),
  the class-II elimination (6.7)--(6.9), and the corrected zero-free branch.
  Their deterministic weld gives the already-certified terminal ledger and
  hence the principal selected-system estimate.

No final zero-density estimate is assumed in this source surface.
-/

namespace MAPPrincipalZetaHuxley1972CorrectedTerminalSource

open DirichletZeros
open MAPHuxleyCompactGapExponent
open MAPPrincipalZetaHuxley1972TerminalProofReduction
open MAPJutilaGappedCollarSelectedP53Adapter
open Filter MAPKhaleAppendixBSource
open MAPPrincipalZetaHuxley1972Equation39Exceptions
open MAPPrincipalZetaHuxley1972Equation35Identity
open MAPPrincipalZetaHuxley1972Equation314GammaNormalizer
open MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic
open MAPPrincipalZetaHuxley1972Equation315RightClassifier
open MAPPrincipalZetaHuxley1972ClassifierWitnesses
open MAPPrincipalZetaHuxley1972LiteralClassCover
open PostA5TypeIIFourthMoment
open MAPPrincipalZetaContourTails
open PostA5HighStripSplitReductionFromFourthMoment
open MAPPrincipalZetaHuxley1972CorrectedLog45Terminal

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- The constant printed in Huxley (6.10). -/
def printedEquation610Constant : ℝ := 32400

/-- The constant required by (5.5) when (6.9) and the following sentence use
the index `300`. -/
def correctedEquation610Constant : ℝ := 3240000

/-- The normalized right side of the Jutila-break condition (5.5). -/
def equation55Budget (R : ℝ) : ℝ := Real.sqrt R / 6

theorem printed_constant_eq_six_mul_thirty_sq :
    printedEquation610Constant = (6 * 30 : ℝ) ^ 2 := by
  norm_num [printedEquation610Constant]

theorem corrected_constant_eq_six_mul_threeHundred_sq :
    correctedEquation610Constant = (6 * 300 : ℝ) ^ 2 := by
  norm_num [correctedEquation610Constant]

/-- The complement of the printed (6.10) forces the (5.5) budget past 30. -/
theorem printed_equation610_complement_forces_thirty
    {R : ℝ} (hR : printedEquation610Constant < R) :
    30 < equation55Budget R := by
  have hsqrt : (180 : ℝ) < Real.sqrt R := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [printedEquation610Constant]
    simpa [printedEquation610Constant] using hR
  unfold equation55Budget
  linarith

/-- Exact death certificate: the printed constant does not imply that the
(5.5) budget reaches the index 300 used in (6.9). -/
theorem printed_equation610_complement_does_not_force_threeHundred :
    ∃ R : ℝ,
      printedEquation610Constant < R ∧ equation55Budget R < 300 := by
  refine ⟨32401, by norm_num [printedEquation610Constant], ?_⟩
  unfold equation55Budget
  have hsqrt : Real.sqrt (32401 : ℝ) < 181 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- The factor-100 repaired constant forces precisely the index required by
the printed `Y_300` / `a <= 300` terminal step. -/
theorem corrected_equation610_complement_forces_threeHundred
    {R : ℝ} (hR : correctedEquation610Constant < R) :
    300 < equation55Budget R := by
  have hsqrt : (1800 : ℝ) < Real.sqrt R := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [correctedEquation610Constant]
    simpa [correctedEquation610Constant] using hR
  unfold equation55Budget
  linarith

private theorem eventually_log_le_eighth_rpow :
    ∀ᶠ L : ℝ in atTop, Real.log L ≤ Real.rpow L (1 / 8 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 8)).eventuallyLE
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  have hrpow0 : 0 ≤ Real.rpow L (1 / 8 : ℝ) :=
    Real.rpow_nonneg (zero_lt_one.trans hL1).le _
  have hL' : Real.log L ≤ |Real.rpow L (1 / 8 : ℝ)| := by
    simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlog0] using hL
  rwa [abs_of_nonneg hrpow0] at hL'

/-- Any fixed multiple of `log log T / log T` is eventually strictly inside
the certified weak-VK gap `c (log T)^(-3/4)`.  This is why repairing the
constant in (6.10) does not change the terminal theorem. -/
theorem eventually_correctedThreshold_lt_weakVKScale
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop,
      correctedEquation610Constant *
          Real.log (Real.log T) / Real.log T <
        c * Real.rpow (Real.log T) (-(3 / 4 : ℝ)) := by
  have hgrowth : ∀ᶠ L : ℝ in atTop,
      correctedEquation610Constant / c < Real.rpow L (1 / 8 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually
      (eventually_gt_atTop (correctedEquation610Constant / c))
  have hlogT := Real.tendsto_log_atTop.eventually eventually_log_le_eighth_rpow
  have hgrowthT := Real.tendsto_log_atTop.eventually hgrowth
  filter_upwards [hlogT, hgrowthT,
      eventually_gt_atTop (Real.exp (Real.exp 1))]
    with T hlog hgrowth' hT
  let L := Real.log T
  have hLone : 1 < L := by
    dsimp [L]
    have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans hT
    rw [Real.lt_log_iff_exp_lt hTpos]
    exact (Real.exp_lt_exp.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)).trans hT
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hLone.le
  have hpowPos : 0 < Real.rpow L (1 / 8 : ℝ) :=
    Real.rpow_pos_of_pos hLpos _
  have hconstGrowth : correctedEquation610Constant <
      c * Real.rpow L (1 / 8 : ℝ) := by
    have h := (div_lt_iff₀ hc).mp (by simpa [L] using hgrowth')
    simpa [mul_comm] using h
  have hraw : correctedEquation610Constant * Real.log L <
      c * Real.rpow L (1 / 4 : ℝ) := by
    calc
      correctedEquation610Constant * Real.log L ≤
          correctedEquation610Constant * Real.rpow L (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa [L] using hlog)
          (by norm_num [correctedEquation610Constant])
      _ < (c * Real.rpow L (1 / 8 : ℝ)) *
          Real.rpow L (1 / 8 : ℝ) :=
        mul_lt_mul_of_pos_right hconstGrowth hpowPos
      _ = c * Real.rpow L (1 / 4 : ℝ) := by
        have hpow : Real.rpow L (1 / 8 : ℝ) *
            Real.rpow L (1 / 8 : ℝ) = Real.rpow L (1 / 4 : ℝ) := by
          calc
            Real.rpow L (1 / 8 : ℝ) * Real.rpow L (1 / 8 : ℝ) =
                Real.rpow L ((1 / 8 : ℝ) + 1 / 8) :=
              (Real.rpow_add hLpos _ _).symm
            _ = Real.rpow L (1 / 4 : ℝ) := by norm_num
        rw [show (c * Real.rpow L (1 / 8 : ℝ)) *
            Real.rpow L (1 / 8 : ℝ) =
            c * (Real.rpow L (1 / 8 : ℝ) *
              Real.rpow L (1 / 8 : ℝ)) by ring, hpow]
  have hdiv : correctedEquation610Constant * Real.log L / L <
      (c * Real.rpow L (1 / 4 : ℝ)) / L :=
    (div_lt_div_iff_of_pos_right hLpos).2 hraw
  have hright : (c * Real.rpow L (1 / 4 : ℝ)) / L =
      c * Real.rpow L (-(3 / 4 : ℝ)) := by
    calc
      (c * Real.rpow L (1 / 4 : ℝ)) / L =
          c * (Real.rpow L (1 / 4 : ℝ) / L) := by ring
      _ = c * (Real.rpow L (1 / 4 : ℝ) / Real.rpow L 1) := by
        exact congrArg
          (fun x : ℝ => c * (Real.rpow L (1 / 4 : ℝ) / x))
          (Real.rpow_one L).symm
      _ = c * Real.rpow L ((1 / 4 : ℝ) - 1) := by
        exact congrArg (fun x : ℝ => c * x)
          (Real.rpow_sub hLpos (1 / 4 : ℝ) 1).symm
      _ = c * Real.rpow L (-(3 / 4 : ℝ)) := by norm_num
  rw [hright] at hdiv
  simpa [L, correctedEquation610Constant] using hdiv

/-- The corrected zero-free branch is not a new analytic source: Khale's
Appendix-B weak-VK gap, already present in the MAP endpoint, implies it. -/
def Huxley1972CorrectedEquation610ZeroFree : Prop :=
  ∃ T₀ : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      1 - sigma ≤ correctedEquation610Constant *
          Real.log (Real.log T) / Real.log T →
      (zeroSupport chiOne sigma T).card = 0

theorem correctedEquation610ZeroFree_of_appendixB
    (hKhale : AppendixBCorollary104) :
    Huxley1972CorrectedEquation610ZeroFree := by
  obtain ⟨c, hc, hgapEventually⟩ :=
    MAPPrincipalWeakVKZeroGap.exists_eventually_principal_weakVK_gap_of_appendixB
      hKhale
  obtain ⟨Tgap, hgap⟩ := Filter.eventually_atTop.1 hgapEventually
  obtain ⟨Ttrade, htrade⟩ := Filter.eventually_atTop.1
    (eventually_correctedThreshold_lt_weakVKScale hc)
  let T₀ : ℝ := max (Real.exp (Real.exp 1)) (max Tgap Ttrade)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T sigma hT hsigmaLow hsigmaHigh hzero
  have hTgap : Tgap ≤ T :=
    (le_max_left Tgap Ttrade).trans (le_max_right _ _) |>.trans hT
  have hTtrade : Ttrade ≤ T :=
    (le_max_right Tgap Ttrade).trans (le_max_right _ _) |>.trans hT
  have hgapT := hgap T hTgap T le_rfl
  have htradeT := htrade T hTtrade
  rw [Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨rho, hrho⟩ := hnonempty
  have hfull : rho ∈ zeroSupport chiOne 0 T :=
    MAPMellinDetectorLeaf.zeroSupport_mono chiOne (by linarith) le_rfl hrho
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    chiOne sigma T hrho
  rw [zeroRectangle, Complex.mem_reProdIm] at hrect
  have hweak := hgapT rho hfull
  have hre : sigma ≤ rho.re := hrect.1.1
  linarith

/-- The three natural-number pieces immediately after Huxley's classification:
the exceptions to (3.9), class (i), and class (ii). -/
structure TerminalCounts where
  exceptional : ℕ
  classI : ℕ
  classII : ℕ

/-- Haneke's bound as quoted verbatim in Huxley (6.7), before Huxley's
elementary relaxation to exponent `13/80`.  The constants hidden by `≪` are
made explicit in the usual eventual form.  This is a genuine external
analytic theorem, not a density estimate. -/
def Huxley1972HanekeEquation67 : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ t : ℝ, T₀ ≤ |t| →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * Real.rpow |t| (6 / 37 : ℝ) *
          Real.log (|t| + Real.exp 1)

/-- The exponent reserve used when the logarithm in Haneke (6.7) is absorbed
into Huxley's `13/80` power. -/
theorem haneke67_exponent_reserve :
    (13 / 80 : ℝ) - 6 / 37 = 1 / 2960 := by
  norm_num

/-- The relaxed second inequality printed in (6.7), with its quantifiers
made explicit. -/
def Huxley1972HanekeEquation67Relaxed : Prop :=
  ∃ T₀ : ℝ, Real.exp 1 ≤ T₀ ∧
    ∀ t : ℝ, T₀ ≤ |t| →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Real.rpow |t| (13 / 80 : ℝ)

/-- Haneke's quoted `6/37` bound implies Huxley's `13/80` relaxation.
The exact reserve is `1/2960`; it absorbs both the source constant and the
single logarithm. -/
theorem hanekeEquation67Relaxed_of_hanekeEquation67
    (h : Huxley1972HanekeEquation67) :
    Huxley1972HanekeEquation67Relaxed := by
  obtain ⟨C, Tsource, hC, hTsource, hsource⟩ := h
  have hpoly := eventually_const_mul_polylog_le_rpow
    (2 * C) 1 (1 / 2960 : ℝ) (by positivity) (by norm_num)
  obtain ⟨Tpoly, hpoly⟩ := Filter.eventually_atTop.1 hpoly
  let T₀ : ℝ := max (Real.exp 1) (max Tsource Tpoly)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro t ht
  have hinner : max Tsource Tpoly ≤ |t| :=
    (le_max_right (Real.exp 1) (max Tsource Tpoly)).trans ht
  have hTabs : 0 < |t| :=
    (Real.exp_pos 1).trans_le ((le_max_left _ _).trans ht)
  have hTsource' : Tsource ≤ |t| :=
    (le_max_left Tsource Tpoly).trans hinner
  have hTpoly' : Tpoly ≤ |t| :=
    (le_max_right Tsource Tpoly).trans hinner
  have hE : Real.exp 1 ≤ |t| := (le_max_left _ _).trans ht
  have htwo : (2 : ℝ) ≤ |t| := by
    exact (show (2 : ℝ) ≤ Real.exp 1 by
      exact (show (2 : ℝ) ≤ 2.7182818283 by norm_num).trans
        Real.exp_one_gt_d9.le) |>.trans hE
  have hlogPos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hshiftPos : 0 < |t| + Real.exp 1 := by positivity
  have hshift : |t| + Real.exp 1 ≤ 2 * |t| := by linarith
  have hlogShift : Real.log (|t| + Real.exp 1) ≤
      2 * Real.log |t| := by
    calc
      Real.log (|t| + Real.exp 1) ≤ Real.log (2 * |t|) :=
        Real.log_le_log hshiftPos hshift
      _ = Real.log 2 + Real.log |t| := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTabs.ne']
      _ ≤ 2 * Real.log |t| := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
        linarith
  have hpoly' : 2 * C * Real.log |t| ≤
      Real.rpow |t| (1 / 2960 : ℝ) := by
    have hp := hpoly |t| hTpoly'
    simpa [Real.rpow_one] using hp
  have hfront : C * Real.log (|t| + Real.exp 1) ≤
      Real.rpow |t| (1 / 2960 : ℝ) := by
    calc
      C * Real.log (|t| + Real.exp 1) ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlogShift hC.le
      _ = 2 * C * Real.log |t| := by ring
      _ ≤ Real.rpow |t| (1 / 2960 : ℝ) := hpoly'
  have hsource' := hsource t hTsource'
  calc
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * Real.rpow |t| (6 / 37 : ℝ) *
          Real.log (|t| + Real.exp 1) := hsource'
    _ = Real.rpow |t| (6 / 37 : ℝ) *
          (C * Real.log (|t| + Real.exp 1)) := by ring
    _ ≤ Real.rpow |t| (6 / 37 : ℝ) *
          Real.rpow |t| (1 / 2960 : ℝ) :=
      mul_le_mul_of_nonneg_left hfront (Real.rpow_nonneg hTabs.le _)
    _ = Real.rpow |t| (13 / 80 : ℝ) := by
      calc
        Real.rpow |t| (6 / 37 : ℝ) * Real.rpow |t| (1 / 2960 : ℝ) =
            Real.rpow |t| ((6 / 37 : ℝ) + 1 / 2960) :=
          (Real.rpow_add hTabs _ _).symm
        _ = Real.rpow |t| (13 / 80 : ℝ) := by norm_num

/-- The strict exponent reserve in Haneke's theorem absorbs an arbitrary
positive prefactor.  This is the form actually needed to make (3.13)
contradict (6.8), because the normalizing constant `c₂` in (3.14) is fixed
but not numerically evaluated in the paper. -/
theorem hanekeEquation67_powerSaving
    (h : Huxley1972HanekeEquation67) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ T₀ : ℝ, Real.exp 1 ≤ T₀ ∧
      ∀ t : ℝ, T₀ ≤ |t| →
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          delta * Real.rpow |t| (13 / 80 : ℝ) := by
  obtain ⟨C, Tsource, hC, hTsource, hsource⟩ := h
  have hpoly := eventually_const_mul_polylog_le_rpow
    (2 * C / delta) 1 (1 / 2960 : ℝ) (by positivity) (by norm_num)
  obtain ⟨Tpoly, hpoly⟩ := Filter.eventually_atTop.1 hpoly
  let T₀ : ℝ := max (Real.exp 1) (max Tsource Tpoly)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro t ht
  have hinner : max Tsource Tpoly ≤ |t| :=
    (le_max_right (Real.exp 1) (max Tsource Tpoly)).trans ht
  have hTabs : 0 < |t| :=
    (Real.exp_pos 1).trans_le ((le_max_left _ _).trans ht)
  have hTsource' : Tsource ≤ |t| :=
    (le_max_left Tsource Tpoly).trans hinner
  have hTpoly' : Tpoly ≤ |t| :=
    (le_max_right Tsource Tpoly).trans hinner
  have hE : Real.exp 1 ≤ |t| := (le_max_left _ _).trans ht
  have htwo : (2 : ℝ) ≤ |t| := by
    exact (show (2 : ℝ) ≤ Real.exp 1 by
      exact (show (2 : ℝ) ≤ 2.7182818283 by norm_num).trans
        Real.exp_one_gt_d9.le) |>.trans hE
  have hlogPos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hshiftPos : 0 < |t| + Real.exp 1 := by positivity
  have hshift : |t| + Real.exp 1 ≤ 2 * |t| := by linarith
  have hlogShift : Real.log (|t| + Real.exp 1) ≤
      2 * Real.log |t| := by
    calc
      Real.log (|t| + Real.exp 1) ≤ Real.log (2 * |t|) :=
        Real.log_le_log hshiftPos hshift
      _ = Real.log 2 + Real.log |t| := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTabs.ne']
      _ ≤ 2 * Real.log |t| := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
        linarith
  have hpoly' : (2 * C / delta) * Real.log |t| ≤
      Real.rpow |t| (1 / 2960 : ℝ) := by
    have hp := hpoly |t| hTpoly'
    simpa [Real.rpow_one] using hp
  have hfront : C * Real.log (|t| + Real.exp 1) ≤
      delta * Real.rpow |t| (1 / 2960 : ℝ) := by
    have hscaled : 2 * C * Real.log |t| ≤
        delta * Real.rpow |t| (1 / 2960 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hpoly' hdelta.le
      field_simp [hdelta.ne'] at this ⊢
      nlinarith
    calc
      C * Real.log (|t| + Real.exp 1) ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlogShift hC.le
      _ = 2 * C * Real.log |t| := by ring
      _ ≤ delta * Real.rpow |t| (1 / 2960 : ℝ) := hscaled
  have hsource' := hsource t hTsource'
  calc
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * Real.rpow |t| (6 / 37 : ℝ) *
          Real.log (|t| + Real.exp 1) := hsource'
    _ = Real.rpow |t| (6 / 37 : ℝ) *
          (C * Real.log (|t| + Real.exp 1)) := by ring
    _ ≤ Real.rpow |t| (6 / 37 : ℝ) *
          (delta * Real.rpow |t| (1 / 2960 : ℝ)) :=
      mul_le_mul_of_nonneg_left hfront (Real.rpow_nonneg hTabs.le _)
    _ = delta * Real.rpow |t| (13 / 80 : ℝ) := by
      rw [show Real.rpow |t| (6 / 37 : ℝ) *
          (delta * Real.rpow |t| (1 / 2960 : ℝ)) =
          delta * (Real.rpow |t| (6 / 37 : ℝ) *
            Real.rpow |t| (1 / 2960 : ℝ)) by ring]
      congr 1
      calc
        Real.rpow |t| (6 / 37 : ℝ) * Real.rpow |t| (1 / 2960 : ℝ) =
            Real.rpow |t| ((6 / 37 : ℝ) + 1 / 2960) :=
          (Real.rpow_add hTabs _ _).symm
        _ = Real.rpow |t| (13 / 80 : ℝ) := by norm_num

/-- Exact deterministic core of Huxley's claim that (6.7)--(6.8) rule out
the class-II inequality (3.13).  The hypotheses retain the literal `2^n`
factor, the translated ordinate window, the critical-line mollifier size,
and the normalized scale equality.  No zero-density statement appears. -/
theorem equation313_contradiction_of_haneke_scale
    {T X Y alpha c₂ gamma t : ℝ} {n : ℕ}
    (hT : 2 ≤ T) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hn : 1 ≤ n) (hc₂ : 0 < c₂)
    (hgamma : |gamma| ≤ T)
    (hnear : |gamma - t| ≤ (2 ^ n : ℕ))
    (hscale : Real.sqrt X * Real.rpow T (13 / 80 : ℝ) =
      Real.rpow Y (alpha - 1 / 2))
    {Z M : ℂ}
    (hZ : ‖Z‖ ≤ (c₂ / 4) * Real.rpow |t| (13 / 80 : ℝ))
    (hM : ‖M‖ ≤ 2 * Real.sqrt X) :
    ¬ c₂ * (2 ^ n : ℕ) * Real.rpow Y (alpha - 1 / 2) < ‖Z * M‖ := by
  intro hlarge
  let D : ℝ := (2 ^ n : ℕ)
  have hDtwo : (2 : ℝ) ≤ D := by
    dsimp [D]
    exact_mod_cast (show 2 ≤ 2 ^ n by
      exact (Nat.pow_le_pow_right (n := 2) (by norm_num) hn))
  have hDpos : 0 < D := by linarith
  have hTpos : 0 < T := by linarith
  have htTriangle : |t| ≤ |gamma| + |gamma - t| := by
    have h := abs_add_le gamma (t - gamma)
    rw [show gamma + (t - gamma) = t by ring, abs_sub_comm] at h
    exact h
  have htTD : |t| ≤ T * D := by
    calc
      |t| ≤ |gamma| + |gamma - t| := htTriangle
      _ ≤ T + D := by dsimp [D]; linarith
      _ ≤ T * D := by nlinarith
  have hpowTD : Real.rpow |t| (13 / 80 : ℝ) ≤
      Real.rpow T (13 / 80 : ℝ) * D := by
    have hmono : Real.rpow |t| (13 / 80 : ℝ) ≤
        Real.rpow (T * D) (13 / 80 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg t) htTD (by norm_num)
    have hsplit : Real.rpow (T * D) (13 / 80 : ℝ) =
        Real.rpow T (13 / 80 : ℝ) *
          Real.rpow D (13 / 80 : ℝ) :=
      Real.mul_rpow hTpos.le hDpos.le
    have hDone : 1 ≤ D := by linarith
    have hDpow : Real.rpow D (13 / 80 : ℝ) ≤ D := by
      calc
        Real.rpow D (13 / 80 : ℝ) ≤ Real.rpow D 1 :=
          Real.rpow_le_rpow_of_exponent_le hDone (by norm_num)
        _ = D := Real.rpow_one D
    calc
      Real.rpow |t| (13 / 80 : ℝ) ≤
          Real.rpow (T * D) (13 / 80 : ℝ) := hmono
      _ = Real.rpow T (13 / 80 : ℝ) *
          Real.rpow D (13 / 80 : ℝ) := hsplit
      _ ≤ Real.rpow T (13 / 80 : ℝ) * D :=
        mul_le_mul_of_nonneg_left hDpow (Real.rpow_nonneg hTpos.le _)
  have hXM : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hprod : ‖Z * M‖ ≤
      c₂ * D * Real.rpow Y (alpha - 1 / 2) := by
    rw [norm_mul]
    calc
      ‖Z‖ * ‖M‖ ≤
          ((c₂ / 4) * Real.rpow |t| (13 / 80 : ℝ)) *
            (2 * Real.sqrt X) :=
        mul_le_mul hZ hM (norm_nonneg _)
          (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg t) _))
      _ ≤ ((c₂ / 4) *
          (Real.rpow T (13 / 80 : ℝ) * D)) *
            (2 * Real.sqrt X) := by
        gcongr
      _ ≤ c₂ * D *
          (Real.sqrt X * Real.rpow T (13 / 80 : ℝ)) := by
        have hnonneg : 0 ≤ c₂ * D *
            (Real.sqrt X * Real.rpow T (13 / 80 : ℝ)) := by
          exact mul_nonneg
            (mul_nonneg hc₂.le hDpos.le)
            (mul_nonneg hXM (Real.rpow_nonneg hTpos.le _))
        nlinarith
      _ = c₂ * D * Real.rpow Y (alpha - 1 / 2) := by rw [hscale]
  exact (not_lt_of_ge hprod) (by simpa [D] using hlarge)

/-! ## Globalized Haneke input and literal class-II elimination -/

/-- Haneke's eventual estimate, together with the certified coarse bound on
the remaining compact segment of the critical line, gives the uniform form
actually needed in Huxley's `(6.7)--(6.8)` argument.  The auxiliary factor
`D = 2^n` is retained: this avoids the invalid inference that the translated
ordinate `t` itself must be large. -/
theorem hanekeEquation67_global_scaled
    (h : Huxley1972HanekeEquation67) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ T D t : ℝ, T₀ ≤ T → 1 ≤ D → |t| ≤ T * D →
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          delta * Real.rpow T (13 / 80 : ℝ) *
            Real.rpow D (13 / 80 : ℝ) := by
  obtain ⟨Tlarge, hTlarge, hlarge⟩ :=
    hanekeEquation67_powerSaving h hdelta
  let K : ℝ := 3200 * (4 + Tlarge) ^ 6
  have hgrow : ∀ᶠ T : ℝ in Filter.atTop,
      K / delta ≤ Real.rpow T (13 / 80 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 80)).eventually
      (Filter.eventually_ge_atTop (K / delta))
  obtain ⟨Tsmall, hsmall⟩ := Filter.eventually_atTop.1 hgrow
  let T₀ : ℝ := max 2 (max Tlarge Tsmall)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T D t hT hD ht
  have hTlarge' : Tlarge ≤ T :=
    (le_max_left Tlarge Tsmall).trans (le_max_right 2 _ ) |>.trans hT
  have hTsmall' : Tsmall ≤ T :=
    (le_max_right Tlarge Tsmall).trans (le_max_right 2 _ ) |>.trans hT
  have hTpos : 0 < T := (show (0 : ℝ) < 2 by norm_num) |>.trans_le
    ((le_max_left 2 (max Tlarge Tsmall)).trans hT)
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hDpowOne : 1 ≤ Real.rpow D (13 / 80 : ℝ) :=
    Real.one_le_rpow hD (by norm_num)
  by_cases htLarge : Tlarge ≤ |t|
  · have hz := hlarge t htLarge
    have hpow : Real.rpow |t| (13 / 80 : ℝ) ≤
        Real.rpow (T * D) (13 / 80 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg t) ht (by norm_num)
    calc
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          delta * Real.rpow |t| (13 / 80 : ℝ) := hz
      _ ≤ delta * Real.rpow (T * D) (13 / 80 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hdelta.le
      _ = delta * Real.rpow T (13 / 80 : ℝ) *
          Real.rpow D (13 / 80 : ℝ) := by
        rw [show Real.rpow (T * D) (13 / 80 : ℝ) =
          Real.rpow T (13 / 80 : ℝ) *
            Real.rpow D (13 / 80 : ℝ) from
          Real.mul_rpow hTpos.le hDpos.le]
        ring
  · have htSmall : |t| ≤ Tlarge := le_of_not_ge htLarge
    have hTlargeNonneg : 0 ≤ Tlarge :=
      (show (0 : ℝ) < Real.exp 1 by positivity) |>.le.trans hTlarge
    have hbase : 4 + |t| ≤ 4 + Tlarge := by linarith
    have hzCoarse := norm_riemannZeta_criticalLine_le t
    have hzK :
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K := by
      calc
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            3200 * (4 + |t|) ^ 6 := hzCoarse
        _ ≤ 3200 * (4 + Tlarge) ^ 6 := by gcongr
        _ = K := rfl
    have hratio := hsmall T hTsmall'
    have hK : K ≤ delta * Real.rpow T (13 / 80 : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hdelta).mp hratio
    calc
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K := hzK
      _ ≤ delta * Real.rpow T (13 / 80 : ℝ) := hK
      _ ≤ delta * Real.rpow T (13 / 80 : ℝ) *
          Real.rpow D (13 / 80 : ℝ) := by
        have hfront : 0 ≤ delta * Real.rpow T (13 / 80 : ℝ) :=
          mul_nonneg hdelta.le (Real.rpow_nonneg hTpos.le _)
        nlinarith

/-- The exact class-II predicate `(3.13)` is impossible once Haneke is put
in the global scaled form and the published `(6.8)` scale inequality is
available.  This proves the deterministic class-II contradiction rather
than retaining it as a record field. -/
theorem not_huxleyClassII_of_globalHaneke_and_scale
    {T Y sigma : ℝ} {U : ℕ} {rho : ℂ}
    (hT : 2 ≤ T) (hY : 0 ≤ Y)
    (hgamma : |rho.im| ≤ T)
    (hscale : Real.sqrt U * Real.rpow T (13 / 80 : ℝ) ≤
      Real.rpow Y (sigma - 1 / 2))
    (hglobal : ∀ D t : ℝ, 1 ≤ D → |t| ≤ T * D →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (shiftedEquation314Normalizer / 2) *
          Real.rpow T (13 / 80 : ℝ) *
            Real.rpow D (13 / 80 : ℝ)) :
    ¬ HuxleyClassII rho U Y sigma shiftedEquation314Normalizer := by
  intro hII
  obtain ⟨n, hn, t, hnear, hlarge⟩ := hII
  let D : ℝ := (2 ^ n : ℕ)
  have hDtwo : (2 : ℝ) ≤ D := by
    have hpowNat : 2 ≤ 2 ^ n := by
      calc
        2 = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    change (2 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ)
    exact_mod_cast hpowNat
  have hDone : (1 : ℝ) ≤ D := by linarith
  have hTpos : 0 < T := by linarith
  have hDpos : 0 < D := by linarith
  have htTriangle : |t| ≤ |rho.im| + |rho.im - t| := by
    have h := abs_add_le rho.im (t - rho.im)
    rw [show rho.im + (t - rho.im) = t by ring, abs_sub_comm] at h
    exact h
  have htTD : |t| ≤ T * D := by
    have hnearD : |rho.im - t| ≤ D := by simpa [D] using hnear
    calc
      |t| ≤ |rho.im| + |rho.im - t| := htTriangle
      _ ≤ T + D := by linarith
      _ ≤ T * D := by nlinarith
  have hZ := hglobal D t hDone htTD
  have hM := norm_mollifier_criticalLine_le_two_sqrt chiOne U
    (s := (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) (by simp)
  have hDpow : Real.rpow D (13 / 80 : ℝ) ≤ D := by
    calc
      Real.rpow D (13 / 80 : ℝ) ≤ Real.rpow D 1 :=
        Real.rpow_le_rpow_of_exponent_le hDone (by norm_num)
      _ = D := Real.rpow_one D
  have hprod :
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          MAPMollifierCoefficientIdentity.mollifier chiOne U
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        shiftedEquation314Normalizer * D *
          Real.rpow Y (sigma - 1 / 2) := by
    rw [norm_mul]
    calc
      _ ≤ ((shiftedEquation314Normalizer / 2) *
            Real.rpow T (13 / 80 : ℝ) *
              Real.rpow D (13 / 80 : ℝ)) *
            (2 * Real.sqrt U) :=
        mul_le_mul hZ hM (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg
              (div_nonneg shiftedEquation314Normalizer_pos.le (by norm_num))
              (Real.rpow_nonneg hTpos.le _))
            (Real.rpow_nonneg hDpos.le _))
      _ = shiftedEquation314Normalizer *
            Real.rpow D (13 / 80 : ℝ) *
              (Real.sqrt U * Real.rpow T (13 / 80 : ℝ)) := by ring
      _ ≤ shiftedEquation314Normalizer *
            Real.rpow D (13 / 80 : ℝ) *
              Real.rpow Y (sigma - 1 / 2) := by
        exact mul_le_mul_of_nonneg_left hscale
          (mul_nonneg shiftedEquation314Normalizer_pos.le
            (Real.rpow_nonneg hDpos.le _))
      _ ≤ shiftedEquation314Normalizer * D *
            Real.rpow Y (sigma - 1 / 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDpow
            shiftedEquation314Normalizer_pos.le)
          (Real.rpow_nonneg hY _)
  exact (not_lt_of_ge hprod) (by simpa [D] using hlarge)

/-! ## Minimal source surface -/

/-- The one surviving class-I analytic source.

This is the literal output of Huxley p.165 `(2.6)` through p.169 `(5.8)`,
stated on the exact finite class-I set used by the certified classifier.  Its
existential witnesses retain all displayed scale conditions and the `(6.8)`
inequality needed by the now-certified class-II elimination.  The proposition
does not assume a zero-density estimate or a class cover.

The remaining source-descent project below this proposition is precisely
Montgomery's choice of weights in `(2.6)` and Huxley's coefficient/Jutila-break
calculation `(4.1)--(5.8)`. -/
def Huxley1972MontgomeryClassIEquation58 : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ Real.exp (Real.exp 1) ≤ T₀ ∧ 480 ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      correctedEquation610Constant *
          Real.log (Real.log T) / Real.log T < 1 - sigma →
      ∃ Y ell : ℝ, ∃ U N : ℕ,
        15 / 2 < Y ∧
        1 ≤ U ∧ U ≤ N ∧
        (U + 1 : ℝ) ≤ 2 * Y ∧ Y ≤ T ^ 2 ∧
        100 * Y * Real.log T ≤ (N + 1 : ℕ) ∧
        0 < ell ∧
        (huxleyOccupiedDyadicBlocks U N Y).card ≤ ⌊2 * ell⌋₊ ∧
        Real.sqrt U * Real.rpow T (13 / 80 : ℝ) ≤
          Real.rpow Y (sigma - 1 / 2) ∧
        ((huxleyClassISet sigma T Y ell U N).card : ℝ) ≤
          C *
            (Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 22 +
              Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 45 +
              Real.rpow T (equation58ThirdExponent sigma) *
                  Real.rpow (Real.log T) 76)

/-- The canonical Huxley terminal surface has exactly two analytic fields:
the literal class-I estimate and Haneke's quoted critical-line estimate.
Classifier geometry, exceptional zeros, and class-II elimination are theorems
below these fields. -/
structure Huxley1972CorrectedTerminalMinimalSourceData where
  classIEquation58 : Huxley1972MontgomeryClassIEquation58
  hanekeEquation67 : Huxley1972HanekeEquation67

/-- A source-faithful bundle below the final density theorem.

The remaining analytic fields correspond respectively to:

* pp.166--167, the (3.12)/(3.13) classification and (3.15) cover;
* pp.168--169, (4.7) through the three-term class-I estimate (5.8);
* Haneke's exact zeta bound quoted at p.169, (6.7);
* the (3.13)/(6.8) contradiction and the choice (6.9), which eliminate class
  II from that bound.

The (3.9) exceptional count is no longer an analytic field: the exceptional
piece is required to be the literal set `|gamma| < 100 log T`, and its
`700000 (log T)^2` bound is proved premise-free in
`PrincipalZetaHuxley1972Equation39Exceptions`.

The contour identity (3.5) is premise-free in
`huxleyEquation35_full_identity`: its arithmetic coefficient is identified
with Huxley's divisor sum (3.4), and the sole crossed zeta-pole residue is
retained explicitly.

The Gamma-shell normalization (3.14) is likewise no longer an analytic
field: `exists_equation314_gamma_shell_normalizer` supplies an explicit
positive `c₂`, pointwise bounds for the central and every dyadic block, and
the literal `2*pi/3` summability budget.

The terminal numerical inequality (3.15) is proved in
`equation315_realPart_gt_oneThird`; once the analytic identity supplies that
lower bound, `equation315_nonzero_of_realPart_lowerBound` gives the claimed
contradiction to `rho` being a zero.

The zero-free alternative with the factor-100 repaired constant is proved
above from the already-shared Appendix-B source rather than retained here as
another analytic field.

The first genuinely deep inputs are visible in these fields; none is a renamed
version of (1.9). -/
structure Huxley1972CorrectedTerminalSourceData where
  counts : ℝ → ℝ → TerminalCounts
  CclassI : ℝ
  T₀ : ℝ
  CclassI_pos : 0 < CclassI
  T₀_large : Real.exp (Real.exp 1) ≤ T₀
  equation39_exceptional_exact :
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      (counts T sigma).exceptional =
        (equation39ExceptionalSet sigma T).card
  equations3915_classification :
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      (zeroSupport chiOne sigma T).card ≤
        (counts T sigma).exceptional +
          (counts T sigma).classI + (counts T sigma).classII
  equation58_classI_bound :
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      correctedEquation610Constant *
          Real.log (Real.log T) / Real.log T < 1 - sigma →
      ((counts T sigma).classI : ℝ) ≤
        CclassI *
          (Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 22 +
            Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 45 +
            Real.rpow T (equation58ThirdExponent sigma) *
                Real.rpow (Real.log T) 76)
  hanekeEquation67 : Huxley1972HanekeEquation67
  equations313_68_classII_elimination_from_haneke :
    Huxley1972HanekeEquation67 →
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      correctedEquation610Constant *
          Real.log (Real.log T) / Real.log T < 1 - sigma →
      (counts T sigma).classII = 0

/-- Backward-compatible name for the former broad source surface.  It is kept
only for downstream comparison; the live endpoint no longer consumes it. -/
def Huxley1972CorrectedTerminalLegacyAnalyticLeaves : Prop :=
  Nonempty Huxley1972CorrectedTerminalSourceData

/-- Proposition-valued canonical endpoint surface.  Only the literal
class-I Huxley--Montgomery estimate and Haneke `(6.7)` remain external. -/
def Huxley1972CorrectedTerminalAnalyticLeaves : Prop :=
  Nonempty Huxley1972CorrectedTerminalMinimalSourceData

/-- The corrected analogue of the classified ledger.  It differs from the
legacy source surface only in the factor-100 repair to (6.10). -/
def Huxley1972CorrectedTerminalClassifiedLedger : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ Real.exp (Real.exp 1) ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      ((1 - sigma ≤ correctedEquation610Constant *
          Real.log (Real.log T) / Real.log T) ∧
        (zeroSupport chiOne sigma T).card = 0) ∨
        (correctedEquation610Constant *
            Real.log (Real.log T) / Real.log T < 1 - sigma ∧
          ∃ Zexception ZI ZII : ℕ,
            (zeroSupport chiOne sigma T).card ≤ Zexception + ZI + ZII ∧
            (Zexception : ℝ) ≤
              C * Real.rpow (Real.log T) 2 ∧
            (ZI : ℝ) ≤
              C * (Real.rpow T (huxleyDensityExponent sigma) *
                    Real.rpow (Real.log T) 22 +
                  Real.rpow T (huxleyDensityExponent sigma) *
                    Real.rpow (Real.log T) 45 +
                  Real.rpow T (equation58ThirdExponent sigma) *
                    Real.rpow (Real.log T) 76) ∧
            ZII = 0)

/-- The line-by-line source bundle gives the corrected classified ledger from
exactly the principal zero-free alternative it consumes. -/
theorem correctedClassifiedLedger_of_sourceData_of_zeroFree
    (hZeroFree : Huxley1972CorrectedEquation610ZeroFree)
    (h : Huxley1972CorrectedTerminalSourceData) :
    Huxley1972CorrectedTerminalClassifiedLedger := by
  obtain ⟨Tzero, hTzeroLarge, hzeroFree⟩ :=
    hZeroFree
  obtain ⟨Texc, hexc⟩ := Filter.eventually_atTop.1
    eventually_equation39ExceptionalSet_card_le_log_sq
  let C := max 700000 h.CclassI
  let Tstart := max h.T₀ (max Tzero Texc)
  refine ⟨C, Tstart, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 700000)
      (le_max_left _ _)
  · exact h.T₀_large.trans (le_max_left _ _)
  intro T sigma hT hsigmaLow hsigmaHigh
  have hTsource : h.T₀ ≤ T := (le_max_left _ _).trans hT
  have hTinner : max Tzero Texc ≤ T :=
    (le_max_right h.T₀ (max Tzero Texc)).trans hT
  have hTzero : Tzero ≤ T :=
    (le_max_left Tzero Texc).trans hTinner
  have hTexc : Texc ≤ T :=
    (le_max_right Tzero Texc).trans hTinner
  by_cases hzero :
      1 - sigma ≤ correctedEquation610Constant *
        Real.log (Real.log T) / Real.log T
  · exact Or.inl ⟨hzero,
      hzeroFree T sigma hTzero hsigmaLow hsigmaHigh hzero⟩
  · have hgap : correctedEquation610Constant *
        Real.log (Real.log T) / Real.log T < 1 - sigma :=
      lt_of_not_ge hzero
    refine Or.inr ⟨hgap,
      (h.counts T sigma).exceptional,
      (h.counts T sigma).classI,
      (h.counts T sigma).classII, ?_, ?_, ?_, ?_⟩
    · exact h.equations3915_classification T sigma hTsource hsigmaLow hsigmaHigh
    · rw [h.equation39_exceptional_exact T sigma hTsource
        hsigmaLow hsigmaHigh]
      have hraw := hexc T hTexc sigma
        ((by norm_num : (0 : ℝ) ≤ 279 / 280).trans hsigmaLow)
      have hlogNonneg : 0 ≤ Real.log T := by
        have hTlarge := h.T₀_large.trans hTsource
        have hTone : 1 ≤ T := by
          exact (Real.one_le_exp (Real.exp_pos 1).le).trans hTlarge
        exact Real.log_nonneg hTone
      exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hlogNonneg _))
    · have hTlarge := h.T₀_large.trans hTsource
      have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hTlarge
      have hlogPos : 0 < Real.log T := by
        have : Real.exp 1 ≤ Real.log T := by
          calc
            Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
            _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hTlarge
        exact (Real.exp_pos 1).trans_le this
      have hfirst : 0 ≤
          Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 22 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      have hsecond : 0 ≤
          Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 45 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      have hthird : 0 ≤
          Real.rpow T (equation58ThirdExponent sigma) *
            Real.rpow (Real.log T) 76 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      exact (h.equation58_classI_bound T sigma hTsource hsigmaLow hsigmaHigh hgap).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (add_nonneg (add_nonneg hfirst hsecond) hthird))
    · exact h.equations313_68_classII_elimination_from_haneke
        h.hanekeEquation67 T sigma hTsource hsigmaLow hsigmaHigh hgap

/-- Minimal two-source construction of the corrected classified ledger.
The literal pointwise classifier and its finite cover are invoked internally;
Haneke is globalized and eliminates the exact class-II filter internally. -/
theorem correctedClassifiedLedger_of_minimalSourceData_of_zeroFree
    (hZeroFree : Huxley1972CorrectedEquation610ZeroFree)
    (h : Huxley1972CorrectedTerminalMinimalSourceData) :
    Huxley1972CorrectedTerminalClassifiedLedger := by
  classical
  obtain ⟨Tzero, hTzeroLarge, hzeroFree⟩ := hZeroFree
  obtain ⟨CclassI, TclassI, hCclassI, hTclassILarge,
      hTclassI480, hclassI⟩ := h.classIEquation58
  obtain ⟨Thaneke, hThanekeTwo, hhaneke⟩ :=
    hanekeEquation67_global_scaled h.hanekeEquation67
      (show 0 < shiftedEquation314Normalizer / 2 by
        exact div_pos shiftedEquation314Normalizer_pos (by norm_num))
  obtain ⟨Texc, hexc⟩ := Filter.eventually_atTop.1
    eventually_equation39ExceptionalSet_card_le_log_sq
  let C := max 700000 CclassI
  let Tstart := max TclassI (max Tzero (max Thaneke Texc))
  refine ⟨C, Tstart, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 700000)
      (le_max_left _ _)
  · exact hTclassILarge.trans (le_max_left _ _)
  intro T sigma hT hsigmaLow hsigmaHigh
  have hTclass : TclassI ≤ T := (le_max_left _ _).trans hT
  have hTinner : max Tzero (max Thaneke Texc) ≤ T :=
    (le_max_right TclassI _).trans hT
  have hTzero : Tzero ≤ T := (le_max_left _ _).trans hTinner
  have hTdeep : max Thaneke Texc ≤ T := (le_max_right _ _).trans hTinner
  have hThaneke : Thaneke ≤ T := (le_max_left _ _).trans hTdeep
  have hTexc : Texc ≤ T := (le_max_right _ _).trans hTdeep
  by_cases hzero :
      1 - sigma ≤ correctedEquation610Constant *
        Real.log (Real.log T) / Real.log T
  · exact Or.inl ⟨hzero,
      hzeroFree T sigma hTzero hsigmaLow hsigmaHigh hzero⟩
  · have hgap : correctedEquation610Constant *
        Real.log (Real.log T) / Real.log T < 1 - sigma :=
      lt_of_not_ge hzero
    obtain ⟨Y, ell, U, N, hY, hU, hUN, hUY, hYT, hcut,
      hell, hblocks, hscale, hIbound⟩ :=
      hclassI T sigma hTclass hsigmaLow hsigmaHigh hgap
    have hcover := zeroSupport_card_le_exceptional_add_literalClasses
      (T := T) (sigma := sigma) (Y := Y) (ell := ell) (U := U) (N := N)
      (hTclassI480.trans hTclass) hsigmaLow hY hU hUN
      hUY hYT hcut hell hblocks
    have hIIzero : (huxleyClassIISet sigma T Y U).card = 0 := by
      rw [Finset.card_eq_zero]
      unfold huxleyClassIISet
      rw [Finset.filter_eq_empty_iff]
      intro rho hrho hII
      have hrect : rho ∈ zeroRectangle sigma T :=
        (zeroDivisor chiOne sigma T).supportWithinDomain
          ((zeroSupport_mem_iff chiOne sigma T rho).mp hrho)
      have him := (Complex.mem_reProdIm.mp hrect).2
      have hgamma : |rho.im| ≤ T := abs_le.mpr ⟨him.1, him.2⟩
      exact not_huxleyClassII_of_globalHaneke_and_scale
        (hThanekeTwo.trans hThaneke) (by linarith : 0 ≤ Y) hgamma hscale
        (fun D t hD ht => hhaneke T D t hThaneke hD ht) hII
    refine Or.inr ⟨hgap,
      (equation39ExceptionalSet sigma T).card,
      (huxleyClassISet sigma T Y ell U N).card,
      (huxleyClassIISet sigma T Y U).card,
      hcover, ?_, ?_, hIIzero⟩
    · have hraw := hexc T hTexc sigma
        ((by norm_num : (0 : ℝ) ≤ 279 / 280).trans hsigmaLow)
      have hlogNonneg : 0 ≤ Real.log T := by
        have hTone : 1 ≤ T := by
          exact (show (1 : ℝ) ≤ 480 by norm_num) |>.trans
            (hTclassI480.trans hTclass)
        exact Real.log_nonneg hTone
      exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hlogNonneg _))
    · have hTpos : 0 < T := by
        exact (show (0 : ℝ) < 480 by norm_num) |>.trans_le
          (hTclassI480.trans hTclass)
      have hlogPos : 0 < Real.log T := Real.log_pos
        ((show (1 : ℝ) < 480 by norm_num) |>.trans_le
          (hTclassI480.trans hTclass))
      have hfirst : 0 ≤
          Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 22 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      have hsecond : 0 ≤
          Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 45 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      have hthird : 0 ≤
          Real.rpow T (equation58ThirdExponent sigma) *
            Real.rpow (Real.log T) 76 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      exact hIbound.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (add_nonneg (add_nonneg hfirst hsecond) hthird))

/-- Backward-compatible Appendix-B constructor. -/
theorem correctedClassifiedLedger_of_sourceData
    (hKhale : AppendixBCorollary104)
    (h : Huxley1972CorrectedTerminalSourceData) :
    Huxley1972CorrectedTerminalClassifiedLedger :=
  correctedClassifiedLedger_of_sourceData_of_zeroFree
    (correctedEquation610ZeroFree_of_appendixB hKhale) h

/-- Canonical Appendix-B constructor on the minimal two-source surface. -/
theorem correctedClassifiedLedger_of_minimalSourceData
    (hKhale : AppendixBCorollary104)
    (h : Huxley1972CorrectedTerminalMinimalSourceData) :
    Huxley1972CorrectedTerminalClassifiedLedger :=
  correctedClassifiedLedger_of_minimalSourceData_of_zeroFree
    (correctedEquation610ZeroFree_of_appendixB hKhale) h

/-- On the relevant startup range the corrected threshold is nonnegative. -/
theorem corrected_threshold_nonneg
    {T : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) :
    0 ≤ Real.log (Real.log T) / Real.log T := by
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT
  have hlogPos : 0 < Real.log T := (Real.exp_pos 1).trans_le hlogLower
  have hloglogNonneg : 0 ≤ Real.log (Real.log T) :=
    Real.log_nonneg ((Real.one_le_exp zero_le_one).trans hlogLower)
  exact div_nonneg hloglogNonneg hlogPos.le

/-- Aggregate the corrected exceptional/class-I/class-II ledger into the
source-faithful `22,45,76` three-term dichotomy.  This replaces the invalid
conversion through Huxley's printed `22,44,75` ledger. -/
theorem correctedThreeTermDichotomyLog45_of_corrected
    (h : Huxley1972CorrectedTerminalClassifiedLedger) :
    Huxley1972CorrectedTerminalThreeTermDichotomyLog45 := by
  obtain ⟨C, T₀, hC, hT₀, h⟩ := h
  refine ⟨2 * C, T₀, by positivity, hT₀, ?_⟩
  intro T sigma hT hsigmaLow hsigmaHigh
  rcases h T sigma hT hsigmaLow hsigmaHigh with hzero | hclassified
  · exact Or.inl hzero.2
  · refine Or.inr ⟨?_, ?_⟩
    · simpa [
        correctedEquation610ConstantLog45,
        correctedEquation610Constant] using hclassified.1.le
    · obtain ⟨Zexception, ZI, ZII, hcover, hException, hI, hII⟩ :=
        hclassified.2
      subst ZII
      simp only [add_zero] at hcover
      have hTlarge : Real.exp (Real.exp 1) ≤ T := hT₀.trans hT
      let S : ℝ :=
        Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 22 +
          Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 45 +
          Real.rpow T (equation58ThirdExponent sigma) *
            Real.rpow (Real.log T) 76
      have hfirst := equation39_exceptionalTerm_le_equation58_firstTerm
        hTlarge hsigmaLow hsigmaHigh
      have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hTlarge
      have hlogPos : 0 < Real.log T := by
        have : Real.exp 1 ≤ Real.log T := by
          calc
            Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by
              rw [Real.log_exp]
            _ ≤ Real.log T :=
              Real.log_le_log (Real.exp_pos (Real.exp 1)) hTlarge
        exact (Real.exp_pos 1).trans_le this
      have hsecond0 : 0 ≤
          Real.rpow T (huxleyDensityExponent sigma) *
            Real.rpow (Real.log T) 45 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      have hthird0 : 0 ≤
          Real.rpow T (equation58ThirdExponent sigma) *
            Real.rpow (Real.log T) 76 :=
        mul_nonneg (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hlogPos.le _)
      have hfirstS : Real.rpow (Real.log T) 2 ≤ S := by
        dsimp [S]
        calc
          Real.rpow (Real.log T) 2 ≤
              Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 22 := hfirst
          _ ≤ Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 22 +
              Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 45 :=
            le_add_of_nonneg_right hsecond0
          _ ≤ (Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 22 +
                Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 45) +
              Real.rpow T (equation58ThirdExponent sigma) *
                Real.rpow (Real.log T) 76 :=
            le_add_of_nonneg_right hthird0
      have hExceptionS : (Zexception : ℝ) ≤ C * S :=
        hException.trans (mul_le_mul_of_nonneg_left hfirstS hC.le)
      have hIS : (ZI : ℝ) ≤ C * S := by simpa [S] using hI
      have hcoverReal :
          ((zeroSupport chiOne sigma T).card : ℝ) ≤
            (Zexception : ℝ) + (ZI : ℝ) := by
        exact_mod_cast hcover
      calc
        ((zeroSupport chiOne sigma T).card : ℝ) ≤
            (Zexception : ℝ) + (ZI : ℝ) := hcoverReal
        _ ≤ C * S + C * S := add_le_add hExceptionS hIS
        _ = (2 * C) *
            (Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 22 +
                Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 45 +
                Real.rpow T (equation58ThirdExponent sigma) *
                  Real.rpow (Real.log T) 76) := by
          dsimp [S]
          ring

/-- Complete corrected source-to-principal-collar weld, ending at the honest
fixed loss `P=45`. -/
theorem principalSelectedP53_of_correctedSourceData_of_zeroFree
    (hZeroFree : Huxley1972CorrectedEquation610ZeroFree)
    (h : Huxley1972CorrectedTerminalSourceData) :
    JutilaGappedSelectedPrincipalP53Eventually :=
  principalSelectedP53_of_correctedThreeTermDichotomyLog45
      (correctedThreeTermDichotomyLog45_of_corrected
        (correctedClassifiedLedger_of_sourceData_of_zeroFree hZeroFree h))

theorem principalSelectedP53_of_correctedSourceData
    (hKhale : AppendixBCorollary104)
    (h : Huxley1972CorrectedTerminalSourceData) :
    JutilaGappedSelectedPrincipalP53Eventually :=
  principalSelectedP53_of_correctedThreeTermDichotomyLog45
      (correctedThreeTermDichotomyLog45_of_corrected
        (correctedClassifiedLedger_of_sourceData hKhale h))

/-- Complete minimal-source to principal-collar weld. -/
theorem principalSelectedP53_of_correctedMinimalSourceData_of_zeroFree
    (hZeroFree : Huxley1972CorrectedEquation610ZeroFree)
    (h : Huxley1972CorrectedTerminalMinimalSourceData) :
    JutilaGappedSelectedPrincipalP53Eventually :=
  principalSelectedP53_of_correctedThreeTermDichotomyLog45
      (correctedThreeTermDichotomyLog45_of_corrected
        (correctedClassifiedLedger_of_minimalSourceData_of_zeroFree
          hZeroFree h))

theorem principalSelectedP53_of_correctedMinimalSourceData
    (hKhale : AppendixBCorollary104)
    (h : Huxley1972CorrectedTerminalMinimalSourceData) :
    JutilaGappedSelectedPrincipalP53Eventually :=
  principalSelectedP53_of_correctedThreeTermDichotomyLog45
      (correctedThreeTermDichotomyLog45_of_corrected
        (correctedClassifiedLedger_of_minimalSourceData hKhale h))

/-- Proposition-valued endpoint adapter. -/
theorem principalSelectedP53_of_correctedAnalyticLeaves_of_zeroFree
    (hZeroFree : Huxley1972CorrectedEquation610ZeroFree)
    (h : Huxley1972CorrectedTerminalAnalyticLeaves) :
    JutilaGappedSelectedPrincipalP53Eventually := by
  obtain ⟨hsource⟩ := h
  exact principalSelectedP53_of_correctedMinimalSourceData_of_zeroFree
    hZeroFree hsource

theorem principalSelectedP53_of_correctedAnalyticLeaves
    (hKhale : AppendixBCorollary104)
    (h : Huxley1972CorrectedTerminalAnalyticLeaves) :
    JutilaGappedSelectedPrincipalP53Eventually := by
  obtain ⟨hsource⟩ := h
  exact principalSelectedP53_of_correctedMinimalSourceData hKhale hsource

end

end MAPPrincipalZetaHuxley1972CorrectedTerminalSource

#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.printed_equation610_complement_does_not_force_threeHundred
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.corrected_equation610_complement_forces_threeHundred
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.correctedEquation610ZeroFree_of_appendixB
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.hanekeEquation67_powerSaving
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.hanekeEquation67_global_scaled
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.not_huxleyClassII_of_globalHaneke_and_scale
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.equation313_contradiction_of_haneke_scale
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.correctedClassifiedLedger_of_sourceData
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.correctedClassifiedLedger_of_sourceData_of_zeroFree
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.correctedClassifiedLedger_of_minimalSourceData_of_zeroFree
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.correctedThreeTermDichotomyLog45_of_corrected
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.principalSelectedP53_of_correctedAnalyticLeaves
#print axioms MAPPrincipalZetaHuxley1972CorrectedTerminalSource.principalSelectedP53_of_correctedAnalyticLeaves_of_zeroFree
