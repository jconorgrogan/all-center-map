import PrincipalZetaHuxley1972Theorem19Adapter

/-!
# Huxley 1972 terminal-collar proof reduction below equation (1.9)

This module descends below Huxley's final zero-density statement.  On printed
p.169, equation (5.8) gives three distinct class-(i) terms.  For
`alpha >= 9/11`, equations (6.6)--(6.9) eliminate class (ii), while (6.10)
splits off the zero-free extreme.  The last term of (5.8) carries `log^75`;
outside the zero-free extreme its strict power saving absorbs the extra
`log^31`, leaving the published `log^44`.

The proofs below certify that complete exponent and logarithm arithmetic.
They do not assert Huxley's analytic class-(i) estimate, Haneke's zeta bound,
or the classical zero-free region.  The exact remaining source surface is
therefore the terminal dichotomy `Huxley1972TerminalThreeTermDichotomy`, whose
nonzero branch is visibly the three-term (5.8) bound rather than a renaming of
equation (1.9).
-/

namespace MAPPrincipalZetaHuxley1972TerminalProofReduction

open DirichletZeros
open MAPHuxleyCompactGapExponent
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPJutilaCollarMeshCutoff MAPJutilaCollarA5Budget
open MAPJutilaGappedCollarFiniteAggregation

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- The third power of `T` in Huxley 1972, equation (5.8). -/
def equation58ThirdExponent (sigma : ℝ) : ℝ :=
  4 * (1 - sigma) / (5 * sigma - 2)

/-- Huxley's choice of `Y` in equation (6.6), recorded as its `T` exponent. -/
def equation66YExponent (sigma : ℝ) : ℝ :=
  3 / (12 * sigma - 4)

/-- Huxley's choice of `X` after equation (6.8), as printed in (6.9). -/
def equation69XExponent (sigma : ℝ) : ℝ :=
  (21 * sigma - 17) / (120 * sigma - 40)

/-- Substituting the `Y` choice (6.6) into the first term of (5.8) gives
exactly the target exponent in (1.9). -/
theorem equation66_firstTerm_exponent_eq
    {sigma : ℝ} (hsigma : 279 / 280 ≤ sigma) :
    equation66YExponent sigma * (4 * (1 - sigma)) =
      huxleyDensityExponent sigma := by
  have hden : 3 * sigma - 1 ≠ 0 := by
    have : 0 < 3 * sigma - 1 := by linarith
    exact this.ne'
  unfold equation66YExponent huxleyDensityExponent
  rw [show 12 * sigma - 4 = 4 * (3 * sigma - 1) by ring]
  field_simp [hden]

/-- Equations (6.6) and (6.8) solve to the printed exponent (6.9). -/
theorem equation68_solves_to_equation69
    {sigma : ℝ} (hsigma : 279 / 280 ≤ sigma) :
    -(13 / 40 : ℝ) + equation66YExponent sigma * (2 * sigma - 1) =
      equation69XExponent sigma := by
  have hden : 3 * sigma - 1 ≠ 0 := by
    have : 0 < 3 * sigma - 1 := by linarith
    exact this.ne'
  have hden12 : 12 * sigma - 4 ≠ 0 := by
    nlinarith
  have hden120 : 120 * sigma - 40 ≠ 0 := by
    nlinarith
  unfold equation66YExponent equation69XExponent
  rw [show 12 * sigma - 4 = 4 * (3 * sigma - 1) by ring,
    show 120 * sigma - 40 = 40 * (3 * sigma - 1) by ring]
  field_simp [hden]
  ring

/-- Exact power gap between the middle and third terms of (5.8). -/
theorem target_sub_equation58ThirdExponent_eq
    {sigma : ℝ} (hsigma : 279 / 280 ≤ sigma) :
    huxleyDensityExponent sigma - equation58ThirdExponent sigma =
      (1 - sigma) * (3 * sigma - 2) /
        ((3 * sigma - 1) * (5 * sigma - 2)) := by
  have hden3 : 3 * sigma - 1 ≠ 0 := by
    have : 0 < 3 * sigma - 1 := by linarith
    exact this.ne'
  have hden5 : 5 * sigma - 2 ≠ 0 := by
    have : 0 < 5 * sigma - 2 := by linarith
    exact this.ne'
  unfold huxleyDensityExponent equation58ThirdExponent
  rw [show 3 * (1 - sigma) / (3 * sigma - 1) =
      (1 - sigma) * (3 / (3 * sigma - 1)) by ring,
    show 4 * (1 - sigma) / (5 * sigma - 2) =
      (1 - sigma) * (4 / (5 * sigma - 2)) by ring,
    ← mul_sub,
    div_sub_div 3 4 hden3 hden5]
  ring

/-- On the terminal collar, at least one seventh of the distance to one is
available to absorb the excess logarithmic power in the third term. -/
theorem one_sub_div_seven_le_power_gap
    {sigma : ℝ} (hsigmaLow : 279 / 280 ≤ sigma)
    (hsigmaHigh : sigma ≤ 1) :
    (1 - sigma) / 7 ≤
      huxleyDensityExponent sigma - equation58ThirdExponent sigma := by
  rw [target_sub_equation58ThirdExponent_eq hsigmaLow]
  have hd : 0 ≤ 1 - sigma := by linarith
  have hn : 0 ≤ 3 * sigma - 2 := by linarith
  have hden3 : 0 < 3 * sigma - 1 := by linarith
  have hden5 : 0 < 5 * sigma - 2 := by linarith
  have hdenUpper : (3 * sigma - 1) * (5 * sigma - 2) ≤ 6 := by
    nlinarith
  have hnumLower : (6 / 7 : ℝ) ≤ 3 * sigma - 2 := by
    linarith
  have hratio : (1 / 7 : ℝ) ≤
      (3 * sigma - 2) / ((3 * sigma - 1) * (5 * sigma - 2)) := by
    apply (le_div_iff₀ (mul_pos hden3 hden5)).2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hratio hd
  convert hmul using 1 <;> ring

/-- Outside Huxley's zero-free alternative (6.10), the third term's power
gap absorbs exactly the extra `log^31` between `log^75` and `log^44`. -/
theorem log31_le_power_gap_of_equation610_complement
    {T sigma : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hsigmaLow : 279 / 280 ≤ sigma) (hsigmaHigh : sigma ≤ 1)
    (hnotZeroFree :
      32400 * Real.log (Real.log T) / Real.log T ≤ 1 - sigma) :
    Real.rpow (Real.log T) 31 ≤
      Real.rpow T
        (huxleyDensityExponent sigma - equation58ThirdExponent sigma) := by
  have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by
        rw [Real.log_exp]
      _ ≤ Real.log T :=
        Real.log_le_log (Real.exp_pos (Real.exp 1)) hT
  have hlogPos : 0 < Real.log T :=
    (Real.exp_pos 1).trans_le hlogLower
  have hloglogNonneg : 0 ≤ Real.log (Real.log T) :=
    Real.log_nonneg ((Real.one_le_exp zero_le_one).trans hlogLower)
  have hgap := one_sub_div_seven_le_power_gap hsigmaLow hsigmaHigh
  have hcross :
      32400 * Real.log (Real.log T) ≤
        (1 - sigma) * Real.log T := by
    exact (div_le_iff₀ hlogPos).mp hnotZeroFree
  have htrade :
      31 * Real.log (Real.log T) ≤
        Real.log T *
          (huxleyDensityExponent sigma - equation58ThirdExponent sigma) := by
    have hmul := mul_le_mul_of_nonneg_right hgap hlogPos.le
    nlinarith
  change (Real.log T) ^ (31 : ℝ) ≤
    T ^ (huxleyDensityExponent sigma - equation58ThirdExponent sigma)
  rw [Real.rpow_def_of_pos hlogPos, Real.rpow_def_of_pos hTpos]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The literal third term of (5.8) is bounded by the middle term outside
the (6.10) zero-free extreme. -/
theorem equation58_thirdTerm_le_target
    {T sigma : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hsigmaLow : 279 / 280 ≤ sigma) (hsigmaHigh : sigma ≤ 1)
    (hnotZeroFree :
      32400 * Real.log (Real.log T) / Real.log T ≤ 1 - sigma) :
    Real.rpow T (equation58ThirdExponent sigma) *
        Real.rpow (Real.log T) 75 ≤
      Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 44 := by
  have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by
        rw [Real.log_exp]
      _ ≤ Real.log T :=
        Real.log_le_log (Real.exp_pos (Real.exp 1)) hT
  have hlogPos : 0 < Real.log T :=
    (Real.exp_pos 1).trans_le hlogLower
  have h31 := log31_le_power_gap_of_equation610_complement
    hT hsigmaLow hsigmaHigh hnotZeroFree
  have hTthird0 : 0 ≤ Real.rpow T (equation58ThirdExponent sigma) :=
    Real.rpow_nonneg hTpos.le _
  have hlog44zero : 0 ≤ Real.rpow (Real.log T) 44 :=
    Real.rpow_nonneg hlogPos.le _
  have hlogsplit :
      Real.rpow (Real.log T) 75 =
        Real.rpow (Real.log T) 31 * Real.rpow (Real.log T) 44 := by
    change (Real.log T) ^ (75 : ℝ) =
      (Real.log T) ^ (31 : ℝ) * (Real.log T) ^ (44 : ℝ)
    calc
      (Real.log T) ^ (75 : ℝ) =
          (Real.log T) ^ ((31 : ℝ) + 44) := by norm_num
      _ = (Real.log T) ^ (31 : ℝ) * (Real.log T) ^ (44 : ℝ) :=
        Real.rpow_add hlogPos 31 44
  calc
    Real.rpow T (equation58ThirdExponent sigma) *
        Real.rpow (Real.log T) 75 =
      (Real.rpow T (equation58ThirdExponent sigma) *
          Real.rpow (Real.log T) 31) *
        Real.rpow (Real.log T) 44 := by
          rw [hlogsplit]
          ring
    _ ≤ (Real.rpow T (equation58ThirdExponent sigma) *
          Real.rpow T
            (huxleyDensityExponent sigma - equation58ThirdExponent sigma)) *
        Real.rpow (Real.log T) 44 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h31 hTthird0) hlog44zero
    _ = Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 44 := by
      congr 1
      calc
        Real.rpow T (equation58ThirdExponent sigma) *
            Real.rpow T
              (huxleyDensityExponent sigma - equation58ThirdExponent sigma) =
          Real.rpow T
            (equation58ThirdExponent sigma +
              (huxleyDensityExponent sigma - equation58ThirdExponent sigma)) :=
          (Real.rpow_add hTpos _ _).symm
        _ = Real.rpow T (huxleyDensityExponent sigma) := by
          congr 1
          ring

/-- The first term of (5.8), after the `Y` substitution (6.6), has the
target `T` exponent and only `log^22`, hence is smaller than the middle
`log^44` term. -/
theorem equation58_firstTerm_le_target
    {T sigma : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T) :
    Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 22 ≤
      Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 44 := by
  have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by
        rw [Real.log_exp]
      _ ≤ Real.log T :=
        Real.log_le_log (Real.exp_pos (Real.exp 1)) hT
  have hlogOne : 1 ≤ Real.log T :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hlogLower
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num))
    (Real.rpow_nonneg hTpos.le _)

/-- Pure deterministic closure of Huxley's three terms (5.8) on the
non-zero-free terminal branch. -/
theorem equation58_threeTerms_le_three_target
    {T sigma : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hsigmaLow : 279 / 280 ≤ sigma) (hsigmaHigh : sigma ≤ 1)
    (hnotZeroFree :
      32400 * Real.log (Real.log T) / Real.log T ≤ 1 - sigma) :
    Real.rpow T (huxleyDensityExponent sigma) *
          Real.rpow (Real.log T) 22 +
        Real.rpow T (huxleyDensityExponent sigma) *
          Real.rpow (Real.log T) 44 +
        Real.rpow T (equation58ThirdExponent sigma) *
          Real.rpow (Real.log T) 75 ≤
      3 * (Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 44) := by
  have hfirst := equation58_firstTerm_le_target
    (sigma := sigma) hT
  have hthird := equation58_thirdTerm_le_target
    hT hsigmaLow hsigmaHigh hnotZeroFree
  linarith

/-- The exact source-facing terminal split below Huxley (1.9).

The zero branch is the classical zero-free conclusion invoked after (6.10).
The other branch retains both the complement of (6.10) and the literal
three powers/logarithmic losses of (5.8), after the substitutions (6.6)--
(6.9) and elimination of class (ii) by (6.7)--(6.8). -/
def Huxley1972TerminalThreeTermDichotomy : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ Real.exp (Real.exp 1) ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      (zeroSupport chiOne sigma T).card = 0 ∨
        (32400 * Real.log (Real.log T) / Real.log T ≤ 1 - sigma ∧
          ((zeroSupport chiOne sigma T).card : ℝ) ≤
            C * (Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 22 +
                Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 44 +
                Real.rpow T (equation58ThirdExponent sigma) *
                  Real.rpow (Real.log T) 75))

/-- The distinct-zero counting ledger immediately below the terminal
three-term dichotomy.

The three natural-number witnesses retain the three pieces of Huxley's
printed proof: the `O(log^2 T)` exceptions to (3.9), the class-(i) zeros
bounded by (5.8), and the class-(ii) zeros eliminated by (6.7)--(6.9).
The strict inequality is the literal complement of the closed zero-free
condition (6.10).  Thus this source surface does not silently fold the
classification or the exceptional zeros into the final estimate. -/
def Huxley1972TerminalClassifiedLedger : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ Real.exp (Real.exp 1) ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      ((1 - sigma ≤
          32400 * Real.log (Real.log T) / Real.log T) ∧
        (zeroSupport chiOne sigma T).card = 0) ∨
        (32400 * Real.log (Real.log T) / Real.log T < 1 - sigma ∧
          ∃ Zexception ZI ZII : ℕ,
            (zeroSupport chiOne sigma T).card ≤ Zexception + ZI + ZII ∧
            (Zexception : ℝ) ≤
              C * Real.rpow (Real.log T) 2 ∧
            (ZI : ℝ) ≤
              C * (Real.rpow T (huxleyDensityExponent sigma) *
                    Real.rpow (Real.log T) 22 +
                  Real.rpow T (huxleyDensityExponent sigma) *
                    Real.rpow (Real.log T) 44 +
                  Real.rpow T (equation58ThirdExponent sigma) *
                    Real.rpow (Real.log T) 75) ∧
            ZII = 0)

/-- The `O(log^2 T)` exceptions following (3.11) fit inside the first term
of (5.8) on the terminal range. -/
theorem equation39_exceptionalTerm_le_equation58_firstTerm
    {T sigma : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hsigmaLow : 279 / 280 ≤ sigma) (hsigmaHigh : sigma ≤ 1) :
    Real.rpow (Real.log T) 2 ≤
      Real.rpow T (huxleyDensityExponent sigma) *
        Real.rpow (Real.log T) 22 := by
  have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hT
  have hTone : 1 ≤ T :=
    (Real.one_le_exp (Real.exp_pos 1).le).trans hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by
        rw [Real.log_exp]
      _ ≤ Real.log T :=
        Real.log_le_log (Real.exp_pos (Real.exp 1)) hT
  have hlogOne : 1 ≤ Real.log T :=
    (Real.one_le_exp zero_le_one).trans hlogLower
  have hlogpow : Real.rpow (Real.log T) 2 ≤
      Real.rpow (Real.log T) 22 :=
    Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
  have hexp0 : 0 ≤ huxleyDensityExponent sigma :=
    huxleyDensityExponent_nonneg
      ((by norm_num : (4 / 5 : ℝ) ≤ 279 / 280).trans hsigmaLow)
      hsigmaHigh
  have hpowOne : 1 ≤ Real.rpow T (huxleyDensityExponent sigma) :=
    Real.one_le_rpow hTone hexp0
  have hlog22zero : 0 ≤ Real.rpow (Real.log T) 22 :=
    Real.rpow_nonneg (by linarith) _
  calc
    Real.rpow (Real.log T) 2 ≤
        Real.rpow (Real.log T) 22 := hlogpow
    _ = 1 * Real.rpow (Real.log T) 22 := by ring
    _ ≤ Real.rpow T (huxleyDensityExponent sigma) *
          Real.rpow (Real.log T) 22 :=
      mul_le_mul_of_nonneg_right hpowOne hlog22zero

/-- Deterministic aggregation of the literal exceptional/class-I/class-II
ledger into the terminal three-term source. -/
theorem terminalThreeTermDichotomy_of_classifiedLedger
    (hsource : Huxley1972TerminalClassifiedLedger) :
    Huxley1972TerminalThreeTermDichotomy := by
  obtain ⟨C, T₀, hC, hT₀, hsource⟩ := hsource
  refine ⟨2 * C, T₀, by positivity, hT₀, ?_⟩
  intro T sigma hT hsigmaLow hsigmaHigh
  rcases hsource T sigma hT hsigmaLow hsigmaHigh with hzero | hclassified
  · exact Or.inl hzero.2
  · refine Or.inr ⟨hclassified.1.le, ?_⟩
    obtain ⟨Zexception, ZI, ZII, hcover, hException, hI, hII⟩ :=
      hclassified.2
    subst ZII
    simp only [add_zero] at hcover
    have hTlarge : Real.exp (Real.exp 1) ≤ T := hT₀.trans hT
    let S : ℝ :=
      Real.rpow T (huxleyDensityExponent sigma) *
          Real.rpow (Real.log T) 22 +
        Real.rpow T (huxleyDensityExponent sigma) *
          Real.rpow (Real.log T) 44 +
        Real.rpow T (equation58ThirdExponent sigma) *
          Real.rpow (Real.log T) 75
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
          Real.rpow (Real.log T) 44 :=
      mul_nonneg (Real.rpow_nonneg hTpos.le _)
        (Real.rpow_nonneg hlogPos.le _)
    have hthird0 : 0 ≤
        Real.rpow T (equation58ThirdExponent sigma) *
          Real.rpow (Real.log T) 75 :=
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
              Real.rpow (Real.log T) 44 :=
          le_add_of_nonneg_right hsecond0
        _ ≤ (Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 22 +
              Real.rpow T (huxleyDensityExponent sigma) *
                Real.rpow (Real.log T) 44) +
            Real.rpow T (equation58ThirdExponent sigma) *
              Real.rpow (Real.log T) 75 :=
          le_add_of_nonneg_right hthird0
    have hExceptionS : (Zexception : ℝ) ≤ C * S := by
      exact hException.trans
        (mul_le_mul_of_nonneg_left hfirstS hC.le)
    have hIS : (ZI : ℝ) ≤ C * S := by
      simpa [S] using hI
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
                Real.rpow (Real.log T) 44 +
              Real.rpow T (equation58ThirdExponent sigma) *
                Real.rpow (Real.log T) 75) := by
        dsimp [S]
        ring

/-- Exact explicit-log density surface on the terminal collar.  Unlike
Huxley (1.9), it is only asked for on the range consumed by MAP. -/
def Huxley1972TerminalCollarExactLogDensity : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      ((zeroSupport chiOne sigma T).card : ℝ) ≤
        C * Real.rpow (Real.log T) 44 *
          Real.rpow T (huxleyDensityExponent sigma)

/-- The terminal three-term source yields the exact explicit-log density
surface needed by the principal collar. -/
theorem principalZetaCollarExactLogDensity_of_terminalThreeTermDichotomy
    (hsource : Huxley1972TerminalThreeTermDichotomy) :
    Huxley1972TerminalCollarExactLogDensity := by
  obtain ⟨C, T₀, hC, hT₀, hsource⟩ := hsource
  have htwoT₀ : 2 ≤ T₀ := by
    have htwoExpOne : (2 : ℝ) ≤ Real.exp 1 :=
      (show (2 : ℝ) ≤ 2.7182818283 by norm_num).trans
        Real.exp_one_gt_d9.le
    have hExpMono : Real.exp 1 ≤ Real.exp (Real.exp 1) :=
      Real.exp_le_exp.mpr (Real.one_le_exp zero_le_one)
    exact (htwoExpOne.trans hExpMono).trans hT₀
  refine ⟨3 * C, T₀, by positivity, htwoT₀, ?_⟩
  intro T sigma hT hsigmaLow hsigmaHigh
  have hTlarge : Real.exp (Real.exp 1) ≤ T := hT₀.trans hT
  have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hTlarge
  have hlogPos : 0 < Real.log T := by
    have hlogLower : Real.exp 1 ≤ Real.log T := by
      calc
        Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by
          rw [Real.log_exp]
        _ ≤ Real.log T :=
          Real.log_le_log (Real.exp_pos (Real.exp 1)) hTlarge
    exact (Real.exp_pos 1).trans_le hlogLower
  rcases hsource T sigma hT hsigmaLow hsigmaHigh with hzero | hthree
  · have hlogTNonneg : 0 ≤ Real.log T := hlogPos.le
    have hnonneg : 0 ≤
        (3 * C) * Real.rpow (Real.log T) 44 *
          Real.rpow T (huxleyDensityExponent sigma) :=
      mul_nonneg
        (mul_nonneg (by positivity)
          (Real.rpow_nonneg hlogTNonneg _))
        (Real.rpow_nonneg hTpos.le _)
    simpa [hzero] using hnonneg
  · have hcollapse := equation58_threeTerms_le_three_target
      hTlarge hsigmaLow hsigmaHigh hthree.1
    have hbound :
        ((zeroSupport chiOne sigma T).card : ℝ) ≤
          (3 * C) * Real.rpow (Real.log T) 44 *
            Real.rpow T (huxleyDensityExponent sigma) := by
      calc
        ((zeroSupport chiOne sigma T).card : ℝ) ≤
            C * (Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 22 +
                Real.rpow T (huxleyDensityExponent sigma) *
                  Real.rpow (Real.log T) 44 +
                Real.rpow T (equation58ThirdExponent sigma) *
                  Real.rpow (Real.log T) 75) := hthree.2
        _ ≤ C * (3 * (Real.rpow T (huxleyDensityExponent sigma) *
              Real.rpow (Real.log T) 44)) :=
          mul_le_mul_of_nonneg_left hcollapse hC.le
        _ = (3 * C) * Real.rpow (Real.log T) 44 *
              Real.rpow T (huxleyDensityExponent sigma) := by ring
    exact hbound

/-- The terminal-collar exact-log estimate directly inhabits the principal
selected-system leaf.  This is the exact consumer of the Huxley descent. -/
theorem principalSelectedP53_of_terminalCollarExactLogDensity
    (hsource : Huxley1972TerminalCollarExactLogDensity) :
    JutilaGappedSelectedPrincipalP53Eventually := by
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hsource
  let R₀ : ℝ := max T₀ 6
  refine ⟨C, R₀, 44, hC, le_max_right _ _, by norm_num, ?_⟩
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
  have hlog0 : 0 ≤ Real.rpow (Real.log T) (44 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg hTone) _
  calc
    (W.card : ℝ) ≤ ((zeroSupport chiOne sigma T).card : ℝ) := hcard
    _ ≤ C * Real.rpow (Real.log T) 44 *
          Real.rpow T (huxleyDensityExponent sigma) := hsourceBound
    _ ≤ C * Real.rpow (Real.log T) 44 *
          Real.rpow T
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma)) := by
      exact mul_le_mul_of_nonneg_left hpower
        (mul_nonneg hC.le hlog0)

/-- End-to-end deterministic adapter from the literal terminal dichotomy below
Huxley (1.9) to MAP's principal selected-system p.53 leaf. -/
theorem principalSelectedP53_of_terminalThreeTermDichotomy
    (hsource : Huxley1972TerminalThreeTermDichotomy) :
    JutilaGappedSelectedPrincipalP53Eventually :=
  principalSelectedP53_of_terminalCollarExactLogDensity
    (principalZetaCollarExactLogDensity_of_terminalThreeTermDichotomy hsource)

/-- Full deterministic weld from the first classified Huxley source ledger
to MAP's conductor-one selected-system leaf. -/
theorem principalSelectedP53_of_terminalClassifiedLedger
    (hsource : Huxley1972TerminalClassifiedLedger) :
    JutilaGappedSelectedPrincipalP53Eventually :=
  principalSelectedP53_of_terminalThreeTermDichotomy
    (terminalThreeTermDichotomy_of_classifiedLedger hsource)

end

end MAPPrincipalZetaHuxley1972TerminalProofReduction

#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.equation66_firstTerm_exponent_eq
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.equation68_solves_to_equation69
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.one_sub_div_seven_le_power_gap
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.log31_le_power_gap_of_equation610_complement
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.equation58_thirdTerm_le_target
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.equation58_threeTerms_le_three_target
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.equation39_exceptionalTerm_le_equation58_firstTerm
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.terminalThreeTermDichotomy_of_classifiedLedger
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.principalZetaCollarExactLogDensity_of_terminalThreeTermDichotomy
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.principalSelectedP53_of_terminalThreeTermDichotomy
#print axioms MAPPrincipalZetaHuxley1972TerminalProofReduction.principalSelectedP53_of_terminalClassifiedLedger
