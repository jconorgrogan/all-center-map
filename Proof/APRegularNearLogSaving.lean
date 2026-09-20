import APRegularNearMeshRoute
import APPrimitiveRegularLowGap
import KhaleWeakVKAbsoluteBridge
import APExceptionalUnconditional

/-!
# Source-faithful closure of the regular near-one AP zero mass

This file closes the last noncompact range in equation (2.7) from the literal
published inputs used in the paper:

* Jutila's fixed-modulus family zero-density theorem (1.7), on the closed
  source range `4/5 <= sigma <= 1`;
* the certified primitive Koukoulopoulos Theorem 12.3 collar at bounded
  ordinate; and
* Khale's sign-symmetric high-ordinate nonvanishing region.

The proof applies the source theorems at the primitive conductor.  Repetition
of a primitive inducer among ambient characters and moduli is then paid by the
explicit `Q^2` factor in `apRegularNearOneRangeMass_le_sq_mul`.  Analytic zero
multiplicity is retained throughout the relative-mesh integration.

No weighted zero-mass estimate is assumed.  Only the Jutila and Khale source
statements remain hypotheses; the bounded-height branch is premise-free.
-/

namespace MAPAPRegularNearLogSaving

open Filter Set
open scoped BigOperators
open DirichletZeros MAPFixedScaleAPZeroRoute MAPAPZeroDensityCert
open MAPAPWeightedZeroMassIntegration MAPAPRelativeMeshPrimitiveApplication
open MAPAPRegularNearMeshRoute MAPRelativeNearOneMesh27
open MAPGuthMaynard ZeroDensityArithmetic ZeroDensityInterface
open MAPAPPrimitiveRegularLowGap MAPKhaleWeakVKApplication

noncomputable section

/-- Jutila, Theorem 1, equation (1.7), with its fixed-modulus family count and
the source's uniform constant after `eta` is fixed. -/
abbrev JutilaEquation17 : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 4 / 5 ≤ sigma → sigma ≤ 1 →
          (ambientZeroCountAtLevel q sigma T : ℝ) ≤
            C * Real.rpow ((q : ℝ) * T)
              ((2 + eta) * (1 - sigma))

/-- The exact source fragment used by MAP.  The downstream proof never
queries equation (1.7) at any loss other than `eta = 1/10`; exposing this
minimal contract avoids making a full all-eta formalization an artificial
prerequisite. -/
abbrev JutilaEquation17OneTenth : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      1 ≤ T → 4 / 5 ≤ sigma → sigma ≤ 1 →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T)
            ((21 / 10) * (1 - sigma))

/-- The source-faithful asymptotic fragment actually needed by MAP.  Jutila's
detector proof is stated only once `q*T` exceeds a loss-dependent threshold;
the MAP application has `T = X^tau -> infinity`, so no artificial bounded
scale patch is needed. -/
abbrev JutilaEquation17OneTenthEventually : Prop :=
  ∃ C R₀ : ℝ, 0 < C ∧ 0 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      1 ≤ T → 4 / 5 ≤ sigma → sigma ≤ 1 →
      R₀ ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T)
            ((21 / 10) * (1 - sigma))

theorem jutilaEquation17_oneTenthEventually_of_oneTenth
    (hJutila : JutilaEquation17OneTenth) :
    JutilaEquation17OneTenthEventually := by
  obtain ⟨C, hC, hsource⟩ := hJutila
  refine ⟨C, 0, hC, le_rfl, ?_⟩
  intro q _inst T sigma hT hsigmaLow hsigmaHigh _hscale
  exact hsource q T sigma hT hsigmaLow hsigmaHigh

/-- The published all-loss formulation specializes to the sole loss used by
the MAP near-one argument. -/
theorem jutilaEquation17_oneTenth_of_full
    (hJutila : JutilaEquation17) :
    JutilaEquation17OneTenth := by
  obtain ⟨C, hC, hsource⟩ := hJutila (1 / 10) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q _inst T sigma hT hsigmaLow hsigmaHigh
  simpa only [show (2 + 1 / 10 : ℝ) = 21 / 10 by norm_num] using
    hsource q T sigma hT hsigmaLow hsigmaHigh

/-- Khale's sign-symmetric high-ordinate nonvanishing conclusion, retaining
the source's literal absolute-ordinate denominator. -/
abbrev KhaleAbsoluteNonvanishing : Prop :=
  ∀ (q : ℕ) [NeZero q] (t sigma : ℝ)
      (chi : DirichletCharacter ℂ q),
    1 ≤ q → 3 ≤ |t| →
    1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma →
      DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-! ## A premise-free cutoff for the relative mesh -/

/-- A deliberately coarse rational majorant for the geometric relative mesh.
It is strong enough to let `floor (log X)` reach every weak-VK gap. -/
theorem relativeDistance_le_twentyFour_div (L : ℕ) :
    relativeDistance L ≤ 24 / ((L : ℝ) + 24) := by
  induction L with
  | zero => norm_num [relativeDistance]
  | succ L ih =>
      rw [show relativeDistance (Nat.succ L) =
          (23 / 24 : ℝ) * relativeDistance L by
        simpa [Nat.succ_eq_add_one] using relativeDistance_succ L]
      have hden : 0 < (L : ℝ) + 24 := by positivity
      have hden' : 0 < (L : ℝ) + 25 := by positivity
      calc
        (23 / 24 : ℝ) * relativeDistance L ≤
            (23 / 24 : ℝ) * (24 / ((L : ℝ) + 24)) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 23 / ((L : ℝ) + 24) := by field_simp
        _ ≤ 24 / ((Nat.succ L : ℝ) + 24) := by
          have hfrac : 23 / ((L : ℝ) + 24) ≤
              24 / ((L : ℝ) + 25) := by
            rw [div_le_div_iff₀ hden hden']
            nlinarith
          convert hfrac using 1 <;> push_cast <;> ring

/-- The explicit logarithmic mesh depth reaches every gap
`c * (log X)^(-3/4)`.  This discharges both cutoff minimality and the bound on
the number of cells; no analytic input enters. -/
theorem eventually_relativeDistance_floor_log_le_weakGap
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop,
      relativeDistance ⌊Real.log X⌋₊ ≤
        c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) := by
  have hsmallL : ∀ᶠ L : ℝ in atTop,
      Real.rpow L (-(1 / 4 : ℝ)) ≤ c / 24 := by
    have ht := tendsto_rpow_neg_atTop
      (show 0 < (1 / 4 : ℝ) by norm_num)
    have hnhds : Set.Iio (c / 24) ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds (by positivity)
    exact (ht.eventually hnhds).mono fun _ h => h.le
  have hsmallX : ∀ᶠ X : ℝ in atTop,
      Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤ c / 24 :=
    Real.tendsto_log_atTop.eventually hsmallL
  filter_upwards [hsmallX, eventually_gt_atTop (Real.exp 1)] with X hsmall hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogOne : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hlogPos : 0 < Real.log X := zero_lt_one.trans hlogOne
  have hfloorLower : Real.log X < (⌊Real.log X⌋₊ : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (Real.log X)
  have hden : Real.log X ≤ (⌊Real.log X⌋₊ : ℝ) + 24 := by linarith
  have hinv : 1 / ((⌊Real.log X⌋₊ : ℝ) + 24) ≤
      1 / Real.log X :=
    one_div_le_one_div_of_le hlogPos hden
  have hcoarse : relativeDistance ⌊Real.log X⌋₊ ≤
      24 / Real.log X := by
    calc
      relativeDistance ⌊Real.log X⌋₊ ≤
          24 / ((⌊Real.log X⌋₊ : ℝ) + 24) :=
        relativeDistance_le_twentyFour_div _
      _ ≤ 24 / Real.log X := by
        calc
          24 / ((⌊Real.log X⌋₊ : ℝ) + 24) =
              24 * (1 / ((⌊Real.log X⌋₊ : ℝ) + 24)) := by ring
          _ ≤ 24 * (1 / Real.log X) :=
            mul_le_mul_of_nonneg_left hinv (by norm_num)
          _ = 24 / Real.log X := by ring
  have hfactor : Real.rpow (Real.log X) (-1 : ℝ) =
      Real.rpow (Real.log X) (-(3 / 4 : ℝ)) *
        Real.rpow (Real.log X) (-(1 / 4 : ℝ)) := by
    calc
      Real.rpow (Real.log X) (-1 : ℝ) =
          Real.rpow (Real.log X)
            ((-(3 / 4 : ℝ)) + (-(1 / 4 : ℝ))) := by norm_num
      _ = Real.rpow (Real.log X) (-(3 / 4 : ℝ)) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) :=
        Real.rpow_add hlogPos _ _
  have htarget : 24 / Real.log X ≤
      c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) := by
    have hnonneg : 0 ≤ Real.rpow (Real.log X) (-(3 / 4 : ℝ)) :=
      Real.rpow_nonneg hlogPos.le _
    have hmul := mul_le_mul_of_nonneg_left hsmall hnonneg
    rw [show 24 / Real.log X =
        24 * Real.rpow (Real.log X) (-1 : ℝ) by
      calc
        24 / Real.log X = 24 * (Real.log X)⁻¹ := by ring
        _ = 24 * Real.rpow (Real.log X) (-1 : ℝ) := by
          exact congrArg (fun z : ℝ => 24 * z)
            (Real.rpow_neg_one (Real.log X)).symm, hfactor]
    nlinarith
  exact hcoarse.trans htarget

/-! ## Source-to-mass closure -/

/-- Jutila, the certified Koukoulopoulos 12.3 collar, and Khale's
sign-symmetric region imply arbitrary logarithmic saving for the exact
multiplicity-weighted regular near-one mass.

The fixed reserve `u = 1/315` absorbs `Q <= (log X)^K` into the Jutila base
`qT`.  The final `Q^2` is kept outside that source bound and absorbed only
after summing the ambient character/modulus pairs. -/
theorem apRegularNearOneRangeMass_logSaving_of_oneTenth_eventual_source
    (hJutila : JutilaEquation17OneTenthEventually)
    (hKhale : KhaleAbsoluteNonvanishing) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  obtain ⟨CJ, Rsource, hCJ, hRsource, hJsource⟩ := hJutila
  obtain ⟨cPrincipal, hcPrincipal, hPrincipalGap⟩ :=
    exists_primitive_principal_regular_low_gap
  let u : ℝ := 1 / 315
  let cLow : ℝ := 1 /
    (100000000000 * (K + Real.log 8))
  let cHigh : ℝ := 1 / (18 * K + 104)
  let c : ℝ := min cLow cHigh
  have hcLow : 0 < cLow := by
    dsimp [cLow]
    have hsum : 0 < K + Real.log 8 :=
      add_pos_of_pos_of_nonneg hK (Real.log_nonneg (by norm_num))
    exact one_div_pos.mpr
      (mul_pos (by norm_num) hsum)
  have hcHigh : 0 < cHigh := by
    dsimp [cHigh]
    positivity
  have hc : 0 < c := lt_min hcLow hcHigh
  have hc_le_low : c ≤ cLow := min_le_left _ _
  have hc_le_high : c ≤ cHigh := min_le_right _ _
  have hpoly := polylog_absorption K u (by norm_num [u])
  have hmesh := eventually_relativeDistance_floor_log_le_weakGap c hc
  have hgapLow := weakGap_le_regularLowGap K hK.le
  have hprincipalWeak :=
    eventually_weakGap_le_constant cPrincipal c hcPrincipal hc
  have hgapHigh :=
    weakGap_le_of_one_div_khaleWeakDenominatorAbs_le K hK.le
  have hdecay := WeakVKNear.weakGap_nearFactor_beats_polylog
    (3 / 4 : ℝ) c (2 * K + 1) A (by norm_num) hc
    (by positivity) hA.le
  have hlarge : ∀ᶠ X : ℝ in atTop,
      Real.exp 1 < X := eventually_gt_atTop (Real.exp 1)
  have htauPosGlobal : 0 < tau epsilon := tau_pos hepsilonCap
  have hsourceHeight : ∀ᶠ X : ℝ in atTop,
      Rsource ≤ apZeroHeight epsilon X := by
    simpa only [apZeroHeight] using
      (tendsto_rpow_atTop htauPosGlobal).eventually
        (eventually_ge_atTop Rsource)
  have hevent : ∀ᶠ X : ℝ in atTop,
      apRegularNearOneRangeMass
          ⌊Real.rpow (Real.log X) K⌋₊ X
          (apZeroHeight epsilon X) ≤
        CJ * Real.rpow (Real.log X) (-A) := by
    filter_upwards [hpoly, hmesh, hgapLow, hprincipalWeak, hgapHigh,
        hdecay, hlarge, hsourceHeight] with
        X hpolyX hmeshX hgapLowX hprincipalWeakX hgapHighX hdecayX hXlarge
          hsourceHeightX
    have hXpos : 0 < X := (Real.exp_pos 1).trans hXlarge
    have hXone : 1 < X :=
      (Real.one_lt_exp_iff.mpr zero_lt_one).trans hXlarge
    have hlogOne : 1 < Real.log X := by
      rw [Real.lt_log_iff_exp_lt hXpos]
      exact hXlarge
    have hlogPos : 0 < Real.log X := zero_lt_one.trans hlogOne
    let Q : ℕ := ⌊Real.rpow (Real.log X) K⌋₊
    let T : ℝ := apZeroHeight epsilon X
    let L : ℕ := ⌊Real.log X⌋₊
    let omega : ℝ := c * Real.rpow (Real.log X) (-(3 / 4 : ℝ))
    have hQlog : (Q : ℝ) ≤ Real.rpow (Real.log X) K := by
      dsimp [Q]
      exact Nat.floor_le (Real.rpow_nonneg hlogPos.le K)
    have hQX : (Q : ℝ) ≤ Real.rpow X u := hQlog.trans hpolyX
    have hT : T = Real.rpow X (tau epsilon) := by
      rfl
    have htauPos : 0 < tau epsilon := htauPosGlobal
    have htauLe : tau epsilon ≤ 1 := by
      unfold tau
      linarith
    have hTone : 1 ≤ T := by
      rw [hT]
      exact Real.one_le_rpow hXone.le htauPos.le
    have hTX : T ≤ X := by
      rw [hT]
      calc
        Real.rpow X (tau epsilon) ≤ Real.rpow X 1 :=
          Real.rpow_le_rpow_of_exponent_le hXone.le htauLe
        _ = X := Real.rpow_one X
    have hLlog : (L : ℝ) ≤ Real.log X := by
      dsimp [L]
      exact Nat.floor_le hlogPos.le
    have homegaPos : 0 < omega := by
      dsimp [omega]
      exact mul_pos hc (Real.rpow_pos_of_pos hlogPos _)
    let B : ℝ := Real.log X *
      (CJ * Real.rpow X (-(omega / 12)))
    have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have hprimitive : ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), q ≤ Q →
          primitiveRegularNearOneRangeMass chi X T ≤ B := by
      intro q _inst chi hqQ
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      let psi := chi.primitiveCharacter
      have hcondQ : chi.conductor ≤ Q :=
        (conductor_le_level chi).trans (hqQ)
      have hcondLog : (chi.conductor : ℝ) ≤
          Real.rpow (Real.log X) K := by
        exact (by exact_mod_cast hcondQ :
          (chi.conductor : ℝ) ≤ (Q : ℝ)) |>.trans hQlog
      have hcondX : (chi.conductor : ℝ) ≤ Real.rpow X u :=
        hcondLog.trans hpolyX
      have hcondOne : 1 ≤ chi.conductor :=
        Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero
      have hR0 : 0 ≤ (chi.conductor : ℝ) * T :=
        mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hTone)
      have hRtoX : (chi.conductor : ℝ) * T ≤
          Real.rpow X (tau epsilon + u) := by
        have hmul : (chi.conductor : ℝ) * T ≤
            Real.rpow X u * Real.rpow X (tau epsilon) := by
          rw [hT]
          exact mul_le_mul hcondX le_rfl
            (Real.rpow_nonneg (zero_le_one.trans hXone.le) _)
            (Real.rpow_nonneg (zero_le_one.trans hXone.le) _)
        calc
          (chi.conductor : ℝ) * T ≤
              Real.rpow X u * Real.rpow X (tau epsilon) := hmul
          _ = Real.rpow X (tau epsilon + u) := by
            calc
              Real.rpow X u * Real.rpow X (tau epsilon) =
                  Real.rpow X (u + tau epsilon) :=
                (Real.rpow_add hXpos _ _).symm
              _ = Real.rpow X (tau epsilon + u) := by ring_nf
      have hbetaGap : ∀ rho : ℂ,
          rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
            4 / 5 < rho.re ∧
              ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) →
          rho.re ≤ 1 - omega := by
        intro rho hrho
        have hfull : rho ∈ zeroSupport psi 0 T :=
          (Finset.mem_filter.mp hrho).1
        have hregular := (Finset.mem_filter.mp hrho).2.2
        have hLzero : DirichletCharacter.LFunction psi
            ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) = 0 := by
          simpa [Complex.re_add_im] using
            (LFunction_eq_zero_of_mem_zeroSupport psi hfull)
        by_cases hheight : |rho.im| < 3
        · by_cases hpsi : psi = 1
          · have hsourceGap := hPrincipalGap chi.conductor psi
              chi.primitiveCharacter_isPrimitive hpsi T rho hfull
              (Finset.mem_filter.mp hrho).2.1 hheight
            linarith
          · have hregular' : ¬ (psi ^ 2 = 1 ∧ rho.im = 0) := by
              intro hbad
              exact hregular ⟨hpsi, hbad.1, hbad.2⟩
            have hrecip := primitive_nonprincipal_regular_low_gap psi
              chi.primitiveCharacter_isPrimitive hpsi hfull
              (Finset.mem_filter.mp hrho).2.1 hheight hregular'
            have hsourceGap := hgapLowX chi.conductor hcondLog
            have hpowMono : Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤
                Real.rpow (Real.log X) (-(1 / 4 : ℝ)) := by
              exact Real.rpow_le_rpow_of_exponent_le hlogOne.le (by norm_num)
            have homegaLow : omega ≤
                cLow * Real.rpow (Real.log X) (-(1 / 4 : ℝ)) := by
              dsimp [omega]
              calc
                c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤
                    cLow * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) := by
                  exact mul_le_mul_of_nonneg_right hc_le_low
                    (Real.rpow_nonneg hlogPos.le _)
                _ ≤ cLow * Real.rpow (Real.log X) (-(1 / 4 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hpowMono hcLow.le
            have homegaLow' : omega ≤
                (1 / (100000000000 * (K + Real.log 8))) *
                  Real.rpow (Real.log X) (-(1 / 4 : ℝ)) := by
              simpa only [cLow] using homegaLow
            have homegaGap := (homegaLow'.trans hsourceGap).trans hrecip
            linarith
        · have hheight' : 3 ≤ |rho.im| := le_of_not_gt hheight
          have hrect :=
            (zeroDivisor psi 0 T).supportWithinDomain
              ((zeroSupport_mem_iff psi 0 T rho).mp hfull)
          rw [zeroRectangle, Complex.mem_reProdIm] at hrect
          have himT : |rho.im| ≤ T := abs_le.mpr hrect.2
          have himX : |rho.im| ≤ X := himT.trans hTX
          have hnonzero := hKhale chi.conductor rho.im rho.re psi
            hcondOne hheight'
          have hrecip :=
            one_div_khaleWeakDenominatorAbs_le_one_sub_sigma_of_zero
              psi hcondOne hheight' hnonzero hLzero
          have hsourceGap := hgapHighX chi.conductor rho.im rho.re
            hcondOne hcondLog hheight' himX hrecip
          have homegaHigh : omega ≤
              cHigh * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) := by
            dsimp [omega]
            exact mul_le_mul_of_nonneg_right hc_le_high
              (Real.rpow_nonneg hlogPos.le _)
          have homegaHigh' : omega ≤
              (1 / (18 * K + 104)) *
                Real.rpow (Real.log X) (-(3 / 4 : ℝ)) := by
            simpa only [cHigh] using homegaHigh
          linarith [homegaHigh', hsourceGap]
      have hdensity : ∀ j < L,
          (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
            CJ * Real.rpow ((chi.conductor : ℝ) * T)
              ((21 / 10) * (1 - relativePoint j)) := by
        intro j _hj
        have hsingleNat := dirichletZeroCount_le_ambientZeroCountAtLevel
          psi (relativePoint j) T
        have hsingle :
            (dirichletZeroCount psi (relativePoint j) T : ℝ) ≤
              (ambientZeroCountAtLevel chi.conductor
                (relativePoint j) T : ℝ) := by
          exact_mod_cast hsingleNat
        have hsigmaLow : 4 / 5 ≤ relativePoint j := by
          simpa using relativePoint_mono (Nat.zero_le j)
        have hsource := hJsource chi.conductor T (relativePoint j)
          hTone hsigmaLow (relativePoint_le_one j) (by
            have hcondOneReal : (1 : ℝ) ≤ chi.conductor := by
              exact_mod_cast hcondOne
            calc
              Rsource ≤ T := by simpa only [T] using hsourceHeightX
              _ = 1 * T := by ring
              _ ≤ (chi.conductor : ℝ) * T :=
                mul_le_mul_of_nonneg_right hcondOneReal
                  (zero_le_one.trans hTone))
        simpa only [primitiveDirichletZeroCount] using hsingle.trans hsource
      simpa only [primitiveRegularNearOneRangeMass,
        primitiveFilteredNearMass, psi, B] using
        (primitiveFilteredNearMass_le_relative_of_source_density chi
          (fun rho => 4 / 5 < rho.re ∧
            ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0))
          hepsilon.le (by norm_num [u]) (by norm_num [u])
          (by
            intro rho hrho
            exact (Finset.mem_filter.mp hrho).2.1)
          hbetaGap
          (by simpa [L, omega] using hmeshX)
          hLlog hXone.le hCJ.le hR0 hRtoX hdensity)
    have hfamily := apRegularNearOneRangeMass_le_sq_mul hB hprimitive
    have hQsq : (Q : ℝ) ^ 2 ≤
        Real.rpow (Real.log X) (2 * K) := by
      have hpow0 : 0 ≤ Real.rpow (Real.log X) K :=
        Real.rpow_nonneg hlogPos.le _
      calc
        (Q : ℝ) ^ 2 ≤ (Real.rpow (Real.log X) K) ^ 2 := by
          nlinarith [sq_nonneg ((Q : ℝ) + Real.rpow (Real.log X) K)]
        _ = Real.rpow (Real.log X) (2 * K) := by
          rw [pow_two]
          calc
            Real.rpow (Real.log X) K * Real.rpow (Real.log X) K =
                Real.rpow (Real.log X) (K + K) :=
              (Real.rpow_add hlogPos _ _).symm
            _ = Real.rpow (Real.log X) (2 * K) := by ring_nf
    have hprefactor : (Q : ℝ) ^ 2 * Real.log X ≤
        Real.rpow (Real.log X) (2 * K + 1) := by
      calc
        (Q : ℝ) ^ 2 * Real.log X ≤
            Real.rpow (Real.log X) (2 * K) * Real.log X :=
        mul_le_mul_of_nonneg_right hQsq hlogPos.le
      _ = Real.rpow (Real.log X) (2 * K + 1) := by
        calc
          Real.rpow (Real.log X) (2 * K) * Real.log X =
              Real.rpow (Real.log X) (2 * K) *
                Real.rpow (Real.log X) 1 := by
            exact congrArg
              (fun z : ℝ => Real.rpow (Real.log X) (2 * K) * z)
              (Real.rpow_one (Real.log X)).symm
          _ = Real.rpow (Real.log X) (2 * K + 1) :=
            (Real.rpow_add hlogPos _ _).symm
    have hdecayOmega : Real.rpow (Real.log X) (2 * K + 1) *
        Real.rpow X (-(omega / 12)) ≤
          Real.rpow (Real.log X) (-A) := by
      exact hdecayX omega (by rfl)
    have hfinal : apRegularNearOneRangeMass Q X T ≤
        CJ * Real.rpow (Real.log X) (-A) := by
      calc
        apRegularNearOneRangeMass Q X T ≤ (Q : ℝ) ^ 2 * B := hfamily
        _ = CJ * (((Q : ℝ) ^ 2 * Real.log X) *
            Real.rpow X (-(omega / 12))) := by
          dsimp [B]
          ring
        _ ≤ CJ * (Real.rpow (Real.log X) (2 * K + 1) *
            Real.rpow X (-(omega / 12))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprefactor
              (Real.rpow_nonneg (zero_le_one.trans hXone.le) _)) hCJ.le
        _ ≤ CJ * Real.rpow (Real.log X) (-A) :=
          mul_le_mul_of_nonneg_left hdecayOmega hCJ.le
    simpa only [Q, T] using hfinal
  obtain ⟨Xevent, hXevent⟩ := eventually_atTop.1 hevent
  let X₀ : ℝ := max Xevent 2
  refine ⟨CJ, X₀, hCJ, le_max_right _ _, ?_⟩
  intro X hX
  exact hXevent X ((le_max_left _ _).trans hX)

/-- Threshold-free convenience wrapper for existing callers. -/
theorem apRegularNearOneRangeMass_logSaving_of_oneTenth_source
    (hJutila : JutilaEquation17OneTenth)
    (hKhale : KhaleAbsoluteNonvanishing) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) :=
  apRegularNearOneRangeMass_logSaving_of_oneTenth_eventual_source
    (jutilaEquation17_oneTenthEventually_of_oneTenth hJutila) hKhale

/-- Backward-compatible wrapper retaining the manuscript's full source
statement while routing the proof through the exact one-tenth fragment. -/
theorem apRegularNearOneRangeMass_logSaving_of_sources
    (hJutila : JutilaEquation17)
    (hKhale : KhaleAbsoluteNonvanishing) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) :=
  apRegularNearOneRangeMass_logSaving_of_oneTenth_source
    (jutilaEquation17_oneTenth_of_full hJutila) hKhale


/-- Final short weld: after a compact-strip constructor is supplied, the
certified low and exceptional branches and the preceding regular-near theorem
give the exact equation-(2.7) source consumed by the MAP endpoint. -/
theorem apWeightedZeroMassLogSaving_of_compact_and_oneTenth_eventual_source
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hJutila : JutilaEquation17OneTenthEventually)
    (hKhale : KhaleAbsoluteNonvanishing) :
    APWeightedZeroMassLogSaving :=
  MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    hCompact
    (apRegularNearOneRangeMass_logSaving_of_oneTenth_eventual_source
      hJutila hKhale)

theorem apWeightedZeroMassLogSaving_of_compact_and_oneTenth_source
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hJutila : JutilaEquation17OneTenth)
    (hKhale : KhaleAbsoluteNonvanishing) :
    APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_compact_and_oneTenth_eventual_source
    hCompact (jutilaEquation17_oneTenthEventually_of_oneTenth hJutila) hKhale

/-- Backward-compatible final weld from the full published formulation. -/
theorem apWeightedZeroMassLogSaving_of_compact_and_sources
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hJutila : JutilaEquation17)
    (hKhale : KhaleAbsoluteNonvanishing) :
    APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_compact_and_oneTenth_source
    hCompact (jutilaEquation17_oneTenth_of_full hJutila) hKhale

end
end MAPAPRegularNearLogSaving

#print axioms MAPAPRegularNearLogSaving.relativeDistance_le_twentyFour_div
#print axioms MAPAPRegularNearLogSaving.eventually_relativeDistance_floor_log_le_weakGap
#print axioms MAPAPRegularNearLogSaving.jutilaEquation17_oneTenth_of_full
#print axioms MAPAPRegularNearLogSaving.jutilaEquation17_oneTenthEventually_of_oneTenth
#print axioms MAPAPRegularNearLogSaving.apRegularNearOneRangeMass_logSaving_of_oneTenth_eventual_source
#print axioms MAPAPRegularNearLogSaving.apRegularNearOneRangeMass_logSaving_of_oneTenth_source
#print axioms MAPAPRegularNearLogSaving.apRegularNearOneRangeMass_logSaving_of_sources
#print axioms MAPAPRegularNearLogSaving.apWeightedZeroMassLogSaving_of_compact_and_oneTenth_eventual_source
#print axioms MAPAPRegularNearLogSaving.apWeightedZeroMassLogSaving_of_compact_and_oneTenth_source
#print axioms MAPAPRegularNearLogSaving.apWeightedZeroMassLogSaving_of_compact_and_sources
