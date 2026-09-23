import APRegularNearHuxleyJutilaSourceAdapter
import APRegularNearAppendixBAdapter

/-!
# Premise-minimal regular-near source adapter

The live endpoint consumes a logarithmic saving for the weighted regular
near-one mass.  It does not consume a full-range Jutila density theorem.
This module keeps the source split literal: Huxley is used only through
`279/280`, Jutila only on the closed collar, and Appendix B supplies the
regular high-ordinate zero gap.
-/

namespace MAPAPRegularNearHuxleyJutilaAppendixBAdapter

open Filter Set
open scoped BigOperators
open DirichletZeros MAPFixedScaleAPZeroRoute MAPAPZeroDensityCert
open MAPAPWeightedZeroMassIntegration MAPAPRelativeMeshPrimitiveApplication
open MAPAPRegularNearMeshRoute MAPRelativeNearOneMesh27
open MAPGuthMaynard ZeroDensityArithmetic ZeroDensityInterface
open MAPAPPrimitiveRegularLowGap MAPKhaleWeakVKApplication
open MAPAPRegularNearLogSaving MAPKhaleAppendixBSource
open MAPAPRegularNearAppendixBAdapter
open MAPAPRegularNearHuxleyJutilaSourceAdapter
open MAPHuxleyCompactGapExponent

noncomputable section

/-- The exact eventual regular-near estimate needed by the final four-range
weighted-mass weld, from the two disjoint density sources and the already
reduced primitive high-ordinate gap. -/
theorem apRegularNearOneRangeMass_logSaving_of_huxley_collar_and_high_gap
    (hHuxley : HuxleyFixedModulusEventually)
    (hJutila : JutilaCollarOneTenthEventually)
    (hHighGap : PrimitiveRegularHighGap) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  obtain ⟨CH, RH, hCH, hRH, hHsource⟩ := hHuxley
  obtain ⟨CJ, RJ, hCJ, hRJ, hJsource⟩ := hJutila
  obtain ⟨cHigh, hcHigh, hgapHigh⟩ := hHighGap K hK
  obtain ⟨cPrincipal, hcPrincipal, hPrincipalGap⟩ :=
    exists_primitive_principal_regular_low_gap
  let u : ℝ := 1 / 315
  let cLow : ℝ := 1 /
    (100000000000 * (K + Real.log 8))
  let cCap : ℝ := 12 * huxleyCompactSaving
  let c : ℝ := min (min cLow cHigh) cCap
  have hcLow : 0 < cLow := by
    dsimp [cLow]
    have hsum : 0 < K + Real.log 8 :=
      add_pos_of_pos_of_nonneg hK (Real.log_nonneg (by norm_num))
    exact one_div_pos.mpr
      (mul_pos (by norm_num) hsum)
  have hcCap : 0 < cCap := by
    dsimp [cCap]
    exact mul_pos (by norm_num) huxleyCompactSaving_pos
  have hc : 0 < c := lt_min (lt_min hcLow hcHigh) hcCap
  have hc_le_low : c ≤ cLow := (min_le_left cLow cHigh).trans' (min_le_left _ _)
  have hc_le_high : c ≤ cHigh := (min_le_right cLow cHigh).trans' (min_le_left _ _)
  have hc_le_cap : c ≤ cCap := min_le_right _ _
  have hpoly := polylog_absorption K u (by norm_num [u])
  have hmesh := eventually_relativeDistance_floor_log_le_weakGap c hc
  have hgapLow := weakGap_le_regularLowGap K hK.le
  have hprincipalWeak :=
    eventually_weakGap_le_constant cPrincipal c hcPrincipal hc
  have hdecay := WeakVKNear.weakGap_nearFactor_beats_polylog
    (3 / 4 : ℝ) c (2 * K + 1) A (by norm_num) hc
    (by positivity) hA.le
  have hlarge : ∀ᶠ X : ℝ in atTop,
      Real.exp 1 < X := eventually_gt_atTop (Real.exp 1)
  have htauPosGlobal : 0 < tau epsilon := tau_pos hepsilonCap
  have hHuxleyHeight : ∀ᶠ X : ℝ in atTop,
      RH ≤ apZeroHeight epsilon X := by
    simpa only [apZeroHeight] using!
      (tendsto_rpow_atTop htauPosGlobal).eventually
        (eventually_ge_atTop RH)
  have hJutilaHeight : ∀ᶠ X : ℝ in atTop,
      RJ ≤ apZeroHeight epsilon X := by
    simpa only [apZeroHeight] using!
      (tendsto_rpow_atTop htauPosGlobal).eventually
        (eventually_ge_atTop RJ)
  have hevent : ∀ᶠ X : ℝ in atTop,
      apRegularNearOneRangeMass
          ⌊Real.rpow (Real.log X) K⌋₊ X
          (apZeroHeight epsilon X) ≤
        (CH + CJ) * Real.rpow (Real.log X) (-A) := by
    filter_upwards [hpoly, hmesh, hgapLow, hprincipalWeak, hgapHigh,
        hdecay, hlarge, hHuxleyHeight, hJutilaHeight] with
        X hpolyX hmeshX hgapLowX hprincipalWeakX hgapHighX hdecayX hXlarge
          hHuxleyHeightX hJutilaHeightX
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
    let P : ℕ → Prop := fun n => relativeDistance n ≤ omega
    have hP : ∃ n, P n := ⟨L, by simpa [P, L, omega] using hmeshX⟩
    let J : ℕ := Nat.find hP
    have hdepthJ : relativeDistance J ≤ omega := by
      simpa [J, P] using Nat.find_spec hP
    have hJL : J ≤ L := by
      dsimp [J]
      exact Nat.find_min' hP (by simpa [P, L, omega] using hmeshX)
    have hmeshGapJ : ∀ j < J, omega ≤ relativeDistance j := by
      intro j hj
      have hnot : ¬ P j := Nat.find_min hP (by simpa [J] using hj)
      dsimp [P] at hnot
      exact (lt_of_not_ge hnot).le
    have hJlog : (J : ℝ) ≤ Real.log X := by
      have hJLreal : (J : ℝ) ≤ (L : ℝ) := by exact_mod_cast hJL
      exact hJLreal.trans hLlog
    have homegaCap : omega / 12 ≤ huxleyCompactSaving := by
      have hrpowLe : Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlogOne.le (by norm_num)
      have homegaLe : omega ≤ c := by
        dsimp [omega]
        simpa only [mul_one] using!
          (mul_le_mul_of_nonneg_left hrpowLe hc.le)
      dsimp [cCap] at hc_le_cap
      linarith
    let B : ℝ := Real.log X *
      (CH * Real.rpow X (-huxleyCompactSaving) +
        CJ * Real.rpow X (-(omega / 12)))
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
          have hsourceGap := hgapHighX chi.conductor psi
            chi.primitiveCharacter_isPrimitive hcondLog T rho hfull
            (Finset.mem_filter.mp hrho).2.1 hheight' himX
          have homegaHigh : omega ≤
              cHigh * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) := by
            dsimp [omega]
            exact mul_le_mul_of_nonneg_right hc_le_high
              (Real.rpow_nonneg hlogPos.le _)
          linarith [homegaHigh, hsourceGap]
      have hcondOneReal : (1 : ℝ) ≤ chi.conductor := by
        exact_mod_cast hcondOne
      have hHuxleyScale : RH ≤ (chi.conductor : ℝ) * T := by
        calc
          RH ≤ T := by simpa only [T] using hHuxleyHeightX
          _ = 1 * T := by ring
          _ ≤ (chi.conductor : ℝ) * T :=
            mul_le_mul_of_nonneg_right hcondOneReal
              (zero_le_one.trans hTone)
      have hJutilaScale : RJ ≤ (chi.conductor : ℝ) * T := by
        calc
          RJ ≤ T := by simpa only [T] using hJutilaHeightX
          _ = 1 * T := by ring
          _ ≤ (chi.conductor : ℝ) * T :=
            mul_le_mul_of_nonneg_right hcondOneReal
              (zero_le_one.trans hTone)
      simpa only [B] using
        (primitiveRegularNearOneRangeMass_le_of_sources
          hCH hCJ hHsource hJsource chi hepsilon.le
          (by norm_num [u]) (by norm_num [u]) hbetaGap
          hdepthJ hmeshGapJ hJlog hXone.le hTone hRtoX
          hHuxleyScale hJutilaScale)
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
    have hHuxleyToNear : Real.rpow X (-huxleyCompactSaving) ≤
        Real.rpow X (-(omega / 12)) := by
      exact Real.rpow_le_rpow_of_exponent_le hXone.le (by linarith)
    have hsourceSum :
        CH * Real.rpow X (-huxleyCompactSaving) +
            CJ * Real.rpow X (-(omega / 12)) ≤
          (CH + CJ) * Real.rpow X (-(omega / 12)) := by
      calc
        CH * Real.rpow X (-huxleyCompactSaving) +
            CJ * Real.rpow X (-(omega / 12)) ≤
          CH * Real.rpow X (-(omega / 12)) +
            CJ * Real.rpow X (-(omega / 12)) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hHuxleyToNear hCH.le) le_rfl
        _ = (CH + CJ) * Real.rpow X (-(omega / 12)) := by ring
    have hdecayOmega : Real.rpow (Real.log X) (2 * K + 1) *
        Real.rpow X (-(omega / 12)) ≤
          Real.rpow (Real.log X) (-A) := by
      exact hdecayX omega (by rfl)
    have hCsum : 0 ≤ CH + CJ := add_nonneg hCH.le hCJ.le
    have hfinal : apRegularNearOneRangeMass Q X T ≤
        (CH + CJ) * Real.rpow (Real.log X) (-A) := by
      calc
        apRegularNearOneRangeMass Q X T ≤ (Q : ℝ) ^ 2 * B := hfamily
        _ ≤ (Q : ℝ) ^ 2 *
            (Real.log X * ((CH + CJ) *
              Real.rpow X (-(omega / 12)))) := by
          dsimp [B]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsourceSum hlogPos.le)
            (sq_nonneg (Q : ℝ))
        _ = (CH + CJ) * (((Q : ℝ) ^ 2 * Real.log X) *
            Real.rpow X (-(omega / 12))) := by ring
        _ ≤ (CH + CJ) * (Real.rpow (Real.log X) (2 * K + 1) *
            Real.rpow X (-(omega / 12))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprefactor
              (Real.rpow_nonneg (zero_le_one.trans hXone.le) _)) hCsum
        _ ≤ (CH + CJ) * Real.rpow (Real.log X) (-A) :=
          mul_le_mul_of_nonneg_left hdecayOmega hCsum
    simpa only [Q, T] using hfinal
  obtain ⟨Xevent, hXevent⟩ := eventually_atTop.1 hevent
  let X₀ : ℝ := max Xevent 2
  refine ⟨CH + CJ, X₀, add_pos hCH hCJ, le_max_right _ _, ?_⟩
  intro X hX
  exact hXevent X ((le_max_left _ _).trans hX)

/-- Literal Appendix-B Corollary 10.4 supplies the high-gap premise. -/
theorem apRegularNearOneRangeMass_logSaving_of_huxley_collar_appendixB104
    (hHuxley : HuxleyFixedModulusEventually)
    (hJutila : JutilaCollarOneTenthEventually)
    (hKhale104 : AppendixBCorollary104) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) :=
  apRegularNearOneRangeMass_logSaving_of_huxley_collar_and_high_gap
    hHuxley hJutila (primitiveRegularHighGap_of_appendixB104 hKhale104)

/-- The compact strip is the sole extra premise needed to reach the exact
equation-(2.7) type consumed by the live endpoint. -/
theorem apWeightedZeroMassLogSaving_of_compact_huxley_collar_appendixB104
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hHuxley : HuxleyFixedModulusEventually)
    (hJutila : JutilaCollarOneTenthEventually)
    (hKhale104 : AppendixBCorollary104) :
    APWeightedZeroMassLogSaving :=
  MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    hCompact
    (apRegularNearOneRangeMass_logSaving_of_huxley_collar_appendixB104
      hHuxley hJutila hKhale104)

end
end MAPAPRegularNearHuxleyJutilaAppendixBAdapter

#print axioms MAPAPRegularNearHuxleyJutilaAppendixBAdapter.apRegularNearOneRangeMass_logSaving_of_huxley_collar_and_high_gap
#print axioms MAPAPRegularNearHuxleyJutilaAppendixBAdapter.apRegularNearOneRangeMass_logSaving_of_huxley_collar_appendixB104
#print axioms MAPAPRegularNearHuxleyJutilaAppendixBAdapter.apWeightedZeroMassLogSaving_of_compact_huxley_collar_appendixB104
