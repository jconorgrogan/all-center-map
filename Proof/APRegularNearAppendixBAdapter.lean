import APRegularNearLogSaving
import KhaleAppendixBSourceReduction

/-!
# Corrected Khale Appendix-B adapter for the regular near-one mass

This module leaves the published Khale statement at its literal `q >= 3`
scope.  It consumes the primitive regular high-ordinate gap already obtained
from that statement, instead of manufacturing the old all-level
nonvanishing wrapper.
-/

namespace MAPAPRegularNearAppendixBAdapter

open Filter Set
open scoped BigOperators
open DirichletZeros MAPFixedScaleAPZeroRoute MAPAPZeroDensityCert
open MAPAPWeightedZeroMassIntegration MAPAPRelativeMeshPrimitiveApplication
open MAPAPRegularNearMeshRoute MAPRelativeNearOneMesh27
open MAPGuthMaynard ZeroDensityArithmetic ZeroDensityInterface
open MAPAPPrimitiveRegularLowGap MAPKhaleWeakVKApplication
open MAPAPRegularNearLogSaving MAPKhaleAppendixBSource

noncomputable section

/-- Exact internal interface after the literal Appendix-B level split has been
performed. -/
abbrev PrimitiveRegularHighGap : Prop :=
  forall K : Real, 0 < K ->
    exists c : Real, 0 < c /\
      Filter.Eventually (fun X : Real =>
        forall (q : Nat) [NeZero q] (chi : DirichletCharacter Complex q),
          chi.IsPrimitive ->
          (q : Real) <= Real.rpow (Real.log X) K ->
          forall (T : Real) (rho : Complex),
            rho ∈ DirichletZeros.zeroSupport chi 0 T ->
            4 / 5 < rho.re -> 3 <= |rho.im| -> |rho.im| <= X ->
            c * Real.rpow (Real.log X) (-(3 / 4 : Real)) <=
              1 - rho.re) Filter.atTop

theorem apRegularNearOneRangeMass_logSaving_of_oneTenth_eventual_and_high_gap
    (hJutila : JutilaEquation17OneTenthEventually)
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
  obtain ⟨CJ, Rsource, hCJ, hRsource, hJsource⟩ := hJutila
  obtain ⟨cHigh, hcHigh, hgapHigh⟩ := hHighGap K hK
  obtain ⟨cPrincipal, hcPrincipal, hPrincipalGap⟩ :=
    exists_primitive_principal_regular_low_gap
  let u : ℝ := 1 / 315
  let cLow : ℝ := 1 /
    (100000000000 * (K + Real.log 8))
  let c : ℝ := min cLow cHigh
  have hcLow : 0 < cLow := by
    dsimp [cLow]
    have hsum : 0 < K + Real.log 8 :=
      add_pos_of_pos_of_nonneg hK (Real.log_nonneg (by norm_num))
    exact one_div_pos.mpr
      (mul_pos (by norm_num) hsum)
  have hc : 0 < c := lt_min hcLow hcHigh
  have hc_le_low : c ≤ cLow := min_le_left _ _
  have hc_le_high : c ≤ cHigh := min_le_right _ _
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
  have hsourceHeight : ∀ᶠ X : ℝ in atTop,
      Rsource ≤ apZeroHeight epsilon X := by
    simpa only [apZeroHeight] using!
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

/-- The literal `q >= 3` Appendix-B theorem supplies precisely the internal
primitive high-gap interface, including the conductor-one level change. -/
theorem primitiveRegularHighGap_of_appendixB104
    (hKhale104 : AppendixBCorollary104) :
    PrimitiveRegularHighGap := by
  intro K hK
  exact exists_eventually_primitive_regular_high_gap_of_appendixB
    hKhale104 K hK

/-- Corrected regular-near source theorem: no all-level Khale wrapper. -/
theorem apRegularNearOneRangeMass_logSaving_of_jutila_appendixB104
    (hJutila : JutilaEquation17)
    (hKhale104 : AppendixBCorollary104) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) :=
  apRegularNearOneRangeMass_logSaving_of_oneTenth_eventual_and_high_gap
    (jutilaEquation17_oneTenthEventually_of_oneTenth
      (jutilaEquation17_oneTenth_of_full hJutila))
    (primitiveRegularHighGap_of_appendixB104 hKhale104)

/-- Final equation-(2.7) weld with the corrected literal Appendix-B source. -/
theorem apWeightedZeroMassLogSaving_of_compact_jutila_appendixB104
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hJutila : JutilaEquation17)
    (hKhale104 : AppendixBCorollary104) :
    APWeightedZeroMassLogSaving :=
  MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    hCompact
    (apRegularNearOneRangeMass_logSaving_of_jutila_appendixB104
      hJutila hKhale104)

end
end MAPAPRegularNearAppendixBAdapter

#print axioms MAPAPRegularNearAppendixBAdapter.primitiveRegularHighGap_of_appendixB104
#print axioms MAPAPRegularNearAppendixBAdapter.apRegularNearOneRangeMass_logSaving_of_jutila_appendixB104
#print axioms MAPAPRegularNearAppendixBAdapter.apWeightedZeroMassLogSaving_of_compact_jutila_appendixB104
