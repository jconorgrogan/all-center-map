import MAPNearOneBulkBypassConsumer
import APRegularNearCGLGappedJutilaAppendixBAdapter

/-! The fixed-strip bypass retains the live regular/gapped selected-P53
collar source; it does not strengthen that source to all ambient zeros. -/
namespace MAPNearOneBulkBypassGappedConsumer
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
open MAPAPRegularNearCGLGappedCollarRoute
open MAPJutilaGappedCollarSourceAdapter MAPJutilaCollarA5Budget
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPJutilaGappedCollarFiniteAggregation
open MAPCGLNearFineMesh MAPCGLNearFineMeshSourceAdapter
open CGLMeshFormalization MAPAPTailReserveAbsorption
open MAPJutilaCollarMeshCutoff

open MAPNearOneBulkBypassInterface MAPNearOneBulkBypassConsumer
open MAPAPRegularNearCGLGappedJutilaAppendixBAdapter
noncomputable section

theorem regularNear_logSaving_of_bulk_gappedCumulative_and_high_gap
    (hbulk : FixedPrimitiveBulkPolylogDensity)
    (hCollar : JutilaGappedSplitSelectedCumulativeEventually)
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
  let eta : ℝ := epsilon / 2000
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  obtain ⟨CC, hCC, hCGLsource⟩ :=
    eventually_fixedPrimitiveNearDensity_of_bulk
      hbulk K epsilon eta hK hepsilon hepsilonCap heta
  obtain ⟨CJ, RJ, P, hCJ, hRJ, hP, hJsource⟩ := hCollar
  obtain ⟨cHigh, hcHigh, hgapHigh⟩ := hHighGap K hK
  obtain ⟨cPrincipal, hcPrincipal, hPrincipalGap⟩ :=
    exists_primitive_principal_regular_low_gap
  let u : ℝ := 1 / 315
  let cLow : ℝ := 1 / (100000000000 * (K + Real.log 8))
  let c : ℝ := min cLow cHigh
  have hcLow : 0 < cLow := by
    dsimp [cLow]
    have hsum : 0 < K + Real.log 8 :=
      add_pos_of_pos_of_nonneg hK (Real.log_nonneg (by norm_num))
    exact one_div_pos.mpr (mul_pos (by norm_num) hsum)
  have hc : 0 < c := lt_min hcLow hcHigh
  have hc_le_low : c ≤ cLow := min_le_left _ _
  have hc_le_high : c ≤ cHigh := min_le_right _ _
  have hpoly := polylog_absorption K u (by norm_num [u])
  have hmesh := eventually_relativeDistance_floor_log_le_weakGap c hc
  have hgapLow := weakGap_le_regularLowGap K hK.le
  have hprincipalWeak :=
    eventually_weakGap_le_constant cPrincipal c hcPrincipal hc
  have hcollarDecay := WeakVKNear.weakGap_nearFactor_beats_polylog
    (3 / 4 : ℝ) c (2 * K + 1) A (by norm_num) hc
      (by positivity) hA.le
  have hcompactDecay := eventually_tail_power_mul_polylog_le
    A (2 * K + 1) (epsilon / 200) (div_pos hepsilon (by norm_num))
  have hlarge : ∀ᶠ X : ℝ in atTop,
      Real.exp 1 < X := eventually_gt_atTop (Real.exp 1)
  have htauPosGlobal : 0 < tau epsilon := tau_pos hepsilonCap
  have hA5Absorb := eventually_log_rpow_le_scaled_weakGap_power
    (P + 1) (tau epsilon * a5FiberGapBudget) c (by linarith)
    (mul_pos htauPosGlobal (by norm_num [a5FiberGapBudget])) hc
  have hJutilaHeight : ∀ᶠ X : ℝ in atTop,
      RJ ≤ apZeroHeight epsilon X := by
    simpa only [apZeroHeight] using!
      (tendsto_rpow_atTop htauPosGlobal).eventually (eventually_ge_atTop RJ)
  let Cfinal : ℝ := (fineCellCount epsilon : ℝ) * CC + CJ
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    have hcell : 0 ≤ (fineCellCount epsilon : ℝ) := Nat.cast_nonneg _
    exact add_pos_of_nonneg_of_pos (mul_nonneg hcell hCC.le) hCJ
  have hevent : ∀ᶠ X : ℝ in atTop,
      apRegularNearOneRangeMass
          ⌊Real.rpow (Real.log X) K⌋₊ X
          (apZeroHeight epsilon X) ≤
        Cfinal * Real.rpow (Real.log X) (-A) := by
    filter_upwards [hCGLsource, hpoly, hmesh, hgapLow, hprincipalWeak,
        hgapHigh, hcollarDecay, hcompactDecay, hlarge, hJutilaHeight,
        hA5Absorb] with
        X hCGLX hpolyX hmeshX hgapLowX hprincipalWeakX hgapHighX
          hcollarDecayX hcompactDecayX hXlarge hJutilaHeightX hA5AbsorbX
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
    have hT : T = Real.rpow X (tau epsilon) := rfl
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
    let meshPred : ℕ → Prop := fun n => relativeDistance n ≤ omega
    have hMeshPred : ∃ n, meshPred n :=
      ⟨L, by simpa [meshPred, L, omega] using hmeshX⟩
    let J : ℕ := Nat.find hMeshPred
    have hdepthJ : relativeDistance J ≤ omega := by
      simpa [J, meshPred] using Nat.find_spec hMeshPred
    have hJL : J ≤ L := by
      dsimp [J]
      exact Nat.find_min' hMeshPred
        (by simpa [meshPred, L, omega] using hmeshX)
    have hmeshGapJ : ∀ j < J, omega ≤ relativeDistance j := by
      intro j hj
      have hnot : ¬ meshPred j :=
        Nat.find_min hMeshPred (by simpa [J] using hj)
      dsimp [meshPred] at hnot
      exact (lt_of_not_ge hnot).le
    have hJlog : (J : ℝ) ≤ Real.log X := by
      have hJLreal : (J : ℝ) ≤ (L : ℝ) := by exact_mod_cast hJL
      exact hJLreal.trans hLlog
    have hgapAll : ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), q ≤ Q → ∀ rho : ℂ,
        rho ∈ (by
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          let psi := chi.primitiveCharacter
          exact (zeroSupport psi 0 T).filter (fun rho =>
            4 / 5 < rho.re ∧
              ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0))) →
        rho.re ≤ 1 - omega := by
      intro q _inst chi hqQ rho hrho
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      let psi := chi.primitiveCharacter
      have hcondQ : chi.conductor ≤ Q := (conductor_le_level chi).trans hqQ
      have hcondLog : (chi.conductor : ℝ) ≤ Real.rpow (Real.log X) K :=
        (by exact_mod_cast hcondQ : (chi.conductor : ℝ) ≤ (Q : ℝ)) |>.trans hQlog
      have hfull : rho ∈ zeroSupport psi 0 T := (Finset.mem_filter.mp hrho).1
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
              Real.rpow (Real.log X) (-(1 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hlogOne.le (by norm_num)
          have homegaLow : omega ≤
              cLow * Real.rpow (Real.log X) (-(1 / 4 : ℝ)) := by
            dsimp [omega]
            calc
              c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤
                  cLow * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_right hc_le_low
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
    have hScaleToX : ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), q ≤ Q →
        (chi.conductor : ℝ) * Real.rpow X (tau epsilon) ≤
          Real.rpow X (tau epsilon + u) := by
      intro q _inst chi hqQ
      have hcondQ : chi.conductor ≤ Q := (conductor_le_level chi).trans hqQ
      have hcondLog : (chi.conductor : ℝ) ≤ Real.rpow (Real.log X) K :=
        (by exact_mod_cast hcondQ : (chi.conductor : ℝ) ≤ (Q : ℝ)) |>.trans hQlog
      have hcondX : (chi.conductor : ℝ) ≤ Real.rpow X u :=
        hcondLog.trans hpolyX
      have hmul : (chi.conductor : ℝ) * Real.rpow X (tau epsilon) ≤
          Real.rpow X u * Real.rpow X (tau epsilon) :=
        mul_le_mul_of_nonneg_right hcondX (Real.rpow_nonneg hXpos.le _)
      calc
        (chi.conductor : ℝ) * Real.rpow X (tau epsilon) ≤
            Real.rpow X u * Real.rpow X (tau epsilon) := hmul
        _ = Real.rpow X (tau epsilon + u) := by
          calc
            Real.rpow X u * Real.rpow X (tau epsilon) =
                Real.rpow X (u + tau epsilon) :=
              (Real.rpow_add hXpos _ _).symm
            _ = Real.rpow X (tau epsilon + u) := by ring_nf
    have hJutilaScale : ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), q ≤ Q →
        RJ ≤ (chi.conductor : ℝ) * Real.rpow X (tau epsilon) := by
      intro q _inst chi hqQ
      have hcondOneReal : (1 : ℝ) ≤ chi.conductor := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero)
      calc
        RJ ≤ T := by simpa only [T] using hJutilaHeightX
        _ = 1 * Real.rpow X (tau epsilon) := by rw [hT]; ring
        _ ≤ (chi.conductor : ℝ) * Real.rpow X (tau epsilon) :=
          mul_le_mul_of_nonneg_right hcondOneReal
            (Real.rpow_nonneg hXpos.le _)
    have hCGLdensity : ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), q ≤ Q →
        ∀ sigma : ℝ, 4 / 5 ≤ sigma → sigma ≤ relativePoint collarIndex →
          (primitiveDirichletZeroCount chi sigma
            (Real.rpow X (tau epsilon)) : ℝ) ≤
            CC * Real.rpow (Real.rpow X (tau epsilon))
              (densityCoeff * (1 - sigma) + eta) := by
      intro q _inst chi hqQ sigma hsigmaLow hsigmaHigh
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      have hcondQ : chi.conductor ≤ Q := (conductor_le_level chi).trans hqQ
      exact hCGLX Q hQlog sigma hsigmaLow hsigmaHigh chi.conductor
        chi.primitiveCharacter chi.primitiveCharacter_isPrimitive hcondQ
    have hcollarDensity : ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), q ≤ Q →
        ∀ j < J, collarIndex ≤ j →
          (inducedPrimitiveRegularCumulativeCount chi
            (relativePoint j) (Real.rpow X (tau epsilon)) : ℝ) ≤
            CJ * Real.rpow
              ((chi.conductor : ℝ) * Real.rpow X (tau epsilon))
                ((21 / 10) * (1 - relativePoint j)) := by
      intro q _inst chi hqQ j hjJ hjCollar
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      let psi := chi.primitiveCharacter
      let D : ℝ := (chi.conductor : ℝ) * Real.rpow X (tau epsilon)
      have hcondOne : (1 : ℝ) ≤ chi.conductor := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero)
      have hTpos : 0 < Real.rpow X (tau epsilon) :=
        Real.rpow_pos_of_pos hXpos _
      have hTD : Real.rpow X (tau epsilon) ≤ D := by
        dsimp [D]
        calc
          Real.rpow X (tau epsilon) =
              1 * Real.rpow X (tau epsilon) := by ring
          _ ≤ (chi.conductor : ℝ) * Real.rpow X (tau epsilon) :=
            mul_le_mul_of_nonneg_right hcondOne hTpos.le
      have hDpos : 0 < D := hTpos.trans_le hTD
      have htauUle : tau epsilon + u ≤ 1 := by
        dsimp [tau, u]
        linarith
      have hDX : D ≤ X := by
        calc
          D ≤ Real.rpow X (tau epsilon + u) :=
            hScaleToX q chi hqQ
          _ ≤ Real.rpow X 1 :=
            Real.rpow_le_rpow_of_exponent_le hXone.le htauUle
          _ = X := Real.rpow_one X
      have hexp0 : 0 ≤ a5FiberGapBudget * omega :=
        mul_nonneg (by norm_num [a5FiberGapBudget]) homegaPos.le
      have hlogD0 : 0 ≤ Real.log D :=
        Real.log_nonneg (by linarith [hRJ, hJutilaScale q chi hqQ])
      have hpolyD : Real.rpow (Real.log D) (P + 1) ≤
          Real.rpow D (a5FiberGapBudget * omega) := by
        calc
          Real.rpow (Real.log D) (P + 1) ≤
              Real.rpow (Real.log X) (P + 1) := by
            apply Real.rpow_le_rpow hlogD0
            · exact Real.log_le_log hDpos hDX
            · linarith
          _ ≤ Real.rpow X
              ((tau epsilon * a5FiberGapBudget) * omega) :=
            hA5AbsorbX omega (by rfl)
          _ = Real.rpow (Real.rpow X (tau epsilon))
              (a5FiberGapBudget * omega) := by
            calc
              Real.rpow X ((tau epsilon * a5FiberGapBudget) * omega) =
                  Real.rpow X
                    (tau epsilon * (a5FiberGapBudget * omega)) := by
                congr 1
                ring
              _ = Real.rpow (Real.rpow X (tau epsilon))
                    (a5FiberGapBudget * omega) :=
                Real.rpow_mul hXpos.le _ _
          _ ≤ Real.rpow D (a5FiberGapBudget * omega) :=
            Real.rpow_le_rpow hTpos.le hTD hexp0
      have hsigmaGap : omega ≤ 1 - relativePoint j := by
        simpa only [one_sub_relativePoint] using hmeshGapJ j hjJ
      have hregularGap : ∀ rho : ℂ,
          rho ∈ regularCollarSupport psi (relativePoint j)
            (Real.rpow X (tau epsilon)) →
          rho.re ≤ 1 - omega := by
        intro rho hrho
        have hm := Finset.mem_filter.mp hrho
        apply hgapAll q chi hqQ rho
        have houter : rho ∈ zeroSupport psi 0
            (Real.rpow X (tau epsilon)) :=
          MAPMellinDetectorLeaf.zeroSupport_mono psi
            ((by norm_num : (0 : ℝ) ≤ 279 / 280).trans
              (relativePoint_mem_collar hjCollar))
            le_rfl hm.1
        exact Finset.mem_filter.mpr ⟨houter, hm.2⟩
      have hsourcePoint := hJsource chi.conductor psi
        (Real.rpow X (tau epsilon)) (relativePoint j) omega
        chi.primitiveCharacter_isPrimitive hTone
        (relativePoint_mem_collar hjCollar) (relativePoint_le_one j)
        homegaPos.le hsigmaGap (hJutilaScale q chi hqQ) hpolyD hregularGap
      simpa only [inducedPrimitiveRegularCumulativeCount, psi, D] using
        hsourcePoint
    have hfamily := apRegularNearOneRangeMass_le_of_cglfine_gappedCollar
      (Q := Q) (L := J) (epsilon := epsilon) (eta := eta) (u := u)
      (omega := omega) (X := X) (CC := CC) (CJ := CJ)
      hepsilon hepsilonCap heta.le (by rfl) (by norm_num [u])
      (by norm_num [u]) hgapAll hdepthJ hmeshGapJ hJlog hXone.le
      hCC.le hCJ.le hScaleToX hCGLdensity hcollarDensity
    have hQsq : (Q : ℝ) ^ 2 ≤ Real.rpow (Real.log X) (2 * K) := by
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
    have hcompactCore :
        ((Q : ℝ) ^ 2 * Real.log X) * Real.rpow X (-(epsilon / 400)) ≤
          Real.rpow (Real.log X) (-A) := by
      calc
        ((Q : ℝ) ^ 2 * Real.log X) * Real.rpow X (-(epsilon / 400)) ≤
            Real.rpow (Real.log X) (2 * K + 1) *
              Real.rpow X (-(epsilon / 400)) :=
          mul_le_mul_of_nonneg_right hprefactor
            (Real.rpow_nonneg hXpos.le _)
        _ = Real.rpow X (-(epsilon / 400)) *
              Real.rpow (Real.log X) (2 * K + 1) := by ring
        _ = Real.rpow X (-(epsilon / 200) / 2) *
              Real.rpow (Real.log X) (2 * K + 1) := by congr 2 <;> ring
        _ ≤ Real.rpow (Real.log X) (-A) := hcompactDecayX
    have hcollarCore :
        ((Q : ℝ) ^ 2 * Real.log X) * Real.rpow X (-(omega / 12)) ≤
          Real.rpow (Real.log X) (-A) := by
      calc
        ((Q : ℝ) ^ 2 * Real.log X) * Real.rpow X (-(omega / 12)) ≤
            Real.rpow (Real.log X) (2 * K + 1) *
              Real.rpow X (-(omega / 12)) :=
          mul_le_mul_of_nonneg_right hprefactor
            (Real.rpow_nonneg hXpos.le _)
        _ ≤ Real.rpow (Real.log X) (-A) := hcollarDecayX omega (by rfl)
    have hFC : 0 ≤ (fineCellCount epsilon : ℝ) := Nat.cast_nonneg _
    have htarget : 0 ≤ Real.rpow (Real.log X) (-A) :=
      Real.rpow_nonneg hlogPos.le _
    have hfinal : apRegularNearOneRangeMass Q X T ≤
        Cfinal * Real.rpow (Real.log X) (-A) := by
      calc
        apRegularNearOneRangeMass Q X T ≤
            (Q : ℝ) ^ 2 * (Real.log X *
              ((fineCellCount epsilon : ℝ) *
                  (CC * Real.rpow X (-(epsilon / 400))) +
                CJ * Real.rpow X (-(omega / 12)))) := by
          simpa only [T] using! hfamily
        _ = ((fineCellCount epsilon : ℝ) * CC) *
              (((Q : ℝ) ^ 2 * Real.log X) *
                Real.rpow X (-(epsilon / 400))) +
            CJ * (((Q : ℝ) ^ 2 * Real.log X) *
                Real.rpow X (-(omega / 12))) := by ring
        _ ≤ ((fineCellCount epsilon : ℝ) * CC) *
              Real.rpow (Real.log X) (-A) +
            CJ * Real.rpow (Real.log X) (-A) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hcompactCore (mul_nonneg hFC hCC.le))
            (mul_le_mul_of_nonneg_left hcollarCore hCJ.le)
        _ = Cfinal * Real.rpow (Real.log X) (-A) := by
          dsimp [Cfinal]
          ring
    simpa only [Q, T] using hfinal
  obtain ⟨Xevent, hXevent⟩ := eventually_atTop.1 hevent
  let X₀ : ℝ := max Xevent 2
  refine ⟨Cfinal, X₀, hCfinal, le_max_right _ _, ?_⟩
  intro X hX
  exact hXevent X ((le_max_left _ _).trans hX)


theorem apWeightedZeroMassLogSaving_of_bulk_selectedP53_and_high_gap
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤ C * Real.rpow (Real.log X) (-A))
    (hbulk : FixedPrimitiveBulkPolylogDensity)
    (hP53 : JutilaGappedSelectedSystemP53Eventually)
    (hPrincipalP53 : JutilaGappedSelectedPrincipalP53Eventually)
    (hHighGap : PrimitiveRegularHighGap) : APWeightedZeroMassLogSaving :=
  MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    hCompact (regularNear_logSaving_of_bulk_gappedCumulative_and_high_gap
      hbulk (primitiveRegularCumulativeCount_le_of_gappedSelectedP53 hP53 hPrincipalP53) hHighGap)

#print axioms regularNear_logSaving_of_bulk_gappedCumulative_and_high_gap
#print axioms apWeightedZeroMassLogSaving_of_bulk_selectedP53_and_high_gap
end
end MAPNearOneBulkBypassGappedConsumer
