import MRTDynamicD12AnnulusGeometry
import MRTCorollary53SourceBridge

/-!
# Uniform parameter package for the dynamic D12 annulus

The package keeps the canonical choices `Q = (log X)^B`,
`eta = 1 / sqrt Q`, `P = |beta| X^(23/24)`,
`Tmom = 2 |beta| X sqrt Q`, and `rho = |beta| X / (2 sqrt Q)`.
The far condition is the only source of the lower scale needed for the
moment range and the inner-radius inequalities.
-/

namespace MRTDynamicD12ParameterPackage

open Filter
open MAPMRTCorollary53Source
open MAPDynamicHBSourceV3
open MRTDynamicD12AnnulusGeometry
open MRTProposition61HighAnnulusPreservationV3
open MRTDynamicD12MomentSource
open PostA5HighStripSplitReductionFromFourthMoment
open MRTLemma215DyadicPartition
open MRTLemma215HBExpansion

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

structure D12ParameterPackage (X : ℝ) (p : Corollary53Input)
    (B Cc : ℕ) (reserve : ℝ) where
  Q : ℝ
  eta : ℝ
  U : ℝ
  P : ℝ
  Tmom : ℝ
  rho : ℝ
  hX : 1 ≤ X
  hpX : p.X = X
  hpeta : p.eta = eta
  hQ : Q = (Real.log X) ^ B
  hQone : 1 ≤ Q
  heta : eta = 1 / Real.sqrt Q
  hU : U = |p.beta| * p.H
  hP : P = |p.beta| * Real.rpow X (23 / 24 : ℝ)
  hTmom : Tmom = 2 * |p.beta| * X * Real.sqrt Q
  hrho : rho = |p.beta| * X / (2 * Real.sqrt Q)
  hPone : 1 ≤ P
  hrho_pos : 0 < rho
  hrhoT : rho ≤ Tmom
  hXrho : 2 * X ≤ rho ^ 2
  hmoment : DynamicD12MomentRange (8 * X) Tmom B p.q
    (hbFactorCutoff X)
  hPU : P + U ≤ rho
  hband : ∀ component : OuterComponent, ∀ t ∈ Set.Icc
      ((componentEndpoints X p.beta eta component).1 - (P + U))
      ((componentEndpoints X p.beta eta component).2 + (P + U)),
      rho ≤ |t| ∧ |t| ≤ Tmom
  hlength : ∀ component : OuterComponent,
      ((componentEndpoints X p.beta eta component).2 + (P + U)) -
        ((componentEndpoints X p.beta eta component).1 - (P + U)) + 1 ≤ Tmom

theorem exists_d12_parameter_package :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∀ᶠ X : ℝ in atTop,
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            Nonempty (D12ParameterPackage X p B Cc reserve) := by
  refine ⟨0, ?_⟩
  intro B hB
  refine ⟨0, ?_⟩
  intro Cc hCc
  have hloglog : Tendsto (fun z : ℝ => Real.log (Real.log z)) atTop atTop := by
    simpa only [Function.comp_apply] using
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hloglog8 : Tendsto (fun z : ℝ => Real.log (Real.log (8 * z))) atTop atTop := by
    simpa only [Function.comp_apply, mul_comm] using
      hloglog.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))
  have hBEvent : ∀ᶠ X : ℝ in atTop,
      (B : ℝ) ≤ Real.log (Real.log (8 * X)) :=
    hloglog8.eventually (eventually_ge_atTop (B : ℝ))
  have hpolyEvent : ∀ᶠ X : ℝ in atTop,
      Real.rpow (Real.log X) ((B : ℝ) / 2) ≤
        Real.rpow X (1 / 2 - 161 / 1200 : ℝ) := by
    simpa only [one_mul] using
      (eventually_const_mul_polylog_le_rpow 1 ((B : ℝ) / 2)
        (1 / 2 - 161 / 1200 : ℝ) (by norm_num) (by norm_num))
  have hlogEvent : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hPUEvent := eventually_freePerron_add_width_le_innerRadius B
  filter_upwards [hBEvent, hpolyEvent, hlogEvent,
    eventually_ge_atTop (2 : ℝ), hPUEvent] with
    X hB_X hpoly_X hlog_X hX2 hPU_X
  intro p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  rcases hp with ⟨hHone, hHX, hq, haq, hetaPos, hetaOne, hbetaEta,
    hetaCap, hbetaNe, hsource⟩
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlogp : 1 ≤ Real.log p.X := by simpa only [hpX] using hlog_X
  have hQone : 1 ≤ (Real.log p.X) ^ B := one_le_pow₀ hlogp
  have hQpos : 0 < (Real.log p.X) ^ B := by positivity
  have hsqrtQ : Real.sqrt ((Real.log p.X) ^ B) =
      Real.rpow (Real.log p.X) ((B : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Real.rpow_eq_pow, div_eq_mul_inv, one_mul] using
      (Real.rpow_natCast_mul (by linarith [hlogp] : 0 ≤ Real.log p.X) B
        (1 / 2 : ℝ)).symm
  have hpoly_p : Real.sqrt ((Real.log p.X) ^ B) ≤
      Real.rpow p.X (1 / 2 - 161 / 1200 : ℝ) := by
    rw [hsqrtQ]
    simpa only [hpX] using hpoly_X
  have heUpper : 2 / 15 + reserve ≤ 161 / 1200 := by linarith
  have heUpper' : 2 / 15 + reserve ≤ 23 / 24 := by linarith
  have hfar' : 4 * (Real.log p.X) ^ Cc <
      |p.beta| * Real.rpow p.X (2 / 15 + reserve) := by
    have hfar0 : 2 * (Real.log p.X) ^ Cc < |p.beta| * p.H := by
      simpa only [stationaryWidth] using hfar
    calc
      4 * (Real.log p.X) ^ Cc < 2 * (|p.beta| * p.H) := by linarith
      _ = |p.beta| * Real.rpow p.X (2 / 15 + reserve) := by
        rw [hH]
        ring
  have hCcPow : 1 ≤ (Real.log p.X) ^ Cc := one_le_pow₀ hlogp
  have hfarone : 4 < |p.beta| * Real.rpow p.X (2 / 15 + reserve) :=
    lt_of_le_of_lt (by
      have : (4 : ℝ) ≤ 4 * (Real.log p.X) ^ Cc :=
        (by
          have hh := mul_le_mul_of_nonneg_left hCcPow
            (by norm_num : (0 : ℝ) ≤ 4)
          norm_num at hh ⊢
          exact hh)
      exact this) hfar'
  have hrpowE_le : Real.rpow p.X (2 / 15 + reserve) ≤
      Real.rpow p.X (23 / 24 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) heUpper'
  have hPone : 1 ≤ |p.beta| * Real.rpow p.X (23 / 24 : ℝ) := by
    have hfour : 4 ≤ |p.beta| * Real.rpow p.X (23 / 24 : ℝ) :=
      (by
        exact (le_of_lt (lt_of_lt_of_le hfarone (mul_le_mul_of_nonneg_left
          hrpowE_le (abs_nonneg _)))) )
    linarith
  have hq0 : 1 ≤ p.q := hq
  have hqpos : 0 < (p.q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p.q))
  have hbetaPos : 0 < |p.beta| := abs_pos.mpr hbetaNe
  have hXposp : 0 < p.X := by simpa only [hpX] using hXpos
  have hsqrtQpos : 0 < Real.sqrt ((Real.log p.X) ^ B) :=
    Real.sqrt_pos.2 hQpos
  have hTupper : 2 * |p.beta| * X * Real.sqrt ((Real.log p.X) ^ B) ≤ 2 * X := by
    have hbetaEta' : |p.beta| ≤ 1 / Real.sqrt ((Real.log p.X) ^ B) := by
      rw [heta] at hbetaEta
      simpa only [one_mul] using hbetaEta
    have hmul : |p.beta| * Real.sqrt ((Real.log p.X) ^ B) ≤ 1 := by
      exact (le_div_iff₀ hsqrtQpos).mp hbetaEta'
    nlinarith [mul_nonneg (abs_nonneg p.beta) hXpos.le]
  have hpowE : Real.rpow p.X (2 / 15 + reserve) *
      Real.rpow p.X (1 - (2 / 15 + reserve)) = p.X := by
    have h := (Real.rpow_add hXposp (2 / 15 + reserve)
      (1 - (2 / 15 + reserve))).symm
    rw [show 2 / 15 + reserve + (1 - (2 / 15 + reserve)) = (1 : ℝ) by ring,
      Real.rpow_one] at h
    exact h
  have hpowHalf : Real.rpow p.X (1 / 2 - 161 / 1200 : ℝ) ≤
      Real.rpow p.X (1 / 2 - (2 / 15 + reserve)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hpolyHalf : Real.sqrt ((Real.log p.X) ^ B) ≤
      Real.rpow p.X (1 / 2 - (2 / 15 + reserve)) :=
    hpoly_p.trans hpowHalf
  have hpowOne : Real.rpow p.X (1 / 2 - (2 / 15 + reserve)) ≤
      Real.rpow p.X (1 - (2 / 15 + reserve)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hsqrtX : Real.sqrt p.X = Real.rpow p.X (1 / 2) := Real.sqrt_eq_rpow _
  have hqroot : Real.sqrt ((Real.log p.X) ^ B) * Real.sqrt p.X ≤
      Real.rpow p.X (1 - (2 / 15 + reserve)) := by
    calc
      _ ≤ Real.rpow p.X (1 / 2 - (2 / 15 + reserve)) *
          Real.rpow p.X (1 / 2) := by
        rw [hsqrtX]
        exact mul_le_mul_of_nonneg_right hpolyHalf (Real.rpow_nonneg (by linarith) _)
      _ = Real.rpow p.X (1 - (2 / 15 + reserve)) := by
        have h := (Real.rpow_add hXposp
          (1 / 2 - (2 / 15 + reserve)) (1 / 2 : ℝ)).symm
        rw [show 1 / 2 - (2 / 15 + reserve) + (1 / 2 : ℝ) =
            1 - (2 / 15 + reserve) by ring] at h
        exact h
  have hlambdaX : 4 * Real.rpow p.X (1 - (2 / 15 + reserve)) <
      |p.beta| * p.X := by
    have hm := mul_lt_mul_of_pos_right hfarone
      (Real.rpow_pos_of_pos hXposp
        (1 - (2 / 15 + reserve)))
    calc
      4 * Real.rpow p.X (1 - (2 / 15 + reserve)) <
          (|p.beta| * Real.rpow p.X (2 / 15 + reserve)) *
            Real.rpow p.X (1 - (2 / 15 + reserve)) := hm
      _ = |p.beta| * p.X := by
        calc
          _ = |p.beta| *
              (Real.rpow p.X (2 / 15 + reserve) *
                Real.rpow p.X (1 - (2 / 15 + reserve))) := by ring
          _ = _ := by rw [hpowE]
  have hrootBound : 4 * Real.sqrt ((Real.log p.X) ^ B) * Real.sqrt p.X <
      |p.beta| * p.X := by
    exact lt_of_le_of_lt (by nlinarith [hCcPow, hqroot]) hlambdaX
  have hsq : (4 * Real.sqrt ((Real.log p.X) ^ B) * Real.sqrt p.X) ^ 2 ≤
      (|p.beta| * p.X) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hrootBound.le
  have hsqExpand :
      (4 * Real.sqrt ((Real.log p.X) ^ B) * Real.sqrt p.X) ^ 2 =
      16 * (Real.log p.X) ^ B * p.X := by
    calc
      _ = 16 * (Real.sqrt ((Real.log p.X) ^ B)) ^ 2 *
          (Real.sqrt p.X) ^ 2 := by ring
      _ = 16 * (Real.log p.X) ^ B * p.X := by
        rw [Real.sq_sqrt hQpos.le, Real.sq_sqrt (by simpa only [hpX] using hXpos.le)]
  have hsq' : 16 * (Real.log p.X) ^ B * p.X ≤
      (|p.beta| * p.X) ^ 2 := by
    rw [hsqExpand] at hsq
    exact hsq
  have hRhoSq : 2 * p.X ≤
      (|p.beta| * p.X / (2 * Real.sqrt ((Real.log p.X) ^ B))) ^ 2 := by
    have hsqrtSq : (Real.sqrt ((Real.log p.X) ^ B)) ^ 2 =
        (Real.log p.X) ^ B := Real.sq_sqrt hQpos.le
    have hdenpow : (2 * Real.sqrt ((Real.log p.X) ^ B)) ^ 2 =
        4 * (Real.log p.X) ^ B := by
      calc
        _ = 4 * (Real.sqrt ((Real.log p.X) ^ B)) ^ 2 := by ring
        _ = _ := by rw [hsqrtSq]
    rw [div_pow, hdenpow]
    have hden : 0 < 4 * (Real.log p.X) ^ B := by positivity
    apply (le_div_iff₀ hden).2
    nlinarith only [hsq']
  have hQleT : (Real.log p.X) ^ B ≤
      2 * |p.beta| * p.X * Real.sqrt ((Real.log p.X) ^ B) := by
    have hrootOne : Real.sqrt ((Real.log p.X) ^ B) ≤
        Real.rpow p.X (1 - (2 / 15 + reserve)) :=
      hpolyHalf.trans hpowOne
    have hrootX : Real.sqrt ((Real.log p.X) ^ B) ≤ |p.beta| * p.X / 2 := by
      have hhalf : Real.rpow p.X (1 - (2 / 15 + reserve)) ≤
          |p.beta| * p.X / 2 := by linarith [hlambdaX]
      exact hrootOne.trans hhalf
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((Real.log p.X) ^ B) := Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hrootX hsqrt_nonneg
    calc
      (Real.log p.X) ^ B =
          Real.sqrt ((Real.log p.X) ^ B) * Real.sqrt ((Real.log p.X) ^ B) :=
        by simpa only [pow_two] using (Real.sq_sqrt hQpos.le).symm
      _ ≤ (|p.beta| * p.X / 2) * Real.sqrt ((Real.log p.X) ^ B) := hmul
      _ ≤ 2 * |p.beta| * p.X * Real.sqrt ((Real.log p.X) ^ B) := by
        have hnon : 0 ≤ |p.beta| * p.X :=
          mul_nonneg (abs_nonneg _) (by linarith)
        have hcoef : (1 / 2 : ℝ) ≤ 2 := by norm_num
        have hh := mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg hnon hsqrt_nonneg)
        nlinarith only [hh]
  have hqT : (p.q : ℝ) ≤
      2 * |p.beta| * X * Real.sqrt ((Real.log p.X) ^ B) := by
    have hqQ' : (p.q : ℝ) ≤ (Real.log p.X) ^ B := hqQ
    exact hqQ'.trans (by simpa only [hpX] using hQleT)
  have hQleTX : (Real.log X) ^ B ≤
      2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) := by
    simpa only [hpX] using hQleT
  have hqTX : (p.q : ℝ) ≤
      2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) :=
    (by have hqQX : (p.q : ℝ) ≤ (Real.log X) ^ B := by simpa only [hpX] using hqQ
        exact hqQX.trans hQleTX)
  have hTupperX : 2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) ≤ 2 * X := by
    simpa only [hpX] using hTupper
  have hPUraw := hPU_X |p.beta| reserve (abs_nonneg _)
    hr
  have hPU : |p.beta| * Real.rpow X (23 / 24 : ℝ) + |p.beta| * p.H ≤
      |p.beta| * X / (2 * Real.sqrt ((Real.log X) ^ B)) := by
    simpa [d12FreePerronHeight, d12InnerRadius, hH, hpX] using hPUraw
  have hLower : outerLower X p.beta (1 / Real.sqrt ((Real.log X) ^ B)) =
      2 * (|p.beta| * X / (2 * Real.sqrt ((Real.log X) ^ B))) :=
    outerLower_eq_two_rho_of_eta (by simpa [hpX] using hQpos)
  have hUpper : outerUpper X p.beta (1 / Real.sqrt ((Real.log X) ^ B)) =
      (2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B)) / 2 :=
    outerUpper_eq_T_half_of_eta (by simpa [hpX] using hQpos)
  have hOuter : 1 ≤ 2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) / 2 := by
    have houterP : |p.beta| * Real.rpow X (23 / 24 : ℝ) ≤
        2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) / 2 := by
      have hXpow : Real.rpow X (23 / 24 : ℝ) ≤ X := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (show 1 ≤ X by linarith)
            (by norm_num : (23 / 24 : ℝ) ≤ 1)
      have hsqrtQone : 1 ≤ Real.sqrt ((Real.log X) ^ B) :=
        Real.one_le_sqrt.2 (by simpa [hpX] using hQone)
      calc
        |p.beta| * Real.rpow X (23 / 24 : ℝ) ≤ |p.beta| * X :=
          mul_le_mul_of_nonneg_left hXpow (abs_nonneg _)
        _ ≤ |p.beta| * X * Real.sqrt ((Real.log X) ^ B) := by
          have hbase : X * |p.beta| * 1 ≤
              X * |p.beta| * Real.sqrt ((Real.log X) ^ B) :=
            mul_le_mul_of_nonneg_left hsqrtQone
              (mul_nonneg (by linarith) (abs_nonneg _))
          simpa only [mul_one, mul_comm, mul_left_comm, mul_assoc] using hbase
        _ = 2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) / 2 := by ring
    have hPoneX : 1 ≤ |p.beta| * Real.rpow X (23 / 24 : ℝ) := by
      simpa only [hpX] using hPone
    exact hPoneX.trans houterP
  have hTmom2 : 2 ≤ 2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) := by
    linarith only [hOuter]
  have hmoment := dynamicD12MomentRange_eightX hX1 hTmom2 hq0
    (by simpa only [hpX] using hB_X)
    (by
      have hlog8 : Real.log p.X ≤ Real.log (8 * X) := by
        apply Real.log_le_log
        · exact hXposp
        · nlinarith
      exact hqQ.trans (pow_le_pow_left₀ (by linarith [hlogp]) hlog8 B))
    hqTX
    (by
      calc
        2 * (2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B)) ≤ 4 * X := by
          have hh := mul_le_mul_of_nonneg_left hTupperX
            (by norm_num : (0 : ℝ) ≤ 2)
          nlinarith only [hh]
        _ ≤ 8 * X := by nlinarith [hX1])
  let Q : ℝ := (Real.log X) ^ B
  let eta : ℝ := 1 / Real.sqrt Q
  let U : ℝ := |p.beta| * p.H
  let P : ℝ := |p.beta| * Real.rpow X (23 / 24 : ℝ)
  let Tmom : ℝ := 2 * |p.beta| * X * Real.sqrt Q
  let rho : ℝ := |p.beta| * X / (2 * Real.sqrt Q)
  have heta0 : p.eta = eta := by simpa [eta, Q, hpX] using heta
  have hRhoT : |p.beta| * X / (2 * Real.sqrt ((Real.log X) ^ B)) ≤
      2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) := by
    apply (div_le_iff₀ (by positivity)).2
    have hs : (Real.sqrt ((Real.log X) ^ B)) ^ 2 =
        (Real.log X) ^ B := Real.sq_sqrt (by simpa [hpX] using hQpos.le)
    have hQoneX : 1 ≤ (Real.log X) ^ B := by simpa only [hpX] using hQone
    have hmul := mul_le_mul_of_nonneg_left hQoneX
      (mul_nonneg (abs_nonneg p.beta) (by linarith : 0 ≤ X))
    have hprod0 : 0 ≤ |p.beta| * X * (Real.log X) ^ B :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (by linarith)) (by positivity)
    have hRHS : 2 * |p.beta| * X * Real.sqrt ((Real.log X) ^ B) *
        (2 * Real.sqrt ((Real.log X) ^ B)) =
        4 * (|p.beta| * X * (Real.log X) ^ B) := by
      calc
        _ = 4 * (|p.beta| * X) *
            (Real.sqrt ((Real.log X) ^ B)) ^ 2 := by ring
        _ = _ := by rw [hs]; ring
    calc
      |p.beta| * X ≤ |p.beta| * X * (Real.log X) ^ B := by
        simpa only [mul_one] using hmul
      _ ≤ 4 * (|p.beta| * X * (Real.log X) ^ B) := by nlinarith
      _ = _ := hRHS.symm
  have hband : ∀ component : OuterComponent, ∀ t ∈ Set.Icc
      ((componentEndpoints X p.beta eta component).1 - (P + U))
      ((componentEndpoints X p.beta eta component).2 + (P + U)),
      rho ≤ |t| ∧ |t| ≤ Tmom := by
    intro component t ht
    refine enlarged_component_mem_rho_band (X := X) (beta := p.beta)
      (eta := eta) (P := P) (U := U) (T := Tmom) (rho := rho)
      (by linarith) (by positivity)
      (by
        dsimp [eta, Q]
        simpa only [one_div] using
          (inv_le_one_of_one_le₀
            ((Real.one_le_sqrt).2 (by simpa [hpX] using hQone))))
      (by exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith) _))
      (by exact mul_nonneg (abs_nonneg _) (by linarith))
      (by positivity) (by simpa [P, U, rho, Tmom, Q, heta0] using hPU)
      (by simpa [eta, rho, Q] using hLower)
      (by simpa [eta, rho, Tmom, Q] using hUpper)
      component
      (by simpa [P, U, rho, Tmom, Q, heta0] using ht)
  have hlength : ∀ component : OuterComponent,
      ((componentEndpoints X p.beta eta component).2 + (P + U)) -
        ((componentEndpoints X p.beta eta component).1 - (P + U)) + 1 ≤ Tmom := by
    intro component
    refine enlarged_length_succ_le_Tmoment (X := X) (beta := p.beta)
      (eta := eta) (P := P) (U := U) (T := Tmom) (rho := rho)
      (by linarith) (by positivity)
      (by simpa [P, U, rho, Tmom, Q, heta0] using hPU)
      (by simpa [eta, rho, Q] using hLower)
      (by simpa [eta, rho, Tmom, Q] using hUpper)
      (by
        rw [hUpper]
        exact hOuter)
      component
  refine ⟨{
    Q := Q, eta := eta, U := U, P := P, Tmom := Tmom, rho := rho,
    hX := hX1, hpX := hpX, hpeta := heta0, hQ := by rfl,
    hQone := by simpa [Q, hpX] using hQone,
    heta := by rfl, hU := by rfl, hP := by rfl, hTmom := by rfl,
    hrho := by rfl, hPone := by simpa [P, hpX] using hPone,
    hrho_pos := by dsimp [rho, Q]; positivity,
    hrhoT := by simpa [rho, Tmom, Q, hpX] using hRhoT,
    hXrho := by simpa [rho, Q, hpX] using hRhoSq,
    hmoment := by simpa [Tmom, Q, hpX] using hmoment,
    hPU := by simpa [P, U, rho, Q, hpX] using hPU,
    hband := hband, hlength := hlength }⟩

end
end MRTDynamicD12ParameterPackage

#print axioms MRTDynamicD12ParameterPackage.exists_d12_parameter_package
