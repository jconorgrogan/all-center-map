import MRTDynamicD12CanonicalSourceLedger
import MRTDynamicD12ModulusSavings
import MRTDynamicD12LogEnvelope
import MRTDynamicD12NormalizedAlgebra
import MRTProposition61TypeIIActiveCellBudgetV3
import MRTProposition61TypeIIEndpointWidthV3

/-!
# Literal scalar envelope for the canonical D12 source ledger

This is the algebraic consumer of the raw Perron ledger.  Its hypotheses are
the canonical parameter identities and the literal divisor/coefficient
bounds; no pre-packaged main or error estimate is accepted as an input.
-/

namespace MRTDynamicD12CanonicalScalarEnvelope

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPMRTCorollary25Minkowski
open MRTDynamicD12CanonicalSourceLedger
open MRTDynamicD12ParameterPackage
open MRTDynamicD12ModulusSavings
open MRTDynamicD12LogEnvelope
open MRTDynamicD12NormalizedAlgebra
open MRTProposition61TypeIIActiveCellBudgetV3
open MRTProposition61TypeIIEndpointWidthV3

noncomputable section

set_option maxHeartbeats 3000000

theorem normalized_rawLedger_le_three_terms
    {p : Corollary53Input} [NeZero p.q]
    {X Q lambda H U P T D4 Cd D Bcoeff kappa Cm : ℝ}
    {Y : ℕ} {reserve delta : ℝ} {Em : ℕ}
    (hpX : p.X = X) (hX : 3 ≤ X) (hlog : 1 ≤ Real.log X)
    (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (hbeta : |p.beta| = lambda) (hlambda : 0 < lambda)
    (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
    (hreserve0 : 0 ≤ reserve) (hreserve : reserve ≤ 1 / 1200)
    (hUstat : U = stationaryWidth p.beta p.H)
    (hUlambda : U = lambda * H) (hHid : H = p.H)
    (hUone : 1 ≤ U) (heta : p.eta = 1 / Real.sqrt Q)
    (hP : P = lambda * Real.rpow X (23 / 24 : ℝ))
    (hT : T = 2 * lambda * X * Real.sqrt Q)
    (hPone : 1 ≤ P) (hP_le_X : P ≤ X)
    (hBcoeff : Bcoeff = D * Real.rpow X (1 / 1000 : ℝ))
    (hD : 0 < D) (hkappa : 0 < kappa) (hCm : 0 < Cm)
    (hD4 : 0 ≤ D4) (hCd : 0 ≤ Cd)
    (hlambdaCap : lambda ≤ 1 / ((p.q : ℝ) * Q))
    (hD4bound : D4 ≤ Cd * Real.rpow (p.q : ℝ) (1 / 8 : ℝ))
    (hY : (Y : ℝ) ≤ 2 * X) (component : OuterComponent)
    (hDelta0 : 0 ≤ (componentEndpoints p.X p.beta p.eta component).2 -
      (componentEndpoints p.X p.beta p.eta component).1)
    (hDelta : (componentEndpoints p.X p.beta p.eta component).2 -
      (componentEndpoints p.X p.beta p.eta component).1 ≤
      lambda * X * Real.sqrt Q)
    (hXdeltaH : Real.rpow X delta / H ≤
      2 * Real.rpow X (delta - 2 / 15 : ℝ))
    (hHupper : H ≤ (1 / 2 : ℝ) * Real.rpow X (2 / 15 + 1 / 1200 : ℝ)) :
    D4 / ((p.q : ℝ) * U ^ 2) *
        rawLedger p P T Bcoeff Y delta kappa Cm Em component ≤
      (288 * kappa ^ 2 * Cm * Cd * 5 ^ Em +
          72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em + 1) *
        Real.log X ^ (Em + 2) *
          (X * Real.rpow Q (-3 / 8 : ℝ) +
            Real.rpow X (1 + delta - 2 / 15) * Real.rpow Q (5 / 8 : ℝ) +
            Real.rpow X (439 / 2000 : ℝ) * Real.rpow Q (13 / 8 : ℝ)) := by
  let I : ℝ := ∫ u in (-P)..P, perronWeight u
  let L : ℝ := 1 + Real.log (8 * X)
  let W : ℝ :=
    (componentEndpoints p.X p.beta p.eta component).2 -
      (componentEndpoints p.X p.beta p.eta component).1
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hQ0 : 0 < Q := by linarith
  have hq0 : 0 < (p.q : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.q)))
  have hq1 : 1 ≤ (p.q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.q))
  have hH0 : 0 < H := by
    rw [hHid]
    rw [hH, hpX]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have hU0 : 0 < U := by rw [hUlambda]; exact mul_pos hlambda hH0
  have hP0 : 0 < P := by
    rw [hP]
    exact mul_pos hlambda (Real.rpow_pos_of_pos hX0 _)
  have hlog0 : 0 ≤ Real.log X := by linarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have : 0 ≤ Real.log (8 * X) := Real.log_nonneg (by linarith)
    linarith
  have hIlog : I ^ 2 ≤ 36 * Real.log X ^ 2 := by
    dsimp [I]
    exact (perron_logs_sq_le hX hlog (by linarith) hP_le_X).1
  have hLlog : L ^ Em ≤ 5 ^ Em * Real.log X ^ Em := by
    dsimp [L]
    exact moment_log_pow_le hX hlog Em
  have hJ : (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) ≤ (p.q : ℝ) :=
    dirichletCharacter_card_le p.q (by exact_mod_cast hq0)
  have hJ0 : 0 ≤ (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) := by positivity
  have hBcoeff0 : 0 ≤ Bcoeff := by
    rw [hBcoeff]
    exact mul_nonneg hD.le (Real.rpow_nonneg hX0.le _)
  have hY0 : 0 ≤ (Y : ℝ) := by positivity
  have hD40 : 0 ≤ D4 := hD4
  have hD4mod := modulus_savings_of_d4_bound
    (X := X) (Q := Q) (q := (p.q : ℝ)) (lambda := lambda) (H := H)
    hX0 hQ0 hq1 hlambda hH0 hqQ hlambdaCap hD4 hCd hD4bound
  have hmainEq :
      D4 / ((p.q : ℝ) * U ^ 2) *
          (2 * kappa ^ 2 *
            (I ^ 2 *
              (Cm * ((p.q : ℝ) * U + Real.rpow X delta) * U *
                ((p.q : ℝ) * T) * L ^ Em))) =
        4 * kappa ^ 2 * Cm * D4 * I ^ 2 * X * Real.sqrt Q *
          ((p.q : ℝ) * lambda + Real.rpow X delta / H) * L ^ Em := by
    have hh := normalized_d12_main_identity D4 kappa Cm I
      (p.q : ℝ) lambda U H X Q delta L Em hq0 hlambda hH0 hUlambda
      (by rfl)
    simpa [I, L, Real.rpow_eq_pow, mul_assoc, mul_comm, mul_left_comm,
      hT, hHid] using hh
  have hmain :
      D4 / ((p.q : ℝ) * U ^ 2) *
          (2 * kappa ^ 2 *
            (I ^ 2 *
              (Cm * ((p.q : ℝ) * U + Real.rpow X delta) * U *
                ((p.q : ℝ) * T) * L ^ Em))) ≤
        144 * kappa ^ 2 * Cm * D4 * X * Real.sqrt Q *
          ((p.q : ℝ) * lambda + Real.rpow X delta / H) *
            Real.log X ^ 2 * L ^ Em := by
    rw [hmainEq]
    have hterm : 0 ≤ (p.q : ℝ) * lambda + Real.rpow X delta / H := by
      exact add_nonneg (mul_nonneg hq0.le hlambda.le)
        (div_nonneg (Real.rpow_nonneg hX0.le _) hH0.le)
    have hc : 0 ≤ 4 * kappa ^ 2 * Cm * D4 * X * Real.sqrt Q *
        ((p.q : ℝ) * lambda + Real.rpow X delta / H) * L ^ Em := by
      positivity
    have hi := mul_le_mul_of_nonneg_right hIlog (by positivity : 0 ≤
      4 * kappa ^ 2 * Cm * D4 * X * Real.sqrt Q *
        ((p.q : ℝ) * lambda + Real.rpow X delta / H) * L ^ Em)
    calc
      _ ≤ 4 * kappa ^ 2 * Cm * D4 * X * Real.sqrt Q *
          ((p.q : ℝ) * lambda + Real.rpow X delta / H) * L ^ Em *
          (36 * Real.log X ^ 2) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hi
      _ = _ := by ring
  have hmain' :
      D4 / ((p.q : ℝ) * U ^ 2) *
          (2 * kappa ^ 2 *
            (I ^ 2 *
              (Cm * ((p.q : ℝ) * U + Real.rpow X delta) * U *
                ((p.q : ℝ) * T) * L ^ Em))) ≤
        288 * kappa ^ 2 * Cm * Cd * 5 ^ Em * Real.log X ^ (Em + 2) *
          (X * Real.rpow Q (-3 / 8 : ℝ) +
            Real.rpow X (1 + delta - 2 / 15) * Real.rpow Q (5 / 8 : ℝ)) := by
    have hpowdelta :
        Real.rpow X delta / H ≤ 2 * Real.rpow X (delta - 2 / 15 : ℝ) :=
      hXdeltaH
    obtain ⟨hm1, hm2, hm3⟩ := hD4mod
    have hsum :
        D4 * Real.sqrt Q * ((p.q : ℝ) * lambda + Real.rpow X delta / H) ≤
          Cd * Real.rpow Q (-3 / 8 : ℝ) +
            2 * Cd * Real.rpow X (delta - 2 / 15 : ℝ) *
              Real.rpow Q (5 / 8 : ℝ) := by
      calc
        _ = D4 * Real.sqrt Q * ((p.q : ℝ) * lambda) +
            D4 * Real.sqrt Q * (Real.rpow X delta / H) := by ring
        _ ≤ Cd * Real.rpow Q (-3 / 8 : ℝ) +
            2 * Cd * Real.rpow X (delta - 2 / 15 : ℝ) *
              Real.rpow Q (5 / 8 : ℝ) := by
          apply add_le_add hm1
          have hpart := mul_le_mul_of_nonneg_left hpowdelta
            (mul_nonneg hD4 (Real.sqrt_nonneg Q))
          have hmult : 0 ≤ (2 : ℝ) * Real.rpow X
              (delta - 2 / 15 : ℝ) :=
            mul_nonneg (by norm_num)
              (Real.rpow_nonneg hX0.le (delta - 2 / 15 : ℝ))
          have hpart' := mul_le_mul_of_nonneg_right hm2 hmult
          calc
            D4 * Real.sqrt Q * (Real.rpow X delta / H) ≤
                D4 * Real.sqrt Q * (2 * Real.rpow X
                  (delta - 2 / 15 : ℝ)) := by
              simpa [mul_assoc] using hpart
            _ ≤ Cd * Real.rpow Q (5 / 8 : ℝ) *
                (2 * Real.rpow X (delta - 2 / 15 : ℝ)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hpart'
            _ = _ := by ring
    calc
      _ ≤ 144 * kappa ^ 2 * Cm * X * Real.log X ^ 2 * L ^ Em *
          (Cd * Real.rpow Q (-3 / 8 : ℝ) +
            2 * Cd * Real.rpow X (delta - 2 / 15 : ℝ) *
              Real.rpow Q (5 / 8 : ℝ)) := by
        apply hmain.trans
        have hh := mul_le_mul_of_nonneg_left hsum
          (by positivity : 0 ≤ 144 * kappa ^ 2 * Cm * X *
            Real.log X ^ 2 * L ^ Em)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ 288 * kappa ^ 2 * Cm * Cd * 5 ^ Em * Real.log X ^ (Em + 2) *
          (X * Real.rpow Q (-3 / 8 : ℝ) +
            Real.rpow X (1 + delta - 2 / 15) * Real.rpow Q (5 / 8 : ℝ)) := by
        have hxpow : Real.rpow X (1 + delta - 2 / 15 : ℝ) =
            X * Real.rpow X (delta - 2 / 15 : ℝ) := by
          have hadd := Real.rpow_add hX0 (1 : ℝ)
            (delta - 2 / 15 : ℝ)
          have hone : Real.rpow X (1 : ℝ) = X := by
            simpa only [Real.rpow_eq_pow] using (Real.rpow_one X)
          calc
            _ = Real.rpow X (1 : ℝ) * Real.rpow X
                (delta - 2 / 15 : ℝ) := by
              convert hadd using 1 <;> simp only [Real.rpow_eq_pow] <;> ring
            _ = _ := by rw [hone]
        have hfac : Real.log X ^ 2 * L ^ Em ≤
            5 ^ Em * Real.log X ^ (Em + 2) := by
          have hh := mul_le_mul_of_nonneg_left hLlog
            (by positivity : 0 ≤ Real.log X ^ 2)
          have hadd : Real.log X ^ 2 * Real.log X ^ Em =
              Real.log X ^ (Em + 2) := by
            rw [← pow_add]
            congr 1 <;> omega
          calc
            _ ≤ Real.log X ^ 2 * (5 ^ Em * Real.log X ^ Em) := hh
            _ = 5 ^ Em * Real.log X ^ (Em + 2) := by rw [← hadd]; ring
        have hmult : 0 ≤ Cd * Real.rpow Q (-3 / 8 : ℝ) +
            2 * Cd * Real.rpow X (delta - 2 / 15 : ℝ) *
              Real.rpow Q (5 / 8 : ℝ) := by
          have hc2 : 0 ≤ (2 : ℝ) * Cd := mul_nonneg (by norm_num) hCd
          have hx2 : 0 ≤ Real.rpow X (delta - 2 / 15 : ℝ) :=
            Real.rpow_nonneg hX0.le _
          exact add_nonneg
            (mul_nonneg hCd (Real.rpow_nonneg hQ0.le _))
            (mul_nonneg (mul_nonneg hc2 hx2)
              (Real.rpow_nonneg hQ0.le _))
        have hmult2 : 0 ≤ 144 * kappa ^ 2 * Cm * X *
            (Cd * Real.rpow Q (-3 / 8 : ℝ) +
              2 * Cd * Real.rpow X (delta - 2 / 15 : ℝ) *
                Real.rpow Q (5 / 8 : ℝ)) :=
          mul_nonneg (by positivity) hmult
        have hh := mul_le_mul_of_nonneg_right hfac hmult2
        calc
          _ ≤ 144 * kappa ^ 2 * Cm * X *
              (5 ^ Em * Real.log X ^ (Em + 2)) *
              (Cd * Real.rpow Q (-3 / 8 : ℝ) +
                2 * Cd * Real.rpow X (delta - 2 / 15 : ℝ) *
                  Real.rpow Q (5 / 8 : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hh
          _ = 144 * kappa ^ 2 * Cm * Cd * 5 ^ Em *
              Real.log X ^ (Em + 2) *
              (X * Real.rpow Q (-3 / 8 : ℝ) +
                2 * X * Real.rpow X (delta - 2 / 15 : ℝ) *
                  Real.rpow Q (5 / 8 : ℝ)) := by ring
          _ ≤ _ := by
            rw [hxpow]
            have hcoef : 0 ≤ 144 * kappa ^ 2 * Cm * Cd * 5 ^ Em *
                Real.log X ^ (Em + 2) := by positivity
            have hA : 0 ≤ X * Real.rpow Q (-3 / 8 : ℝ) := by
              exact mul_nonneg hX0.le (Real.rpow_nonneg hQ0.le _)
            have hB : 0 ≤ X * Real.rpow X (delta - 2 / 15 : ℝ) *
                Real.rpow Q (5 / 8 : ℝ) := by
              exact mul_nonneg (mul_nonneg hX0.le
                (Real.rpow_nonneg hX0.le _)) (Real.rpow_nonneg hQ0.le _)
            nlinarith
  have herr := normalized_d12_error_bound_ordered
    (D4 := D4) (kappa := kappa) (D := D) (q := (p.q : ℝ))
      (lambda := lambda) (U := U) (H := H) (X := X) (Q := Q)
      (Delta := W) (P := P) (Bcoeff := Bcoeff) (Y := (Y : ℝ))
      (J := (Fintype.card (DirichletCharacter ℂ p.q) : ℝ))
      (epsilon := (1 / 1000 : ℝ)) hD4 (by positivity) hD.le hq0 hlambda
      hUlambda hH0 hX0 hQ0.le hDelta0 hDelta hJ hJ0
      (by simpa only [Real.rpow_eq_pow] using (le_of_eq hBcoeff))
        hBcoeff0 hY hY0 hP hP0
      (Real.log_nonneg (by linarith [hP0]))
  have herr' :
      D4 / ((p.q : ℝ) * U ^ 2) *
          (2 * kappa ^ 2 * W *
            (2 * U * (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
              (Bcoeff * Real.sqrt (Y : ℝ) * Real.log (2 + P) / P)) ^ 2) ≤
        72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em * Real.log X ^ (Em + 2) *
          (Real.rpow X (439 / 2000 : ℝ) * Real.rpow Q (13 / 8 : ℝ)) := by
    obtain ⟨_, _, hm3⟩ := hD4mod
    calc
      _ ≤ 16 * D4 * kappa ^ 2 * D ^ 2 * (p.q : ℝ) * Real.sqrt Q *
          (H / U) * Real.log (2 + P) ^ 2 *
            Real.rpow X (1 / 12 + 2 / 1000 : ℝ) := by
        have hcore :
            2 * U * (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
                (Bcoeff * Real.sqrt (Y : ℝ) * Real.log (2 + P) / P) =
              2 * U * (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
                Bcoeff * Real.sqrt (Y : ℝ) * Real.log (2 + P) / P := by
          ring
        rw [hcore]
        convert herr using 1 <;> norm_num
      _ ≤ 16 * D4 * kappa ^ 2 * D ^ 2 * (p.q : ℝ) * Real.sqrt Q *
          H * (9 * Real.log X ^ 2) *
            Real.rpow X (1 / 12 + 2 / 1000 : ℝ) := by
        have hHU : H / U ≤ H := by
          apply (div_le_iff₀ hU0).2
          nlinarith [mul_le_mul_of_nonneg_left hUone hH0.le]
        have hlogs := (perron_logs_sq_le hX hlog (by linarith) hP_le_X).2
        have hlogP : 0 ≤ Real.log (2 + P) := Real.log_nonneg (by linarith)
        have hXpowerr : 0 ≤ Real.rpow X (1 / 12 + 2 / 1000 : ℝ) :=
          Real.rpow_nonneg hX0.le _
        gcongr
        all_goals try positivity
      _ ≤ 72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em * Real.log X ^ (Em + 2) *
          (Real.rpow X (439 / 2000 : ℝ) * Real.rpow Q (13 / 8 : ℝ)) := by
        have hxH : H * Real.rpow X (1 / 12 + 2 / 1000 : ℝ) ≤
            (1 / 2 : ℝ) * Real.rpow X (439 / 2000 : ℝ) := by
          have hpow := mul_le_mul_of_nonneg_right hHupper
            (Real.rpow_nonneg hX0.le (1 / 12 + 2 / 1000 : ℝ))
          have hadd : Real.rpow X (2 / 15 + 1 / 1200 : ℝ) *
              Real.rpow X (1 / 12 + 2 / 1000 : ℝ) =
              Real.rpow X (439 / 2000 : ℝ) := by
            calc
              _ = Real.rpow X ((2 / 15 + 1 / 1200 : ℝ) +
                  (1 / 12 + 2 / 1000 : ℝ)) :=
                (Real.rpow_add hX0 _ _).symm
              _ = _ := by congr 1 <;> norm_num
          calc
            _ ≤ (1 / 2 : ℝ) * Real.rpow X
                (2 / 15 + 1 / 1200 : ℝ) *
                Real.rpow X (1 / 12 + 2 / 1000 : ℝ) := hpow
            _ = (1 / 2 : ℝ) *
                (Real.rpow X (2 / 15 + 1 / 1200 : ℝ) *
                  Real.rpow X (1 / 12 + 2 / 1000 : ℝ)) := by ring
            _ = _ := by rw [hadd]
        have hlogpow : Real.log X ^ 2 ≤ Real.log X ^ (Em + 2) := by
          exact pow_le_pow_right₀ (by linarith [hlog]) (by omega)
        have hcomb :
            D4 * (p.q : ℝ) * Real.sqrt Q * H *
                Real.log X ^ 2 * Real.rpow X (1 / 12 + 2 / 1000 : ℝ) ≤
              (1 / 2 : ℝ) * Cd * Real.rpow Q (13 / 8 : ℝ) *
                Real.rpow X (439 / 2000 : ℝ) *
                Real.log X ^ (Em + 2) := by
          have hmult1 : 0 ≤ H * Real.rpow X (1 / 12 + 2 / 1000 : ℝ) *
              Real.log X ^ 2 :=
            mul_nonneg
              (mul_nonneg hH0.le
                (Real.rpow_nonneg hX0.le (1 / 12 + 2 / 1000 : ℝ)))
              (sq_nonneg _)
          have h1 := mul_le_mul_of_nonneg_right hm3 hmult1
          have hmult2 : 0 ≤ Cd * Real.rpow Q (13 / 8 : ℝ) :=
            mul_nonneg hCd (Real.rpow_nonneg hQ0.le _)
          have hmult2log : 0 ≤ Cd * Real.rpow Q (13 / 8 : ℝ) *
              Real.log X ^ 2 :=
            mul_nonneg hmult2 (sq_nonneg _)
          have h2 := mul_le_mul_of_nonneg_left hxH hmult2log
          have hmult3 : 0 ≤ Cd * Real.rpow Q (13 / 8 : ℝ) *
              ((1 / 2 : ℝ) * Real.rpow X (439 / 2000 : ℝ)) := by
            exact mul_nonneg hmult2
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hX0.le _))
          have h3 := mul_le_mul_of_nonneg_left hlogpow hmult3
          calc
            _ ≤ Cd * Real.rpow Q (13 / 8 : ℝ) * H *
                Real.log X ^ 2 * Real.rpow X (1 / 12 + 2 / 1000 : ℝ) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using h1
            _ ≤ Cd * Real.rpow Q (13 / 8 : ℝ) *
                ((1 / 2 : ℝ) * Real.rpow X (439 / 2000 : ℝ)) *
                Real.log X ^ 2 := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using h2
            _ ≤ Cd * Real.rpow Q (13 / 8 : ℝ) *
                ((1 / 2 : ℝ) * Real.rpow X (439 / 2000 : ℝ)) *
                Real.log X ^ (Em + 2) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using h3
            _ = _ := by ring
        have hcoef : 0 ≤ 16 * 9 * kappa ^ 2 * D ^ 2 := by positivity
        have hfinal := mul_le_mul_of_nonneg_left hcomb hcoef
        calc
          _ ≤ 16 * 9 * kappa ^ 2 * D ^ 2 *
              ((1 / 2 : ℝ) * Cd * Real.rpow Q (13 / 8 : ℝ) *
                Real.rpow X (439 / 2000 : ℝ) * Real.log X ^ (Em + 2)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hfinal
          _ ≤ _ := by
            have h5 : (1 : ℝ) ≤ 5 ^ Em := by
              exact one_le_pow₀ (by norm_num)
            have hbase : 0 ≤ 72 * kappa ^ 2 * D ^ 2 * Cd *
                Real.log X ^ (Em + 2) *
                (Real.rpow X (439 / 2000 : ℝ) *
                  Real.rpow Q (13 / 8 : ℝ)) := by
              have hk2 : 0 ≤ kappa ^ 2 := sq_nonneg kappa
              have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
              have hlogpow : 0 ≤ Real.log X ^ (Em + 2) := by positivity
              exact mul_nonneg
                (mul_nonneg
                  (mul_nonneg
                    (mul_nonneg
                      (mul_nonneg (by norm_num) hk2) hD2) hCd)
                    hlogpow)
                (mul_nonneg (Real.rpow_nonneg hX0.le _)
                  (Real.rpow_nonneg hQ0.le _))
            have hh := mul_le_mul_of_nonneg_right h5 hbase
            convert hh using 1 <;> ring
  have hsum := add_le_add hmain' herr'
  have hconst1 : 0 ≤ 288 * kappa ^ 2 * Cm * Cd * 5 ^ Em := by positivity
  have hconst2 : 0 ≤ 72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em := by positivity
  calc
    D4 / ((p.q : ℝ) * U ^ 2) * rawLedger p P T Bcoeff Y delta kappa Cm Em component =
        D4 / ((p.q : ℝ) * U ^ 2) *
          (2 * kappa ^ 2 *
            (I ^ 2 *
              (Cm * ((p.q : ℝ) * U + Real.rpow X delta) * U *
                ((p.q : ℝ) * T) * L ^ Em)) +
            2 * kappa ^ 2 * W *
              (2 * U * (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
                (Bcoeff * Real.sqrt (Y : ℝ) * Real.log (2 + P) / P)) ^ 2) := by
          simp only [rawLedger, I, L, W, hpX, ← hUstat]
          ring
    _ ≤ 288 * kappa ^ 2 * Cm * Cd * 5 ^ Em * Real.log X ^ (Em + 2) *
          (X * Real.rpow Q (-3 / 8 : ℝ) +
            Real.rpow X (1 + delta - 2 / 15) * Real.rpow Q (5 / 8 : ℝ)) +
          72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em * Real.log X ^ (Em + 2) *
            (Real.rpow X (439 / 2000 : ℝ) * Real.rpow Q (13 / 8 : ℝ)) := by
          simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum
    _ ≤ (288 * kappa ^ 2 * Cm * Cd * 5 ^ Em +
          72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em + 1) *
        Real.log X ^ (Em + 2) *
          (X * Real.rpow Q (-3 / 8 : ℝ) +
            Real.rpow X (1 + delta - 2 / 15) * Real.rpow Q (5 / 8 : ℝ) +
        Real.rpow X (439 / 2000 : ℝ) * Real.rpow Q (13 / 8 : ℝ)) := by
          let A : ℝ := X * Real.rpow Q (-3 / 8 : ℝ) +
              Real.rpow X (1 + delta - 2 / 15) * Real.rpow Q (5 / 8 : ℝ)
          let B : ℝ := Real.rpow X (439 / 2000 : ℝ) *
              Real.rpow Q (13 / 8 : ℝ)
          have hA : 0 ≤ A := by
            dsimp [A]
            exact add_nonneg
              (mul_nonneg hX0.le (Real.rpow_nonneg hQ0.le _))
              (mul_nonneg (Real.rpow_nonneg hX0.le _)
                (Real.rpow_nonneg hQ0.le _))
          have hB : 0 ≤ B := by
            dsimp [B]
            exact mul_nonneg (Real.rpow_nonneg hX0.le _)
              (Real.rpow_nonneg hQ0.le _)
          have hlogpow : 0 ≤ Real.log X ^ (Em + 2) := by positivity
          have hcA : 0 ≤ 288 * kappa ^ 2 * Cm * Cd * 5 ^ Em *
              Real.log X ^ (Em + 2) * A :=
            mul_nonneg (mul_nonneg hconst1 hlogpow) hA
          have hcB : 0 ≤ 72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em *
              Real.log X ^ (Em + 2) * B :=
            mul_nonneg (mul_nonneg hconst2 hlogpow) hB
          have hxA : 0 ≤ Real.log X ^ (Em + 2) * A :=
            mul_nonneg hlogpow hA
          have hxB : 0 ≤ Real.log X ^ (Em + 2) * B :=
            mul_nonneg hlogpow hB
          have hc2A : 0 ≤ 72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em *
              Real.log X ^ (Em + 2) * A := by positivity
          have hc1B : 0 ≤ 288 * kappa ^ 2 * Cm * Cd * 5 ^ Em *
              Real.log X ^ (Em + 2) * B := by positivity
          have hlogA : 0 ≤ Real.log X ^ (Em + 2) * A := hxA
          have hlogB : 0 ≤ Real.log X ^ (Em + 2) * B := hxB
          dsimp [A, B] at *
          nlinarith

end
end MRTDynamicD12CanonicalScalarEnvelope

#print axioms MRTDynamicD12CanonicalScalarEnvelope.normalized_rawLedger_le_three_terms
