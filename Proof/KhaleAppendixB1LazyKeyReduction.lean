import KhaleAppendixB1PenultimateReduction
import KhaleAppendixBEtaAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# From Khale's `(lazykey)` estimate to the penultimate display

The remaining proposition is the post-zeta form of equation `(lazykey)`.  This
file certifies the tight scale algebra, startup absorption, and decimal
rounding leading to the penultimate display.
-/

namespace MAPKhaleAppendixB1LazyKeyReduction

open MAPKhaleAppendixBSource MAPKhaleAppendixB1PenultimateReduction
open MAPKhaleAppendixBEtaAlgebra MAPKhaleAppendixBNumericalCore

noncomputable section

/-- Equation `(lazykey)` after applying the displayed zeta bound `(lazyzeta)`.
All constants and the source choice of `eta` are literal. -/
abbrev AppendixBLazyKeyAfterZetaEstimate : Prop :=
  ∀ (A B T₀ : ℝ),
    0 < A → 0 < B → B ≤ 4.45 →
    FordHurwitzEquation12 A B →
    Real.exp 10650 ≤ T₀ →
    5110.6 / B ≤ Real.log T₀ / Real.log (Real.log T₀) →
    183 / B ^ 2 ≤ Real.log (Real.log T₀) →
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (gamma beta : ℝ),
      3 ≤ q → T₀ ≤ gamma →
      Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ gamma →
      1 - beta ≤ 1 /
        (18 * Real.log q + appendixBHeightCoefficient A T₀ *
          Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) →
      DirichletCharacter.LFunction chi
          ((beta : ℂ) + (gamma : ℂ) * Complex.I) = 0 →
      beta < 1 ∧
      let eta := khaleEta B gamma
      0.953 / (1 - beta) ≤
        (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        (10.01055 / 2) * (1 / eta) * Real.log (1 / eta) +
        0.3 * 10.01055 +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937)

private theorem log_B_over_C_le
    {B : ℝ} (hB : 0 < B) (hBtop : B ≤ 4.45) :
    Real.log (B / (4 / 3 : ℝ)) ≤ Real.log (3.3375 : ℝ) := by
  apply Real.log_le_log (div_pos hB (by norm_num))
  norm_num
  linarith

private theorem correction_coefficient_le
    {A B gamma : ℝ} (hA : 0 < A) (hB : 0 < B) (hBtop : B ≤ 4.45)
    (hell : 1 ≤ Real.log (Real.log gamma)) :
    sourceScale *
          ((33.3275 / 2) * Real.log (A + 1) +
            (10.01055 / 3) *
              (Real.log (B / (4 / 3 : ℝ)) -
                Real.log (Real.log (Real.log gamma)))) +
        0.010122 ≤
      -2.7545 * Real.log (Real.log (Real.log gamma)) +
        13.75563 * Real.log (A + 1) + 3.33 := by
  have hlogA : 0 ≤ Real.log (A + 1) := (Real.log_pos (by linarith)).le
  have hlog3 : 0 ≤ Real.log (Real.log (Real.log gamma)) :=
    Real.log_nonneg hell
  have hk0 : 0 ≤ sourceScale := Real.rpow_nonneg (by norm_num) _
  have hlogBC := log_B_over_C_le hB hBtop
  have hlog3375 : 0 ≤ Real.log (3.3375 : ℝ) := Real.log_nonneg (by norm_num)
  have hAterm : sourceScale * (33.3275 / 2) * Real.log (A + 1) ≤
      13.75563 * Real.log (A + 1) :=
    mul_le_mul_of_nonneg_right sourceScale_logA_coefficient hlogA
  have hnegterm :
      -(sourceScale * (10.01055 / 3)) *
          Real.log (Real.log (Real.log gamma)) ≤
        -2.7545 * Real.log (Real.log (Real.log gamma)) := by
    have := sourceScale_log3_coefficient
    nlinarith
  have hconst : sourceScale * (10.01055 / 3) *
        Real.log (B / (4 / 3 : ℝ)) + 0.010122 ≤ 3.33 := by
    calc
      sourceScale * (10.01055 / 3) *
            Real.log (B / (4 / 3 : ℝ)) + 0.010122 ≤
          sourceScale * (10.01055 / 3) * Real.log 3.3375 + 0.010122 := by
        gcongr
      _ ≤ 3.33 := sourceScale_constant_coefficient
  nlinarith

/-- The exact deterministic passage from `(lazykey)+(lazyzeta)` to Khale's
penultimate reciprocal display. -/
theorem penultimateEstimate_of_lazyKeyAfterZeta
    (hLazy : AppendixBLazyKeyAfterZetaEstimate) :
    AppendixBPenultimateZeroEstimate := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hlazy := hLazy A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  refine ⟨hlazy.1, ?_⟩
  let L : ℝ := Real.log gamma
  let ell : ℝ := Real.log (Real.log gamma)
  let eta : ℝ := khaleEta B gamma
  let R : ℝ := Real.rpow (L / ell) (2 / 3 : ℝ)
  let BP : ℝ := Real.rpow B (2 / 3 : ℝ)
  let M : ℝ := BP * R
  let P : ℝ := BP * Real.rpow L (2 / 3 : ℝ) * Real.rpow ell (1 / 3 : ℝ)
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma0
  have hLlower : (10650 : ℝ) ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma0
  have hL : 0 < L := by linarith
  have hellLower : Real.log 10650 ≤ ell := by
    dsimp [ell, L]
    exact Real.log_le_log (by norm_num) hLlower
  have hellOne : 1 ≤ ell := by
    have : (1 : ℝ) < Real.log 10650 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10650)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    exact this.le.trans hellLower
  have hell : 0 < ell := zero_lt_one.trans_le hellOne
  have hRpos : 0 < R := Real.rpow_pos_of_pos (div_pos hL hell) _
  have hBPpos : 0 < BP := Real.rpow_pos_of_pos hB _
  have hMpos : 0 < M := mul_pos hBPpos hRpos
  have hPpos : 0 < P := by
    dsimp [P]
    exact mul_pos (mul_pos hBPpos (Real.rpow_pos_of_pos hL _))
      (Real.rpow_pos_of_pos hell _)
  have hinvEta : 1 / eta = sourceScale * M := by
    have h := one_div_khaleEta hB (by simpa only [L] using hL)
      (by simpa only [ell] using hell)
    simpa only [eta, khaleInvEtaScale, M, BP, R, L, ell, mul_assoc] using h
  have hetaPow : B * Real.rpow eta (3 / 2 : ℝ) * L = (4 / 3 : ℝ) * ell := by
    simpa only [eta, L, ell] using
      B_mul_eta_three_halves_mul_log hB
        (by simpa only [L] using hL) (by simpa only [ell] using hell)
  have hlogEta : Real.log (1 / eta) = (2 / 3 : ℝ) *
      (ell - Real.log ell + Real.log (B / (4 / 3 : ℝ))) := by
    simpa only [eta, L, ell] using
      log_one_div_khaleEta hB (by simpa only [L] using hL)
        (by simpa only [ell] using hell)
  have hMell : M * ell = P := by
    have hratio := ratio_two_thirds_mul_loglog
      (by simpa only [L] using hL) (by simpa only [ell] using hell)
    have hratio' : R * ell =
        Real.rpow L (2 / 3 : ℝ) * Real.rpow ell (1 / 3 : ℝ) := by
      simpa only [R, L, ell] using hratio
    calc
      M * ell = BP * (R * ell) := by dsimp [M]; ring
      _ = BP * (Real.rpow L (2 / 3 : ℝ) * Real.rpow ell (1 / 3 : ℝ)) := by
        rw [hratio']
      _ = P := by dsimp [P]; ring
  have hratioT : 5110.6 / B ≤ L / ell := by
    have hlogT : Real.log T₀ ≤ L := by
      dsimp [L]
      exact Real.log_le_log (Real.exp_pos 10650 |>.trans_le hT₀) hgamma
    have hloglogTpos : 0 < Real.log (Real.log T₀) := by
      have hlogTlower : (10650 : ℝ) ≤ Real.log T₀ := by
        rw [← Real.log_exp 10650]
        exact Real.log_le_log (Real.exp_pos 10650) hT₀
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 10650) hlogTlower
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 10650)).trans_le this
    have hlogTpos : 0 < Real.log T₀ := by
      apply Real.log_pos
      exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 10650)).trans_le hT₀
    have hlogTlarge : Real.exp 1 ≤ Real.log T₀ := by
      have hlogTlower : (10650 : ℝ) ≤ Real.log T₀ := by
        rw [← Real.log_exp 10650]
        exact Real.log_le_log (Real.exp_pos 10650) hT₀
      exact (Real.exp_one_lt_three.le.trans (by norm_num)).trans hlogTlower
    have hLlarge : Real.exp 1 ≤ L := hlogTlarge.trans hlogT
    have hanti : ell / L ≤ Real.log (Real.log T₀) / Real.log T₀ := by
      have h := Real.log_div_self_antitoneOn hlogTlarge hLlarge hlogT
      simpa only [L, ell] using h
    have hcross : ell * Real.log T₀ ≤ Real.log (Real.log T₀) * L := by
      exact (div_le_div_iff₀ hL hlogTpos).mp hanti
    have hfrac : Real.log T₀ / Real.log (Real.log T₀) ≤ L / ell := by
      apply (div_le_div_iff₀ hloglogTpos hell).2
      nlinarith
    exact hratio.trans hfrac
  have habsorb : 0.3 * 10.01055 + 33.3275 * Real.exp (-1937) ≤
      0.010122 * M := by
    simpa only [M, BP, R, mul_assoc] using
      startup_constant_absorption hB hell hratioT
  let Cmain : ℝ := sourceScale *
    (33.3275 * ((1 / 3 : ℝ) + (4 / 3 : ℝ) / 2) + 10.01055 / 3)
  let Ccorr : ℝ := sourceScale *
    ((33.3275 / 2) * Real.log (A + 1) +
      (10.01055 / 3) *
        (Real.log (B / (4 / 3 : ℝ)) - Real.log ell))
  have hmain : Cmain ≤ 30.26576 := sourceScale_main_coefficient
  have hcorr : Ccorr + 0.010122 ≤
      -2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33 := by
    exact correction_coefficient_le hA hB hBtop hellOne
  have hlazy' : 0.953 / (1 - beta) ≤
      (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * ell + B * Real.rpow eta (3 / 2 : ℝ) * L +
            Real.log (A + 1)) +
        (10.01055 / 2) * (1 / eta) * Real.log (1 / eta) +
        0.3 * 10.01055 + (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937) := by
    simpa only [eta, L, ell] using hlazy.2
  have hdecompose :
      (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * ell + B * Real.rpow eta (3 / 2 : ℝ) * L +
            Real.log (A + 1)) +
        (10.01055 / 2) * (1 / eta) * Real.log (1 / eta) =
      Cmain * P + Ccorr * M := by
    rw [hlogEta, hinvEta, hetaPow]
    dsimp [Cmain, Ccorr]
    rw [← hMell]
    ring
  rw [hdecompose] at hlazy'
  have hcorrConst : Ccorr * M +
          (0.3 * 10.01055 + 33.3275 * Real.exp (-1937)) ≤
      (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M := by
    calc
      Ccorr * M +
          (0.3 * 10.01055 + 33.3275 * Real.exp (-1937)) ≤
        Ccorr * M + 0.010122 * M := by
          simpa only [add_comm] using add_le_add_left habsorb (Ccorr * M)
      _ = (Ccorr + 0.010122) * M := by ring
      _ ≤ (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M :=
        mul_le_mul_of_nonneg_right hcorr hMpos.le
  have htarget :
      Cmain * P + Ccorr * M +
          0.3 * 10.01055 + (33.3275 / 2) * Real.log q +
          33.3275 * Real.exp (-1937) ≤
        16.66375 * Real.log q +
          30.26576 * P +
          (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M := by
    have hmainP := mul_le_mul_of_nonneg_right hmain hPpos.le
    have hqcoeff : (33.3275 / 2 : ℝ) = 16.66375 := by norm_num
    rw [hqcoeff]
    nlinarith [hcorrConst]
  apply hlazy'.trans
  have ht := htarget
  have hrewrite :
      30.26576 * P +
          (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M =
        (30.26576 +
          (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) / ell) * P := by
    rw [← hMell]
    field_simp [ne_of_gt hell]
  have hout :
      16.66375 * Real.log q + 30.26576 * P +
          (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M =
        16.66375 * Real.log q +
          (30.26576 +
            (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) / ell) * P := by
    calc
      16.66375 * Real.log q + 30.26576 * P +
          (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M =
        16.66375 * Real.log q +
          (30.26576 * P +
            (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M) := by ring
      _ = _ := congrArg (fun z : ℝ => 16.66375 * Real.log q + z) hrewrite
  have hfinal := ht.trans_eq hout
  simpa only [P, BP, L, ell, mul_assoc] using hfinal

end
end MAPKhaleAppendixB1LazyKeyReduction

#print axioms MAPKhaleAppendixB1LazyKeyReduction.penultimateEstimate_of_lazyKeyAfterZeta
