import KhaleAppendixB1ZetaReduction

/-!
# Cotangent isolation from Khale's `firstpart` to `(lazykey)`

This exposes the first combined analytic inequality in the proof and separates
the tiny elementary cotangent estimate.  All zero-region, eta-scale, and
constant arithmetic between `firstpart` and `(lazykey)` is certified here.
-/

namespace MAPKhaleAppendixB1FirstPartReduction

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixBNumericalCore MAPKhaleAppendixB1ZetaReduction

noncomputable section

/-- The normalized cotangent inequality used in the source. -/
abbrev AppendixBCotangent0012 : Prop :=
  ∀ y : ℝ, 0 < y → y ≤ 0.012 →
    0.99988 / y ≤
      (Real.pi / 2) * Real.cot ((Real.pi / 2) * y)

/-- The final upper inequality in display `(firstpart)`, specialized to the
source choice `sigma = 1 + 3.238(1-beta)`. -/
abbrev AppendixBFirstPartEstimate : Prop :=
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
      let sigmaAux := 1 + 3.238 * (1 - beta)
      let y := (sigmaAux - beta) / eta
      0 ≤
        -17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        10.01055 / (sigmaAux - 1) +
        (10.01055 / 2) * (1 / eta) * zetaLog eta +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937)

theorem loglog_gamma_lower_924
    {B T₀ gamma : ℝ} (hB : 0 < B) (hBtop : B ≤ 4.45)
    (hT₀ : Real.exp 10650 ≤ T₀) (hgamma : T₀ ≤ gamma)
    (hloglog : 183 / B ^ 2 ≤ Real.log (Real.log T₀)) :
    (9.24 : ℝ) ≤ Real.log (Real.log gamma) := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have h924 : (9.24 : ℝ) ≤ 183 / B ^ 2 := by
    apply (le_div_iff₀ hBsq).2
    nlinarith [sq_nonneg (4.45 - B), sq_nonneg B]
  have hTpos : 0 < T₀ := (Real.exp_pos 10650).trans_le hT₀
  have hlogTpos : 0 < Real.log T₀ := by
    apply Real.log_pos
    exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 10650)).trans_le hT₀
  have hlogmono : Real.log T₀ ≤ Real.log gamma := Real.log_le_log hTpos hgamma
  have hllmono : Real.log (Real.log T₀) ≤ Real.log (Real.log gamma) :=
    Real.log_le_log hlogTpos hlogmono
  exact h924.trans (hloglog.trans hllmono)

/-- `firstpart` plus the tiny cotangent estimate gives `(lazykey)` before the
zeta insertion. -/
theorem lazyKeyBeforeZeta_of_firstPart_and_cotangent
    (hFirst : AppendixBFirstPartEstimate)
    (hCot : AppendixBCotangent0012) :
    AppendixBLazyKeyBeforeZetaEstimate := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hfirst := hFirst A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  refine ⟨hfirst.1, ?_⟩
  let delta : ℝ := 1 - beta
  let eta : ℝ := khaleEta B gamma
  let sigmaAux : ℝ := 1 + 3.238 * delta
  let y : ℝ := (sigmaAux - beta) / eta
  have hdelta : 0 < delta := by dsimp [delta]; linarith [hfirst.1]
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma0
  have hL : 0 < Real.log gamma := by linarith
  have hell : 0 < Real.log (Real.log gamma) := Real.log_pos (by linarith)
  have heta : 0 < eta := khaleEta_pos hB hL hell
  let R : ℝ := Real.rpow
    (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ)
  let BP : ℝ := Real.rpow B (2 / 3 : ℝ)
  let M : ℝ := BP * R
  let P : ℝ := BP * Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  have hMpos : 0 < M := by
    dsimp [M, BP, R]
    positivity
  have hPpos : 0 < P := by
    dsimp [P, BP]
    positivity
  have hMell : M * Real.log (Real.log gamma) = P := by
    have hr := ratio_two_thirds_mul_loglog hL hell
    have hr' : R * Real.log (Real.log gamma) =
        Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ) := by
      simpa only [R] using hr
    calc
      M * Real.log (Real.log gamma) =
          BP * (R * Real.log (Real.log gamma)) := by dsimp [M]; ring
      _ = BP * (Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) := by rw [hr']
      _ = P := by dsimp [P]; ring
  have hinvEta : 1 / eta = sourceScale * M := by
    simpa only [eta, khaleInvEtaScale, M, BP, R, mul_assoc] using
      one_div_khaleEta hB hL hell
  have hcoeffLower : (31.76 : ℝ) ≤ appendixBHeightCoefficient A T₀ := by
    unfold appendixBHeightCoefficient
    linarith [le_max_right (sSup (appendixBCorrection A '' Set.Ici T₀)) 0]
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqNonneg : 0 ≤ Real.log q :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 3).trans hqReal)
  have hdenLower : 31.76 * P ≤
      18 * Real.log q + appendixBHeightCoefficient A T₀ * P := by
    have hc := mul_le_mul_of_nonneg_right hcoeffLower hPpos.le
    nlinarith
  have hbaseDenPos : 0 < 31.76 * P := mul_pos (by norm_num) hPpos
  have hinvDen : 1 /
      (18 * Real.log q + appendixBHeightCoefficient A T₀ * P) ≤
      1 / (31.76 * P) :=
    one_div_le_one_div_of_le hbaseDenPos hdenLower
  have hgapP : delta ≤ 1 / (31.76 * P) := by
    have hgap' : delta ≤ 1 /
        (18 * Real.log q + appendixBHeightCoefficient A T₀ * P) := by
      simpa only [delta, P, BP, mul_assoc] using hgap
    exact hgap'.trans hinvDen
  have hellLower := loglog_gamma_lower_924 hB hBtop hT₀ hgamma hloglog
  have hkNonneg : 0 ≤ sourceScale := by
    unfold sourceScale
    exact Real.rpow_nonneg (by norm_num) _
  have hscaled := mul_le_mul_of_nonneg_right hgapP
    (mul_nonneg hkNonneg hMpos.le)
  have hyTop : y ≤ 0.012 := by
    have hk := sourceScale_upper
    have hbound : (1 + 3.238) * sourceScale /
        (31.76 * Real.log (Real.log gamma)) ≤ 0.012 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hell)).2
      nlinarith
    have hscaled' : delta * (sourceScale * M) ≤
        (1 / (31.76 * P)) * (sourceScale * M) := hscaled
    have hdeltaInv : delta * (1 / eta) ≤
        sourceScale / (31.76 * Real.log (Real.log gamma)) := by
      rw [hinvEta]
      calc
        delta * (sourceScale * M) ≤
            (1 / (31.76 * P)) * (sourceScale * M) := hscaled'
        _ = sourceScale / (31.76 * Real.log (Real.log gamma)) := by
          rw [← hMell]
          field_simp [hMpos.ne', hell.ne']
    have hmul := mul_le_mul_of_nonneg_left hdeltaInv
      (by norm_num : (0 : ℝ) ≤ 1 + 3.238)
    have hyEq : y = (1 + 3.238) * delta / eta := by
      dsimp [y, sigmaAux, delta]
      congr 1
      ring
    rw [hyEq]
    calc
      (1 + 3.238) * delta / eta =
          (1 + 3.238) * (delta * (1 / eta)) := by field_simp
      _ ≤ (1 + 3.238) *
          (sourceScale / (31.76 * Real.log (Real.log gamma))) := hmul
      _ = (1 + 3.238) * sourceScale /
          (31.76 * Real.log (Real.log gamma)) := by ring
      _ ≤ 0.012 := hbound
  have hyPos : 0 < y := by
    dsimp [y, sigmaAux, delta]
    have : sigmaAux - beta = (1 + 3.238) * delta := by
      dsimp [sigmaAux, delta]
      ring
    rw [this]
    positivity
  have hcot := hCot y hyPos hyTop
  let Rest : ℝ :=
    (33.3275 / 2) * (1 / eta) *
        ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
          B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
          Real.log (A + 1)) +
      (10.01055 / 2) * (1 / eta) * zetaLog eta +
      (33.3275 / 2) * Real.log q +
      33.3275 * Real.exp (-1937)
  have hcotTerm :
      -17.145 * (1 / eta) *
          ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        10.01055 / (sigmaAux - 1) ≤
      -0.953 / delta := by
    have hfac : 0 ≤ 17.145 * (1 / eta) :=
      mul_nonneg (by norm_num) (one_div_nonneg.mpr heta.le)
    have hmul := mul_le_mul_of_nonneg_left hcot
      hfac
    have hyEq : y = (1 + 3.238) * delta / eta := by
      dsimp [y, sigmaAux, delta]
      congr 1
      ring
    have hsigmaEq : sigmaAux - 1 = 3.238 * delta := by
      dsimp [sigmaAux]
      ring
    rw [hyEq] at hmul
    rw [hyEq, hsigmaEq]
    field_simp [hdelta.ne', heta.ne'] at hmul ⊢
    nlinarith
  have hfirst' : 0 ≤
      -17.145 * (1 / eta) *
          ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        10.01055 / (sigmaAux - 1) + Rest := by
    have hf := hfirst.2
    change 0 ≤
      -17.145 * (1 / eta) *
          ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        10.01055 / (sigmaAux - 1) +
        (10.01055 / 2) * (1 / eta) * zetaLog eta +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937) at hf
    have hRest : Rest =
        (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        (10.01055 / 2) * (1 / eta) * zetaLog eta +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937) := rfl
    rw [hRest]
    have heq :
        (-17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
          (33.3275 / 2) * (1 / eta) *
            ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
              B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
              Real.log (A + 1)) +
          10.01055 / (sigmaAux - 1) +
          (10.01055 / 2) * (1 / eta) * zetaLog eta +
          (33.3275 / 2) * Real.log q +
          33.3275 * Real.exp (-1937)) =
        (-17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
          10.01055 / (sigmaAux - 1) +
          ((33.3275 / 2) * (1 / eta) *
            ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
              B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
              Real.log (A + 1)) +
          (10.01055 / 2) * (1 / eta) * zetaLog eta +
          (33.3275 / 2) * Real.log q +
          33.3275 * Real.exp (-1937))) := by ring
    rw [← heq]
    exact hf
  let N : ℝ := -17.145 * (1 / eta) *
      ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
    10.01055 / (sigmaAux - 1)
  have hN : N ≤ -0.953 / delta := by exact hcotTerm
  have hNR : 0 ≤ N + Rest := by exact hfirst'
  have hneg : 0.953 / delta ≤ -N := by
    have h := neg_le_neg hN
    simpa only [neg_div, neg_neg] using h
  have hrest : -N ≤ Rest := by
    have h := sub_le_sub_right hNR N
    change 0 - N ≤ N + Rest - N at h
    simpa only [zero_sub, add_sub_cancel_left] using h
  have : 0.953 / delta ≤ Rest := hneg.trans hrest
  change 0.953 / delta ≤ Rest
  exact this

end
end MAPKhaleAppendixB1FirstPartReduction

#print axioms MAPKhaleAppendixB1FirstPartReduction.lazyKeyBeforeZeta_of_firstPart_and_cotangent
