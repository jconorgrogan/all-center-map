import KhaleAppendixBFirstPartExactHeightSlack
import KhaleAppendixBFirstPartScaleCorrected
import KhaleAppendixBLemma51ExpansionReduction
import KhaleAppendixBLemma51EulerFourierCertified
import KhaleAppendixBLemma51KernelCertified
import KhaleAppendixBZetaPrimePowerCertified
import KhaleAppendixBCotangentCertified
import KhaleAppendixBZetaPointwiseCertified
import KhaleAppendixB1HighZeroReduction

/-!
# Source-faithful exact-height repair of Khale Appendix B

This is the proof-level adapter for the scalar estimates in
`KhaleAppendixBFirstPartExactHeightSlack`.  Its analytic input is the literal
four-ordinate output `AppendixBLemma41TrigNaturalScales`, not the invalid
gamma-collapsed `AppendixBFirstPartRawEstimate`.
-/

namespace MAPKhaleAppendixBFirstPartExactHeightRepair

set_option maxHeartbeats 2000000

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixBNumericalCore
open MAPKhaleAppendixBFirstPartAnalyticReduction
open MAPKhaleAppendixBFirstPartScaleCorrected
open MAPKhaleAppendixBFirstPartExactHeightSlack
open MAPKhaleAppendixB1ZetaReduction
open MAPKhaleAppendixB1FinalReduction
open MAPKhaleAppendixB1HighZeroReduction

noncomputable section

/-- Corrected `(firstpart)` with the exact weighted four-height error retained. -/
abbrev AppendixBFirstPartEstimateExact : Prop :=
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
        33.3275 * Real.exp (-1937) +
        exactHeightCorrection B eta gamma

private theorem envelope_at_multiple_le_base_add_exact
    {A B sigma eta gamma j : ℝ} {q : ℕ}
    (hB : 0 < B) (hdelta : 0 ≤ 1 - sigma + eta)
    (hdeltaTop : 1 - sigma + eta ≤ eta)
    (hgamma : Real.exp 10650 ≤ gamma) (hj : 1 ≤ j) :
    lemma41Envelope A B q sigma eta (j * gamma) ≤
      eta * Real.log q +
        ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
          B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
          Real.log (A + 1)) +
        ((2 / 3 : ℝ) *
            (Real.log (Real.log (j * gamma)) -
              Real.log (Real.log gamma)) +
          B * Real.rpow eta (3 / 2 : ℝ) * Real.log j) := by
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma
  have hjPos : 0 < j := zero_lt_one.trans_le hj
  have hL : 0 < Real.log gamma := by
    have : (10650 : ℝ) ≤ Real.log gamma := by
      rw [← Real.log_exp 10650]
      exact Real.log_le_log (Real.exp_pos 10650) hgamma
    linarith
  have hlogj : 0 ≤ Real.log j := Real.log_nonneg hj
  have hlogq : 0 ≤ Real.log q := by positivity
  have hpow : Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) ≤
      Real.rpow eta (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hdelta hdeltaTop (by norm_num)
  have hqterm : (1 - sigma + eta) * Real.log q ≤
      eta * Real.log q := mul_le_mul_of_nonneg_right hdeltaTop hlogq
  have hheightCoeff :
      B * Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) ≤
        B * Real.rpow eta (3 / 2 : ℝ) := by gcongr
  have hlogmul : Real.log (j * gamma) =
      Real.log gamma + Real.log j := by
    rw [Real.log_mul hjPos.ne' hgammaPos.ne']
    ring
  have hheight :
      B * Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) *
          Real.log (j * gamma) ≤
        B * Real.rpow eta (3 / 2 : ℝ) *
          (Real.log gamma + Real.log j) := by
    rw [hlogmul]
    gcongr
  unfold lemma41Envelope
  linarith

/-- The literal four applications of Lemma 6.2, the certified Lemma 5.1,
and closed-half-plane nonvanishing give the corrected first-part inequality. -/
theorem exactFirstPart_of_naturalScales_and_lemma51
    (hNatural : AppendixBLemma41TrigNaturalScales)
    (h51 : AppendixBLemma51Specialized) :
    AppendixBFirstPartEstimateExact := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hn := hNatural A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  let eta := khaleEta B gamma
  let sigmaAux := 1 + 3.238 * (1 - beta)
  let y := (sigmaAux - beta) / eta
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma0
  have hbeta :=
    MAPKhaleAppendixBFirstPartSourceReduction.beta_lt_one_of_nonzero_ordinate_zero
      chi hgammaPos hzero
  refine ⟨hbeta, ?_⟩
  have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma0
  have hL : 0 < Real.log gamma := by linarith
  have hell : 0 < Real.log (Real.log gamma) :=
    Real.log_pos (by linarith [hLlower])
  have heta : 0 < eta := khaleEta_pos hB hL hell
  have hsigma : 1 ≤ sigmaAux := by
    dsimp [sigmaAux]
    nlinarith
  have h51' := h51 q chi sigmaAux eta gamma hsigma heta
  have hIntegral :
      -(1 / (4 * eta)) * appendixBIntegralCombination chi sigmaAux eta gamma ≤
        (10.01055 / 2) * (1 / eta) * zetaLog eta := by
    have hm := mul_le_mul_of_nonneg_left h51'
      (show 0 ≤ 1 / (4 * eta) by positivity)
    calc
      -(1 / (4 * eta)) * appendixBIntegralCombination chi sigmaAux eta gamma ≤
          -((1 / (4 * eta)) * (-2 * 10.01055 * zetaLog eta)) := by
            nlinarith
      _ = (10.01055 / 2) * (1 / eta) * zetaLog eta := by ring
  have hcollar : 0 ≤ 1 - sigmaAux + eta := by
    simpa only [eta, sigmaAux, y] using hn.1
  have hcollarTop : 1 - sigmaAux + eta ≤ eta := by linarith
  have h1 := envelope_at_multiple_le_base_add_exact
    (A := A) (q := q) (B := B) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 1) hB hcollar hcollarTop hgamma0 (by norm_num)
  have h2 := envelope_at_multiple_le_base_add_exact
    (A := A) (q := q) (B := B) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 2) hB hcollar hcollarTop hgamma0 (by norm_num)
  have h3 := envelope_at_multiple_le_base_add_exact
    (A := A) (q := q) (B := B) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 3) hB hcollar hcollarTop hgamma0 (by norm_num)
  have h4 := envelope_at_multiple_le_base_add_exact
    (A := A) (q := q) (B := B) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 4) hB hcollar hcollarTop hgamma0 (by norm_num)
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 17.145)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 10.6825)
  have hh3 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 4.5)
  have hsum := add_le_add (add_le_add (add_le_add hh1 hh2) hh3) h4
  have hn2 : 0 ≤
        -17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (1 / (2 * eta)) *
          (17.145 * lemma41Envelope A B q sigmaAux eta gamma +
           10.6825 * lemma41Envelope A B q sigmaAux eta (2 * gamma) +
           4.5 * lemma41Envelope A B q sigmaAux eta (3 * gamma) +
           lemma41Envelope A B q sigmaAux eta (4 * gamma)) +
        10.01055 / (sigmaAux - 1) -
        (1 / (4 * eta)) * appendixBIntegralCombination chi sigmaAux eta gamma +
        33.3275 * Real.exp (-1937) := by
    simpa only [eta, sigmaAux, y] using hn.2
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 1 / (2 * eta) by positivity)
  have hscaled' :
      (1 / (2 * eta)) *
          (17.145 * lemma41Envelope A B q sigmaAux eta gamma +
           10.6825 * lemma41Envelope A B q sigmaAux eta (2 * gamma) +
           4.5 * lemma41Envelope A B q sigmaAux eta (3 * gamma) +
           lemma41Envelope A B q sigmaAux eta (4 * gamma)) ≤
        (1 / (2 * eta)) *
          (17.145 *
              (eta * Real.log q +
                ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
                  Real.log (A + 1)) +
                ((2 / 3 : ℝ) *
                    (Real.log (Real.log gamma) - Real.log (Real.log gamma)) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log 1)) +
           10.6825 *
              (eta * Real.log q +
                ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
                  Real.log (A + 1)) +
                ((2 / 3 : ℝ) *
                    (Real.log (Real.log (2 * gamma)) - Real.log (Real.log gamma)) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log 2)) +
           4.5 *
              (eta * Real.log q +
                ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
                  Real.log (A + 1)) +
                ((2 / 3 : ℝ) *
                    (Real.log (Real.log (3 * gamma)) - Real.log (Real.log gamma)) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log 3)) +
           (eta * Real.log q +
                ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
                  Real.log (A + 1)) +
                ((2 / 3 : ℝ) *
                    (Real.log (Real.log (4 * gamma)) - Real.log (Real.log gamma)) +
                  B * Real.rpow eta (3 / 2 : ℝ) * Real.log 4))) := by
    simpa only [one_mul] using hscaled
  have hscaledExact :
      (1 / (2 * eta)) *
          (17.145 * lemma41Envelope A B q sigmaAux eta gamma +
           10.6825 * lemma41Envelope A B q sigmaAux eta (2 * gamma) +
           4.5 * lemma41Envelope A B q sigmaAux eta (3 * gamma) +
           lemma41Envelope A B q sigmaAux eta (4 * gamma)) ≤
        (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        (33.3275 / 2) * Real.log q +
        exactHeightCorrection B eta gamma := by
    apply hscaled'.trans_eq
    unfold exactHeightCorrection exactHeightWeightedLog
    simp only [one_mul, Real.log_one, mul_zero, sub_self, zero_add]
    field_simp [heta.ne']
    ring
  dsimp only
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
        33.3275 * Real.exp (-1937) + exactHeightCorrection B eta gamma
  nlinarith [hn2, hscaledExact, hIntegral]

/-- All finite Lemma-5.1 leaves used above are already certified in the
repository.  Thus the only remaining analytic input here is the literal
four-scale Lemma-6.2/trigonometric statement. -/
theorem exactFirstPart_of_naturalScales
    (hNatural : AppendixBLemma41TrigNaturalScales) :
    AppendixBFirstPartEstimateExact := by
  let h51 : AppendixBLemma51Specialized :=
    MAPKhaleAppendixBLemma51ExpansionReduction.lemma51Specialized_of_expansions_and_ford
      MAPKhaleAppendixBLemma51EulerFourierCertified.appendixBLemma51EulerFourierExpansion
      MAPKhaleAppendixBLemma51KernelCertified.fordCoshSqFourierIdentity
      MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity
  exact exactFirstPart_of_naturalScales_and_lemma51 hNatural h51

/-- Corrected `(lazykey)` before the elementary zeta insertion. -/
abbrev AppendixBLazyKeyBeforeZetaEstimateExact : Prop :=
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
        (10.01055 / 2) * (1 / eta) * zetaLog eta +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937) +
        exactHeightCorrection B eta gamma

theorem exactLazyKeyBeforeZeta_of_firstPart
    (hFirst : AppendixBFirstPartEstimateExact) :
    AppendixBLazyKeyBeforeZetaEstimateExact := by
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
  have hell : 0 < Real.log (Real.log gamma) :=
    Real.log_pos (by linarith [hLlower])
  have heta : 0 < eta := khaleEta_pos hB hL hell
  let R : ℝ := Real.rpow
    (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ)
  let BP : ℝ := Real.rpow B (2 / 3 : ℝ)
  let M : ℝ := BP * R
  let P : ℝ := BP * Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  have hMpos : 0 < M := by dsimp [M, BP, R]; positivity
  have hPpos : 0 < P := by dsimp [P, BP]; positivity
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
  have hellLower :=
    MAPKhaleAppendixB1FirstPartReduction.loglog_gamma_lower_924
      hB hBtop hT₀ hgamma hloglog
  have hkNonneg : 0 ≤ sourceScale := Real.rpow_nonneg (by norm_num) _
  have hscaled := mul_le_mul_of_nonneg_right hgapP
    (mul_nonneg hkNonneg hMpos.le)
  have hyTop : y ≤ 0.012 := by
    have hk := sourceScale_upper
    have hbound : (1 + 3.238) * sourceScale /
        (31.76 * Real.log (Real.log gamma)) ≤ 0.012 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hell)).2
      nlinarith
    have hdeltaInv : delta * (1 / eta) ≤
        sourceScale / (31.76 * Real.log (Real.log gamma)) := by
      rw [hinvEta]
      calc
        delta * (sourceScale * M) ≤
            (1 / (31.76 * P)) * (sourceScale * M) := hscaled
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
  have hcot := MAPKhaleAppendixBCotangentCertified.appendixBCotangent0012
    y hyPos hyTop
  let Rest : ℝ :=
    (33.3275 / 2) * (1 / eta) *
        ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
          B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
          Real.log (A + 1)) +
      (10.01055 / 2) * (1 / eta) * zetaLog eta +
      (33.3275 / 2) * Real.log q +
      33.3275 * Real.exp (-1937) +
      exactHeightCorrection B eta gamma
  let N : ℝ := -17.145 * (1 / eta) *
      ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
    10.01055 / (sigmaAux - 1)
  have hN : N ≤ -0.953 / delta := by
    have hfac : 0 ≤ 17.145 * (1 / eta) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcot hfac
    have hyEq : y = (1 + 3.238) * delta / eta := by
      dsimp [y, sigmaAux, delta]
      congr 1
      ring
    have hsigmaEq : sigmaAux - 1 = 3.238 * delta := by
      dsimp [sigmaAux]
      ring
    dsimp [N]
    rw [hyEq] at hmul
    rw [hyEq, hsigmaEq]
    field_simp [hdelta.ne', heta.ne'] at hmul ⊢
    nlinarith
  have hNR : 0 ≤ N + Rest := by
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
        33.3275 * Real.exp (-1937) +
        exactHeightCorrection B eta gamma at hf
    calc
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
          33.3275 * Real.exp (-1937) +
          exactHeightCorrection B eta gamma := hf
      _ = N + Rest := by dsimp [N, Rest]; ring
  have hneg : 0.953 / delta ≤ -N := by
    have h := neg_le_neg hN
    simpa only [neg_div, neg_neg] using h
  have hrest : -N ≤ Rest := by
    have h := sub_le_sub_right hNR N
    change 0 - N ≤ N + Rest - N at h
    simpa only [zero_sub, add_sub_cancel_left] using h
  have hout : 0.953 / delta ≤ Rest := hneg.trans hrest
  change 0.953 / delta ≤ Rest
  exact hout

/-- Corrected `(lazykey)` after the certified pointwise zeta bound. -/
abbrev AppendixBLazyKeyAfterZetaEstimateExact : Prop :=
  ∀ (A B T₀ : ℝ),
    0 < A → 0 < B → B ≤ 4.45 → FordHurwitzEquation12 A B →
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
        0.3 * 10.01055 + (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937) +
        exactHeightCorrection B eta gamma

theorem exactLazyKeyAfterZeta_of_before
    (hKey : AppendixBLazyKeyBeforeZetaEstimateExact) :
    AppendixBLazyKeyAfterZetaEstimateExact := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hk := hKey A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  refine ⟨hk.1, ?_⟩
  let eta := khaleEta B gamma
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma0
  have hL : 0 < Real.log gamma := by linarith
  have hell : 0 < Real.log (Real.log gamma) :=
    Real.log_pos (by linarith [hLlower])
  have hratioGamma : 5110.6 / B ≤
      Real.log gamma / Real.log (Real.log gamma) :=
    hratio.trans (log_ratio_mono_from_exp10650 hT₀ hgamma)
  have hetaPos : 0 < eta := khaleEta_pos hB hL hell
  have hetaTop : eta ≤ 0.06 :=
    khaleEta_le_point_zero_six_of_ratio hB hL hell hratioGamma
  have hZeta := MAPKhaleAppendixB1ZetaReduction.lazyZetaBound_of_pointwise06
    MAPKhaleAppendixBZetaPointwiseCertified.appendixBZetaPointwise06
  have hz := hZeta eta hetaPos hetaTop
  have hk' := hk.2
  dsimp only [eta] at hk' ⊢
  nlinarith

private theorem log_B_over_C_le_exact
    {B : ℝ} (hB : 0 < B) (hBtop : B ≤ 4.45) :
    Real.log (B / (4 / 3 : ℝ)) ≤ Real.log (3.3375 : ℝ) := by
  apply Real.log_le_log (div_pos hB (by norm_num))
  norm_num
  linarith

private theorem correction_coefficient_le_exact
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
  have hlogBC := log_B_over_C_le_exact hB hBtop
  have hAterm : sourceScale * (33.3275 / 2) * Real.log (A + 1) ≤
      13.75563 * Real.log (A + 1) :=
    mul_le_mul_of_nonneg_right sourceScale_logA_coefficient hlogA
  have hnegterm :
      -(sourceScale * (10.01055 / 3)) *
          Real.log (Real.log (Real.log gamma)) ≤
        -2.7545 * Real.log (Real.log (Real.log gamma)) := by
    nlinarith [sourceScale_log3_coefficient]
  have hconst : sourceScale * (10.01055 / 3) *
        Real.log (B / (4 / 3 : ℝ)) + 0.010122 ≤ 3.33 := by
    have hcoef0 : 0 ≤ sourceScale * (10.01055 / 3) := by
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hlogBC hcoef0
    calc
      sourceScale * (10.01055 / 3) *
            Real.log (B / (4 / 3 : ℝ)) + 0.010122 ≤
          sourceScale * (10.01055 / 3) * Real.log 3.3375 + 0.010122 := by
        linarith
      _ ≤ 3.33 := sourceScale_constant_coefficient
  nlinarith

/-- Even the larger half of the exact-height split fits the final `3.495`
rounding reserve. -/
theorem penultimate_add_0008_le_final
    {A gamma : ℝ} (hA : 0 < A)
    (hgamma : Real.exp 10650 ≤ gamma) :
    30.26576 +
        (-2.7545 * Real.log (Real.log (Real.log gamma)) +
          13.75563 * Real.log (A + 1) + 3.33) /
            Real.log (Real.log gamma) + 0.0008 ≤
      0.953 * (31.76 + appendixBFinalCorrection A gamma) := by
  have hloggamma : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma
  have hellLower : Real.log 10650 ≤ Real.log (Real.log gamma) :=
    Real.log_le_log (by norm_num) hloggamma
  have hellPos : 0 < Real.log (Real.log gamma) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 10650) |>.trans_le hellLower
  have hlog3 : 0 ≤ Real.log (Real.log (Real.log gamma)) :=
    Real.log_nonneg (show 1 ≤ Real.log (Real.log gamma) by
      have hone : (1 : ℝ) < Real.log 10650 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10650)]
        exact Real.exp_one_lt_three.trans (by norm_num)
      exact hone.le.trans hellLower)
  have hlogA : 0 < Real.log (A + 1) := Real.log_pos (by linarith)
  unfold appendixBFinalCorrection
  field_simp [hellPos.ne']
  nlinarith

/-- Deterministic completion of the corrected exact-height chain. -/
theorem highZeroReciprocalEstimate_of_exactLazy
    (hLazy : AppendixBLazyKeyAfterZetaEstimateExact) :
    AppendixBHighZeroReciprocalEstimate := by
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
  have hMpos : 0 < M := by dsimp [M, BP, R]; positivity
  have hPpos : 0 < P := by dsimp [P, BP]; positivity
  have hinvEta : 1 / eta = sourceScale * M := by
    simpa only [eta, khaleInvEtaScale, M, BP, R, L, ell, mul_assoc] using
      one_div_khaleEta hB (by simpa only [L] using hL)
        (by simpa only [ell] using hell)
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
    have hr := ratio_two_thirds_mul_loglog
      (by simpa only [L] using hL) (by simpa only [ell] using hell)
    calc
      M * ell = BP * (R * ell) := by dsimp [M]; ring
      _ = BP * (Real.rpow L (2 / 3 : ℝ) * Real.rpow ell (1 / 3 : ℝ)) := by
        rw [show R * ell = Real.rpow L (2 / 3 : ℝ) *
            Real.rpow ell (1 / 3 : ℝ) by simpa only [R, L, ell] using hr]
      _ = P := by dsimp [P]; ring
  have hratioT : 5110.6 / B ≤ L / ell := by
    have hlogT : Real.log T₀ ≤ L := by
      dsimp [L]
      exact Real.log_le_log (Real.exp_pos 10650 |>.trans_le hT₀) hgamma
    have hloglogTpos : 0 < Real.log (Real.log T₀) := by
      have ht : (10650 : ℝ) ≤ Real.log T₀ := by
        rw [← Real.log_exp 10650]
        exact Real.log_le_log (Real.exp_pos 10650) hT₀
      exact Real.log_pos (by linarith)
    have hlogTpos : 0 < Real.log T₀ := by
      apply Real.log_pos
      exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 10650)).trans_le hT₀
    have hlargeT : Real.exp 1 ≤ Real.log T₀ := by
      have ht : (10650 : ℝ) ≤ Real.log T₀ := by
        rw [← Real.log_exp 10650]
        exact Real.log_le_log (Real.exp_pos 10650) hT₀
      exact Real.exp_one_lt_three.le.trans (by linarith)
    have hlargeL : Real.exp 1 ≤ L := hlargeT.trans hlogT
    have hanti : ell / L ≤ Real.log (Real.log T₀) / Real.log T₀ := by
      have h := Real.log_div_self_antitoneOn hlargeT hlargeL hlogT
      simpa only [L, ell] using h
    have hcross : ell * Real.log T₀ ≤ Real.log (Real.log T₀) * L :=
      (div_le_div_iff₀ hL hlogTpos).mp hanti
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
    exact correction_coefficient_le_exact hA hB hBtop hellOne
  have hlazy' : 0.953 / (1 - beta) ≤
      (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * ell + B * Real.rpow eta (3 / 2 : ℝ) * L +
            Real.log (A + 1)) +
        (10.01055 / 2) * (1 / eta) * Real.log (1 / eta) +
        0.3 * 10.01055 + (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937) + exactHeightCorrection B eta gamma := by
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
      Ccorr * M + (0.3 * 10.01055 + 33.3275 * Real.exp (-1937)) ≤
        Ccorr * M + 0.010122 * M := by
          simpa only [add_comm] using add_le_add_left habsorb (Ccorr * M)
      _ = (Ccorr + 0.010122) * M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcorr hMpos.le
  have hbasePen : 0.953 / (1 - beta) ≤
      16.66375 * Real.log q +
        (30.26576 +
          (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) / ell) * P +
        exactHeightCorrection B eta gamma := by
    have hmainP := mul_le_mul_of_nonneg_right hmain hPpos.le
    have hqcoeff : (33.3275 / 2 : ℝ) = 16.66375 := by norm_num
    rw [hqcoeff] at hlazy'
    have htmp :
        Cmain * P + Ccorr * M + 0.3 * 10.01055 +
            16.66375 * Real.log q + 33.3275 * Real.exp (-1937) +
            exactHeightCorrection B eta gamma ≤
          16.66375 * Real.log q + 30.26576 * P +
            (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) * M +
            exactHeightCorrection B eta gamma := by
      nlinarith [hmainP, hcorrConst]
    apply hlazy'.trans
    apply htmp.trans_eq
    rw [← hMell]
    field_simp [hell.ne']
    ring
  have hD08 : exactHeightCorrection B eta gamma ≤ 0.0008 * P := by
    by_cases hsplit : L ≤ 20000
    · simpa only [eta, P, BP, L, ell, mul_assoc] using
        exactHeightCorrection_le_low hB hgamma0 hsplit
    · have hh := exactHeightCorrection_le_high hB hgamma0
        (le_of_lt (lt_of_not_ge hsplit))
      have h04 : (0.0004 : ℝ) * P ≤ 0.0008 * P := by nlinarith [hPpos.le]
      have hh' : exactHeightCorrection B eta gamma ≤ 0.0004 * P := by
        simpa only [eta, P, BP, L, ell, mul_assoc] using hh
      exact hh'.trans h04
  let Cpen : ℝ := 30.26576 +
    (-2.7545 * Real.log ell + 13.75563 * Real.log (A + 1) + 3.33) / ell
  let Cfinal : ℝ := 31.76 + appendixBFinalCorrection A gamma
  have hcoeff : Cpen + 0.0008 ≤ 0.953 * Cfinal := by
    simpa only [Cpen, Cfinal, ell] using penultimate_add_0008_le_final hA hgamma0
  have hpen08 : 0.953 / (1 - beta) ≤
      16.66375 * Real.log q + (Cpen + 0.0008) * P := by
    have hb : 0.953 / (1 - beta) ≤
        16.66375 * Real.log q + Cpen * P + exactHeightCorrection B eta gamma := by
      simpa only [Cpen] using hbasePen
    have hd :
        16.66375 * Real.log q + Cpen * P + exactHeightCorrection B eta gamma ≤
          16.66375 * Real.log q + Cpen * P + 0.0008 * P :=
      by nlinarith [hD08]
    exact hb.trans (hd.trans_eq (by ring))
  have hlogq : 0 ≤ Real.log q := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ q by omega)
  have hcoeffP := mul_le_mul_of_nonneg_right hcoeff hPpos.le
  have hRhs :
      16.66375 * Real.log q + (Cpen + 0.0008) * P ≤
        0.953 * (17.49 * Real.log q + Cfinal * P) := by
    nlinarith [hcoeffP]
  have hscaled := hpen08.trans hRhs
  have hfinal : 1 / (1 - beta) ≤
      17.49 * Real.log q + Cfinal * P := by
    have hs : 0.953 * (1 / (1 - beta)) ≤
        0.953 * (17.49 * Real.log q + Cfinal * P) := by
      simpa [div_eq_mul_inv] using hscaled
    nlinarith
  simpa only [Cfinal, P, BP, L, ell, add_comm, mul_assoc] using hfinal

/-- Final source-facing replacement for the old false-as-sourced raw route. -/
theorem appendixBHighZeroReciprocalEstimate_of_naturalScales
    (hNatural : AppendixBLemma41TrigNaturalScales) :
    AppendixBHighZeroReciprocalEstimate :=
  highZeroReciprocalEstimate_of_exactLazy
    (exactLazyKeyAfterZeta_of_before
      (exactLazyKeyBeforeZeta_of_firstPart
        (exactFirstPart_of_naturalScales hNatural)))

end
end MAPKhaleAppendixBFirstPartExactHeightRepair

#print axioms MAPKhaleAppendixBFirstPartExactHeightRepair.exactFirstPart_of_naturalScales
#print axioms MAPKhaleAppendixBFirstPartExactHeightRepair.penultimate_add_0008_le_final
#print axioms MAPKhaleAppendixBFirstPartExactHeightRepair.highZeroReciprocalEstimate_of_exactLazy
#print axioms MAPKhaleAppendixBFirstPartExactHeightRepair.appendixBHighZeroReciprocalEstimate_of_naturalScales
