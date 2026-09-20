import KhaleAppendixBFirstPartAnalyticReduction

/-!
# Corrected scale bookkeeping in Khale Appendix B `(firstpart)`

Khale applies Lemma 6.2 at ordinates `j * gamma`, `1 <= j <= 4`.
The printed next display silently replaces the increasing quantities
`log (j*gamma)` and `log log (j*gamma)` by their values at `gamma`.
This module records the literal signed output at the four natural scales and
proves the minimal safe common-envelope correction.
-/

namespace MAPKhaleAppendixBFirstPartScaleCorrected

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixBFirstPartAnalyticReduction
open MAPKhaleAppendixB1ZetaReduction
open MAPKhaleAppendixB1ZetaReduction

noncomputable section

/-- The positive error envelope in Khale Lemma 6.2.  The historical theorem
name `lemma41Envelope` is retained to avoid breaking downstream imports. -/
def lemma41Envelope (A B : ℝ) (q : ℕ)
    (sigma eta t : ℝ) : ℝ :=
  (1 - sigma + eta) * Real.log q +
    (2 / 3 : ℝ) * Real.log (Real.log t) +
    B * Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) * Real.log t +
    Real.log (A + 1)

/-- The smallest simple common envelope used below.  The two extra summands
are exactly the cost of replacing `j*gamma` by `gamma` for `j <= 4`. -/
def correctedLemma41Envelope (A B : ℝ) (q : ℕ)
    (sigma eta gamma : ℝ) : ℝ :=
  lemma41Envelope A B q sigma eta gamma +
    (2 / 3 : ℝ) * (Real.log 4 / Real.log gamma) +
    B * Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) * Real.log 4

/-- Exact logarithmic loss from moving a Lemma-6.2 application at
`j*gamma` back to the base ordinate `gamma`. -/
theorem lemma41Envelope_mul_le_corrected
    {A B sigma eta gamma j : ℝ}
    {q : ℕ}
    (hB : 0 ≤ B) (hdelta : 0 ≤ 1 - sigma + eta)
    (hgamma : Real.exp 10650 ≤ gamma)
    (hj1 : 1 ≤ j) (hj4 : j ≤ 4) :
    lemma41Envelope A B q sigma eta (j * gamma) ≤
      correctedLemma41Envelope A B q sigma eta gamma := by
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma
  have hjPos : 0 < j := zero_lt_one.trans_le hj1
  have hlogGamma : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma
  have hlogGammaPos : 0 < Real.log gamma := by linarith
  have hlogjNonneg : 0 ≤ Real.log j := Real.log_nonneg hj1
  have hlogjLe : Real.log j ≤ Real.log 4 :=
    Real.log_le_log hjPos hj4
  have hlog4Pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogProd : Real.log (j * gamma) =
      Real.log j + Real.log gamma := by
    rw [Real.log_mul hjPos.ne' hgammaPos.ne']
  have hsumPos : 0 < Real.log j + Real.log gamma :=
    add_pos_of_nonneg_of_pos hlogjNonneg hlogGammaPos
  have hratioPos : 0 <
      (Real.log j + Real.log gamma) / Real.log gamma := by positivity
  have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
  have hratioSub :
      (Real.log j + Real.log gamma) / Real.log gamma - 1 =
        Real.log j / Real.log gamma := by
    field_simp
    ring
  rw [hratioSub] at hlogRatio
  have hdiff :
      Real.log (Real.log j + Real.log gamma) -
          Real.log (Real.log gamma) =
        Real.log ((Real.log j + Real.log gamma) / Real.log gamma) := by
    rw [Real.log_div hsumPos.ne' hlogGammaPos.ne']
  have hlogjDiv : Real.log j / Real.log gamma ≤
      Real.log 4 / Real.log gamma :=
    (div_le_div_iff_of_pos_right hlogGammaPos).2 hlogjLe
  have hloglog : Real.log (Real.log (j * gamma)) ≤
      Real.log (Real.log gamma) + Real.log 4 / Real.log gamma := by
    rw [hlogProd]
    linarith [hlogRatio, hdiff, hlogjDiv]
  have hlogOrd : Real.log (j * gamma) ≤
      Real.log gamma + Real.log 4 := by
    rw [hlogProd]
    linarith
  have hpowNonneg :
      0 ≤ Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) :=
    Real.rpow_nonneg hdelta _
  have hBpow : 0 ≤ B * Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) :=
    mul_nonneg hB hpowNonneg
  have hloglogWeighted :
      (2 / 3 : ℝ) * Real.log (Real.log (j * gamma)) ≤
        (2 / 3 : ℝ) *
          (Real.log (Real.log gamma) + Real.log 4 / Real.log gamma) :=
    mul_le_mul_of_nonneg_left hloglog (by norm_num)
  have hlogOrdWeighted :
      B * Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) *
          Real.log (j * gamma) ≤
        B * Real.rpow (1 - sigma + eta) (3 / 2 : ℝ) *
          (Real.log gamma + Real.log 4) :=
    mul_le_mul_of_nonneg_left hlogOrd hBpow
  unfold correctedLemma41Envelope lemma41Envelope
  linarith

/-- Literal result of the four applications of Khale Lemma 6.2 together
with the certified nonnegative trigonometric polynomial.  Unlike the printed
`(firstpart)`, each application retains its actual ordinate. -/
abbrev AppendixBLemma41TrigNaturalScales : Prop :=
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
      let eta := khaleEta B gamma
      let sigmaAux := 1 + 3.238 * (1 - beta)
      let y := (sigmaAux - beta) / eta
      0 ≤ 1 - sigmaAux + eta ∧
      0 ≤
        -17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (1 / (2 * eta)) *
          (17.145 * lemma41Envelope A B q sigmaAux eta gamma +
           10.6825 * lemma41Envelope A B q sigmaAux eta (2 * gamma) +
           4.5 * lemma41Envelope A B q sigmaAux eta (3 * gamma) +
           lemma41Envelope A B q sigmaAux eta (4 * gamma)) +
        10.01055 / (sigmaAux - 1) -
        (1 / (4 * eta)) *
          appendixBIntegralCombination chi sigmaAux eta gamma +
        33.3275 * Real.exp (-1937)

/-- Corrected counterpart of `AppendixBFirstPartRawEstimate`. -/
abbrev AppendixBFirstPartRawEstimateCorrected : Prop :=
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
      let eta := khaleEta B gamma
      let sigmaAux := 1 + 3.238 * (1 - beta)
      let y := (sigmaAux - beta) / eta
      0 ≤ 1 - sigmaAux + eta ∧
      0 ≤
        -17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (33.3275 / 2) * (1 / eta) *
          correctedLemma41Envelope A B q sigmaAux eta gamma +
        10.01055 / (sigmaAux - 1) -
        (1 / (4 * eta)) *
          appendixBIntegralCombination chi sigmaAux eta gamma +
        33.3275 * Real.exp (-1937)

/-- The explicit excess over the printed gamma-level envelope after the
collar `1 - sigma + eta <= eta` is used. -/
def firstPartHeightCorrection (B eta gamma : ℝ) : ℝ :=
  (33.3275 / 2) * (1 / eta) *
    ((2 / 3 : ℝ) * (Real.log 4 / Real.log gamma) +
      B * Real.rpow eta (3 / 2 : ℝ) * Real.log 4)

/-- Corrected final upper inequality in `(firstpart)`. -/
abbrev AppendixBFirstPartEstimateCorrected : Prop :=
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
        firstPartHeightCorrection B eta gamma

/-- The literal four-scale signed inequality implies the corrected common
envelope.  This is the exact step that the printed proof attempted with no
scale correction. -/
theorem correctedRawEstimate_of_naturalScales
    (hNatural : AppendixBLemma41TrigNaturalScales) :
    AppendixBFirstPartRawEstimateCorrected := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hn := hNatural A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  let eta := khaleEta B gamma
  let sigmaAux := 1 + 3.238 * (1 - beta)
  let y := (sigmaAux - beta) / eta
  dsimp only [eta, sigmaAux, y] at hn ⊢
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have heta : 0 < eta := by
    have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma0
    have hlogGamma : (10650 : ℝ) ≤ Real.log gamma := by
      rw [← Real.log_exp 10650]
      exact Real.log_le_log (Real.exp_pos 10650) hgamma0
    have hlogGammaPos : 0 < Real.log gamma := by linarith
    have hloglogGammaPos : 0 < Real.log (Real.log gamma) :=
      Real.log_pos (by linarith)
    exact khaleEta_pos hB hlogGammaPos hloglogGammaPos
  have h1 := lemma41Envelope_mul_le_corrected
    (A := A) (q := q) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 1) hB.le hn.1 hgamma0
    (show (1 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 4 by norm_num)
  have h2 := lemma41Envelope_mul_le_corrected
    (A := A) (q := q) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 2) hB.le hn.1 hgamma0
    (show (1 : ℝ) ≤ 2 by norm_num) (show (2 : ℝ) ≤ 4 by norm_num)
  have h3 := lemma41Envelope_mul_le_corrected
    (A := A) (q := q) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 3) hB.le hn.1 hgamma0
    (show (1 : ℝ) ≤ 3 by norm_num) (show (3 : ℝ) ≤ 4 by norm_num)
  have h4 := lemma41Envelope_mul_le_corrected
    (A := A) (q := q) (sigma := sigmaAux) (eta := eta)
    (gamma := gamma) (j := 4) hB.le hn.1 hgamma0
    (show (1 : ℝ) ≤ 4 by norm_num) (show (4 : ℝ) ≤ 4 by norm_num)
  norm_num at h1
  have hh1 := mul_le_mul_of_nonneg_left h1
    (show (0 : ℝ) ≤ 17.145 by norm_num)
  have hh2 := mul_le_mul_of_nonneg_left h2
    (show (0 : ℝ) ≤ 10.6825 by norm_num)
  have hh3 := mul_le_mul_of_nonneg_left h3
    (show (0 : ℝ) ≤ 4.5 by norm_num)
  have hsum :
      17.145 * lemma41Envelope A B q sigmaAux eta gamma +
          10.6825 * lemma41Envelope A B q sigmaAux eta (2 * gamma) +
          4.5 * lemma41Envelope A B q sigmaAux eta (3 * gamma) +
          lemma41Envelope A B q sigmaAux eta (4 * gamma) ≤
        33.3275 * correctedLemma41Envelope A B q sigmaAux eta gamma := by
    nlinarith [hh1, hh2, hh3, h4]
  have hfac : 0 < 1 / (2 * eta) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hfac.le
  refine ⟨hn.1, ?_⟩
  dsimp only [eta, sigmaAux, y] at hscaled ⊢
  have hrewrite :
      (1 / (2 * khaleEta B gamma)) *
          (33.3275 * correctedLemma41Envelope A B q
            (1 + 3.238 * (1 - beta)) (khaleEta B gamma) gamma) =
        (33.3275 / 2) * (1 / khaleEta B gamma) *
          correctedLemma41Envelope A B q
            (1 + 3.238 * (1 - beta)) (khaleEta B gamma) gamma := by
    field_simp
  rw [hrewrite] at hscaled
  linarith [hn.2, hscaled]

/-- Corrected raw Lemma-6.2 inequality plus the already certified Lemma 5.1
gives the corrected `(firstpart)` estimate. -/
theorem correctedFirstPart_of_raw_and_lemma51
    (hRaw : AppendixBFirstPartRawEstimateCorrected)
    (h51 : AppendixBLemma51Specialized) :
    AppendixBFirstPartEstimateCorrected := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hraw := hRaw A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  let delta : ℝ := 1 - beta
  let eta : ℝ := khaleEta B gamma
  let sigmaAux : ℝ := 1 + 3.238 * delta
  let y : ℝ := (sigmaAux - beta) / eta
  have hgammaPos : 0 < gamma :=
    (Real.exp_pos 10650).trans_le (hT₀.trans hgamma)
  have hbeta :=
    MAPKhaleAppendixBFirstPartSourceReduction.beta_lt_one_of_nonzero_ordinate_zero
      chi hgammaPos hzero
  refine ⟨hbeta, ?_⟩
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hsigma : 1 ≤ sigmaAux := by dsimp [sigmaAux]; nlinarith
  have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) (hT₀.trans hgamma)
  have hL : 0 < Real.log gamma := by linarith
  have hell : 0 < Real.log (Real.log gamma) := Real.log_pos (by linarith)
  have heta : 0 < eta := khaleEta_pos hB hL hell
  have h51' := h51 q chi sigmaAux eta gamma hsigma heta
  have hInv : 0 < 1 / (4 * eta) := by positivity
  have hIntegral :
      -(1 / (4 * eta)) * appendixBIntegralCombination chi sigmaAux eta gamma ≤
        (10.01055 / 2) * (1 / eta) * zetaLog eta := by
    have hm := mul_le_mul_of_nonneg_left h51' hInv.le
    calc
      -(1 / (4 * eta)) * appendixBIntegralCombination chi sigmaAux eta gamma ≤
          -((1 / (4 * eta)) * (-2 * 10.01055 * zetaLog eta)) := by
            nlinarith
      _ = (10.01055 / 2) * (1 / eta) * zetaLog eta := by ring
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 3).trans hqReal)
  have hcollar : 0 ≤ 1 - sigmaAux + eta := by
    simpa only [eta, sigmaAux, delta, y] using hraw.1
  have hcollarTop : 1 - sigmaAux + eta ≤ eta := by linarith
  have hrpow : Real.rpow (1 - sigmaAux + eta) (3 / 2 : ℝ) ≤
      Real.rpow eta (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hcollar hcollarTop (by norm_num)
  have hBterm :
      B * Real.rpow (1 - sigmaAux + eta) (3 / 2 : ℝ) *
          (Real.log gamma + Real.log 4) ≤
        B * Real.rpow eta (3 / 2 : ℝ) *
          (Real.log gamma + Real.log 4) := by
    gcongr
  have hqterm :
      (1 - sigmaAux + eta) * Real.log q ≤ eta * Real.log q :=
    mul_le_mul_of_nonneg_right hcollarTop hlogq
  have hrawIneq : 0 ≤
        -17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (33.3275 / 2) * (1 / eta) *
          correctedLemma41Envelope A B q sigmaAux eta gamma +
        10.01055 / (sigmaAux - 1) -
        (1 / (4 * eta)) *
          appendixBIntegralCombination chi sigmaAux eta gamma +
        33.3275 * Real.exp (-1937) := by
    simpa only [eta, sigmaAux, delta, y] using hraw.2
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
        33.3275 * Real.exp (-1937) +
        firstPartHeightCorrection B eta gamma
  have hcoef : 0 ≤ (33.3275 / 2) * (1 / eta) := by positivity
  have hinside :
      correctedLemma41Envelope A B q sigmaAux eta gamma ≤
        eta * Real.log q +
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
          ((2 / 3 : ℝ) * (Real.log 4 / Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log 4) := by
    unfold correctedLemma41Envelope lemma41Envelope
    linarith [hBterm, hqterm]
  have hscaled := mul_le_mul_of_nonneg_left hinside hcoef
  have hetaCancel : (1 / eta) * (eta * Real.log q) = Real.log q := by
    field_simp [heta.ne']
  unfold firstPartHeightCorrection
  nlinarith

end

end MAPKhaleAppendixBFirstPartScaleCorrected

#print axioms MAPKhaleAppendixBFirstPartScaleCorrected.lemma41Envelope_mul_le_corrected
#print axioms MAPKhaleAppendixBFirstPartScaleCorrected.correctedRawEstimate_of_naturalScales
#print axioms MAPKhaleAppendixBFirstPartScaleCorrected.correctedFirstPart_of_raw_and_lemma51
