import KhaleAppendixBFirstPartScaleCorrected
import KhaleAppendixBTrigLogDerivativeCertified
import KhaleAppendixBLemma41Applicability

/-!
# Source-faithful four-height Khale Lemma 6.2 weld

This file removes the trigonometric/Euler-product argument from the analytic
source surface of Appendix B.  The remaining large-height input is the four
literal specializations of Khale's Lemma 6.2, at ordinates
`gamma, 2*gamma, 3*gamma, 4*gamma`.  In particular, the source proposition
does not already assert the combined `(B.4)` inequality.

The elementary zeta logarithmic-derivative estimate from Khale's Lemma 4.1 is
kept as a separate source statement.  Everything which combines these five
upper bounds with the nonnegative trigonometric polynomial is proved here.
-/

namespace MAPKhaleAppendixBLemma62NaturalScaleWeld

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixB1FirstPartReduction MAPKhaleAppendixBLemma41Applicability
open MAPKhaleAppendixBFirstPartAnalyticReduction
open MAPKhaleAppendixBFirstPartScaleCorrected
open MAPKhaleAppendixBFirstPartSourceReduction
open MAPKhaleAppendixBTrigLogDerivativeCertified

noncomputable section

/-- The exact real-axis zeta estimate used in Appendix B.  This is the second
inequality of Khale's Lemma 4.1, isolated from the four character bounds. -/
abbrev AppendixBLemma41ZetaLogDerivativeBound : Prop :=
  ∀ sigma : ℝ, 1 < sigma → sigma ≤ 1.001 →
    (-logDeriv riemannZeta (sigma : ℂ)).re ≤ 1 / (sigma - 1)

/-- The four source inequalities obtained by applying Khale Lemma 6.2 at its
actual ordinates.  The exponentially small parity term is enlarged to one
copy of `exp (-1937)` in each row; after weighting this costs exactly at most
`b5 * exp (-1937)`.  The first conjunct records the elementary admissibility
collar needed for the four applications.

Unlike `AppendixBLemma41TrigNaturalScales`, this proposition contains neither
the trigonometric-polynomial positivity nor the linear combination of rows. -/
abbrev AppendixBLemma62FourNaturalScaleBounds : Prop :=
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
      (-logDeriv (DirichletCharacter.LFunction chi)
          ((sigmaAux : ℂ) + Complex.I * (gamma : ℂ))).re ≤
        -(1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
          (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta gamma -
          (1 / (4 * eta)) * appendixBLogIntegral chi 1 sigmaAux eta gamma +
          Real.exp (-1937) ∧
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
          ((sigmaAux : ℂ) + Complex.I * ((2 * gamma : ℝ) : ℂ))).re ≤
        (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (2 * gamma) -
          (1 / (4 * eta)) * appendixBLogIntegral chi 2 sigmaAux eta gamma +
          Real.exp (-1937) ∧
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 3))
          ((sigmaAux : ℂ) + Complex.I * ((3 * gamma : ℝ) : ℂ))).re ≤
        (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (3 * gamma) -
          (1 / (4 * eta)) * appendixBLogIntegral chi 3 sigmaAux eta gamma +
          Real.exp (-1937) ∧
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 4))
          ((sigmaAux : ℂ) + Complex.I * ((4 * gamma : ℝ) : ℂ))).re ≤
        (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (4 * gamma) -
          (1 / (4 * eta)) * appendixBLogIntegral chi 4 sigmaAux eta gamma +
          Real.exp (-1937)

/-- The four literal Lemma-6.2 rows, the elementary zeta bound, and the
certified Euler-product positivity imply the exact natural-scale `(B.4)`
interface consumed by the repaired Appendix-B chain. -/
theorem lemma41TrigNaturalScales_of_lemma62Four_and_zeta
    (h62 : AppendixBLemma62FourNaturalScaleBounds)
    (hZeta : AppendixBLemma41ZetaLogDerivativeBound) :
    AppendixBLemma41TrigNaturalScales := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hrows := h62 A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  let eta : ℝ := khaleEta B gamma
  let sigmaAux : ℝ := 1 + 3.238 * (1 - beta)
  let y : ℝ := (sigmaAux - beta) / eta
  have hgammaPos : 0 < gamma :=
    (Real.exp_pos 10650).trans_le (hT₀.trans hgamma)
  have hbeta : beta < 1 :=
    beta_lt_one_of_nonzero_ordinate_zero chi hgammaPos hzero
  have hsigma : 1 < sigmaAux := by
    dsimp [sigmaAux]
    nlinarith
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos _) hgamma0
  have hL : 0 < Real.log gamma := by linarith
  have hell : 0 < Real.log (Real.log gamma) := Real.log_pos (by linarith)
  have hell924 := loglog_gamma_lower_924 hB hBtop hT₀ hgamma hloglog
  have heta : 0 < eta := by
    dsimp only [eta]
    exact khaleEta_pos hB hL hell
  have hratioGamma : 5110.6 / B ≤
      Real.log gamma / Real.log (Real.log gamma) :=
    hratio.trans (log_ratio_mono_from_exp10650 hT₀ hgamma)
  have hetaTop : eta ≤ 0.06 := by
    dsimp only [eta]
    exact khaleEta_le_point_zero_six_of_ratio hB hL hell hratioGamma
  have hdeltaEta : (1 - beta) / eta ≤ 0.0029 := by
    dsimp only [eta]
    exact appendixB_delta_div_eta_le_0029
      hB hL hell hell924 hq hgap
  have hdeltaUpper : 1 - beta ≤ 0.0029 * eta :=
    (div_le_iff₀ heta).mp hdeltaEta
  have hsigmaTop : sigmaAux ≤ 1.001 := by
    have hdeltaUpper' : 1 - beta ≤ 0.0029 * 0.06 :=
      hdeltaUpper.trans (mul_le_mul_of_nonneg_left hetaTop (by norm_num))
    dsimp only [sigmaAux]
    nlinarith
  have htrig := appendixB_neg_logDeriv_re_nonneg chi hsigma gamma
  have hzeta := hZeta sigmaAux hsigma hsigmaTop
  have hrows' :
      0 ≤ 1 - sigmaAux + eta ∧
      (-logDeriv (DirichletCharacter.LFunction chi)
          ((sigmaAux : ℂ) + Complex.I * (gamma : ℂ))).re ≤
        -(1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
          (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta gamma -
          (1 / (4 * eta)) * appendixBLogIntegral chi 1 sigmaAux eta gamma +
          Real.exp (-1937) ∧
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
          ((sigmaAux : ℂ) + Complex.I * ((2 * gamma : ℝ) : ℂ))).re ≤
        (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (2 * gamma) -
          (1 / (4 * eta)) * appendixBLogIntegral chi 2 sigmaAux eta gamma +
          Real.exp (-1937) ∧
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 3))
          ((sigmaAux : ℂ) + Complex.I * ((3 * gamma : ℝ) : ℂ))).re ≤
        (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (3 * gamma) -
          (1 / (4 * eta)) * appendixBLogIntegral chi 3 sigmaAux eta gamma +
          Real.exp (-1937) ∧
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 4))
          ((sigmaAux : ℂ) + Complex.I * ((4 * gamma : ℝ) : ℂ))).re ≤
        (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (4 * gamma) -
          (1 / (4 * eta)) * appendixBLogIntegral chi 4 sigmaAux eta gamma +
          Real.exp (-1937) := by
    simpa only [eta, sigmaAux, y] using hrows
  refine ⟨hrows'.1, ?_⟩
  have htrig' :
      0 ≤ 10.01055 * (-logDeriv riemannZeta (sigmaAux : ℂ)).re +
        17.145 * (-logDeriv (DirichletCharacter.LFunction chi)
          ((sigmaAux : ℂ) + Complex.I * (gamma : ℂ))).re +
        10.6825 * (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
          ((sigmaAux : ℂ) + Complex.I * ((2 * gamma : ℝ) : ℂ))).re +
        4.5 * (-logDeriv (DirichletCharacter.LFunction (chi ^ 3))
          ((sigmaAux : ℂ) + Complex.I * ((3 * gamma : ℝ) : ℂ))).re +
        (-logDeriv (DirichletCharacter.LFunction (chi ^ 4))
          ((sigmaAux : ℂ) + Complex.I * ((4 * gamma : ℝ) : ℂ))).re := by
    simpa using htrig
  let Z : ℝ := (-logDeriv riemannZeta (sigmaAux : ℂ)).re
  let D1 : ℝ := (-logDeriv (DirichletCharacter.LFunction chi)
    ((sigmaAux : ℂ) + Complex.I * (gamma : ℂ))).re
  let D2 : ℝ := (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
    ((sigmaAux : ℂ) + Complex.I * ((2 * gamma : ℝ) : ℂ))).re
  let D3 : ℝ := (-logDeriv (DirichletCharacter.LFunction (chi ^ 3))
    ((sigmaAux : ℂ) + Complex.I * ((3 * gamma : ℝ) : ℂ))).re
  let D4 : ℝ := (-logDeriv (DirichletCharacter.LFunction (chi ^ 4))
    ((sigmaAux : ℂ) + Complex.I * ((4 * gamma : ℝ) : ℂ))).re
  let U1 : ℝ :=
    -(1 / eta) * ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
      (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta gamma -
      (1 / (4 * eta)) * appendixBLogIntegral chi 1 sigmaAux eta gamma +
      Real.exp (-1937)
  let U2 : ℝ :=
    (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (2 * gamma) -
      (1 / (4 * eta)) * appendixBLogIntegral chi 2 sigmaAux eta gamma +
      Real.exp (-1937)
  let U3 : ℝ :=
    (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (3 * gamma) -
      (1 / (4 * eta)) * appendixBLogIntegral chi 3 sigmaAux eta gamma +
      Real.exp (-1937)
  let U4 : ℝ :=
    (1 / (2 * eta)) * lemma41Envelope A B q sigmaAux eta (4 * gamma) -
      (1 / (4 * eta)) * appendixBLogIntegral chi 4 sigmaAux eta gamma +
      Real.exp (-1937)
  have htrigD : 0 ≤ 10.01055 * Z + 17.145 * D1 +
      10.6825 * D2 + 4.5 * D3 + D4 := by
    simpa only [Z, D1, D2, D3, D4] using htrig'
  have hzetaZ : Z ≤ 1 / (sigmaAux - 1) := by
    simpa only [Z] using hzeta
  have hD1 : D1 ≤ U1 := by simpa only [D1, U1] using hrows'.2.1
  have hD2 : D2 ≤ U2 := by simpa only [D2, U2] using hrows'.2.2.1
  have hD3 : D3 ≤ U3 := by simpa only [D3, U3] using hrows'.2.2.2.1
  have hD4 : D4 ≤ U4 := by simpa only [D4, U4] using hrows'.2.2.2.2
  have hcombined :
      0 ≤ 10.01055 * (1 / (sigmaAux - 1)) +
        17.145 * U1 + 10.6825 * U2 + 4.5 * U3 + U4 := by
    linarith
  change 0 ≤
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
  dsimp only [U1, U2, U3, U4] at hcombined
  unfold appendixBIntegralCombination
  convert hcombined using 1
  ring

end
end MAPKhaleAppendixBLemma62NaturalScaleWeld

#print axioms MAPKhaleAppendixBLemma62NaturalScaleWeld.lemma41TrigNaturalScales_of_lemma62Four_and_zeta
