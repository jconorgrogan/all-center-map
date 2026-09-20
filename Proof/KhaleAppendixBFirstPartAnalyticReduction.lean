import KhaleAppendixBFirstPartSourceReduction
import KhaleAppendixBTrigPolynomialCertified
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Analytic source leaves under Khale Appendix B `(firstpart)`

This opens the remaining first-part upper estimate into the two signed
statements actually used from the source proof:

* the result of Lemma 6.2 plus the certified trigonometric polynomial, before
  the logarithmic L-integrals are discarded;
* Lemma 5.1 specialized to `a₁=0.225`, `a₂=0.9`.

The theorem below certifies the sign-preserving weld between them.  In
particular the integral combination remains visible; it is not replaced by a
premise equivalent to the final zero-free statement.
-/

namespace MAPKhaleAppendixBFirstPartAnalyticReduction

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixB1ZetaReduction
open MAPKhaleAppendixBFirstPartSourceReduction
open MeasureTheory

noncomputable section

/-- The logarithmic L-integral appearing in Lemmas 4.1 and 5.1. -/
def appendixBLogIntegral {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (j : ℕ)
    (sigma eta gamma : ℝ) : ℝ :=
  ∫ u : ℝ,
    Real.log ‖DirichletCharacter.LFunction (chi ^ j)
      (((sigma + eta : ℝ) : ℂ) +
        Complex.I * (((j : ℝ) * gamma + 2 * eta * u / Real.pi : ℝ) : ℂ))‖ /
      (Real.cosh u) ^ 2

/-- The exact coefficient combination in the Appendix-B specialization of
Lemma 5.1. -/
def appendixBIntegralCombination {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma eta gamma : ℝ) : ℝ :=
  17.145 * appendixBLogIntegral chi 1 sigma eta gamma +
  10.6825 * appendixBLogIntegral chi 2 sigma eta gamma +
  4.5 * appendixBLogIntegral chi 3 sigma eta gamma +
  appendixBLogIntegral chi 4 sigma eta gamma

/-- Literal signed consequence of applying Khale Lemma 6.2 at
`sigma + i*j*gamma`, summing with (5.1), and bounding the principal term.
The first conjunct records the collar needed by Lemma 6.2 and by monotonicity
of the `3/2` power.  The final parity correction uses the uniform safe
coefficient `b₅=33.3275`; the printed `(b₂+b₄)` only covers an odd starting
character and undercounts the even-character case. -/
abbrev AppendixBFirstPartRawEstimate : Prop :=
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
          ((1 - sigmaAux + eta) * Real.log q +
            (2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow (1 - sigmaAux + eta) (3 / 2 : ℝ) *
              Real.log gamma +
            Real.log (A + 1)) +
        10.01055 / (sigmaAux - 1) -
        (1 / (4 * eta)) *
          appendixBIntegralCombination chi sigmaAux eta gamma +
        33.3275 * Real.exp (-1937)

/-- Exact Appendix-B specialization of Khale Lemma 5.1.  The published proof
reduces this to Ford's Fourier identity
`∫ exp(i y u)/cosh(u)^2 du = pi*y/sinh(pi*y/2)` and the Euler product. -/
abbrev AppendixBLemma51Specialized : Prop :=
  ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (sigma eta gamma : ℝ),
    1 ≤ sigma → 0 < eta →
    -2 * 10.01055 * zetaLog eta ≤
      appendixBIntegralCombination chi sigma eta gamma

/-- The raw Lemma-6.2 inequality and signed Lemma-5.1 integral bound imply the
published final upper inequality `(firstpart)`. -/
theorem firstPartUpper_of_raw_and_lemma51
    (hRaw : AppendixBFirstPartRawEstimate)
    (h51 : AppendixBLemma51Specialized) :
    AppendixBFirstPartUpperEstimate := by
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
  have hbeta := beta_lt_one_of_nonzero_ordinate_zero chi hgammaPos hzero
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
  have hcollarTop : 1 - sigmaAux + eta ≤ eta := by
    linarith
  have hrpow : Real.rpow (1 - sigmaAux + eta) (3 / 2 : ℝ) ≤
      Real.rpow eta (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hcollar hcollarTop (by norm_num)
  have hBterm :
      B * Real.rpow (1 - sigmaAux + eta) (3 / 2 : ℝ) * Real.log gamma ≤
        B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma := by
    gcongr
  have hqterm :
      (1 - sigmaAux + eta) * Real.log q ≤ eta * Real.log q := by
    exact mul_le_mul_of_nonneg_right hcollarTop hlogq
  have hrawIneq : 0 ≤
        -17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (33.3275 / 2) * (1 / eta) *
          ((1 - sigmaAux + eta) * Real.log q +
            (2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow (1 - sigmaAux + eta) (3 / 2 : ℝ) *
              Real.log gamma +
            Real.log (A + 1)) +
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
        33.3275 * Real.exp (-1937)
  have hcoef : 0 ≤ (33.3275 / 2) * (1 / eta) := by positivity
  have hinside :
      (1 - sigmaAux + eta) * Real.log q +
          (2 / 3 : ℝ) * Real.log (Real.log gamma) +
          B * Real.rpow (1 - sigmaAux + eta) (3 / 2 : ℝ) * Real.log gamma +
          Real.log (A + 1) ≤
        eta * Real.log q +
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
          B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
          Real.log (A + 1)) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hinside hcoef
  have hetaCancel : (1 / eta) * (eta * Real.log q) = Real.log q := by
    field_simp [heta.ne']
  nlinarith

end
end MAPKhaleAppendixBFirstPartAnalyticReduction

#print axioms MAPKhaleAppendixBFirstPartAnalyticReduction.firstPartUpper_of_raw_and_lemma51
