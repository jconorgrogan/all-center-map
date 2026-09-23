import KhaleAppendixBTrigLogDerivativeCertified
import KhaleAppendixBFirstPartScaleCorrected

/-!
# Literal four-application weld below Khale Appendix B `(firstpart)`

This file contains no version of Khale Lemma 4.1 as an assumption.  Instead,
it records the four inequalities produced by the four literal applications
at `gamma, 2*gamma, 3*gamma, 4*gamma` and proves their deterministic weighted
weld.  Thus the remaining source obligation can be stated pointwise, at the
level of Lemma 4.1 itself.
-/

namespace MAPKhaleAppendixBLemma41FourApplicationWeld

open MAPKhaleAppendixBFirstPartScaleCorrected
open MAPKhaleAppendixBFirstPartAnalyticReduction
open MAPKhaleAppendixBTrigPolynomialCertified
open MAPKhaleAppendixBTrigLogDerivativeCertified

noncomputable section

/-- The selected-zero application of Lemma 4.1 at the first ordinate. -/
def selectedApplicationBound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (A B sigma eta gamma beta e : ℝ) : Prop :=
  (-logDeriv (DirichletCharacter.LFunction chi)
      ((sigma : ℂ) + Complex.I * gamma)).re ≤
    -(1 / eta) *
      ((Real.pi / 2) * Real.cot ((Real.pi / 2) * ((sigma - beta) / eta))) +
    (1 / (2 * eta)) * lemma41Envelope A B q sigma eta gamma -
    (1 / (4 * eta)) * appendixBLogIntegral chi 1 sigma eta gamma +
    e * Real.exp (-1937)

/-- An empty-selected-set application of Lemma 4.1 at the `j`th ordinate. -/
def emptyApplicationBound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (j : ℕ)
    (A B sigma eta gamma e : ℝ) : Prop :=
  (-logDeriv (DirichletCharacter.LFunction (chi ^ j))
      ((sigma : ℂ) + Complex.I * ((j : ℝ) * gamma))).re ≤
    (1 / (2 * eta)) *
      lemma41Envelope A B q sigma eta ((j : ℝ) * gamma) -
    (1 / (4 * eta)) * appendixBLogIntegral chi j sigma eta gamma +
    e * Real.exp (-1937)

/-- Exact deterministic weld of the four Lemma-4.1 applications, equation
`(5.1)`, the Euler-product positivity, the principal zeta bound, and the
uniform parity correction.  Every analytic inequality is a separate local
hypothesis; no bundled Appendix-B conclusion is assumed. -/
theorem naturalScaleConclusion_of_four_applications
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {A B sigma eta gamma beta e1 e2 e3 e4 : ℝ}
    (heta : 0 < eta) (hsigma : 1 < sigma)
    (hselected : selectedApplicationBound chi A B sigma eta gamma beta e1)
    (hempty2 : emptyApplicationBound chi 2 A B sigma eta gamma e2)
    (hempty3 : emptyApplicationBound chi 3 A B sigma eta gamma e3)
    (hempty4 : emptyApplicationBound chi 4 A B sigma eta gamma e4)
    (hzeta : (-logDeriv riemannZeta (sigma : ℂ)).re ≤ 1 / (sigma - 1))
    (he1zero : 0 ≤ e1) (he1one : e1 ≤ 1)
    (he2zero : 0 ≤ e2) (he2one : e2 ≤ 1)
    (he3zero : 0 ≤ e3) (he3one : e3 ≤ 1)
    (he4zero : 0 ≤ e4) (he4one : e4 ≤ 1) :
    0 ≤
      -17.145 * (1 / eta) *
          ((Real.pi / 2) * Real.cot
            ((Real.pi / 2) * ((sigma - beta) / eta))) +
      (1 / (2 * eta)) *
        (17.145 * lemma41Envelope A B q sigma eta gamma +
         10.6825 * lemma41Envelope A B q sigma eta (2 * gamma) +
         4.5 * lemma41Envelope A B q sigma eta (3 * gamma) +
         lemma41Envelope A B q sigma eta (4 * gamma)) +
      10.01055 / (sigma - 1) -
      (1 / (4 * eta)) *
        appendixBIntegralCombination chi sigma eta gamma +
      33.3275 * Real.exp (-1937) := by
  have hpositive := appendixB_neg_logDeriv_re_nonneg chi hsigma gamma
  have hparity := parity_correction_coefficient_le
    he1zero he1one he2zero he2one he3zero he3one he4zero he4one
  have h2 :
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
        ((sigma : ℂ) + Complex.I * (2 * gamma))).re ≤
      (1 / (2 * eta)) * lemma41Envelope A B q sigma eta (2 * gamma) -
      (1 / (4 * eta)) * appendixBLogIntegral chi 2 sigma eta gamma +
      e2 * Real.exp (-1937) := by
    simpa only [emptyApplicationBound, Nat.cast_ofNat, Complex.ofReal_ofNat] using hempty2
  have h3 :
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 3))
        ((sigma : ℂ) + Complex.I * (3 * gamma))).re ≤
      (1 / (2 * eta)) * lemma41Envelope A B q sigma eta (3 * gamma) -
      (1 / (4 * eta)) * appendixBLogIntegral chi 3 sigma eta gamma +
      e3 * Real.exp (-1937) := by
    simpa only [emptyApplicationBound, Nat.cast_ofNat, Complex.ofReal_ofNat] using hempty3
  have h4 :
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 4))
        ((sigma : ℂ) + Complex.I * (4 * gamma))).re ≤
      (1 / (2 * eta)) * lemma41Envelope A B q sigma eta (4 * gamma) -
      (1 / (4 * eta)) * appendixBLogIntegral chi 4 sigma eta gamma +
      e4 * Real.exp (-1937) := by
    simpa only [emptyApplicationBound, Nat.cast_ofNat, Complex.ofReal_ofNat] using hempty4
  unfold selectedApplicationBound at hselected
  unfold appendixBIntegralCombination
  have hetaInv : 0 < 1 / eta := one_div_pos.mpr heta
  have hweighted1 := mul_le_mul_of_nonneg_left hselected
    (by norm_num : (0 : ℝ) ≤ 17.145)
  have hweighted2 := mul_le_mul_of_nonneg_left h2
    (by norm_num : (0 : ℝ) ≤ 10.6825)
  have hweighted3 := mul_le_mul_of_nonneg_left h3
    (by norm_num : (0 : ℝ) ≤ 4.5)
  have hweighted4 := h4
  have hzetaWeighted := mul_le_mul_of_nonneg_left hzeta
    (by norm_num : (0 : ℝ) ≤ 10.01055)
  have hcorrection :
      (17.145 * e1 + 10.6825 * e2 + 4.5 * e3 + e4) *
          Real.exp (-1937) ≤
        33.3275 * Real.exp (-1937) :=
    mul_le_mul_of_nonneg_right hparity.2 (Real.exp_pos _).le
  let U : ℝ :=
    10.01055 * (1 / (sigma - 1)) +
    17.145 *
      (-(1 / eta) *
          ((Real.pi / 2) * Real.cot
            ((Real.pi / 2) * ((sigma - beta) / eta))) +
        (1 / (2 * eta)) * lemma41Envelope A B q sigma eta gamma -
        (1 / (4 * eta)) * appendixBLogIntegral chi 1 sigma eta gamma +
        e1 * Real.exp (-1937)) +
    10.6825 *
      ((1 / (2 * eta)) * lemma41Envelope A B q sigma eta (2 * gamma) -
        (1 / (4 * eta)) * appendixBLogIntegral chi 2 sigma eta gamma +
        e2 * Real.exp (-1937)) +
    4.5 *
      ((1 / (2 * eta)) * lemma41Envelope A B q sigma eta (3 * gamma) -
        (1 / (4 * eta)) * appendixBLogIntegral chi 3 sigma eta gamma +
        e3 * Real.exp (-1937)) +
      ((1 / (2 * eta)) * lemma41Envelope A B q sigma eta (4 * gamma) -
        (1 / (4 * eta)) * appendixBLogIntegral chi 4 sigma eta gamma +
        e4 * Real.exp (-1937))
  have hsumUpper :
      10.01055 * (-logDeriv riemannZeta (sigma : ℂ)).re +
            17.145 * (-logDeriv (DirichletCharacter.LFunction chi)
              ((sigma : ℂ) + Complex.I * gamma)).re +
          10.6825 * (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
              ((sigma : ℂ) + Complex.I * (2 * gamma))).re +
        4.5 * (-logDeriv (DirichletCharacter.LFunction (chi ^ 3))
              ((sigma : ℂ) + Complex.I * (3 * gamma))).re +
          (-logDeriv (DirichletCharacter.LFunction (chi ^ 4))
              ((sigma : ℂ) + Complex.I * (4 * gamma))).re ≤ U := by
    dsimp only [U]
    linarith
  have hU : 0 ≤ U := hpositive.trans hsumUpper
  let Base : ℝ :=
      -17.145 * (1 / eta) *
          ((Real.pi / 2) * Real.cot
            ((Real.pi / 2) * ((sigma - beta) / eta))) +
      (1 / (2 * eta)) *
        (17.145 * lemma41Envelope A B q sigma eta gamma +
         10.6825 * lemma41Envelope A B q sigma eta (2 * gamma) +
         4.5 * lemma41Envelope A B q sigma eta (3 * gamma) +
         lemma41Envelope A B q sigma eta (4 * gamma)) +
      10.01055 / (sigma - 1) -
      (1 / (4 * eta)) *
        (17.145 * appendixBLogIntegral chi 1 sigma eta gamma +
         10.6825 * appendixBLogIntegral chi 2 sigma eta gamma +
         4.5 * appendixBLogIntegral chi 3 sigma eta gamma +
         appendixBLogIntegral chi 4 sigma eta gamma)
  have hUeq : U = Base +
      (17.145 * e1 + 10.6825 * e2 + 4.5 * e3 + e4) *
        Real.exp (-1937) := by
    dsimp only [U, Base]
    ring
  have hBase : 0 ≤ Base + 33.3275 * Real.exp (-1937) := by
    rw [hUeq] at hU
    exact hU.trans (by linarith)
  simpa only [Base] using hBase

end
end MAPKhaleAppendixBLemma41FourApplicationWeld

#print axioms MAPKhaleAppendixBLemma41FourApplicationWeld.naturalScaleConclusion_of_four_applications
