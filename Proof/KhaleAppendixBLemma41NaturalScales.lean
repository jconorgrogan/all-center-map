import KhaleAppendixBLemma41FourApplicationWeld
import KhaleAppendixBLemma41Applicability
import KhaleLemma41PointwiseSource

/-!
# Khale Appendix-B natural-scale detector from Lemma 4.1

This module inhabits `AppendixBLemma41TrigNaturalScales` from the literal
finite-selected-set statement of Khale Lemma 4.1.  The four applications keep
their actual heights `gamma, 2*gamma, 3*gamma, 4*gamma`; no gamma-level
positive envelope is substituted.
-/

namespace MAPKhaleAppendixBLemma41NaturalScales

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixBNumericalCore
open MAPKhaleAppendixB1FirstPartReduction
open MAPKhaleAppendixBFirstPartSourceReduction
open MAPKhaleAppendixBFirstPartScaleCorrected
open MAPKhaleAppendixBFirstPartAnalyticReduction
open MAPKhaleAppendixBLemma41FourApplicationWeld
open MAPKhaleAppendixBLemma41Applicability
open MAPKhaleLemma41PointwiseSource

noncomputable section

/-- The exact zeta part of Ford's elementary Lemma 3.1 on the tiny interval
actually reached by Appendix B.  The historical all-`sigma > 1` interface was
unnecessarily strong: the Appendix-B choices force `sigma ≤ 1.001`.  This is
deliberately separate from Khale Lemma 4.1. -/
abbrev FordLemma31ZetaLogDerivativeBound : Prop :=
  ∀ sigma : ℝ, 1 < sigma → sigma ≤ 1.001 →
    (-logDeriv riemannZeta (sigma : ℂ)).re ≤ 1 / (sigma - 1)

/-- Full natural-scale Appendix-B detector from the two source-level analytic
inputs: Khale Lemma 4.1 and the zeta case of Ford Lemma 3.1.  All parameter
applicability, Euler-product positivity, four-height summation, and correction
bookkeeping are certified in Lean. -/
theorem appendixBLemma41TrigNaturalScales_of_source
    (h41 : KhaleLemma41FiniteSelectedEstimate)
    (hzetaSource : FordLemma31ZetaLogDerivativeBound) :
    AppendixBLemma41TrigNaturalScales := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  let eta : ℝ := khaleEta B gamma
  let sigma : ℝ := 1 + 3.238 * (1 - beta)
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hgammaPos : 0 < gamma := (Real.exp_pos _).trans_le hgamma0
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
  have hbeta : beta < 1 :=
    beta_lt_one_of_nonzero_ordinate_zero chi hgammaPos hzero
  have hdelta : 0 < 1 - beta := by linarith
  have hsigma : 1 < sigma := by
    dsimp only [sigma]
    nlinarith
  have hdeltaEta : (1 - beta) / eta ≤ 0.0029 := by
    dsimp only [eta]
    exact appendixB_delta_div_eta_le_0029
      hB hL hell hell924 hq hgap
  have hdeltaUpper : 1 - beta ≤ 0.0029 * eta := by
    exact (div_le_iff₀ heta).mp hdeltaEta
  have hselectedStrip : sigma - eta ≤ beta := by
    dsimp only [sigma]
    nlinarith
  have hetaTen : eta < 10 := hetaTop.trans_lt (by norm_num)
  have hsigmaMinus : 1 / 2 < sigma - eta := by
    nlinarith
  have hcollarBase : sigma ≤ 1 + eta -
      1.92 * Real.rpow (Real.log (gamma / 100)) (-2 / 3 : ℝ) := by
    dsimp only [sigma, eta]
    exact appendixB_sigmaAux_collar
      hB hBtop hgamma0 hell924 hq hgap
  have hcollarNonneg : 0 ≤ 1 - sigma + eta := by
    have hlog100 : Real.log (100 : ℝ) < 99 := by
      have := Real.log_lt_sub_one_of_pos (x := (100 : ℝ))
        (by norm_num) (by norm_num)
      norm_num at this ⊢
      exact this
    have hlogDiv : 0 < Real.log (gamma / 100) := by
      rw [Real.log_div hgammaPos.ne' (by norm_num : (100 : ℝ) ≠ 0)]
      linarith
    have hp := Real.rpow_nonneg hlogDiv.le (-2 / 3 : ℝ)
    nlinarith
  have hexpHeight : Real.exp 1938 ≤ gamma := by
    exact (Real.exp_le_exp.mpr (by norm_num)).trans hgamma0
  have hmulHeight (j : ℝ) (hj : 1 ≤ j) : gamma ≤ j * gamma := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hj hgammaPos.le
  have hcollarMul (j : ℝ) (hj : 1 ≤ j) :
      sigma ≤ 1 + eta -
        1.92 * Real.rpow (Real.log ((j * gamma) / 100))
          (-2 / 3 : ℝ) := by
    have hr := collar_rpow_mul_le_base hgamma0 hj
    nlinarith
  let rho : ℂ := (beta : ℂ) + (gamma : ℂ) * Complex.I
  have hrhoZero : DirichletCharacter.LFunction chi rho = 0 := by
    simpa only [rho] using hzero
  have hrhoRe : rho.re = beta := by
    dsimp only [rho]
    simp
  have hselectedMembers : ∀ z ∈ ({rho} : Finset ℂ),
      sigma - eta ≤ z.re ∧ z.re ≤ 1 ∧
        DirichletCharacter.LFunction chi z = 0 := by
    intro z hz
    simp only [Finset.mem_singleton] at hz
    subst z
    refine ⟨?_, ?_, hrhoZero⟩
    · rw [hrhoRe]
      exact hselectedStrip
    · rw [hrhoRe]
      exact hbeta.le
  have happ1 := h41 A B hA hB hFord q chi sigma eta gamma ({rho} : Finset ℂ)
    hq hexpHeight hqheight heta hetaTen hsigmaMinus hsigma.le hcollarBase
    hselectedMembers
  rcases happ1 with ⟨e1, he1zero, he1one, happ1⟩
  have hint1 : lemma41LogIntegral chi sigma eta gamma =
      appendixBLogIntegral chi 1 sigma eta gamma := by
    simpa using lemma41LogIntegral_power_eq_appendixB chi 1 sigma eta gamma
  have hkernel : lemma41CotKernel sigma eta gamma rho =
      (1 / eta) * ((Real.pi / 2) * Real.cot
        ((Real.pi / 2) * ((sigma - beta) / eta))) := by
    simpa only [rho] using
      lemma41CotKernel_aligned (sigma := sigma) (eta := eta)
        (t := gamma) (beta := beta) heta.ne'
  have hbound1 : selectedApplicationBound chi A B sigma eta gamma beta e1 := by
    unfold selectedApplicationBound
    rw [Finset.sum_singleton, hkernel, hint1] at happ1
    convert happ1 using 1 <;> ring
  have hemptyMembers (j : ℕ) : ∀ z ∈ (∅ : Finset ℂ),
      sigma - eta ≤ z.re ∧ z.re ≤ 1 ∧
        DirichletCharacter.LFunction (chi ^ j) z = 0 := by
    intro z hz
    simp at hz
  have applicationAt (j : ℕ) (hj0 : j ≠ 0) (hj1 : (1 : ℝ) ≤ j) :
      ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1 ∧
        emptyApplicationBound chi j A B sigma eta gamma e := by
    have hjHeight : Real.exp 1938 ≤ (j : ℝ) * gamma :=
      hexpHeight.trans (hmulHeight j hj1)
    have hjQ : Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤
        (j : ℝ) * gamma := hqheight.trans (hmulHeight j hj1)
    have happ := h41 A B hA hB hFord q (chi ^ j) sigma eta
      ((j : ℝ) * gamma) (∅ : Finset ℂ) hq hjHeight hjQ heta hetaTen
      hsigmaMinus hsigma.le (hcollarMul j hj1) (hemptyMembers j)
    rcases happ with ⟨e, he0, he1, happ⟩
    refine ⟨e, he0, he1, ?_⟩
    unfold emptyApplicationBound
    rw [Finset.sum_empty, neg_zero, zero_add,
      lemma41LogIntegral_power_eq_appendixB chi j sigma eta gamma] at happ
    convert happ using 1 <;> push_cast <;> ring
  rcases applicationAt 2 (by norm_num) (by norm_num) with
    ⟨e2, he2zero, he2one, hbound2⟩
  rcases applicationAt 3 (by norm_num) (by norm_num) with
    ⟨e3, he3zero, he3one, hbound3⟩
  rcases applicationAt 4 (by norm_num) (by norm_num) with
    ⟨e4, he4zero, he4one, hbound4⟩
  have hsigmaTop : sigma ≤ 1.001 := by
    have hdeltaUpper' : 1 - beta ≤ 0.0029 * 0.06 :=
      hdeltaUpper.trans (mul_le_mul_of_nonneg_left hetaTop (by norm_num))
    dsimp only [sigma]
    nlinarith
  have hzeta := hzetaSource sigma hsigma hsigmaTop
  refine ⟨hcollarNonneg, ?_⟩
  simpa only [sigma, eta] using
    naturalScaleConclusion_of_four_applications chi heta hsigma
      hbound1 hbound2 hbound3 hbound4 hzeta
      he1zero he1one he2zero he2one he3zero he3one he4zero he4one

end
end MAPKhaleAppendixBLemma41NaturalScales

#print axioms MAPKhaleAppendixBLemma41NaturalScales.appendixBLemma41TrigNaturalScales_of_source
