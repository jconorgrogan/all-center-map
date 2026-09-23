import FordScaledBlaschkeFill
import FordScaledCanonicalCorrection

open scoped BigOperators
noncomputable section
namespace FordScaledBlaschkeLogDerivative

open Complex ComplexConjugate Set Metric Filter Topology
open FiniteBlaschkeAlgebra FordScaledBlaschkeFill
open WideDiskLocalLogDerivative FordScaledCanonicalCorrection

/-- Exact local logarithmic derivative decomposition for a generic scaled
Blaschke fill.  The normal-form germ is used explicitly at the evaluation
point, so this is an identity of derivatives rather than a pointwise shortcut. -/
theorem logDeriv_scaledBlaschkeFill_decomposition
    {a : ℝ} (ha : 0 < a) {c : ℂ} {f : ℂ → ℂ} {S : Finset ℂ}
    {m : ℂ → ℕ} {s : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c (3 * a)))
    (hS : ∀ ρ ∈ S, ρ ∈ ball c (3 * a))
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ)
    (hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤)
    (hs : s ∈ ball c a) (hfs : f s ≠ 0) (hsF : s ∉ S) :
    logDeriv f s =
      logDeriv (scaledBlaschkeFill f c (3 * a) S m) s +
        ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) -
        ∑ ρ ∈ S, (m ρ : ℂ) *
          logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s := by
  have ha3 : 0 < 3 * a := by positivity
  have hsclosed : s ∈ closedBall c (3 * a) := by
    rw [mem_closedBall]
    exact (mem_ball.mp hs).le.trans (by linarith)
  have hprodMer :
      MeromorphicOn (finiteBlaschkeProduct c (3 * a) S m) Set.univ := by
    change MeromorphicOn
      (fun z : ℂ => ∏ ρ ∈ S,
        (shiftedCanonicalFactor c (3 * a) ρ z) ^ m ρ) Set.univ
    apply MeromorphicOn.fun_prod
    intro ρ hρ
    change MeromorphicOn
      ((shiftedCanonicalFactor c (3 * a) ρ) ^ m ρ) Set.univ
    apply MeromorphicOn.pow
    intro z hz
    unfold shiftedCanonicalFactor Complex.canonicalFactor
    fun_prop
  let raw : ℂ → ℂ := fun z =>
    f z * finiteBlaschkeProduct c (3 * a) S m z
  have hrawMer : MeromorphicOn raw (closedBall c (3 * a)) := by
    apply MeromorphicOn.mul
    · exact hf.meromorphicOn
    · intro z hz
      exact hprodMer z (Set.mem_univ z)
  have hprodAn :
      AnalyticAt ℂ (finiteBlaschkeProduct c (3 * a) S m) s := by
    change AnalyticAt ℂ
      (fun z : ℂ => ∏ ρ ∈ S,
        (shiftedCanonicalFactor c (3 * a) ρ z) ^ m ρ) s
    apply Finset.analyticAt_fun_prod
    intro ρ hρ
    have hsρ : s ≠ ρ := by
      intro h
      apply hsF
      rwa [h]
    have hne : s - c ≠ ρ - c :=
      fun h => hsρ (sub_left_inj.mp h)
    have hcan := Complex.analyticOnNhd_canonicalFactor
      (3 * a) (ρ - c) (s - c) hne
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - c) s := by fun_prop
    exact (AnalyticAt.comp (f := fun z : ℂ => z - c)
      (x := s) hcan hsub).pow _
  have hrawAn : AnalyticAt ℂ raw s :=
    (hf s hsclosed).mul hprodAn
  have heqNF : toMeromorphicNFAt raw s = raw :=
    toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt
  have hevent : scaledBlaschkeFill f c (3 * a) S m =ᶠ[𝓝 s] raw := by
    unfold scaledBlaschkeFill
    exact (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
      hrawMer hsclosed).trans
      (Filter.Eventually.of_forall fun z => by rw [heqNF])
  have hlogfill :
      logDeriv (scaledBlaschkeFill f c (3 * a) S m) s = logDeriv raw s := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [hevent.deriv_eq, hevent.eq_of_nhds]
  have hprod0 : finiteBlaschkeProduct c (3 * a) S m s ≠ 0 := by
    simp only [finiteBlaschkeProduct, Finset.prod_ne_zero_iff]
    intro ρ hρ
    apply pow_ne_zero
    apply Complex.canonicalFactor_ne_zero
    · simpa [mem_ball, dist_eq_norm] using hS ρ hρ
    · simpa [mem_closedBall, dist_eq_norm] using hsclosed
    · intro h
      apply hsF
      exact (sub_left_inj.mp h) ▸ hρ
  have hlograw :
      logDeriv raw s = logDeriv f s +
        logDeriv (finiteBlaschkeProduct c (3 * a) S m) s := by
    dsimp [raw]
    exact logDeriv_mul s hfs hprod0
      (hf s hsclosed).differentiableAt hprodAn.differentiableAt
  have hprodLog :
      logDeriv (finiteBlaschkeProduct c (3 * a) S m) s =
        ∑ ρ ∈ S,
          logDeriv (fun z : ℂ =>
            (shiftedCanonicalFactor c (3 * a) ρ z) ^ m ρ) s := by
    change logDeriv (fun z : ℂ => ∏ ρ ∈ S,
      (shiftedCanonicalFactor c (3 * a) ρ z) ^ m ρ) s = _
    rw [logDeriv_fun_prod]
    · intro ρ hρ
      have hsρ : s ≠ ρ := by
        intro h
        apply hsF
        rwa [h]
      apply pow_ne_zero
      apply Complex.canonicalFactor_ne_zero
      · simpa [mem_ball, dist_eq_norm] using hS ρ hρ
      · simpa [mem_closedBall, dist_eq_norm] using hsclosed
      · intro h
        exact hsρ (sub_left_inj.mp h)
    · intro ρ hρ
      have hsρ : s ≠ ρ := by
        intro h
        apply hsF
        rwa [h]
      have hne : s - c ≠ ρ - c :=
        fun h => hsρ (sub_left_inj.mp h)
      have hcan := Complex.analyticOnNhd_canonicalFactor
        (3 * a) (ρ - c) (s - c) hne
      have hsub : AnalyticAt ℂ (fun z : ℂ => z - c) s := by fun_prop
      exact ((AnalyticAt.comp (f := fun z : ℂ => z - c)
        (x := s) hcan hsub).pow _).differentiableAt
  have hsum :
      (∑ ρ ∈ S,
          logDeriv (fun z : ℂ =>
            (shiftedCanonicalFactor c (3 * a) ρ z) ^ m ρ) s) +
        ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) =
      ∑ ρ ∈ S, (m ρ : ℂ) *
        logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hsρ : s ≠ ρ := by
      intro h
      apply hsF
      rwa [h]
    have hne : s - c ≠ ρ - c :=
      fun h => hsρ (sub_left_inj.mp h)
    have hcan := Complex.analyticOnNhd_canonicalFactor
      (3 * a) (ρ - c) (s - c) hne
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - c) s := by fun_prop
    have hdiff : DifferentiableAt ℂ
        (shiftedCanonicalFactor c (3 * a) ρ) s :=
      (AnalyticAt.comp (f := fun z : ℂ => z - c)
        (x := s) hcan hsub).differentiableAt
    rw [logDeriv_fun_pow hdiff]
    have hfactor := logDeriv_shiftedCanonicalFactor_add_inv
      (c := c) (ρ := ρ) (s := s) (R := 3 * a)
      (by linarith) hsρ
      (shiftedCanonicalNumerator_ne_zero ha (hS ρ hρ) hs)
    push_cast
    linear_combination (m ρ : ℂ) * hfactor
  calc
    logDeriv f s = logDeriv raw s -
        logDeriv (finiteBlaschkeProduct c (3 * a) S m) s := by
      rw [hlograw]
      ring
    _ = logDeriv (scaledBlaschkeFill f c (3 * a) S m) s +
        ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) -
        ∑ ρ ∈ S, (m ρ : ℂ) *
          logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s := by
      rw [hlogfill, hprodLog]
      linear_combination -hsum

end FordScaledBlaschkeLogDerivative

#print axioms FordScaledBlaschkeLogDerivative.logDeriv_scaledBlaschkeFill_decomposition
