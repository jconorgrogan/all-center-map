import RealCharacterLFunctionConjugation
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Conjugation symmetry for every Dirichlet L-function away from its pole

The nonprincipal case was already available as an entire-function identity.
This version works uniformly for principal characters by applying the identity
theorem on `ℂ \ {1}`.
-/

namespace MAPDirichletLFunctionConjugationGeneral

open Complex Set LSeries Filter
open scoped ComplexConjugate

noncomputable section

theorem LFunction_inv_conj_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) :
    DirichletCharacter.LFunction chi⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  let U : Set ℂ := ({1} : Set ℂ)ᶜ
  let f : ℂ → ℂ := DirichletCharacter.LFunction chi⁻¹
  let g : ℂ → ℂ := conj ∘ DirichletCharacter.LFunction chi ∘ conj
  have hf : AnalyticOnNhd ℂ f U := by
    apply DifferentiableOn.analyticOnNhd _
      (isOpen_compl_iff.mpr isClosed_singleton)
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction chi⁻¹ z
      (Or.inl (by simpa [U] using hz))).differentiableWithinAt
  have hgdiff : DifferentiableOn ℂ g U := by
    intro z hz
    apply ((differentiableAt_conj_conj_iff
      (f := DirichletCharacter.LFunction chi)).2 ?_).differentiableWithinAt
    apply DirichletCharacter.differentiableAt_LFunction chi
    left
    intro hconj
    have hz1 : z = 1 := by
      have := congrArg conj hconj
      simpa using this
    have hzmem : z ≠ 1 := by simpa [U] using hz
    exact hzmem hz1
  have hg : AnalyticOnNhd ℂ g U :=
    hgdiff.analyticOnNhd (isOpen_compl_iff.mpr isClosed_singleton)
  have hU : IsPreconnected U := by
    exact (isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isConnected.isPreconnected
  have htwo : (2 : ℂ) ∈ U := by simp [U]
  have hevent : f =ᶠ[nhds (2 : ℂ)] g := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const continuous_re
    apply eventually_of_mem (hopen.mem_nhds (by norm_num))
    intro z hz
    dsimp [f, g]
    rw [DirichletCharacter.LFunction_eq_LSeries chi⁻¹]
    · rw [DirichletCharacter.LFunction_eq_LSeries chi]
      · simpa using
          MAPRealCharacterLFunctionConjugation.LSeries_inv_conj chi (conj z)
      · simpa using hz
    · simpa using hz
  have heq : Set.EqOn f g U :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg hU htwo hevent
  have hmem : conj s ∈ U := by
    simp only [U, mem_compl_iff, mem_singleton_iff]
    intro hconj
    apply hs
    have := congrArg conj hconj
    simpa using this
  simpa [f, g, Function.comp_def] using heq hmem

end
end MAPDirichletLFunctionConjugationGeneral

#print axioms MAPDirichletLFunctionConjugationGeneral.LFunction_inv_conj_of_ne_one
