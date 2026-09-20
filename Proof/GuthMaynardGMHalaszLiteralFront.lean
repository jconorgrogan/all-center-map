import GuthMaynardGMKernelCorrelation

namespace GuthMaynardGMHalaszLiteralFront
open scoped BigOperators ComplexConjugate
open GuthMaynardSectionFourTrace GuthMaynardGMHighValueComplement
open MAPJutilaDeterministicCore MAPHuxleyHalaszFront
noncomputable section

theorem sourcePhase_conj_mul (n : ℕ) (t u : ℝ) :
    conj (sourcePhase n t) * sourcePhase n u = sourcePhase n (u - t) := by
  unfold sourcePhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

theorem exists_literal_halasz_front (N : ℕ) (W : Finset ℝ)
    (a : ℕ → ℂ) {V : ℝ} (hV : 0 ≤ V)
    (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W,
      V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * sourcePhase n t‖) :
    ∃ eta : ℝ → ℂ, (∀ t ∈ W, ‖eta t‖ = 1) ∧
      ((W.card : ℝ) * V) ^ 2 ≤ (N : ℝ) *
        ‖∑ t ∈ W, ∑ u ∈ W, conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ := by
  classical
  let cols := Finset.Ioc N (2 * N)
  let v : ℝ → ℕ → ℂ := fun t n => sourcePhase n t
  have hlarge' : ∀ t ∈ W, V ≤ ‖finitePolynomial cols a v t‖ := by
    simpa [finitePolynomial, cols, v] using hlarge
  obtain ⟨eta, heta, hf, heq⟩ := finite_halasz_large_value_front_expanded W cols a v V hV hlarge'
  have hcoef : coefficientEnergy cols a ≤ N := by
    unfold coefficientEnergy
    calc
      _ ≤ ∑ n ∈ cols, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := ha n hn
        nlinarith [norm_nonneg (a n)]
      _ = _ := by simp [cols]; omega
  have hcorr0 : 0 ≤ correlationEnergy W cols (fun _ => 1) eta v := by
    unfold correlationEnergy
    positivity
  have hkernel : (correlationEnergy W cols (fun _ => 1) eta v : ℂ) =
      ∑ t ∈ W, ∑ u ∈ W, conj (eta t) * eta u * gmDyadicKernel N (u - t) := by
    simpa only [v, sourcePhase_conj_mul, gmDyadicKernel, cols] using heq
  have hnorm := congrArg norm hkernel
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcorr0] at hnorm
  refine ⟨eta, heta, ?_⟩
  have hh := hf.trans (mul_le_mul_of_nonneg_right hcoef hcorr0)
  rw [hnorm] at hh
  exact hh

end
end GuthMaynardGMHalaszLiteralFront
#print axioms GuthMaynardGMHalaszLiteralFront.exists_literal_halasz_front
