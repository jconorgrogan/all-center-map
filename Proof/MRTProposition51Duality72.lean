import MRTProposition51FirstAnalytic

/-!
# Exact normalized L² duality for MRT equation (72)

This module proves the Hilbert-space normalization used after the smooth
Gallagher reduction. It is cutoff-independent. The separate remaining issue is
to feed it the same smooth field that generates the logarithmic function `G`.
-/

namespace MAPMRTProposition51Duality72

open MeasureTheory Set

noncomputable section

/-- The normalized conjugate witness for the bilinear (non-Hermitian) pairing
used in the source. -/
def normalizedDualWitness (F : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ star (F x) / (Real.sqrt (∫ y : ℝ, ‖F y‖ ^ 2) : ℂ)

/-- A positive-energy integrable field has an integrable, normalized L² dual
witness, with the same pointwise support, and the pairing recovers its energy
exactly after squaring the norm. -/
theorem normalizedDualWitness_spec
    {F : ℝ → ℂ}
    (hF : Integrable F)
    (hF2 : Integrable (fun x : ℝ ↦ ‖F x‖ ^ 2))
    (hE : 0 < ∫ x : ℝ, ‖F x‖ ^ 2) :
    Integrable (normalizedDualWitness F) ∧
    MemLp (normalizedDualWitness F) 2 ∧
    (∀ x, F x = 0 → normalizedDualWitness F x = 0) ∧
    (∫ x : ℝ, ‖normalizedDualWitness F x‖ ^ 2) = 1 ∧
    ‖∫ x : ℝ, F x * normalizedDualWitness F x‖ ^ 2 =
      ∫ x : ℝ, ‖F x‖ ^ 2 := by
  let E : ℝ := ∫ x : ℝ, ‖F x‖ ^ 2
  have hE' : 0 < E := hE
  have hsqrt : 0 < Real.sqrt E := Real.sqrt_pos.2 hE'
  have hstar : Integrable (fun x : ℝ ↦ star (F x)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hF
  have hg : Integrable (normalizedDualWitness F) := by
    unfold normalizedDualWitness
    exact hstar.div_const (Real.sqrt E : ℂ)
  have hnormPoint (x : ℝ) :
      ‖normalizedDualWitness F x‖ ^ 2 = ‖F x‖ ^ 2 / E := by
    unfold normalizedDualWitness
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt]
    rw [div_pow, Real.sq_sqrt hE'.le]
  have hnorm : (∫ x : ℝ, ‖normalizedDualWitness F x‖ ^ 2) = 1 := by
    simp_rw [hnormPoint]
    rw [integral_div]
    change E / E = 1
    exact div_self (ne_of_gt hE')
  have hgmeas : AEStronglyMeasurable (normalizedDualWitness F) :=
    hg.aestronglyMeasurable
  have hg2 : MemLp (normalizedDualWitness F) 2 :=
    (memLp_two_iff_integrable_sq_norm hgmeas).2 (by
      have hdiv : Integrable (fun x : ℝ ↦ ‖F x‖ ^ 2 / E) :=
        hF2.div_const E
      apply hdiv.congr
      filter_upwards with x
      exact (hnormPoint x).symm)
  have hpairPoint (x : ℝ) :
      F x * normalizedDualWitness F x =
        ((‖F x‖ ^ 2 : ℝ) : ℂ) / (Real.sqrt E : ℂ) := by
    unfold normalizedDualWitness
    change F x * (star (F x) / (Real.sqrt E : ℂ)) = _
    rw [div_eq_mul_inv, ← mul_assoc]
    change (F x * starRingEnd ℂ (F x)) * _ = _
    rw [RCLike.mul_conj]
    push_cast
    simp only [div_eq_mul_inv]
    rfl
  have hreal : Integrable (fun x : ℝ ↦ ((‖F x‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hF2
  have hpair : (∫ x : ℝ, F x * normalizedDualWitness F x) =
      (Real.sqrt E : ℂ) := by
    simp_rw [hpairPoint]
    rw [integral_div]
    have hmap := Complex.ofRealCLM.integral_comp_comm hF2
    have hmap' : (∫ x : ℝ, ((‖F x‖ ^ 2 : ℝ) : ℂ)) = (E : ℂ) := by
      simpa [E] using hmap
    change (∫ x : ℝ, ((‖F x‖ ^ 2 : ℝ) : ℂ)) /
      (Real.sqrt E : ℂ) = _
    rw [hmap']
    change (E : ℂ) / (Real.sqrt E : ℂ) = (Real.sqrt E : ℂ)
    apply (div_eq_iff (by exact_mod_cast (ne_of_gt hsqrt))).2
    exact_mod_cast (by simpa [pow_two] using (Real.sq_sqrt hE'.le).symm)
  refine ⟨hg, hg2, ?_, hnorm, ?_⟩
  · intro x hx
    simp [normalizedDualWitness, hx]
  · rw [hpair]
    change ‖(Real.sqrt E : ℂ)‖ ^ 2 = E
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt,
      Real.sq_sqrt hE'.le]

#print axioms normalizedDualWitness_spec

end
end MAPMRTProposition51Duality72
