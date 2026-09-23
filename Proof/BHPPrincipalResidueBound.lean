import BHPCorrectedContourShift

/-!
# Exact bound for the principal residue crossed by the BHP contour
-/

namespace MAPBHPPrincipalResidueBound

open Complex
open MAPBHPCorrectedContourShift
open DirichletZeros

noncomputable section

private theorem norm_prime_euler_factor_le_one
    {p : ℕ} (hp : p.Prime) :
    ‖(1 : ℂ) - (p : ℂ)⁻¹‖ ≤ 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hinv : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hpPos.le
  have hinvOne : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hpPos]
    exact hpR
  have hreal : (1 : ℂ) - (p : ℂ)⁻¹ =
      ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    norm_cast
  rw [hreal, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- The residue of the principal Dirichlet L-function at one has norm at most
one, uniformly in the ambient modulus. -/
theorem norm_regularized_principal_one_le_one
    (q : ℕ) [NeZero q] :
    ‖regularizedLFunction (1 : DirichletCharacter ℂ q) 1‖ ≤ 1 := by
  classical
  unfold regularizedLFunction
  rw [if_pos rfl]
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
  change ‖∏ p ∈ q.primeFactors, ((1 : ℂ) - (p : ℂ)⁻¹)‖ ≤ 1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    exact norm_prime_euler_factor_le_one (Nat.prime_of_mem_primeFactors hp)

private theorem principalPole_norm_lower_one
    (t : ℝ) : (1 : ℝ) ≤ 2 * ‖bhpPrincipalPole t‖ := by
  have hre : (1 / 2 : ℝ) ≤ ‖bhpPrincipalPole t‖ := by
    calc
      (1 / 2 : ℝ) = |(bhpPrincipalPole t).re| := by
        simp [bhpPrincipalPole]
      _ ≤ ‖bhpPrincipalPole t‖ := Complex.abs_re_le_norm _
  linarith

private theorem principalPole_norm_lower_abs
    (t : ℝ) : |t| ≤ ‖bhpPrincipalPole t‖ := by
  calc
    |t| = |(bhpPrincipalPole t).im| := by simp [bhpPrincipalPole]
    _ ≤ ‖bhpPrincipalPole t‖ := Complex.abs_im_le_norm _

private theorem principalPole_inv_le_decay
    (t : ℝ) : ‖(bhpPrincipalPole t)⁻¹‖ ≤ 3 / (1 + |t|) := by
  have hden : 0 < ‖bhpPrincipalPole t‖ := by
    have := principalPole_norm_lower_one t
    nlinarith [norm_nonneg (bhpPrincipalPole t)]
  have hscale : 1 + |t| ≤ 3 * ‖bhpPrincipalPole t‖ := by
    linarith [principalPole_norm_lower_one t,
      principalPole_norm_lower_abs t]
  rw [norm_inv]
  rw [← one_div]
  exact (div_le_div_iff₀ hden (by positivity : 0 < 1 + |t|)).2 (by
    simpa using hscale)

private theorem norm_principalPole_power (X t : ℝ) (hX : 0 < X) :
    ‖Complex.exp (bhpPrincipalPole t * Real.log X)‖ =
      Real.rpow X (1 / 2) := by
  have hp : bhpPrincipalPole t =
      ((1 / 2 : ℝ) : ℂ) + Complex.I * (-t) := by
    unfold bhpPrincipalPole
    push_cast
    ring
  rw [hp]
  have heq := PerronKernel.verticalPower_eq_exp hX (1 / 2) (-t)
  have hnorm := congrArg norm heq
  rw [Real.rpow_eq_pow]
  simpa using hnorm.symm.trans
    (PerronKernel.norm_verticalPower hX (1 / 2) (-t))

/-- The exact crossed residue has precisely the decaying principal error scale
used in BHP/MRT. -/
theorem norm_bhpPrincipalResidue_le
    (q : ℕ) [NeZero q] {X t : ℝ} (hX : 0 < X) :
    ‖bhpPrincipalResidue q X t‖ ≤
      3 * Real.sqrt X / (1 + |t|) := by
  have hp0 : bhpPrincipalPole t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [bhpPrincipalPole] at hre
  have harg : ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) +
      bhpPrincipalPole t) = 1 := by
    unfold bhpPrincipalPole
    push_cast
    ring
  unfold bhpPrincipalResidue bhpPrincipalNumerator
  rw [harg, norm_div, norm_mul, norm_principalPole_power X t hX]
  have hreg := norm_regularized_principal_one_le_one q
  have hinv := principalPole_inv_le_decay t
  rw [norm_inv] at hinv
  rw [div_eq_mul_inv]
  calc
    ‖regularizedLFunction (1 : DirichletCharacter ℂ q) 1‖ *
        Real.rpow X (1 / 2) * ‖bhpPrincipalPole t‖⁻¹ ≤
      1 * Real.rpow X (1 / 2) * (3 / (1 + |t|)) := by
        have hpow0 : 0 ≤ Real.rpow X (1 / 2) :=
          Real.rpow_nonneg hX.le _
        have hfirst := mul_le_mul_of_nonneg_right hreg hpow0
        exact mul_le_mul hfirst hinv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg zero_le_one hpow0)
    _ = 3 * Real.sqrt X / (1 + |t|) := by
      have hsqrt : Real.rpow X (1 / 2) = Real.sqrt X := by
        symm
        exact Real.sqrt_eq_rpow X
      rw [hsqrt]
      ring

end
end MAPBHPPrincipalResidueBound

#print axioms MAPBHPPrincipalResidueBound.norm_regularized_principal_one_le_one
#print axioms MAPBHPPrincipalResidueBound.norm_bhpPrincipalResidue_le
