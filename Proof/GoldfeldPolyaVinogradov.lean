import GoldfeldFullContour
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The Pólya--Vinogradov input for Goldfeld's argument

We only need primitive quadratic characters.  The square-root conductor gain
comes directly from the exact Gauss-sum product and discrete Fourier inversion.
-/

namespace MAPGoldfeldSiegel

open Complex
open scoped ZMod BigOperators

noncomputable section

set_option maxHeartbeats 800000

/-- A primitive quadratic Gauss sum has norm exactly the square root of its
level. -/
theorem norm_gaussSum_stdAddChar_eq_sqrt
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hreal : chi ^ 2 = 1) :
    ‖gaussSum chi ZMod.stdAddChar‖ = Real.sqrt N := by
  have hchiInv : chi⁻¹ = chi := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hreal
  have hminusSq : chi (-1) * chi (-1) = 1 := by
    rw [← map_mul]
    simp
  have hminusNorm : ‖chi (-1)‖ = 1 := by
    have hn := congrArg norm hminusSq
    rw [norm_mul, norm_one] at hn
    nlinarith [norm_nonneg (chi (-1))]
  let tau : ℂ := gaussSum chi ZMod.stdAddChar
  have hF (k : ZMod N) : ZMod.dft chi k = chi (-k) * tau := by
    simpa only [hchiInv, tau] using hprim.fourierTransform_eq_inv_mul_gaussSum k
  have hdouble : chi (-1) * tau * tau = (N : ℂ) := by
    have hdd := congrFun (ZMod.dft_dft chi) (-1 : ZMod N)
    have hmul := congrFun
      (ZMod.dft_mul_const (fun j : ZMod N ↦ chi (-j)) tau) (-1 : ZMod N)
    have hneg := congrFun (ZMod.dft_comp_neg chi) (-1 : ZMod N)
    rw [funext hF] at hdd
    rw [hmul, hneg, hF] at hdd
    simpa [smul_eq_mul, mul_assoc] using hdd
  have hnprod := congrArg norm hdouble
  rw [norm_mul, norm_mul, hminusNorm, one_mul, Complex.norm_natCast] at hnprod
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg N)
  have hnorm0 := norm_nonneg tau
  have hsqrt0 := Real.sqrt_nonneg (N : ℝ)
  change ‖tau‖ = Real.sqrt N
  nlinarith

/-- Fourier inversion for a primitive Dirichlet character, with the Gauss sum
left visible.  This is the exact bridge from a character interval to the
Fourier `L¹` norm of that interval. -/
theorem primitive_character_fourier_inversion
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (x : ZMod N) :
    chi x = (N : ℂ)⁻¹ * ∑ k : ZMod N,
      ZMod.stdAddChar (k * x) *
        (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) := by
  have hinv := congrFun (LinearEquiv.symm_apply_apply ZMod.dft chi) x
  rw [ZMod.invDFT_apply] at hinv
  simp_rw [hprim.fourierTransform_eq_inv_mul_gaussSum] at hinv
  simpa only [smul_eq_mul, Finset.mul_sum] using hinv.symm

/-- The additive Fourier kernel of the integer interval `[A, A + M)`. -/
def additiveIntervalKernel (N A M : ℕ) [NeZero N] (k : ZMod N) : ℂ :=
  ∑ n ∈ Finset.range M,
    ZMod.stdAddChar (k * ((A + n : ℕ) : ZMod N))

/-- Exact Fourier expansion of a primitive character sum over an interval. -/
theorem primitive_partialSum_eq_fourier
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (A M : ℕ) :
    (∑ n ∈ Finset.range M, chi ((A + n : ℕ) : ZMod N)) =
      (N : ℂ)⁻¹ * ∑ k : ZMod N,
        (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
          additiveIntervalKernel N A M k := by
  simp_rw [primitive_character_fourier_inversion chi hprim]
  simp only [additiveIntervalKernel]
  conv_lhs => rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The character-theoretic half of Pólya--Vinogradov.  It turns any
character-free `L¹` estimate for interval Fourier kernels into a clean partial
character-sum bound. -/
theorem primitive_partialSum_norm_le_of_kernel
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hreal : chi ^ 2 = 1)
    (A M K : ℕ)
    (hkernel : (∑ k : ZMod N, ‖additiveIntervalKernel N A M k‖) ≤ K) :
    ‖∑ n ∈ Finset.range M, chi ((A + n : ℕ) : ZMod N)‖ ≤
      (Real.sqrt N)⁻¹ * K := by
  rw [primitive_partialSum_eq_fourier chi hprim]
  have hsum :
      ‖∑ k : ZMod N,
        (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
          additiveIntervalKernel N A M k‖ ≤
        Real.sqrt N *
          ∑ k : ZMod N, ‖additiveIntervalKernel N A M k‖ := by
    calc
      ‖∑ k : ZMod N,
          (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
            additiveIntervalKernel N A M k‖
          ≤ ∑ k : ZMod N,
              ‖(chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
                additiveIntervalKernel N A M k‖ := norm_sum_le _ _
      _ ≤ Real.sqrt N *
            ∑ k : ZMod N, ‖additiveIntervalKernel N A M k‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul, norm_mul,
            norm_gaussSum_stdAddChar_eq_sqrt chi hprim hreal]
          gcongr 1
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right ((chi⁻¹).norm_le_one (-k))
              (Real.sqrt_nonneg (N : ℝ)))
  calc
    ‖(N : ℂ)⁻¹ * ∑ k : ZMod N,
        (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
          additiveIntervalKernel N A M k‖
        = (N : ℝ)⁻¹ *
            ‖∑ k : ZMod N,
              (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
                additiveIntervalKernel N A M k‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (N : ℝ)⁻¹ * (Real.sqrt N *
          ∑ k : ZMod N, ‖additiveIntervalKernel N A M k‖) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((N : ℝ)⁻¹ * Real.sqrt N) *
          ∑ k : ZMod N, ‖additiveIntervalKernel N A M k‖ := by ring
    _ ≤ ((N : ℝ)⁻¹ * Real.sqrt N) * K := by
      gcongr
    _ = (Real.sqrt N)⁻¹ * K := by
      have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.ne N).bot_lt
      have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
      field_simp [hs, hN.ne']
      nlinarith [Real.sq_sqrt hN.le]

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.norm_gaussSum_stdAddChar_eq_sqrt
