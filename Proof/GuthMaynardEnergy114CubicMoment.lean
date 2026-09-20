import CGLProofDAG
import GuthMaynardRatioKernelIdentity

open scoped BigOperators ComplexConjugate
open GuthMaynardRatioKernelIdentity
open GuthMaynardHeathBrownMajorant

namespace GuthMaynardEnergy114CubicMoment

noncomputable section

private abbrev S (N : ℕ) : Finset ℕ := Finset.Ioc N (2 * N)

private theorem phase_product
    (n m : ℕ) (t : ℝ) :
    Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) *
        star (Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (Complex.I * (((t * (Real.log n - Real.log m)) : ℝ) : ℂ)) := by
  rw [show star (Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (star (((t * Real.log m : ℝ) : ℂ) * Complex.I)) by
    exact (Complex.exp_conj _).symm]
  change Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) *
      Complex.exp (star (((t * Real.log m : ℝ) : ℂ) * Complex.I)) = _
  rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_product_I
    (n m : ℕ) (t : ℝ) :
    Complex.exp (Complex.I * ((t * Real.log n : ℝ) : ℂ)) *
        star (Complex.exp (Complex.I * ((t * Real.log m : ℝ) : ℂ))) =
      Complex.exp (Complex.I * (((t * (Real.log n - Real.log m)) : ℝ) : ℂ)) := by
  rw [show star (Complex.exp (Complex.I * ((t * Real.log m : ℝ) : ℂ))) =
      Complex.exp (star (Complex.I * ((t * Real.log m : ℝ) : ℂ))) by
    exact (Complex.exp_conj _).symm]
  rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_product_target
    (n m : ℕ) (t : ℝ) :
    Complex.exp (Complex.I * (t * Real.log m)) *
        star (Complex.exp (Complex.I * (t * Real.log n))) =
      Complex.exp (Complex.I * (t * (Real.log m - Real.log n))) := by
  rw [show star (Complex.exp (Complex.I * (t * Real.log n))) =
      Complex.exp (star (Complex.I * (t * Real.log n))) by
    exact (Complex.exp_conj _).symm]
  rw [Complex.star_def]
  simp_rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem phase_product_cast
    (n m : ℕ) (t : ℝ) :
    Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (m : ℝ)) : ℂ))) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ)) : ℂ)))) =
      Complex.exp (Complex.I * ((t : ℂ) * (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) := by
  rw [show (starRingEnd ℂ) (Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ)) : ℂ)))) =
      Complex.exp ((starRingEnd ℂ) (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ)) : ℂ)))) by
    exact (Complex.exp_conj _).symm]
  simp_rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem ratio_kernel_sum
    (W : Finset ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∑ a ∈ W, Complex.exp (Complex.I * (((a * (Real.log n - Real.log m)) : ℝ) : ℂ))) =
      ratioDirichletKernel W ((n : ℝ) / (m : ℝ)) := by
  have h := gramKernel_dirichletPhase_eq_ratioDirichletKernel W hn hm
  unfold gramKernel dirichletPhase at h
  simp_rw [phase_product] at h
  exact h

set_option maxHeartbeats 900000 in
private theorem complex_normsq_cubic_expansion
    {N : ℕ} (W : Finset ℝ) (b : ℕ → ℂ) (s : ℝ) :
    (((∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        ‖CGLProofDAG.dirichletPolynomial b N (a + b0 - c - s)‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n ∈ S N, ∑ m ∈ S N,
        b m * star (b n) *
          Complex.exp (Complex.I * (((-s * (Real.log m - Real.log n)) : ℝ) : ℂ)) *
          (ratioDirichletKernel W ((m : ℝ) / (n : ℝ))) ^ 2 *
          star (ratioDirichletKernel W ((m : ℝ) / (n : ℝ))) := by
  classical
  simp only [CGLProofDAG.dirichletPolynomial]
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum]
  have hnorm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [Complex.sq_norm]
    exact (Complex.mul_conj z).symm
  simp_rw [hnorm]
  simp_rw [Complex.star_def]
  simp_rw [map_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  -- Reorder the five finite sums by adjacent, direction-fixed swaps.
  have h_reorder (F : ℝ → ℝ → ℝ → ℕ → ℕ → ℂ) :
      (∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W, ∑ n ∈ S N, ∑ m ∈ S N,
        F a b0 c n m) =
        ∑ n ∈ S N, ∑ m ∈ S N, ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
          F a b0 c n m := by
    calc
      (∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W, ∑ n ∈ S N, ∑ m ∈ S N,
          F a b0 c n m) =
          ∑ a ∈ W, ∑ b0 ∈ W, ∑ n ∈ S N, ∑ c ∈ W, ∑ m ∈ S N,
            F a b0 c n m := by
              apply Finset.sum_congr rfl; intro a ha
              apply Finset.sum_congr rfl; intro b0 hb0
              rw [Finset.sum_comm]
      _ = ∑ a ∈ W, ∑ n ∈ S N, ∑ b0 ∈ W, ∑ c ∈ W, ∑ m ∈ S N,
            F a b0 c n m := by
              apply Finset.sum_congr rfl; intro a ha
              rw [Finset.sum_comm]
      _ = ∑ n ∈ S N, ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W, ∑ m ∈ S N,
            F a b0 c n m := by
              rw [Finset.sum_comm]
      _ = ∑ n ∈ S N, ∑ a ∈ W, ∑ b0 ∈ W, ∑ m ∈ S N, ∑ c ∈ W,
            F a b0 c n m := by
              apply Finset.sum_congr rfl; intro n hn
              apply Finset.sum_congr rfl; intro a ha
              apply Finset.sum_congr rfl; intro b0 hb0
              rw [Finset.sum_comm]
      _ = ∑ n ∈ S N, ∑ a ∈ W, ∑ m ∈ S N, ∑ b0 ∈ W, ∑ c ∈ W,
            F a b0 c n m := by
              apply Finset.sum_congr rfl; intro n hn
              apply Finset.sum_congr rfl; intro a ha
              rw [Finset.sum_comm]
      _ = ∑ n ∈ S N, ∑ m ∈ S N, ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
            F a b0 c n m := by
              apply Finset.sum_congr rfl; intro n hn
              rw [Finset.sum_comm]
  rw [h_reorder]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [map_mul]
  -- Factor the three independent phase sums.
  have hprod (a b0 c : ℝ) :
      b m * Complex.exp (Complex.I * (((a + b0 - c - s : ℝ) : ℂ) * ((Real.log (m : ℝ)) : ℂ))) *
          ((starRingEnd ℂ) (b n) * (starRingEnd ℂ) (Complex.exp
            (Complex.I * (((a + b0 - c - s : ℝ) : ℂ) * ((Real.log (n : ℝ)) : ℂ))))) =
        b m * (starRingEnd ℂ) (b n) *
          (Complex.exp (Complex.I * (((a + b0 - c - s : ℝ) : ℂ) * ((Real.log (m : ℝ)) : ℂ))) *
            (starRingEnd ℂ) (Complex.exp
              (Complex.I * (((a + b0 - c - s : ℝ) : ℂ) * ((Real.log (n : ℝ)) : ℂ))))) := by ring
  simp_rw [hprod]
  simp_rw [phase_product_cast]
  have hexp (a b0 c : ℝ) :
      Complex.exp (Complex.I * (((a + b0 - c - s : ℝ) : ℂ) *
        (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) =
        Complex.exp (Complex.I * (((-s : ℝ) : ℂ) *
          (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
          Complex.exp (Complex.I * (((a : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
          Complex.exp (Complex.I * (((b0 : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
          Complex.exp (Complex.I * (((-c : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp]
  have hfactor (a b0 c : ℝ) :
      b m * (starRingEnd ℂ) (b n) *
          (Complex.exp (Complex.I * (((-s : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
           Complex.exp (Complex.I * (((a : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
           Complex.exp (Complex.I * (((b0 : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
           Complex.exp (Complex.I * (((-c : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ))))) =
        (b m * (starRingEnd ℂ) (b n) *
          Complex.exp (Complex.I * (((-s : ℝ) : ℂ) *
            (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ))))) *
        Complex.exp (Complex.I * (((a : ℝ) : ℂ) *
          (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
        Complex.exp (Complex.I * (((b0 : ℝ) : ℂ) *
          (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) *
        Complex.exp (Complex.I * (((-c : ℝ) : ℂ) *
          (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ)))) := by
    ring
  simp_rw [hfactor]
  have hfactorSum (A : ℂ) (f g h : ℝ → ℂ) :
      (∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W, A * f a * g b0 * h c) =
        A * (∑ a ∈ W, f a) * (∑ b0 ∈ W, g b0) * (∑ c ∈ W, h c) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs =>
      enter [2, a]
      rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs =>
      enter [2, c]
      rw [Finset.sum_comm]
  rw [hfactorSum]
  have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hm).1
  have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hratio :
      (∑ a ∈ W, Complex.exp (Complex.I * (((a : ℝ) : ℂ) *
        (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ))))) =
        ratioDirichletKernel W ((m : ℝ) / (n : ℝ)) := by
    convert ratio_kernel_sum W hmpos hnpos using 1 <;> push_cast <;> ring
  have hneg :
      (∑ c ∈ W, Complex.exp (Complex.I * (((-c : ℝ) : ℂ) *
        (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ))))) =
        star (ratioDirichletKernel W ((m : ℝ) / (n : ℝ))) := by
    rw [← hratio]
    rw [Complex.star_def, map_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [show (starRingEnd ℂ) (Complex.exp (Complex.I * (((c : ℝ) : ℂ) *
        (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ))))) =
        Complex.exp ((starRingEnd ℂ) (Complex.I * (((c : ℝ) : ℂ) *
          (((Real.log (m : ℝ)) : ℂ) - ((Real.log (n : ℝ)) : ℂ))))) by
      exact (Complex.exp_conj _).symm]
    simp only [map_sub, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  simp_rw [hratio]
  rw [hneg]
  have hsphase :
      Complex.exp (Complex.I * ((-s : ℂ) *
        ((Real.log (m : ℝ) : ℂ) - (Real.log (n : ℝ) : ℂ)))) =
        Complex.exp (Complex.I * ((-(s * Real.log (m : ℝ)) +
          s * Real.log (n : ℝ) : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  push_cast at hsphase ⊢
  simp only [Complex.star_def]
  ring



set_option maxHeartbeats 900000 in
/-- Literal finite pointwise cubic moment bound behind Lemma 11.4. -/
theorem cubic_moment_pointwise
    {N : ℕ} (hN : 1 ≤ N) (W : Finset ℝ) (b : ℕ → ℂ)
    (hb : ∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1) (s : ℝ) :
    ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        ‖CGLProofDAG.dirichletPolynomial b N (a + b0 - c - s)‖ ^ 2 ≤
      ∑ n1 ∈ Finset.Ioc N (2 * N), ∑ n2 ∈ Finset.Ioc N (2 * N),
        ‖ratioDirichletKernel W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 := by
  classical
  let L : ℝ := ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        ‖CGLProofDAG.dirichletPolynomial b N (a + b0 - c - s)‖ ^ 2
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hident := complex_normsq_cubic_expansion (N := N) W b s
  have hLnorm : L ≤ ‖(L : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  change L ≤ ‖(L : ℂ)‖ at hLnorm
  rw [show (L : ℂ) = _ by exact hident] at hLnorm
  rw [Finset.sum_comm] at hLnorm
  calc
    _ = L := rfl
    _ ≤ ‖∑ n ∈ S N, ∑ m ∈ S N,
        b n * star (b m) *
          Complex.exp (Complex.I * (((-s * (Real.log n - Real.log m)) : ℝ) : ℂ)) *
          (ratioDirichletKernel W ((n : ℝ) / (m : ℝ))) ^ 2 *
          star (ratioDirichletKernel W ((n : ℝ) / (m : ℝ)))‖ := hLnorm
    _ ≤ ∑ n ∈ S N, ∑ m ∈ S N,
        ‖b n * star (b m) *
          Complex.exp (Complex.I * (((-s * (Real.log n - Real.log m)) : ℝ) : ℂ)) *
          (ratioDirichletKernel W ((n : ℝ) / (m : ℝ))) ^ 2 *
          star (ratioDirichletKernel W ((n : ℝ) / (m : ℝ)))‖ := by
      calc
        ‖∑ n ∈ S N, ∑ m ∈ S N,
            b n * star (b m) *
              Complex.exp (Complex.I * (((-s * (Real.log n - Real.log m)) : ℝ) : ℂ)) *
              (ratioDirichletKernel W ((n : ℝ) / (m : ℝ))) ^ 2 *
              star (ratioDirichletKernel W ((n : ℝ) / (m : ℝ)))‖
            ≤ ∑ n ∈ S N, ‖∑ m ∈ S N,
                b n * star (b m) *
                  Complex.exp (Complex.I * (((-s * (Real.log n - Real.log m)) : ℝ) : ℂ)) *
                  (ratioDirichletKernel W ((n : ℝ) / (m : ℝ))) ^ 2 *
                  star (ratioDirichletKernel W ((n : ℝ) / (m : ℝ)))‖ := by
              apply norm_sum_le
        _ ≤ ∑ n ∈ S N, ∑ m ∈ S N,
            ‖b n * star (b m) *
              Complex.exp (Complex.I * (((-s * (Real.log n - Real.log m)) : ℝ) : ℂ)) *
              (ratioDirichletKernel W ((n : ℝ) / (m : ℝ))) ^ 2 *
              star (ratioDirichletKernel W ((n : ℝ) / (m : ℝ)))‖ := by
              apply Finset.sum_le_sum
              intro n hn
              apply norm_sum_le
    _ ≤ ∑ n ∈ S N, ∑ m ∈ S N,
        ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 3 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star, norm_pow, Complex.norm_exp,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Real.exp_zero, one_mul]
      have hbn := hb n hn
      have hbm := hb m hm
      have hbn0 : 0 ≤ ‖b n‖ := norm_nonneg _
      have hbm0 : 0 ≤ ‖b m‖ := norm_nonneg _
      have hprod : ‖b n‖ * ‖b m‖ ≤ 1 := by
        nlinarith [mul_le_mul_of_nonneg_left hbm hbn0]
      have hr : 0 ≤ ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 2 := by positivity
      calc
        ‖b n‖ * ‖b m‖ * 1 *
              ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 2 *
              ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ =
            (‖b n‖ * ‖b m‖) *
              (‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 2 *
                ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖) := by ring
        _ ≤ 1 * (‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 2 *
              ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
        _ = ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 3 := by ring

end
end GuthMaynardEnergy114CubicMoment

#print axioms GuthMaynardEnergy114CubicMoment.cubic_moment_pointwise
