import FordLemma33WeightedHolder
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators

namespace FordLemma33MixedProduct

open FordBoundaryWeightedHolder
open FordLemma33WeightedHolder

noncomputable section

private theorem prod_le_avg_pow
    {k : ℕ} (hk : 1 ≤ k) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ (∑ i, z i ^ k) / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hgm := Real.geom_mean_le_arith_mean
    (s := (Finset.univ : Finset (Fin k)))
    (w := fun _ => (1 : ℝ))
    (z := fun i => z i ^ k)
    (fun _ _ => by norm_num) (by simp [hkR])
    (fun i _ => pow_nonneg (hz i) _)
  have hsum : ∑ i : Fin k, (1 : ℝ) = (k : ℝ) := by simp
  have hprod : (∏ i : Fin k, (z i ^ k) ^ (1 : ℝ)) = (∏ i, z i) ^ k := by
    simp only [Real.rpow_one]
    rw [← Finset.prod_pow]
  have hprod_nonneg : 0 ≤ ∏ i : Fin k, z i := Finset.prod_nonneg (fun i _ => hz i)
  have hleft :
      (∏ i : Fin k, (z i ^ k) ^ (1 : ℝ)) ^ (∑ i : Fin k, (1 : ℝ))⁻¹ =
        ∏ i, z i := by
    rw [hsum, hprod, ← Real.rpow_natCast]
    rw [← Real.rpow_mul hprod_nonneg]
    have hkinv : (k : ℝ) * (k : ℝ)⁻¹ = 1 := by
      field_simp
    rw [hkinv, Real.rpow_one]
  rw [hleft] at hgm
  simpa [hsum] using hgm

theorem mixed_product_uniform_bound
    {α H : Type*} [Fintype α] [Nonempty α] [Fintype H] [Nonempty H]
    (w : α → ℝ) (b : H → α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hw : ∀ x, 0 ≤ w x) (hb : ∀ h x, 0 ≤ b h x) :
    ∃ h0 : H, ∀ hs : Fin k → H,
      (fordAvg (fun x => w x * ∏ i, b (hs i) x)) ^ 2 ≤
        fordAvg w * fordAvg (fun x => w x * b h0 x ^ (2 * k)) := by
  let moment : H → ℝ := fun h => fordAvg (fun x => w x * b h x ^ (2 * k))
  obtain ⟨h0, hh0, hmax⟩ := Finset.exists_max_image
    (s := (Finset.univ : Finset H)) moment Finset.univ_nonempty
  refine ⟨h0, ?_⟩
  intro hs
  let B : ℝ := fordAvg w
  let Emax : ℝ := moment h0
  let R : ℝ := Real.sqrt (B * Emax)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.expect_nonneg (fun x _ => hw x)
  have hEmax : 0 ≤ Emax := by
    dsimp [Emax, moment]
    exact Finset.expect_nonneg (fun x _ => mul_nonneg (hw x) (pow_nonneg (hb h0 x) _))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hpoint (x : α) :
      w x * ∏ i, b (hs i) x ≤
        w x * ((∑ i, b (hs i) x ^ k) / (k : ℝ)) := by
    exact mul_le_mul_of_nonneg_left
      (prod_le_avg_pow hk (fun i => b (hs i) x) (fun i => hb (hs i) x)) (hw x)
  have hmixed_le :
      fordAvg (fun x => w x * ∏ i, b (hs i) x) ≤
        (∑ i : Fin k, fordAvg (fun x => w x * b (hs i) x ^ k)) / (k : ℝ) := by
    have he := Finset.expect_le_expect (s := (Finset.univ : Finset α))
      (fun x _ => hpoint x)
    have hrewrite :
        fordAvg (fun x => w x * ((∑ i, b (hs i) x ^ k) / (k : ℝ))) =
          (∑ i : Fin k, fordAvg (fun x => w x * b (hs i) x ^ k)) / (k : ℝ) := by
      unfold fordAvg
      calc
        _ = (Finset.univ.expect (fun x =>
            (∑ i : Fin k, w x * b (hs i) x ^ k) / (k : ℝ))) := by
          apply Finset.expect_congr rfl
          intro x hx
          field_simp
          rw [Finset.mul_sum]
        _ = (Finset.univ.expect (fun x =>
            ∑ i : Fin k, w x * b (hs i) x ^ k)) / (k : ℝ) := by
          rw [Finset.expect_div]
        _ = (∑ i : Fin k, fordAvg (fun x => w x * b (hs i) x ^ k)) /
            (k : ℝ) := by
          rw [Finset.expect_sum_comm]
          rfl
    change fordAvg (fun x => w x * ∏ i, b (hs i) x) ≤
      fordAvg (fun x => w x * ((∑ i, b (hs i) x ^ k) / (k : ℝ))) at he
    rw [hrewrite] at he
    exact he
  have hsingle : ∀ h : H,
      fordAvg (fun x => w x * b h x ^ k) ≤ R := by
    intro h
    have hint := weighted_moment_interpolation w (fun x => b h x ^ k) 2
      (by norm_num) hw (fun x => pow_nonneg (hb h x) _)
    have hsq :
        (fordAvg (fun x => w x * b h x ^ k)) ^ 2 ≤ B * Emax := by
      have hE : fordAvg (fun x => w x * b h x ^ (2 * k)) ≤ Emax := by
        simpa [moment] using hmax h (Finset.mem_univ h)
      have hprod :
          fordAvg w * fordAvg (fun x => w x * (b h x ^ k) ^ 2) ≤ B * Emax := by
        have hE' : fordAvg (fun x => w x * (b h x ^ k) ^ 2) ≤ Emax := by
          simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using hE
        exact mul_le_mul_of_nonneg_left hE' hB
      have hint' :
          (fordAvg (fun x => w x * b h x ^ k)) ^ 2 ≤
            fordAvg w * fordAvg (fun x => w x * (b h x ^ k) ^ 2) := by
        simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using hint
      simpa [B] using hint'.trans hprod
    have hEh : 0 ≤ fordAvg (fun x => w x * b h x ^ k) :=
      Finset.expect_nonneg (fun x _ => mul_nonneg (hw x) (pow_nonneg (hb h x) _))
    apply (Real.le_sqrt hEh (mul_nonneg hB hEmax)).2
    exact hsq
  have hsum_le :
      (∑ i : Fin k, fordAvg (fun x => w x * b (hs i) x ^ k)) ≤
        ∑ _i : Fin k, R := Finset.sum_le_sum (fun i _ => hsingle (hs i))
  have hM :
      fordAvg (fun x => w x * ∏ i, b (hs i) x) ≤ R := by
    calc
      _ ≤ (∑ i : Fin k, fordAvg (fun x => w x * b (hs i) x ^ k)) / (k : ℝ) := hmixed_le
      _ ≤ (∑ _i : Fin k, R) / (k : ℝ) := div_le_div_of_nonneg_right hsum_le (by positivity)
      _ = R := by
        have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        field_simp
  have hMnonneg : 0 ≤ fordAvg (fun x => w x * ∏ i, b (hs i) x) := by
    exact Finset.expect_nonneg (fun x _ =>
      mul_nonneg (hw x) (Finset.prod_nonneg (fun i _ => hb (hs i) x)))
  have hsqM := (sq_le_sq₀ hMnonneg hR).2 hM
  simpa [B, Emax, R, Real.sq_sqrt (mul_nonneg hB hEmax)] using hsqM

end
end FordLemma33MixedProduct

#print axioms FordLemma33MixedProduct.mixed_product_uniform_bound
