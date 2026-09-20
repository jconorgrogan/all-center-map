import FordScaleFloor
open FordWEnvelopeScalar
noncomputable section
namespace FordScaleCancellation

lemma two_scale_bound {N x y a d : ℝ} (hN : 0 < N) (hx : 0 ≤ x)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hhi : x ≤ N^mu1) (hlo : N^mu2/2 ≤ y) :
    x^a * y^(-d) ≤ (2 : ℝ)^d * N^(mu1*a-mu2*d) := by
  have hxp : x^a ≤ N^(mu1*a) := by
    simpa [Real.rpow_mul hN.le] using Real.rpow_le_rpow hx hhi ha
  have hyp : y^(-d) ≤ (N^mu2/2)^(-d) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)
  calc
    _ ≤ N^(mu1*a)*(N^mu2/2)^(-d) := mul_le_mul hxp hyp
      (Real.rpow_nonneg (by linarith [Real.rpow_pos_of_pos hN mu2]) _) (by positivity)
    _ = (2 : ℝ)^d * N^(mu1*a-mu2*d) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      rw [sub_eq_add_neg, Real.rpow_add hN]
      have he : mu2 * -d = -(mu2*d) := by ring
      rw [he]
      ring

def deficit (k : ℕ) : ℝ := (k : ℝ)*(k+1)/2 - eps*(k : ℝ)^2
lemma deficit_nonneg (k : ℕ) : 0 ≤ deficit k := by
  unfold deficit eps
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith [sq_nonneg (k : ℝ)]

/-- Exact cancellation of the chosen scale powers; the floor loss remains as 2^deficit. -/
theorem scale_cancellation {N M1 M2 k : ℕ} (hN : 1 ≤ N)
    (hhi : (M1 : ℝ) ≤ (N : ℝ)^mu1) (hlo : (N : ℝ)^mu2/2 ≤ M2) :
    (M1 : ℝ)^(eps*(k : ℝ)^2) * (M2 : ℝ)^(-deficit k) *
      (N : ℝ)^(mu2*(k : ℝ)*(k+1)/2-eps*(mu1+mu2)*(k : ℝ)^2-(k : ℝ)^2/100) ≤
        (2 : ℝ)^(deficit k) * (N : ℝ)^(-(k : ℝ)^2/100) := by
  have hn0 : (0 : ℝ) < N := by positivity
  have hb := two_scale_bound (a := eps*(k : ℝ)^2) (d := deficit k)
    hn0 (by positivity : (0 : ℝ) ≤ M1) (by positivity) (deficit_nonneg k) hhi hlo
  have he : mu1*(eps*(k : ℝ)^2)-mu2*deficit k +
      (mu2*(k : ℝ)*(k+1)/2-eps*(mu1+mu2)*(k : ℝ)^2-(k : ℝ)^2/100) =
      -(k : ℝ)^2/100 := by unfold deficit; ring
  calc
    _ ≤ ((2 : ℝ)^(deficit k)*(N : ℝ)^(mu1*(eps*(k : ℝ)^2)-mu2*deficit k))*
      (N : ℝ)^(mu2*(k : ℝ)*(k+1)/2-eps*(mu1+mu2)*(k : ℝ)^2-(k : ℝ)^2/100) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hn0, he]
end FordScaleCancellation
#print axioms FordScaleCancellation.scale_cancellation
