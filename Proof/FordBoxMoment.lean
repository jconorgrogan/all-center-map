import FordBoxFourier
import FordPhaseMoment

open scoped BigOperators
noncomputable section
namespace FordBoxMoment
open FordPolynomialPhase

/-- The complete finite frequency-box moment is bounded by products of literal
Dirichlet kernels, at the exact signed differences of the tuple sums. -/
theorem box_moment_bound {B : Type*} [Fintype B] (k s : ℕ)
    (L : Fin k → ℕ) (gamma : Fin k → ℝ) (v : B → Fin k → ℝ)
    (a : B → ℂ) (ha : ∀ b, ‖a b‖ = 1) :
    (∑ c ∈ FordBoxFourier.box L,
      ‖∑ b, a b * e (∑ j, gamma j * v b j * (c j : ℝ))‖ ^ (2 * s)) ≤
      ∑ x : Fin s → B, ∑ y : Fin s → B,
        ∏ j : Fin k, ‖FordDirichletPointwise.dirichletSum (L j)
          (gamma j * ((∑ i, v (x i) j) - (∑ i, v (y i) j)))‖ := by
  classical
  have h := FordPhaseMoment.unit_weight_moment_bound a ha
    (fun c : FordBoxFourier.box L => fun b =>
      ∑ j, gamma j * v b j * (c.1 j : ℝ)) s
  rw [Finset.sum_coe_sort (FordBoxFourier.box L)
    (fun c => ‖∑ b, a b * e (∑ j, gamma j * v b j * (c j : ℝ))‖ ^ (2 * s))] at h
  have hphase (c : Fin k → ℕ) (x y : Fin s → B) :
      (∑ i, ∑ j, gamma j * v (x i) j * (c j : ℝ)) -
        (∑ i, ∑ j, gamma j * v (y i) j * (c j : ℝ)) =
      ∑ j, (gamma j * ((∑ i, v (x i) j) - (∑ i, v (y i) j))) * (c j : ℝ) := by
    rw [Finset.sum_comm (f := fun i : Fin s => fun j : Fin k => gamma j * v (x i) j * (c j : ℝ)),
      Finset.sum_comm (f := fun i : Fin s => fun j : Fin k => gamma j * v (y i) j * (c j : ℝ))]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, sub_mul]
  have hkernel (x y : Fin s → B) :
      ‖∑ c : FordBoxFourier.box L,
        e ((∑ i, ∑ j, gamma j * v (x i) j * (c.1 j : ℝ)) -
          (∑ i, ∑ j, gamma j * v (y i) j * (c.1 j : ℝ)))‖ =
      ∏ j, ‖FordDirichletPointwise.dirichletSum (L j)
        (gamma j * ((∑ i, v (x i) j) - (∑ i, v (y i) j)))‖ := by
    simp_rw [hphase]
    rw [Finset.sum_coe_sort (FordBoxFourier.box L)
      (fun c => e (∑ j, (gamma j * ((∑ i, v (x i) j) - (∑ i, v (y i) j))) * (c j : ℝ))),
      FordBoxFourier.box_fourier, norm_prod]
  simpa only [hkernel] using h

end FordBoxMoment
#print axioms FordBoxMoment.box_moment_bound
