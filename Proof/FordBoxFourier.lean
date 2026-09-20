import FordPowerBox
import FordDirichletPointwise
import FordPolynomialPhase

open scoped BigOperators
noncomputable section

namespace FordBoxFourier

abbrev e := FordPolynomialPhase.e

def box (L : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun j : Fin k => Finset.Icc 1 (L j))

lemma iCC_one_eq_image_succ (L : ℕ) :
    Finset.Icc 1 L = (Finset.range L).image Nat.succ := by
  ext c
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hc
    exact ⟨c - 1, by omega, by omega⟩
  · rintro ⟨n, hn, rfl⟩
    omega

lemma iCC_sum_eq_dirichlet (L : ℕ) (t : ℝ) :
    (∑ c ∈ Finset.Icc 1 L, e (t * (c : ℝ))) =
      FordDirichletPointwise.dirichletSum L t := by
  rw [iCC_one_eq_image_succ, Finset.sum_image]
  · unfold FordDirichletPointwise.dirichletSum
    simp only [FordPolynomialPhase.e]
    apply Finset.sum_congr rfl
    intro c hc
    congr 1
    push_cast
    ring
  · intro a ha b hb hab
    exact Nat.succ_injective hab

theorem box_fourier (k : ℕ) (L : Fin k → ℕ) (t : Fin k → ℝ) :
    (∑ c ∈ box L, e (∑ j : Fin k, t j * (c j : ℝ))) =
      ∏ j : Fin k, FordDirichletPointwise.dirichletSum (L j) (t j) := by
  rw [show (∑ c ∈ box L, e (∑ j : Fin k, t j * (c j : ℝ))) =
      ∑ c ∈ box L, ∏ j : Fin k, e (t j * (c j : ℝ)) by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [FordPolynomialPhase.e]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    ]
  calc
    (∑ c ∈ box L, ∏ j : Fin k, e (t j * (c j : ℝ))) =
        ∏ j : Fin k, ∑ c ∈ Finset.Icc 1 (L j), e (t j * (c : ℝ)) := by
          rw [show box L = Fintype.piFinset
            (fun j : Fin k => Finset.Icc 1 (L j)) by rfl]
          exact (Finset.prod_univ_sum
            (fun j : Fin k => Finset.Icc 1 (L j))
            (fun j c => e (t j * (c : ℝ)))).symm
    _ = ∏ j : Fin k,
        FordDirichletPointwise.dirichletSum (L j) (t j) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact iCC_sum_eq_dirichlet (L j) (t j)

theorem coordinateBox_fourier (r k M : ℕ) (t : Fin k → ℝ) :
    (∑ c ∈ FordPowerBox.coordinateBox r k M,
      e (∑ j : Fin k, t j * (c j : ℝ))) =
      ∏ j : Fin k,
        FordDirichletPointwise.dirichletSum (r * M ^ (j.val + 1)) (t j) := by
  exact box_fourier k (fun j => r * M ^ (j.val + 1)) t

end FordBoxFourier

#print axioms FordBoxFourier.box_fourier
#print axioms FordBoxFourier.coordinateBox_fourier
