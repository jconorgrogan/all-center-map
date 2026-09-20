import GuthMaynardProp31DirectAbsorption

set_option maxHeartbeats 500000

namespace GuthMaynardProp31SeamMonomials
noncomputable section
open scoped BigOperators
open GuthMaynardProp31DirectAbsorption

/-- At `T=N^(6/5)`, the literal `N^3`, sharp S2, and inserted S3
monomials are exactly the eight-row optimized sum. -/
theorem seam_monomial_identity
    {N R σ T : ℝ} (hN : 0 < N) (hT : T = Real.rpow N (6 / 5 : ℝ)) :
    Real.rpow N 3 +
        (Real.rpow N 2 * Real.rpow R 2 +
          T * N * Real.rpow R (3 / 2 : ℝ) +
          Real.rpow N 2 * Real.rpow T (1 / 4 : ℝ) * Real.rpow R (13 / 8 : ℝ)) +
        (Real.rpow T 2 * Real.rpow R (3 / 2 : ℝ) +
          T * R * Real.rpow N (3 - 2 * σ) +
          Real.rpow T (9 / 8 : ℝ) * Real.rpow R (29 / 16 : ℝ) *
            Real.rpow N (3 / 2 - σ) +
          T * Real.rpow R 2 * Real.rpow N (3 / 2 - σ)) =
      ∑ i : Fin 8, (Real.rpow N (a σ i) * Real.rpow R (b i)) := by
  change N ^ (3 : ℝ) +
    (N ^ (2 : ℝ) * R ^ (2 : ℝ) + T * N * R ^ (3 / 2 : ℝ) +
      N ^ (2 : ℝ) * T ^ (1 / 4 : ℝ) * R ^ (13 / 8 : ℝ)) +
    (T ^ (2 : ℝ) * R ^ (3 / 2 : ℝ) + T * R * N ^ (3 - 2 * σ : ℝ) +
      T ^ (9 / 8 : ℝ) * R ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ : ℝ) +
      T * R ^ (2 : ℝ) * N ^ (3 / 2 - σ : ℝ)) =
    ∑ i : Fin 8, N ^ (a σ i) * R ^ (b i)
  have hT' : T = N ^ (6 / 5 : ℝ) := hT
  rw [hT']
  rw [← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
    ← Real.rpow_mul hN.le]
  norm_num only [show (6 / 5 : ℝ) * 2 = 12 / 5 by norm_num,
    show (6 / 5 : ℝ) * (1 / 4) = 3 / 10 by norm_num,
    show (6 / 5 : ℝ) * (9 / 8) = 27 / 20 by norm_num]
  have hpair (x y : ℝ) : N ^ x * N ^ y = N ^ (x + y) :=
    (Real.rpow_add hN _ _).symm
  have h12 : N ^ (6 / 5 : ℝ) * N = N ^ (11 / 5 : ℝ) := by
    calc
      _ = N ^ (6 / 5 : ℝ) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = N ^ ((6 / 5 : ℝ) + 1) := hpair _ _
      _ = _ := by norm_num
  have h13 : N ^ (2 : ℝ) * N ^ (3 / 10 : ℝ) = N ^ (23 / 10 : ℝ) := by
    rw [hpair]
    norm_num
  have h15 : N ^ (6 / 5 : ℝ) * R * N ^ (3 - 2 * σ : ℝ) =
      N ^ (21 / 5 - 2 * σ : ℝ) * R := by
    calc
      _ = (N ^ (6 / 5 : ℝ) * N ^ (3 - 2 * σ : ℝ)) * R := by ring
      _ = N ^ ((6 / 5 : ℝ) + (3 - 2 * σ)) * R := by rw [hpair]
      _ = _ := by congr 2 <;> ring
  have h16 : N ^ (27 / 20 : ℝ) * R ^ (29 / 16 : ℝ) *
      N ^ (3 / 2 - σ : ℝ) = N ^ (57 / 20 - σ : ℝ) * R ^ (29 / 16 : ℝ) := by
    calc
      _ = (N ^ (27 / 20 : ℝ) * N ^ (3 / 2 - σ : ℝ)) * R ^ (29 / 16 : ℝ) := by ring
      _ = N ^ ((27 / 20 : ℝ) + (3 / 2 - σ)) * R ^ (29 / 16 : ℝ) := by rw [hpair]
      _ = _ := by congr 2 <;> ring
  have h17 : N ^ (6 / 5 : ℝ) * R ^ (2 : ℝ) * N ^ (3 / 2 - σ : ℝ) =
      N ^ (27 / 10 - σ : ℝ) * R ^ (2 : ℝ) := by
    calc
      _ = (N ^ (6 / 5 : ℝ) * N ^ (3 / 2 - σ : ℝ)) * R ^ (2 : ℝ) := by ring
      _ = N ^ ((6 / 5 : ℝ) + (3 / 2 - σ)) * R ^ (2 : ℝ) := by rw [hpair]
      _ = _ := by congr 2 <;> ring
  rw [h12, h13, h15, h16, h17]
  simp [a, b, Fin.sum_univ_succ]
  <;> ring


/-- The common exponent in the direct absorption is exactly the normalized
`T*N^(12/5)/(N^σ)^4` exponent. -/
theorem q_normalization
    {N R σ T : ℝ} (hN : 0 < N) (hT : T = Real.rpow N (6 / 5 : ℝ)) :
    Real.rpow N (18 / 5 - 4 * σ) =
      T * Real.rpow N (12 / 5 : ℝ) /
        (Real.rpow N σ) ^ 4 := by
  change N ^ (18 / 5 - 4 * σ : ℝ) =
    T * N ^ (12 / 5 : ℝ) / (N ^ σ) ^ 4
  have hT' : T = N ^ (6 / 5 : ℝ) := hT
  rw [hT', ← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN,
    ← Real.rpow_sub hN]
  congr 1
  ring

end
end GuthMaynardProp31SeamMonomials

#print axioms GuthMaynardProp31SeamMonomials.seam_monomial_identity
#print axioms GuthMaynardProp31SeamMonomials.q_normalization
