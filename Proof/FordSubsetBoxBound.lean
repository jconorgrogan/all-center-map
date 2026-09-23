import FordBoxMoment
import FordDifferenceWeighted
import FordIntegerPowerMoment
import FordKernelSign
import FordSubsetPower

open scoped BigOperators
noncomputable section

namespace FordSubsetBoxBound

open FordPolynomialPhase FordDirichletPointwise FordSubsetMoment

theorem subset_box_moment_bound (B : Finset ℕ) (s k M : ℕ)
    (hs : 1 ≤ s) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M)
    (L q : Fin k → ℕ) (gamma : Fin k → ℝ)
    (hL : ∀ j, 2 ≤ L j)
    (hK : ∀ j : Fin k, 2 ≤ s * M ^ (j.val + 1))
    (hq : ∀ j, L j < 2 ^ q j) (hg : ∀ j, gamma j ≠ 0)
    (a : FordSubsetMoment.BoundedNat B → ℂ)
    (ha : ∀ b, ‖a b‖ = 1) :
    (∑ c ∈ FordBoxFourier.box L,
      ‖∑ b : FordSubsetMoment.BoundedNat B, a b * e (∑ j : Fin k,
        gamma j * (((b.val : ℕ) : ℝ) ^ (j.val + 1)) * (c j : ℝ))‖ ^ (2 * s)) ≤
    (MAPFordCompleteSystemMoment.completeMoment s k M : ℝ) *
      ∏ j : Fin k, ((L j : ℝ) * min (2 * ((s * M ^ (j.val + 1) : ℕ) : ℝ))
        (6 + (4 * (q j : ℝ) + 2) * ((s * M ^ (j.val + 1) : ℕ) : ℝ) / L j +
          6 * ((s * M ^ (j.val + 1) : ℕ) : ℝ) * |gamma j| +
          (4 * (q j : ℝ) + 2) / ((L j : ℝ) * |gamma j|))) := by
  classical
  let f := FordSubsetPower.subsetFreq B M hB (s := s) (k := k)
  let S := FordIntegerPower.differenceBox s k M
  let W : (Fin k → ℤ) → ℝ := fun d =>
    ∏ j, ‖dirichletSum (L j) ((d j : ℝ) * gamma j)‖
  have hcast (x : Fin s → FordSubsetMoment.BoundedNat B) (j : Fin k) :
      (f x j : ℝ) = ∑ i, (((x i).val : ℕ) : ℝ) ^ (j.val + 1) := by
    simp [f, FordSubsetPower.subsetFreq_apply]
  have hW (x y : Fin s → FordSubsetMoment.BoundedNat B) :
      W (f x - f y) = ∏ j, ‖dirichletSum (L j)
        (gamma j * ((∑ i, (((x i).val : ℕ) : ℝ) ^ (j.val + 1)) -
          (∑ i, (((y i).val : ℕ) : ℝ) ^ (j.val + 1))))‖ := by
    dsimp [W]
    simp only [Int.cast_sub, hcast, mul_comm]
  have hw := FordDifferenceWeighted.weighted_difference_le_zeroMoment f S
    (by intro x y; exact FordSubsetPower.subsetFreq_difference_mem_box B s k M hB hs x y)
    W (by intro d hd; positivity)
  have hzero : (FordDifferenceDominance.differencePairCount f 0 : ℝ) ≤
      (MAPFordCompleteSystemMoment.completeMoment s k M : ℝ) := by
    exact_mod_cast FordSubsetPower.subsetZeroRep_le_completeMoment B s k M hB
  have hw' : (∑ x : Fin s → FordSubsetMoment.BoundedNat B,
      ∑ y : Fin s → FordSubsetMoment.BoundedNat B, W (f x - f y)) ≤
      (MAPFordCompleteSystemMoment.completeMoment s k M : ℝ) * ∑ d ∈ S, W d := by
    exact hw.trans (mul_le_mul_of_nonneg_right hzero (by positivity))
  have hfact : (∑ d ∈ S, W d) =
      ∏ j : Fin k, ∑ d ∈ FordDirichletShells.diffSet (s * M ^ (j.val + 1)),
        ‖dirichletSum (L j) ((d : ℝ) * gamma j)‖ := by
    exact (Finset.prod_univ_sum
      (fun j : Fin k => FordDirichletShells.diffSet (s * M ^ (j.val + 1)))
      (fun j d => ‖dirichletSum (L j) ((d : ℝ) * gamma j)‖)).symm
  rw [hfact] at hw'
  have hprod : (∏ j : Fin k, ∑ d ∈ FordDirichletShells.diffSet (s * M ^ (j.val + 1)),
      ‖dirichletSum (L j) ((d : ℝ) * gamma j)‖) ≤
      ∏ j : Fin k, ((L j : ℝ) * min (2 * ((s * M ^ (j.val + 1) : ℕ) : ℝ))
        (6 + (4 * (q j : ℝ) + 2) * ((s * M ^ (j.val + 1) : ℕ) : ℝ) / L j +
          6 * ((s * M ^ (j.val + 1) : ℕ) : ℝ) * |gamma j| +
          (4 * (q j : ℝ) + 2) / ((L j : ℝ) * |gamma j|))) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      positivity
    · intro j hj
      exact FordKernelSign.kernel_sum_le_abs_min (hK j) (hL j) (hq j) (hg j)
  have hlast := hw'.trans
    (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hm := FordBoxMoment.box_moment_bound k s L gamma
    (fun b : FordSubsetMoment.BoundedNat B =>
      fun j : Fin k => (((b.val : ℕ) : ℝ) ^ (j.val + 1))) a ha
  exact hm.trans (by simpa only [hW] using hlast)

end FordSubsetBoxBound

#print axioms FordSubsetBoxBound.subset_box_moment_bound
