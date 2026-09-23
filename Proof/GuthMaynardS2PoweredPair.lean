import GuthMaynardHeathBrownCertified
import GuthMaynardSourceLemmas
import FixedCharacterPoweredBridge

/-! # Certified unweighted k=2 pair estimate for Section 6
The polynomial is squared with its literal Dirichlet-convolution coefficient,
then partitioned into the two disjoint dyadic blocks. The divisor majorant
and certified Heath--Brown core bound both blocks uniformly.
-/

namespace GuthMaynardS2PoweredPair

open scoped BigOperators
open CGLProofDAG GuthMaynardSource FixedCharacterPoweredBridge
open GuthMaynardHeathBrownMajorant GuthMaynardHeathBrownInterface

noncomputable section

def squaredCoefficient (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (dyadicCoefficient M a ^ 2) n

def unweightedPairFourthMoment (M : ℕ) (a : ℕ → ℂ) (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W, ‖dirichletPolynomial a M (t - u)‖ ^ 4

theorem dirichletPolynomial_sq_eq_two_blocks (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPolynomial a M t ^ 2 =
      dirichletPolynomial (squaredCoefficient M a) (M ^ 2) t +
      dirichletPolynomial (squaredCoefficient M a) (2 * M ^ 2) t := by
  have h := dirichletPolynomial_pow_eq_sum_blocks
    (N := M) (k := 2) (a := a) (by norm_num) t
  unfold squaredCoefficient
  simpa [Fin.sum_univ_two, poweredBlockPolynomial_eq_dirichletPolynomial,
    Nat.mul_comm] using! h

private theorem norm_add_sq_le (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- The literal fourth moment enters precisely two Heath--Brown blocks. -/
theorem unweightedPairFourthMoment_le_two_blocks (M : ℕ) (a : ℕ → ℂ)
    (W : Finset ℝ) :
    unweightedPairFourthMoment M a W ≤
      2 * (differenceQuadraticForm (lowerEndpointZero (M ^ 2) (squaredCoefficient M a))
        (M ^ 2) W +
      differenceQuadraticForm (lowerEndpointZero (2 * M ^ 2) (squaredCoefficient M a))
        (2 * M ^ 2) W) := by
  unfold unweightedPairFourthMoment differenceQuadraticForm differencePolynomial
  simp_rw [displayedDirichletPolynomial_lowerEndpointZero]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u hu
  have h := norm_add_sq_le
    (dirichletPolynomial (squaredCoefficient M a) (M ^ 2) (t - u))
    (dirichletPolynomial (squaredCoefficient M a) (2 * M ^ 2) (t - u))
  rw [← dirichletPolynomial_sq_eq_two_blocks, norm_pow] at h
  nlinarith

private theorem heathBrownShape_double_le {T : ℝ} (hT : 0 ≤ T)
    (M : ℕ) (W : Finset ℝ) :
    heathBrownShape T (2 * M) W ≤ 4 * heathBrownShape T M W := by
  unfold heathBrownShape
  push_cast
  have h₁ : 0 ≤ (W.card : ℝ) ^ 2 * M := by positivity
  have h₂ : 0 ≤ Real.rpow (W.card : ℝ) (5 / 4 : ℝ) *
      Real.rpow T (1 / 2 : ℝ) * M :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hT _)) (by positivity)
  nlinarith

/-- The source Section-6 unweighted fourth-moment bound, with all analytic
inputs discharged. The constant and threshold are uniform in M,a,W. -/
theorem unweightedPairFourthMoment_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M → (M : ℝ) ≤ T →
        (∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) →
        OneSeparated W → ContainedInIntervalOfLength W T →
        unweightedPairFourthMoment M a W ≤
          C * Real.rpow T eta * heathBrownShape T (M ^ 2) W := by
  obtain ⟨A, hA, hdiv⟩ := orderedDivisorCount_subpolynomial 2 (by norm_num)
    (eta / 16) (by positivity)
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ :=
    GuthMaynardHeathBrownCertified.heathBrownOneCoefficientCore
      (eta / 2) (by positivity)
  refine ⟨10 * A ^ 2 * C, T₀, by positivity, hT₀, ?_⟩
  intro T M a W hT hM hMT ha hsep hinterval
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := by linarith
  let D : ℝ := A * Real.rpow T (eta / 4)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoeff (n : ℕ) (hn : 0 < n) (hnmax : n ≤ 4 * M ^ 2) :
      ‖squaredCoefficient M a n‖ ≤ D := by
    have hnT : (n : ℝ) ≤ T ^ 4 := by
      calc
        (n : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by exact_mod_cast hnmax
        _ ≤ 4 * T ^ 2 := by gcongr
        _ ≤ T ^ 4 := by nlinarith [sq_nonneg (T ^ 2 - 4)]
    have hrpow : Real.rpow n (eta / 16) ≤ Real.rpow T (eta / 4) := by
      calc
        _ ≤ Real.rpow (T ^ 4) (eta / 16) :=
          Real.rpow_le_rpow (by positivity) hnT (by positivity)
        _ = _ := by
          rw [← Real.rpow_natCast T 4]
          change Real.rpow (Real.rpow T (4 : ℝ)) (eta / 16) = _
          exact (Real.rpow_mul hTpos.le (4 : ℝ) (eta / 16)).symm.trans
            (by congr 1; ring)
    exact (norm_dyadic_powered_coefficient_le ha 2 n).trans
      ((hdiv n hn).trans (mul_le_mul_of_nonneg_left hrpow hA.le))
  have hblock (K : ℕ) (hK : 1 ≤ K) (hKmax : 2 * K ≤ 4 * M ^ 2) :
      differenceQuadraticForm (lowerEndpointZero K (squaredCoefficient M a)) K W ≤
        D ^ 2 * (C * Real.rpow T (eta / 2) * heathBrownShape T K W) := by
    have hmajor := differenceQuadraticForm_majorant K W
      (a := lowerEndpointZero K (squaredCoefficient M a)) (b := fun _ => D) (by
        intro n hn
        by_cases hnK : n = K
        · simp [lowerEndpointZero, hnK, hD]
        · simp only [lowerEndpointZero, hnK, if_false]
          exact hcoeff n (lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hn).1)
            ((Finset.mem_Icc.mp hn).2.trans hKmax))
    apply hmajor.trans
    rw [differenceQuadraticForm_constant]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left (hHB T K W hT hK hsep hinterval) (sq_nonneg _)
  have hb₁ := hblock (M ^ 2) (by nlinarith) (by omega)
  have hb₂ := hblock (2 * M ^ 2) (by nlinarith) (by omega)
  have hdouble := heathBrownShape_double_le hTpos.le (M ^ 2) W
  have hmass0 : 0 ≤ C * Real.rpow T (eta / 2) :=
    mul_nonneg hC.le (Real.rpow_nonneg hTpos.le _)
  have hpow : (Real.rpow T (eta / 4)) ^ 2 = Real.rpow T (eta / 2) := by
    calc
      _ = Real.rpow (Real.rpow T (eta / 4)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow T ((eta / 4) * 2) :=
        (Real.rpow_mul hTpos.le (eta / 4) 2).symm
      _ = _ := by congr 1; ring
  have hjoin : Real.rpow T (eta / 2) * Real.rpow T (eta / 2) =
      Real.rpow T eta :=
    (Real.rpow_add hTpos (eta / 2) (eta / 2)).symm.trans (by congr 1; ring)
  have hfactor : D ^ 2 * (C * Real.rpow T (eta / 2)) =
      A ^ 2 * C * Real.rpow T eta := by
    change (A * Real.rpow T (eta / 4)) ^ 2 * (C * Real.rpow T (eta / 2)) = _
    rw [mul_pow, hpow]
    calc
      _ = A ^ 2 * C * (Real.rpow T (eta / 2) * Real.rpow T (eta / 2)) := by ring
      _ = _ := by rw [hjoin]
  calc
    _ ≤ 2 * (D ^ 2 * (C * Real.rpow T (eta / 2) * heathBrownShape T (M ^ 2) W) +
        D ^ 2 * (C * Real.rpow T (eta / 2) * heathBrownShape T (2 * M ^ 2) W)) :=
      (unweightedPairFourthMoment_le_two_blocks M a W).trans
        (mul_le_mul_of_nonneg_left (add_le_add hb₁ hb₂) (by positivity))
    _ ≤ 10 * (D ^ 2 * (C * Real.rpow T (eta / 2))) *
        heathBrownShape T (M ^ 2) W := by
      have h := mul_le_mul_of_nonneg_left hdouble
        (mul_nonneg (sq_nonneg D) hmass0)
      nlinarith
    _ = _ := by rw [hfactor]; ring

/-- The unweighted k=2 interpolation used in (6.2)--(6.4), with the exact
Heath--Brown shape under the square root and no analytic premise. -/
theorem unweightedPairSecondMoment_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M → (M : ℝ) ≤ T →
        (∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) →
        OneSeparated W → ContainedInIntervalOfLength W T →
        (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPolynomial a M (t - u)‖ ^ 2) ≤
          C * Real.rpow T eta * (W.card : ℝ) *
            Real.sqrt (heathBrownShape T (M ^ 2) W) := by
  obtain ⟨C, T₀, hC, hT₀, hfourth⟩ :=
    unweightedPairFourthMoment_bound (eta := 2 * eta) (by positivity)
  refine ⟨Real.sqrt C, T₀, Real.sqrt_pos.mpr hC, hT₀, ?_⟩
  intro T M a W hT hM hMT ha hsep hinterval
  have hTpos : 0 < T := lt_of_lt_of_le (by linarith) hT
  have hF := hfourth T M a W hT hM hMT ha hsep hinterval
  have hW0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hF0 : 0 ≤ unweightedPairFourthMoment M a W := by
    unfold unweightedPairFourthMoment
    positivity
  have hholder :
      (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPolynomial a M (t - u)‖ ^ 2) ≤
        (W.card : ℝ) * Real.sqrt (unweightedPairFourthMoment M a W) := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg hW0 (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hF0]
    exact GuthMaynardS2Source.holder_kTwo_pair_squared W
      (fun t u => dirichletPolynomial a M (t - u))
  have hpow : Real.rpow T (2 * eta) = (Real.rpow T eta) ^ 2 := by
    calc
      _ = Real.rpow T (eta * 2) := by congr 1; ring
      _ = Real.rpow (Real.rpow T eta) (2 : ℝ) := Real.rpow_mul hTpos.le eta 2
      _ = _ := Real.rpow_natCast _ 2
  have hroot : Real.sqrt (Real.rpow T (2 * eta)) = Real.rpow T eta := by
    rw [hpow]
    exact Real.sqrt_sq (x := Real.rpow T eta) (Real.rpow_nonneg hTpos.le eta)
  calc
    _ ≤ (W.card : ℝ) * Real.sqrt
        (C * Real.rpow T (2 * eta) * heathBrownShape T (M ^ 2) W) :=
      hholder.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hF) hW0)
    _ = _ := by
      rw [Real.sqrt_mul (x := C * Real.rpow T (2 * eta))
          (mul_nonneg hC.le (Real.rpow_nonneg hTpos.le (2 * eta))),
        Real.sqrt_mul (x := C) hC.le (Real.rpow T (2 * eta)), hroot]
      ring

end
end GuthMaynardS2PoweredPair

#print axioms GuthMaynardS2PoweredPair.unweightedPairFourthMoment_bound

#print axioms GuthMaynardS2PoweredPair.unweightedPairSecondMoment_bound
