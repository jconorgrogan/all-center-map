import GuthMaynardEnergy114WeightedAverage
import GuthMaynardHeathBrownCertified

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy116ShiftedMean
open CGLProofDAG GuthMaynardSource
open GuthMaynardHeathBrownInterface GuthMaynardHeathBrownMajorant
open GuthMaynardEnergy114WeightedAverage GuthMaynardEnergy114KernelEnvelope

/-- The shift is absorbed into coefficients before the exact endpoint mask. -/
def shiftedCoefficient (b : ℕ → ℂ) (s : ℝ) (n : ℕ) : ℂ :=
  b n * Complex.exp (Complex.I * (((-s * Real.log (n : ℝ)) : ℝ) : ℂ))

theorem norm_shiftedCoefficient (b : ℕ → ℂ) (s : ℝ) (n : ℕ) :
    ‖shiftedCoefficient b s n‖ = ‖b n‖ := by
  unfold shiftedCoefficient
  rw [norm_mul]
  have h : ‖Complex.exp (Complex.I * (((-s * Real.log (n : ℝ)) : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
    norm_num
  rw [h,mul_one]

theorem dirichlet_shift (N : ℕ) (b : ℕ → ℂ) (t s : ℝ) :
    dirichletPolynomial (shiftedCoefficient b s) N t =
      dirichletPolynomial b N (t-s) := by
  unfold dirichletPolynomial shiftedCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Literal shifted open-left difference mean square, from the certified
Heath--Brown theorem. No shift supremum or coefficient estimate is assumed. -/
theorem shifted_difference_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (T : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (s : ℝ),
        T0 ≤ T → 1 ≤ N →
        (∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1) →
        OneSeparated W → ContainedInIntervalOfLength W T →
        (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPolynomial b N (t-u-s)‖^2) ≤
          C * Real.rpow T eta * heathBrownShape T N W := by
  obtain ⟨C,T0,hC,hT0,hbound⟩ :=
    unitCoefficient_differenceMeanSquare_of_oneCoefficientCore
      GuthMaynardHeathBrownCertified.heathBrownOneCoefficientCore heta
  refine ⟨C,T0,hC,hT0,?_⟩
  intro T N b W s hT hN hb hsep hcontained
  have hcoef : ∀ n ∈ Finset.Icc N (2*N),
      ‖lowerEndpointZero N (shiftedCoefficient b s) n‖ ≤ 1 := by
    intro n hn
    by_cases he : n = N
    · simp [lowerEndpointZero,he]
    · rw [lowerEndpointZero,if_neg he,norm_shiftedCoefficient]
      exact hb n (Finset.mem_Ioc.mpr ⟨lt_of_le_of_ne (Finset.mem_Icc.mp hn).1 (Ne.symm he),
        (Finset.mem_Icc.mp hn).2⟩)
  have hh := hbound T N (lowerEndpointZero N (shiftedCoefficient b s)) W
    hT hN hcoef hsep hcontained
  simpa only [differenceQuadraticForm,differencePolynomial,
    displayedDirichletPolynomial_lowerEndpointZero,dirichlet_shift] using hh

/-- The same estimate survives the whole-line integrable averaging used to
remove all shifts within one floor-difference bin. -/
theorem weighted_difference_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (T : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T0 ≤ T → 1 ≤ N →
        (∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1) →
        OneSeparated W → ContainedInIntervalOfLength W T →
        (∑ t ∈ W, ∑ u ∈ W, dirichletWeightedSquareMean N b (t-u)) ≤
          C * Real.rpow T eta * heathBrownShape T N W := by
  obtain ⟨C,T0,hC,hT0,hbound⟩ := shifted_difference_bound heta
  let A : ℝ := ∫ s : ℝ, energy114Weight s
  have hA : 0 ≤ A := integral_nonneg inv_one_add_sq_nonneg
  refine ⟨(A+1)*C,T0,by positivity,hT0,?_⟩
  intro T N b W hT hN hb hsep hcontained
  let K : ℝ := C * Real.rpow T eta * heathBrownShape T N W
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
    (heathBrownShape_nonneg (by linarith) N W)
  have hint (t u : ℝ) := dirichlet_weighted_square_integrable N b (t-u)
  have hint1 (t : ℝ) : Integrable (fun s : ℝ =>
      ∑ u ∈ W, energy114Weight s * ‖dirichletPolynomial b N (t-u-s)‖^2) :=
    integrable_finset_sum W (fun u _ => hint t u)
  have hint2 : Integrable (fun s : ℝ => ∑ t ∈ W, ∑ u ∈ W,
      energy114Weight s * ‖dirichletPolynomial b N (t-u-s)‖^2) :=
    integrable_finset_sum W (fun t _ => hint1 t)
  have heq : (∑ t ∈ W, ∑ u ∈ W, dirichletWeightedSquareMean N b (t-u)) =
      ∫ s : ℝ, ∑ t ∈ W, ∑ u ∈ W,
        energy114Weight s * ‖dirichletPolynomial b N (t-u-s)‖^2 := by
    rw [integral_finset_sum W (fun t _ => hint1 t)]
    apply Finset.sum_congr rfl
    intro t ht
    exact (integral_finset_sum W (fun u _ => hint t u)).symm
  calc
    _ = ∫ s : ℝ, ∑ t ∈ W, ∑ u ∈ W,
        energy114Weight s * ‖dirichletPolynomial b N (t-u-s)‖^2 := heq
    _ ≤ ∫ s : ℝ, energy114Weight s*K := by
      apply integral_mono hint2 (inv_one_add_sq_integrable.mul_const K)
      intro s
      have hh := mul_le_mul_of_nonneg_left (hbound T N b W s hT hN hb hsep hcontained)
        (inv_one_add_sq_nonneg s)
      simpa only [Finset.mul_sum] using hh
    _ = A*K := integral_mul_const _ _
    _ ≤ (A+1)*K := mul_le_mul_of_nonneg_right (by linarith) hK
    _ = _ := by dsimp [K]; ring

end GuthMaynardEnergy116ShiftedMean
#print axioms GuthMaynardEnergy116ShiftedMean.shifted_difference_bound
#print axioms GuthMaynardEnergy116ShiftedMean.weighted_difference_bound
