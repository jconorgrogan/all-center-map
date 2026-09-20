import MRTDynamicD12ContinuumBudget
import MRTDynamicD12SmoothSampledHolder

namespace MRTDynamicD12ContinuumSampling
noncomputable section
open scoped BigOperators
open MRTDynamicD12SmoothSampled MAPMRTLemma211AllCharacterSource
open MAPMRTProposition61TypeD1FirstInequality MRTDynamicD12MomentSource

abbrev continuumMass {q : ℕ} [NeZero q]
    (F : DirichletCharacter ℂ q → ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∑ χ, ∫ t in a..b, ‖F χ t‖^4

def characterPairs (q : ℕ) [NeZero q] : Finset (DirichletCharacter ℂ q × ℝ) := by
  classical
  exact Finset.univ.image (fun χ => (χ,0))

theorem characterPairs_mass {q : ℕ} [NeZero q]
    (F : DirichletCharacter ℂ q → ℝ → ℂ) (a b : ℝ) :
    bhpSampledPieceMass (fun χ t => ‖F χ t‖) (characterPairs q)
      (fun _ => a) (fun _ => b) = continuumMass F a b := by
  classical
  unfold bhpSampledPieceMass characterPairs continuumMass
  rw [Finset.sum_image]
  intro χ hχ ψ hψ h
  exact congrArg Prod.fst h

theorem log_continuum_weighted {q L U : ℕ} [NeZero q] {a b : ℝ}
    (hL : 1 ≤ L) (hLU : L < U) (hab : a ≤ b) :
    continuumMass (smoothLogIntervalPolynomial q L U) a b ≤
      (2 * Real.log (U : ℝ))^3 *
        (Real.log (U : ℝ) * continuumMass (criticalPrefixPolynomial q U) a b +
         Real.log ((L+1 : ℕ) : ℝ) * continuumMass (criticalPrefixPolynomial q L) a b +
         ∑ n ∈ Finset.Ioc L (U-1),
           (Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ)) *
             continuumMass (criticalPrefixPolynomial q n) a b) := by
  have h := smoothLogInterval_sampled_le_weighted_prefixes hL hLU (characterPairs q)
    (fun _ => a) (fun _ => b) (fun _ _ => hab)
  simpa only [characterPairs_mass] using h

theorem log_continuum_le_uniform {q L U : ℕ} [NeZero q] {a b M : ℝ}
    (hL : 1 ≤ L) (hLU : L < U) (hab : a ≤ b)
    (hprefix : ∀ J ∈ Finset.Icc L U,
      continuumMass (criticalPrefixPolynomial q J) a b ≤ M) :
    continuumMass (smoothLogIntervalPolynomial q L U) a b ≤
      16 * Real.log (U : ℝ)^4 * M := by
  let A := Real.log (U : ℝ)
  let D := Real.log ((L+1 : ℕ) : ℝ)
  let w := fun n : ℕ => Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ)
  have hA : 0 ≤ A := Real.log_nonneg (by exact_mod_cast (show 1 ≤ U by omega))
  have hD : 0 ≤ D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L+1 by omega))
  have hw : ∀ n ∈ Finset.Ioc L (U-1), 0 ≤ w n := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast Nat.le_succ n))
  have hW : A+D+(∑ n ∈ Finset.Ioc L (U-1), w n) = 2*A := by
    have h := logAbelVariation_eq hLU
    unfold logAbelVariation at h
    rw [abs_of_nonneg hA, abs_of_nonneg hD] at h
    have heq : (∑ n ∈ Finset.Ioc L (U-1), |w n|) =
        ∑ n ∈ Finset.Ioc L (U-1), w n :=
      Finset.sum_congr rfl (fun n hn => abs_of_nonneg (hw n hn))
    change A+D+(∑ n ∈ Finset.Ioc L (U-1), |w n|) = 2*A at h
    rwa [heq] at h
  have hS : (∑ n ∈ Finset.Ioc L (U-1),
      w n * continuumMass (criticalPrefixPolynomial q n) a b) ≤
      (∑ n ∈ Finset.Ioc L (U-1), w n) * M := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact mul_le_mul_of_nonneg_left (hprefix n (Finset.mem_Icc.mpr (by omega))) (hw n hn)
  have hends := add_le_add
    (mul_le_mul_of_nonneg_left (hprefix U (Finset.mem_Icc.mpr ⟨hLU.le,le_rfl⟩)) hA)
    (mul_le_mul_of_nonneg_left (hprefix L (Finset.mem_Icc.mpr ⟨le_rfl,hLU.le⟩)) hD)
  have hsum := add_le_add hends hS
  have hweighted := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (2*A)^3)
  have hpoint := log_continuum_weighted (q := q) (a := a) (b := b) hL hLU hab
  change continuumMass (smoothLogIntervalPolynomial q L U) a b ≤ (2*A)^3 * _ at hpoint
  have heq : (2*A)^3 * (A*M+D*M+(∑ n ∈ Finset.Ioc L (U-1), w n)*M) =
      16*A^4*M := by rw [← add_mul, ← add_mul, hW]; ring
  exact hpoint.trans (hweighted.trans_eq heq)

theorem plain_continuum_le_uniform {q L U : ℕ} [NeZero q] {a b M : ℝ}
    (hLU : L ≤ U) (hab : a ≤ b)
    (hU : continuumMass (criticalPrefixPolynomial q U) a b ≤ M)
    (hL : continuumMass (criticalPrefixPolynomial q L) a b ≤ M) :
    continuumMass (smoothIntervalPolynomial q L U) a b ≤ 16*M := by
  classical
  have hc (J : ℕ) (χ : DirichletCharacter ℂ q) :
      Continuous (fun t => ‖criticalPrefixPolynomial q J χ t‖^4) := by
    unfold criticalPrefixPolynomial MAPMRTLemma210OrthogonalityReduction.twistedFinitePolynomial
      MAPMRTLemma210OrthogonalityReduction.twistedPhase
    fun_prop
  have hd (χ : DirichletCharacter ℂ q) :
      Continuous (fun t => ‖smoothIntervalPolynomial q L U χ t‖^4) := by
    simp_rw [smoothIntervalPolynomial_eq_prefix_sub hLU]
    unfold criticalPrefixPolynomial MAPMRTLemma210OrthogonalityReduction.twistedFinitePolynomial
      MAPMRTLemma210OrthogonalityReduction.twistedPhase
    fun_prop
  have hχ (χ : DirichletCharacter ℂ q) :
      (∫ t in a..b, ‖smoothIntervalPolynomial q L U χ t‖^4) ≤
      8*((∫ t in a..b, ‖criticalPrefixPolynomial q U χ t‖^4)+
        (∫ t in a..b, ‖criticalPrefixPolynomial q L χ t‖^4)) := by
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
      ((hd χ).intervalIntegrable _ _) ((continuous_const.mul ((hc U χ).add (hc L χ))).intervalIntegrable _ _)
      (fun t ht => smoothInterval_fourth_le hLU χ t)
    dsimp only [Pi.mul_apply, Pi.add_apply] at h
    simpa only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((hc U χ).intervalIntegrable a b) ((hc L χ).intervalIntegrable a b)] using h
  have h := Finset.sum_le_sum (fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) => hχ χ)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at h
  change continuumMass (smoothIntervalPolynomial q L U) a b ≤
    8*(continuumMass (criticalPrefixPolynomial q U) a b+continuumMass (criticalPrefixPolynomial q L) a b) at h
  linarith

/-- Uniform cutoff envelope retains the small-cutoff error through `L`. -/
def smoothBudgetShape (T : ℝ) (q L U : ℕ) : ℝ :=
  (q : ℝ)*T + (q : ℝ)*T *
    ((q : ℝ)^2/T^2 + (U : ℝ)^2/T^4 + 1/(L : ℝ)^2) +
    (U : ℝ)^2 * (((q : ℝ)*T)*(16/T^4))

theorem continuumBudgetShape_le {T : ℝ} {q L U J : ℕ}
    (hT : 0 ≤ T) (hL : 1 ≤ L) (hLJ : L ≤ J) (hJU : J ≤ U) :
    continuumBudgetShape T q J ≤ smoothBudgetShape T q L U := by
  have hLJ' : (L : ℝ) ≤ J := by exact_mod_cast hLJ
  have hJU' : (J : ℝ) ≤ U := by exact_mod_cast hJU
  have hLp : 0 < (L : ℝ)^2 := by positivity
  have hinv : 1/(J : ℝ)^2 ≤ 1/(L : ℝ)^2 := by
    apply one_div_le_one_div_of_le hLp
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hLJ' 2
  unfold continuumBudgetShape smoothBudgetShape
  gcongr

theorem dynamicD12SmoothContinuumBudget_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
      ∀ {X T K a b : ℝ} {q L U : ℕ} [NeZero q],
        DynamicD12MomentRange X T K q U → 2 ≤ L → L < U →
        a ≤ b → b-a+1 ≤ T →
        (∀ t ∈ Set.Icc a b, T/2 ≤ |t| ∧ |t| ≤ T) →
        continuumMass (smoothIntervalPolynomial q L U) a b ≤
          C*(1+Real.log X)^B*smoothBudgetShape T q L U ∧
        continuumMass (smoothLogIntervalPolynomial q L U) a b ≤
          C*(1+Real.log X)^B*smoothBudgetShape T q L U * Real.log (U : ℝ)^4 := by
  obtain ⟨C,hC,B,hB,hsource⟩ := dynamicD12ContinuumIntervalBudget_proved
  refine ⟨16*C, by positivity, B,hB, ?_⟩
  intro X T K a b q L U _ hrange hL hLU hab hlen hann
  have hlog : 0 ≤ 1+Real.log X := by
    have := Real.log_nonneg (show 1 ≤ X by linarith [hrange.X_large])
    linarith
  have hprefix (J : ℕ) (hJ : J ∈ Finset.Icc L U) :
      continuumMass (criticalPrefixPolynomial q J) a b ≤
      C*(1+Real.log X)^B*smoothBudgetShape T q L U := by
    have hj := Finset.mem_Icc.mp hJ
    have hr : DynamicD12MomentRange X T K q J :=
      { hrange with
        cutoff_ge_two := by omega
        cutoff_le_X := (by exact_mod_cast hj.2 : (J : ℝ) ≤ U).trans hrange.cutoff_le_X }
    exact (hsource hr hab hlen hann).trans
      (mul_le_mul_of_nonneg_left
        (continuumBudgetShape_le (by linarith [hrange.T_ge_two]) (by omega) hj.1 hj.2)
        (by positivity))
  constructor
  · have h := plain_continuum_le_uniform hLU.le hab
      (hprefix U (Finset.mem_Icc.mpr ⟨hLU.le,le_rfl⟩))
      (hprefix L (Finset.mem_Icc.mpr ⟨le_rfl,hLU.le⟩))
    convert h using 1 <;> ring
  · have h := log_continuum_le_uniform (by omega : 1 ≤ L) hLU hab hprefix
    convert h using 1 <;> ring

end
end MRTDynamicD12ContinuumSampling

#print axioms MRTDynamicD12ContinuumSampling.dynamicD12SmoothContinuumBudget_proved
