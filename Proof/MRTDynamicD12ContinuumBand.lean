import MRTDynamicD12ContinuumSmooth

namespace MRTDynamicD12ContinuumSampling
noncomputable section
open scoped BigOperators
open MAPMRTLemma211AllCharacterSource MAPMRTProposition61TypeD1FirstInequality
open MAPPolylogCor212SplitSampled MRTDynamicD12MomentSource MRTDynamicD12SmoothSampled

def bandBudgetShape (T rho : ℝ) (q J : ℕ) : ℝ :=
  (q : ℝ)*T + (q : ℝ)*T *
    ((q : ℝ)^2/T^2 + (J : ℝ)^2/T^4 + 1/(J : ℝ)^2) +
    (J : ℝ)^2 * (((q : ℝ)*T)/rho^4)

/-- Uncentered intervals stay intact; only their actual minimum absolute height enters the residue. -/
theorem dynamicD12ContinuumBandBudget_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
      ∀ {X T K a b rho : ℝ} {q J : ℕ} [NeZero q],
        DynamicD12MomentRange X T K q J →
        a ≤ b → b-a+1 ≤ T → 0 < rho →
        (∀ t ∈ Set.Icc a b, rho ≤ |t| ∧ |t| ≤ T) →
        continuumMass (criticalPrefixPolynomial q J) a b ≤
          C*(1+Real.log X)^B*bandBudgetShape T rho q J := by
  classical
  obtain ⟨C,hC,B,hB,hsource⟩ := dynamicD12SelectedPrefixMoment_proved
  refine ⟨2*C, by positivity, B,hB, ?_⟩
  intro X T K a b rho q J _ hrange hab hlen hrho hann
  let F : DirichletCharacter ℂ q → ℝ → ℝ :=
    fun χ t => ‖criticalPrefixPolynomial q J χ t‖
  have hF : ∀ χ, Continuous (F χ) := by
    intro χ
    unfold F criticalPrefixPolynomial MAPMRTLemma210OrthogonalityReduction.twistedFinitePolynomial
      MAPMRTLemma210OrthogonalityReduction.twistedPhase
    fun_prop
  have hlog : 0 ≤ 1+Real.log X := by
    have := Real.log_nonneg (show 1 ≤ X by linarith [hrange.X_large])
    linarith
  have hcolor (c : ℕ) :
      bhpSampledPieceMass F (fourthSamples (a := a) (b := b) F hF c)
        (fourthLeft (a := a) (b := b) F hF c) (fourthRight (a := a) (b := b) F hF c) ≤
      C*(1+Real.log X)^B*bandBudgetShape T rho q J := by
    let S := fourthSamples (a := a) (b := b) F hF c
    have hcard : (S.card : ℝ) ≤ (q : ℝ)*T :=
      coloredSamples_card_le_qT hab hlen (fun χ t => F χ t ^ 4) (fourthContinuous F hF) c
    have htail : selectedPrincipalDecayMass S ≤ (q : ℝ)*T/rho^4 := by
      have hterm : selectedPrincipalDecayMass S ≤ (S.card : ℝ)*(1/rho^4) := by
        unfold selectedPrincipalDecayMass
        calc
          _ ≤ ∑ z ∈ S, (1/rho^4 : ℝ) := by
            apply Finset.sum_le_sum
            intro z hz
            split_ifs
            · have hz' := (hann z.2 (coloredSamples_range _ _ c hz)).1
              apply one_div_le_one_div_of_le (pow_pos hrho 4)
              exact pow_le_pow_left₀ hrho.le (by linarith) 4
            · positivity
          _ = _ := by simp
      have h := hterm.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
      simpa only [div_eq_mul_inv, one_mul] using h
    have hs := hsource X T K q J S hrange
      (fun z hz => (hann z.2 (coloredSamples_range _ _ c hz)).2)
      (coloredSamples_spacing (a := a) (b := b) (fun χ t => F χ t^4) (fourthContinuous F hF) c)
    have hd := bhpSampledPieceMass_le_selectedFourthMass (S := S)
      (left := fourthLeft (a := a) (b := b) F hF c)
      (right := fourthRight (a := a) (b := b) F hF c) hF
      (fun z hz => fourthSamples_length F hF c hz)
      (fun z hz t ht => fourthSamples_max F hF c hz ht)
    have hd' : bhpSampledPieceMass F S (fourthLeft (a := a) (b := b) F hF c)
        (fourthRight (a := a) (b := b) F hF c) ≤ selectedPrefixFourthMass J S := hd
    apply hd'.trans (hs.trans _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold bandBudgetShape
    gcongr
  change (∑ χ, ∫ t in a..b, F χ t^4) ≤ _
  rw [continuum_fourth_eq_sampled F hF hab]
  have h := add_le_add (hcolor 0) (hcolor 1)
  nlinarith

/-- Uniform cutoff envelope retains the small-cutoff error through `L`. -/
def smoothBandBudgetShape (T rho : ℝ) (q L U : ℕ) : ℝ :=
  (q : ℝ)*T + (q : ℝ)*T *
    ((q : ℝ)^2/T^2 + (U : ℝ)^2/T^4 + 1/(L : ℝ)^2) +
    (U : ℝ)^2 * (((q : ℝ)*T)/rho^4)

theorem bandBudgetShape_le {T rho : ℝ} {q L U J : ℕ}
    (hT : 0 ≤ T) (hL : 1 ≤ L) (hLJ : L ≤ J) (hJU : J ≤ U) :
    bandBudgetShape T rho q J ≤ smoothBandBudgetShape T rho q L U := by
  have hLJ' : (L : ℝ) ≤ J := by exact_mod_cast hLJ
  have hJU' : (J : ℝ) ≤ U := by exact_mod_cast hJU
  have hLp : 0 < (L : ℝ)^2 := by positivity
  have hinv : 1/(J : ℝ)^2 ≤ 1/(L : ℝ)^2 := by
    apply one_div_le_one_div_of_le hLp
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hLJ' 2
  unfold bandBudgetShape smoothBandBudgetShape
  gcongr

theorem dynamicD12SmoothContinuumBandBudget_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
      ∀ {X T K a b rho : ℝ} {q L U : ℕ} [NeZero q],
        DynamicD12MomentRange X T K q U → 2 ≤ L → L < U →
        a ≤ b → b-a+1 ≤ T → 0 < rho →
        (∀ t ∈ Set.Icc a b, rho ≤ |t| ∧ |t| ≤ T) →
        continuumMass (smoothIntervalPolynomial q L U) a b ≤
          C*(1+Real.log X)^B*smoothBandBudgetShape T rho q L U ∧
        continuumMass (smoothLogIntervalPolynomial q L U) a b ≤
          C*(1+Real.log X)^B*smoothBandBudgetShape T rho q L U * Real.log (U : ℝ)^4 := by
  obtain ⟨C,hC,B,hB,hsource⟩ := dynamicD12ContinuumBandBudget_proved
  refine ⟨16*C, by positivity, B,hB, ?_⟩
  intro X T K a b rho q L U _ hrange hL hLU hab hlen hrho hann
  have hlog : 0 ≤ 1+Real.log X := by
    have := Real.log_nonneg (show 1 ≤ X by linarith [hrange.X_large])
    linarith
  have hprefix (J : ℕ) (hJ : J ∈ Finset.Icc L U) :
      continuumMass (criticalPrefixPolynomial q J) a b ≤
      C*(1+Real.log X)^B*smoothBandBudgetShape T rho q L U := by
    have hj := Finset.mem_Icc.mp hJ
    have hr : DynamicD12MomentRange X T K q J :=
      { hrange with
        cutoff_ge_two := by omega
        cutoff_le_X := (by exact_mod_cast hj.2 : (J : ℝ) ≤ U).trans hrange.cutoff_le_X }
    exact (hsource hr hab hlen hrho hann).trans
      (mul_le_mul_of_nonneg_left
        (bandBudgetShape_le (by linarith [hrange.T_ge_two]) (by omega) hj.1 hj.2)
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

#print axioms MRTDynamicD12ContinuumSampling.dynamicD12ContinuumBandBudget_proved

#print axioms MRTDynamicD12ContinuumSampling.dynamicD12SmoothContinuumBandBudget_proved
