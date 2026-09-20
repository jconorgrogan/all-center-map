import GuthMaynardS3LiteralRadial
import GuthMaynardLemma62ReflectionSubstitution
namespace GuthMaynardS3SymmetryGenerators
open scoped BigOperators
open GuthMaynardS1Source GuthMaynardEquation55Split
open GuthMaynardLemma62FarTail
noncomputable section
 theorem sourceHhat_neg_frequency_eq_conj (t xi : ℝ) :
    sourceHhat t (-xi) = starRingEnd ℂ (sourceHhat (-t) xi) := by
  simpa [sourceHhat, sectionThreeFourierCoefficient] using
    (GuthMaynardLemma62ReflectionSubstitution.sectionThreeFourierCoefficient_neg_eq_conj t xi)

 theorem sourceHhat_conj_neg_frequency (t xi : ℝ) :
    starRingEnd ℂ (sourceHhat t (-xi)) = sourceHhat (-t) xi := by
  have h := congrArg (starRingEnd ℂ) (sourceHhat_neg_frequency_eq_conj t xi)
  simpa only [starRingEnd_apply, star_star] using h

 theorem sourceIm_swap_eq_conj_neg (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    sourceIm N W m2 m1 m3 =
      starRingEnd ℂ (sourceIm N W (-m1) (-m2) (-m3)) := by
  unfold sourceIm
  simp only [map_mul, map_sum, map_pow, Int.cast_neg, neg_mul]
  rw [show (starRingEnd ℂ) (↑N : ℂ) ^ 3 = (↑N : ℂ) ^ 3 by norm_num]
  congr 1
  simp_rw [sourceHhat_conj_neg_frequency]
  calc
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      sourceHhat (t₁ - t₂) ((m2 : ℝ) * N) *
      sourceHhat (t₂ - t₃) ((m1 : ℝ) * N) *
      sourceHhat (t₃ - t₁) ((m3 : ℝ) * N)) =
        ∑ t₂ ∈ W, ∑ t₁ ∈ W, ∑ t₃ ∈ W,
          sourceHhat (t₁ - t₂) ((m2 : ℝ) * N) *
          sourceHhat (t₂ - t₃) ((m1 : ℝ) * N) *
          sourceHhat (t₃ - t₁) ((m3 : ℝ) * N) := by rw [Finset.sum_comm]
    _ = ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ t₁ ∈ W,
          sourceHhat (t₁ - t₂) ((m2 : ℝ) * N) *
          sourceHhat (t₂ - t₃) ((m1 : ℝ) * N) *
          sourceHhat (t₃ - t₁) ((m3 : ℝ) * N) := by
      apply Finset.sum_congr rfl
      intro t₂ ht₂
      rw [Finset.sum_comm]
    _ = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        sourceHhat (-(t₁ - t₂)) ((m1 : ℝ) * N) *
        sourceHhat (-(t₂ - t₃)) ((m2 : ℝ) * N) *
        sourceHhat (-(t₃ - t₁)) ((m3 : ℝ) * N) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t₁ ht₁
      apply Finset.sum_congr rfl
      intro t₂ ht₂
      apply Finset.sum_congr rfl
      intro t₃ ht₃
      ring

 theorem norm_sourceIm_swap_global_neg (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ‖sourceIm N W m2 m1 m3‖ = ‖sourceIm N W (-m1) (-m2) (-m3)‖ := by
  rw [sourceIm_swap_eq_conj_neg]
  simp

 theorem sourceIm_cycle (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    sourceIm N W m2 m3 m1 = sourceIm N W m1 m2 m3 := by
  unfold sourceIm
  congr 1
  calc
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      sourceHhat (t₁ - t₂) ((m2 : ℝ) * N) *
      sourceHhat (t₂ - t₃) ((m3 : ℝ) * N) *
      sourceHhat (t₃ - t₁) ((m1 : ℝ) * N)) =
        ∑ t₁ ∈ W, ∑ t₃ ∈ W, ∑ t₂ ∈ W,
          sourceHhat (t₁ - t₂) ((m2 : ℝ) * N) *
          sourceHhat (t₂ - t₃) ((m3 : ℝ) * N) *
          sourceHhat (t₃ - t₁) ((m1 : ℝ) * N) := by
            apply Finset.sum_congr rfl
            intro t₁ ht₁
            rw [Finset.sum_comm]
    _ = ∑ t₃ ∈ W, ∑ t₁ ∈ W, ∑ t₂ ∈ W,
          sourceHhat (t₁ - t₂) ((m2 : ℝ) * N) *
          sourceHhat (t₂ - t₃) ((m3 : ℝ) * N) *
          sourceHhat (t₃ - t₁) ((m1 : ℝ) * N) := by
            rw [Finset.sum_comm]
    _ = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        sourceHhat (t₁ - t₂) ((m1 : ℝ) * N) *
        sourceHhat (t₂ - t₃) ((m2 : ℝ) * N) *
        sourceHhat (t₃ - t₁) ((m3 : ℝ) * N) := by
      apply Finset.sum_congr rfl
      intro t₁ ht₁
      apply Finset.sum_congr rfl
      intro t₂ ht₂
      apply Finset.sum_congr rfl
      intro t₃ ht₃
      ring

 theorem norm_sourceIm_odd_neg_123 (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ‖sourceIm N W m1 m2 m3‖ = ‖sourceIm N W (-m2) (-m1) (-m3)‖ := by
  simpa using (norm_sourceIm_swap_global_neg N W m2 m1 m3)

 theorem norm_sourceIm_odd_neg_132 (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ‖sourceIm N W m1 m3 m2‖ = ‖sourceIm N W (-m3) (-m1) (-m2)‖ := by
  simpa using (norm_sourceIm_swap_global_neg N W m3 m1 m2)

 theorem norm_sourceIm_odd_neg_213 (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ‖sourceIm N W m2 m1 m3‖ = ‖sourceIm N W (-m1) (-m2) (-m3)‖ := by
  exact norm_sourceIm_swap_global_neg N W m1 m2 m3

 theorem norm_sourceIm_odd_neg_231 (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ‖sourceIm N W m2 m3 m1‖ = ‖sourceIm N W (-m3) (-m2) (-m1)‖ := by
  simpa using (norm_sourceIm_swap_global_neg N W m3 m2 m1)

 theorem norm_sourceIm_odd_neg_312 (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ‖sourceIm N W m3 m1 m2‖ = ‖sourceIm N W (-m1) (-m3) (-m2)‖ := by
  simpa using (norm_sourceIm_swap_global_neg N W m1 m3 m2)

 theorem norm_sourceIm_odd_neg_321 (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ‖sourceIm N W m3 m2 m1‖ = ‖sourceIm N W (-m2) (-m3) (-m1)‖ := by
  simpa using (norm_sourceIm_swap_global_neg N W m2 m3 m1)

end
end GuthMaynardS3SymmetryGenerators
#print axioms GuthMaynardS3SymmetryGenerators.sourceIm_cycle
#print axioms GuthMaynardS3SymmetryGenerators.sourceIm_swap_eq_conj_neg
#print axioms GuthMaynardS3SymmetryGenerators.norm_sourceIm_swap_global_neg
#print axioms GuthMaynardS3SymmetryGenerators.norm_sourceIm_odd_neg_123
#print axioms GuthMaynardS3SymmetryGenerators.norm_sourceIm_odd_neg_132
#print axioms GuthMaynardS3SymmetryGenerators.norm_sourceIm_odd_neg_213
#print axioms GuthMaynardS3SymmetryGenerators.norm_sourceIm_odd_neg_231
#print axioms GuthMaynardS3SymmetryGenerators.norm_sourceIm_odd_neg_312
#print axioms GuthMaynardS3SymmetryGenerators.norm_sourceIm_odd_neg_321
