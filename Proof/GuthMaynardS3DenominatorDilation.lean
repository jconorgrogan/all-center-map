import GuthMaynardS3RectangleFourierEnergy

open scoped BigOperators Real
open MeasureTheory
noncomputable section
namespace GuthMaynardS3DenominatorDilation
open GuthMaynardJIteration GuthMaynardS3BlockRectangle GuthMaynardS3LiteralTruncation

/-- Exact denominator reindexing, including the totalized zero denominator. -/
theorem source_sum_dilate_four (R S U : Finset ℤ) (f : ℝ → ℝ) (u : ℝ) :
    sourceFiniteAffineSum R S U f u =
      sourceFiniteAffineSum R (S.image (fun m => 4*m)) U (fun v => f (4*v)) u := by
  unfold sourceFiniteAffineSum
  apply Finset.sum_congr rfl
  intro m1 hm1
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro m2 hm2
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    push_cast
    by_cases h : (m2 : ℝ) = 0
    · simp [h]
    · field_simp
  · intro a ha b hb hab
    dsimp at hab
    omega

private theorem prefix_mono {A B : ℕ} (h : A ≤ B) :
    nonzeroPrefix A ⊆ nonzeroPrefix B := by
  intro m hm
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n,
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans h⟩, rfl⟩)
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n,
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans h⟩, rfl⟩)

private theorem prefix_four {A : ℕ} {m : ℤ} (hm : m ∈ nonzeroPrefix A) :
    4*m ∈ nonzeroPrefix (4*A) := by
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨4*n, Finset.mem_Icc.mpr ?_, ?_⟩
    · have hn := Finset.mem_Icc.mp hn
      constructor <;> omega
    · push_cast; ring
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨4*n, Finset.mem_Icc.mpr ?_, ?_⟩
    · have hn := Finset.mem_Icc.mp hn
      constructor <;> omega
    · push_cast; ring

theorem coordinate_subset_dilated (A k : ℕ) :
    blockCoordinateRange A k ⊆ blockCoordinateRange (4*A) (k+2) := by
  intro m hm
  obtain ⟨hm,hb⟩ := Finset.mem_filter.mp hm
  apply Finset.mem_filter.mpr
  refine ⟨prefix_mono (by omega) hm, ?_⟩
  have hp : (0:ℝ) ≤ 2^k := by positivity
  rw [pow_add]
  norm_num
  nlinarith

theorem middle_image_subset_dilated (A k : ℕ) :
    (blockMiddleRange A k).image (fun m => 4*m) ⊆
      blockMiddleRange (4*A) (k+2) := by
  intro m hm
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hn,hlo,hhi⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨prefix_four hn, ?_⟩
  push_cast
  rw [abs_mul, pow_add]
  norm_num
  constructor <;> nlinarith

private lemma affine_sum_nonneg (R S U : Finset ℤ) (f : ℝ → ℝ)
    (hf : ∀ v, 0 ≤ f v) (u : ℝ) : 0 ≤ sourceFiniteAffineSum R S U f u := by
  unfold sourceFiniteAffineSum
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun m hm =>
    Finset.sum_nonneg (fun j hj => hf _)))

private lemma affine_sum_mono {R S U R' S' U' : Finset ℤ}
    (hR : R ⊆ R') (hS : S ⊆ S') (hU : U ⊆ U')
    (f : ℝ → ℝ) (hf : ∀ v, 0 ≤ f v) (u : ℝ) :
    sourceFiniteAffineSum R S U f u ≤ sourceFiniteAffineSum R' S' U' f u := by
  unfold sourceFiniteAffineSum
  calc
    _ ≤ ∑ i ∈ R, ∑ m ∈ S', ∑ j ∈ U', f (((i : ℝ)*u+j)/m) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ m ∈ S, ∑ j ∈ U', f (((i : ℝ)*u+j)/m) := by
          apply Finset.sum_le_sum
          intro m hm
          exact Finset.sum_le_sum_of_subset_of_nonneg hU (fun j _ _ => hf _)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS
          (fun m _ _ => Finset.sum_nonneg (fun j _ => hf _))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hR
      (fun i _ _ => Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun j _ => hf _)))

/-- Source rectangle energy survives profile compression with exact denominator
reindexing, followed only by nonnegative enlargement of literal masks. -/
theorem rectangle_energy_le_dilated
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F (fun v => f (4*v))) (A k : ℕ) :
    sourceFiniteAffineEnergy (blockCoordinateRange A k) (blockMiddleRange A k)
      (blockCoordinateRange A k) f ≤
    sourceFiniteAffineEnergy (blockCoordinateRange (4*A) (k+2))
      (blockMiddleRange (4*A) (k+2)) (blockCoordinateRange (4*A) (k+2))
      (fun v => f (4*v)) := by
  let R := blockCoordinateRange A k
  let S0 := (blockMiddleRange A k).image (fun m => 4*m)
  let R' := blockCoordinateRange (4*A) (k+2)
  let S' := blockMiddleRange (4*A) (k+2)
  have hr : ∀ m ∈ R, m ≠ 0 := fun m hm =>
    nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1
  have hs : ∀ m ∈ S0, m ≠ 0 := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    exact mul_ne_zero (by norm_num) (nonzeroPrefix_ne_zero (Finset.mem_filter.mp hn).1)
  have hr' : ∀ m ∈ R', m ≠ 0 := fun m hm =>
    nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1
  have hs' : ∀ m ∈ S', m ≠ 0 := fun m hm =>
    nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1
  have hl := integrable_sq_sourceFiniteAffineSum R S0 R (fun v => f (4*v))
    hf.continuous hf.squareIntegrable hr hs
  have hh := integrable_sq_sourceFiniteAffineSum R' S' R' (fun v => f (4*v))
    hf.continuous hf.squareIntegrable hr' hs'
  unfold sourceFiniteAffineEnergy
  simp_rw [source_sum_dilate_four (blockCoordinateRange A k) (blockMiddleRange A k)]
  apply integral_mono hl hh
  intro u
  apply pow_le_pow_left₀ (affine_sum_nonneg R S0 R _ hf.nonneg u)
  exact affine_sum_mono (coordinate_subset_dilated A k)
    (middle_image_subset_dilated A k) (coordinate_subset_dilated A k) _ hf.nonneg u

#print axioms rectangle_energy_le_dilated
#print axioms source_sum_dilate_four
#print axioms coordinate_subset_dilated
#print axioms middle_image_subset_dilated
end GuthMaynardS3DenominatorDilation
