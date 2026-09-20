import GuthMaynardS3BlockRectangle

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3RectangleSymmetry

open GuthMaynardJIteration
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralBalancedGeometry
open GuthMaynardS3WideProfile
open GuthMaynardS3BlockRectangle


private lemma affineCenter_div_eq_swapped_inv
    {v : ℝ} (hv : v ≠ 0) (m1 m2 m3 : ℤ) :
    affineCenter m1 m2 m3 v / v =
      affineCenter m3 m2 m1 v⁻¹ := by
  unfold affineCenter
  field_simp [hv]
  ring

/-- Reciprocal-v symmetry before the final outer-coordinate reindex. -/
theorem rectangleAffineSquareSum_eq_swapped_right_inv
    {B : ℝ} (W : Finset ℝ) (Mcut k : ℕ) {v : ℝ} (hv : v ≠ 0) :
    rectangleAffineSquareSum B W Mcut k v =
      (∑ m3 ∈ blockCoordinateRange Mcut k,
        ∑ m2 ∈ blockMiddleRange Mcut k,
          ∑ m1 ∈ blockCoordinateRange Mcut k,
            wideProfile B W (affineCenter m3 m2 m1 v⁻¹)) := by
  unfold rectangleAffineSquareSum
  calc
    (∑ m1 ∈ blockCoordinateRange Mcut k,
      ∑ m2 ∈ blockMiddleRange Mcut k,
        ∑ m3 ∈ blockCoordinateRange Mcut k,
          wideProfile B W (affineCenter m1 m2 m3 v / v)) =
        ∑ m3 ∈ blockCoordinateRange Mcut k,
          ∑ m2 ∈ blockMiddleRange Mcut k,
            ∑ m1 ∈ blockCoordinateRange Mcut k,
              wideProfile B W (affineCenter m1 m2 m3 v / v) := by
      calc
        _ = ∑ m1 ∈ blockCoordinateRange Mcut k,
            ∑ m3 ∈ blockCoordinateRange Mcut k,
              ∑ m2 ∈ blockMiddleRange Mcut k,
                wideProfile B W (affineCenter m1 m2 m3 v / v) := by
          apply Finset.sum_congr rfl
          intro m1 hm1
          rw [Finset.sum_comm]
        _ = ∑ m3 ∈ blockCoordinateRange Mcut k,
            ∑ m1 ∈ blockCoordinateRange Mcut k,
              ∑ m2 ∈ blockMiddleRange Mcut k,
                wideProfile B W (affineCenter m1 m2 m3 v / v) := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro m3 hm3
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m3 hm3
      apply Finset.sum_congr rfl
      intro m2 hm2
      apply Finset.sum_congr rfl
      intro m1 hm1
      rw [affineCenter_div_eq_swapped_inv hv]


/-- Exact reciprocal-v identity after alpha-renaming the swapped outer binders. -/
theorem rectangleAffineSquareSum_eq_right_inv
    {B : ℝ} (W : Finset ℝ) (Mcut k : ℕ) {v : ℝ} (hv : v ≠ 0) :
    rectangleAffineSquareSum B W Mcut k v =
      rectangleAffineSquareSumRight B W Mcut k v⁻¹ := by
  simpa [rectangleAffineSquareSumRight] using
    (rectangleAffineSquareSum_eq_swapped_right_inv (B := B) W Mcut k hv)

/-- The right rectangle is exactly the finite affine source sum for the
reflected wide profile.  The minus sign in `affineCenter` is absorbed into
that profile, with no positivity or cardinality loss. -/
theorem rectangleAffineSquareSumRight_eq_sourceFiniteAffineSum
    (B : ℝ) (W : Finset ℝ) (Mcut k : ℕ) (v : ℝ) :
    rectangleAffineSquareSumRight B W Mcut k v =
      sourceFiniteAffineSum (blockCoordinateRange Mcut k)
        (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k)
        (fun u => wideProfile B W (-u)) v := by
  unfold rectangleAffineSquareSumRight sourceFiniteAffineSum affineCenter
  apply Finset.sum_congr rfl
  intro m1 hm1
  apply Finset.sum_congr rfl
  intro m2 hm2
  apply Finset.sum_congr rfl
  intro m3 hm3
  congr 1
  ring

end GuthMaynardS3RectangleSymmetry


#print axioms GuthMaynardS3RectangleSymmetry.rectangleAffineSquareSumRight_eq_sourceFiniteAffineSum

#print axioms GuthMaynardS3RectangleSymmetry.rectangleAffineSquareSum_eq_right_inv
