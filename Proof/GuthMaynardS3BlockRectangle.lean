import GuthMaynardS3AffineCauchy
import GuthMaynardS3LiteralBalancedGeometry

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3BlockRectangle

open GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralBalancedGeometry
open GuthMaynardS3LiteralProfile
open GuthMaynardS3WideProfile

/-- The two square sums attached to the actual ordered balanced block. -/
def blockAffineSquareSum (B : ℝ) (W : Finset ℝ)
    (Mcut i k d : ℕ) (v : ℝ) : ℝ :=
  ∑ p ∈ orderedBalancedBlock Mcut i k d,
    wideProfile B W (affineCenter p.1.1 p.1.2 p.2 v / v)

def blockAffineSquareSumRight (B : ℝ) (W : Finset ℝ)
    (Mcut i k d : ℕ) (v : ℝ) : ℝ :=
  ∑ p ∈ orderedBalancedBlock Mcut i k d,
    wideProfile B W (affineCenter p.1.1 p.1.2 p.2 v)

/-- Exact finite Cauchy step on the literal ordered block.  The profile is the
constructed wide profile, so the square sums are already in the source's
admissible-profile language; no block-cardinality factor is introduced. -/
theorem orderedBalancedBlock_diag_sq_le
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    (Mcut i k d : ℕ) (v : ℝ) :
    (∑ p ∈ orderedBalancedBlock Mcut i k d,
      smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v / v) *
        smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v)) ^ 2 ≤
      blockAffineSquareSum B W Mcut i k d v *
        blockAffineSquareSumRight B W Mcut i k d v := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (orderedBalancedBlock Mcut i k d)
    (fun p => smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v / v))
    (fun p => smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v))
  calc
    _ ≤ (∑ p ∈ orderedBalancedBlock Mcut i k d,
      smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v / v) ^ 2) *
        (∑ p ∈ orderedBalancedBlock Mcut i k d,
          smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v) ^ 2) := hcs
    _ = blockAffineSquareSum B W Mcut i k d v *
        blockAffineSquareSumRight B W Mcut i k d v := by
      unfold blockAffineSquareSum blockAffineSquareSumRight wideProfile
      simp_rw [smoothedRatio_sq hB W]

end GuthMaynardS3BlockRectangle

#print axioms GuthMaynardS3BlockRectangle.orderedBalancedBlock_diag_sq_le

namespace GuthMaynardS3BlockRectangle
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralBalancedGeometry

/-- A dyadic O(2^k) signed range containing every coordinate of the selected
balanced block. -/
def blockCoordinateRange (Mcut k : ℕ) : Finset ℤ :=
  (nonzeroPrefix Mcut).filter (fun m => |(m : ℝ)| ≤ 16 * (2 ^ k : ℝ))

def blockMiddleRange (Mcut k : ℕ) : Finset ℤ :=
  (nonzeroPrefix Mcut).filter (fun m =>
    (2 ^ k : ℝ) ≤ |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * (2 ^ k : ℝ))

def blockCoordinateEmbedding (p : Frequency) : ℤ × (ℤ × ℤ) :=
  (p.1.1, (p.1.2, p.2))

private lemma block_mem_prefix_coords {Mcut i k d : ℕ} {p : Frequency}
    (hp : p ∈ orderedBalancedBlock Mcut i k d) :
    p.1.1 ∈ nonzeroPrefix Mcut ∧ p.1.2 ∈ nonzeroPrefix Mcut ∧ p.2 ∈ nonzeroPrefix Mcut := by
  have h := (Finset.mem_filter.mp hp).1
  rcases Finset.mem_product.mp h with ⟨h12, h3⟩
  rcases Finset.mem_product.mp h12 with ⟨h1, h2⟩
  exact ⟨h1, h2, h3⟩

private lemma block_mem_coordinateRange {Mcut i k d : ℕ} {p : Frequency}
    (hd : d < 4) (hp : p ∈ orderedBalancedBlock Mcut i k d) :
    p.1.1 ∈ blockCoordinateRange Mcut k ∧
    p.1.2 ∈ blockCoordinateRange Mcut k ∧
    p.2 ∈ blockCoordinateRange Mcut k := by
  have h := (Finset.mem_filter.mp hp).2
  rcases h with ⟨h1lo, h1hi, h2lo, h2hi, h3lo, h3hi, horder12, horder23⟩
  have hcoord := block_mem_prefix_coords hp
  have hpow : 0 ≤ (2 ^ k : ℝ) := by positivity
  have h1abs : |(p.1.1 : ℝ)| ≤ 16 * (2 ^ k : ℝ) := by
    nlinarith [horder12, h2hi]
  have h2abs : |(p.1.2 : ℝ)| ≤ 16 * (2 ^ k : ℝ) := by
    nlinarith [h2hi]
  have hpowd : (2 ^ d : ℝ) ≤ 8 := by
    interval_cases d <;> norm_num at hd ⊢
  have h3abs : |(p.2 : ℝ)| ≤ 16 * (2 ^ k : ℝ) := by
    rw [show (2 ^ (k + d) : ℝ) = (2 ^ k : ℝ) * (2 ^ d : ℝ) by rw [pow_add]] at h3hi
    nlinarith [h3hi]
  exact ⟨Finset.mem_filter.mpr ⟨hcoord.1, h1abs⟩,
    Finset.mem_filter.mpr ⟨hcoord.2.1, h2abs⟩,
    Finset.mem_filter.mpr ⟨hcoord.2.2, h3abs⟩⟩

end GuthMaynardS3BlockRectangle

namespace GuthMaynardS3BlockRectangle
open GuthMaynardS3WideProfile
open GuthMaynardS3LiteralAffineReduction
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralBalancedGeometry

/-- Rectangular square sums at the O(2^k) signed ranges. -/
def rectangleAffineSquareSum (B : ℝ) (W : Finset ℝ)
    (Mcut k : ℕ) (v : ℝ) : ℝ :=
  ∑ m1 ∈ blockCoordinateRange Mcut k,
    ∑ m2 ∈ blockMiddleRange Mcut k,
      ∑ m3 ∈ blockCoordinateRange Mcut k,
        wideProfile B W (affineCenter m1 m2 m3 v / v)

def rectangleAffineSquareSumRight (B : ℝ) (W : Finset ℝ)
    (Mcut k : ℕ) (v : ℝ) : ℝ :=
  ∑ m1 ∈ blockCoordinateRange Mcut k,
    ∑ m2 ∈ blockMiddleRange Mcut k,
      ∑ m3 ∈ blockCoordinateRange Mcut k,
        wideProfile B W (affineCenter m1 m2 m3 v)

end GuthMaynardS3BlockRectangle

namespace GuthMaynardS3BlockRectangle
open GuthMaynardEquation55Infinite GuthMaynardS3LiteralBalancedGeometry
open GuthMaynardS3WideProfile GuthMaynardS3LiteralAffineReduction

/-- Same-index rectangle: the middle coordinate retains its dyadic shell. -/
theorem block_subset_rectangle {Mcut i k d : ℕ} (hd : d < 4) :
    orderedBalancedBlock Mcut i k d ⊆
      (blockCoordinateRange Mcut k ×ˢ blockMiddleRange Mcut k) ×ˢ
        blockCoordinateRange Mcut k := by
  intro p hp
  have hc := block_mem_coordinateRange hd hp
  have ht := block_mem_prefix_coords hp
  have hh := (Finset.mem_filter.mp hp).2
  have hm : p.1.2 ∈ blockMiddleRange Mcut k :=
    Finset.mem_filter.mpr ⟨ht.2.1, hh.2.2.1, hh.2.2.2.1⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hc.1,hm⟩,hc.2.2⟩

theorem nonnegative_block_sum_le_rectangle
    (H : Frequency → ℝ) (hH : ∀ p, 0 ≤ H p)
    {Mcut i k d : ℕ} (hd : d < 4) :
    (∑ p ∈ orderedBalancedBlock Mcut i k d, H p) ≤
      ∑ m1 ∈ blockCoordinateRange Mcut k,
        ∑ m2 ∈ blockMiddleRange Mcut k,
          ∑ m3 ∈ blockCoordinateRange Mcut k, H ((m1,m2),m3) := by
  have hsub := block_subset_rectangle (Mcut:=Mcut) (i:=i) (k:=k) hd
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := H) hsub
    (fun p _ _ => hH p)
  simpa only [Finset.sum_product] using hh

theorem block_square_sums_le_rectangles
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    (Mcut i k d : ℕ) (hd : d < 4) (v : ℝ) :
    blockAffineSquareSum B W Mcut i k d v ≤ rectangleAffineSquareSum B W Mcut k v ∧
    blockAffineSquareSumRight B W Mcut i k d v ≤ rectangleAffineSquareSumRight B W Mcut k v := by
  constructor
  · exact nonnegative_block_sum_le_rectangle
      (fun p => wideProfile B W (affineCenter p.1.1 p.1.2 p.2 v / v))
      (fun p => wideProfile_nonneg hB W _) hd
  · exact nonnegative_block_sum_le_rectangle
      (fun p => wideProfile B W (affineCenter p.1.1 p.1.2 p.2 v))
      (fun p => wideProfile_nonneg hB W _) hd
end GuthMaynardS3BlockRectangle
#print axioms GuthMaynardS3BlockRectangle.block_square_sums_le_rectangles
