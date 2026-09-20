import GuthMaynardS3BlockRectangle
import GuthMaynardS3RectangleSignSymmetry
import GuthMaynardSourceDyadicRanges

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3MiddleNormalize

open GuthMaynardJIteration
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralTruncation
open GuthMaynardS3LiteralBalancedGeometry
open GuthMaynardS3BlockRectangle

private lemma sum_neg_triple_eq
    {R S : Finset ℤ} (hR : ∀ m, m ∈ R ↔ -m ∈ R)
    (hS : ∀ m, m ∈ S ↔ -m ∈ S)
    (hSzero : ∀ m ∈ S, m ≠ 0) (f : ℝ → ℝ) (u : ℝ) :
    (∑ p ∈ ((R ×ˢ S) ×ˢ R).filter (fun p => 0 < p.1.2),
      f (((p.1.1 : ℝ) * u + (p.2 : ℝ)) / (p.1.2 : ℝ))) =
    (∑ p ∈ ((R ×ˢ S) ×ˢ R).filter (fun p => p.1.2 < 0),
      f (((p.1.1 : ℝ) * u + (p.2 : ℝ)) / (p.1.2 : ℝ))) := by
  apply Finset.sum_bij (fun p _ => ((-p.1.1, -p.1.2), -p.2))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpQ, hpPos⟩
    rcases Finset.mem_product.mp hpQ with ⟨hp12, hp3⟩
    rcases Finset.mem_product.mp hp12 with ⟨hp1, hp2⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨(hR p.1.1).mp hp1, (hS p.1.2).mp hp2⟩,
        (hR p.2).mp hp3⟩
    · exact neg_lt_zero.mpr hpPos
  · intro p hp q hq heq
    rcases p with ⟨⟨p1,p2⟩,p3⟩
    rcases q with ⟨⟨q1,q2⟩,q3⟩
    have h1 := congrArg (fun z => z.1.1) heq
    have h2 := congrArg (fun z => z.1.2) heq
    have h3 := congrArg (fun z => z.2) heq
    exact Prod.ext (Prod.ext (neg_injective h1) (neg_injective h2))
      (neg_injective h3)
  · intro p hp
    rcases p with ⟨⟨p1,p2⟩,p3⟩
    refine ⟨((-p1,-p2),-p3), ?_, ?_⟩
    · rcases Finset.mem_filter.mp hp with ⟨hpQ, hpNeg⟩
      rcases Finset.mem_product.mp hpQ with ⟨hp12, hp3⟩
      rcases Finset.mem_product.mp hp12 with ⟨hp1, hp2⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(hR p1).mp hp1, (hS p2).mp hp2⟩, (hR p3).mp hp3⟩
      · exact neg_pos.mpr hpNeg
    · simp
  · intro p hp
    rcases p with ⟨⟨p1,p2⟩,p3⟩
    congr 1
    push_cast
    ring

private lemma signed_eq_two_positive_filtered
    {R S : Finset ℤ} (hR : ∀ m, m ∈ R ↔ -m ∈ R)
    (hS : ∀ m, m ∈ S ↔ -m ∈ S)
    (hSzero : ∀ m ∈ S, m ≠ 0) (f : ℝ → ℝ) (u : ℝ) :
    sourceFiniteAffineSum R S R f u =
      2 * sourceFiniteAffineSum R (S.filter (fun m => 0 < m)) R f u := by
  let Q := (R ×ˢ S) ×ˢ R
  let Qpos := Q.filter (fun p => 0 < p.1.2)
  let Qneg := Q.filter (fun p => p.1.2 < 0)
  have hpart : Q = Qpos ∪ Qneg := by
    ext p
    constructor
    · intro hp
      have hp0 : p.1.2 ≠ 0 := hSzero p.1.2 ((Finset.mem_product.mp (Finset.mem_product.mp hp).1).2)
      rcases lt_or_gt_of_ne hp0 with hn | hp'
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp, hn⟩))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp, hp'⟩))
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
  have hdisj : Disjoint Qpos Qneg := by
    apply Finset.disjoint_left.mpr
    intro p hp hn
    exact (not_lt_of_ge (le_of_lt (Finset.mem_filter.mp hp).2))
      (Finset.mem_filter.mp hn).2
  have hsum := sum_neg_triple_eq hR hS hSzero f u
  have hsumQ : (∑ p ∈ Qpos, f (((p.1.1 : ℝ)*u+p.2)/(p.1.2 : ℝ))) =
      ∑ p ∈ Qneg, f (((p.1.1 : ℝ)*u+p.2)/(p.1.2 : ℝ)) := by
    exact hsum
  rw [show sourceFiniteAffineSum R S R f u = ∑ p ∈ Q,
      f (((p.1.1 : ℝ)*u+p.2)/(p.1.2 : ℝ)) by
        simp [sourceFiniteAffineSum, Q, Finset.sum_product]]
  rw [hpart, Finset.sum_union hdisj, hsumQ]
  have hQpos : Qpos = (R ×ˢ (S.filter (fun m => 0 < m))) ×ˢ R := by
    ext p
    simp [Q, Qpos, and_assoc, and_left_comm, and_comm]
  have hposEq :
      (∑ p ∈ Qpos, f (((p.1.1 : ℝ)*u+p.2)/(p.1.2 : ℝ))) =
        sourceFiniteAffineSum R (S.filter (fun m => 0 < m)) R f u := by
    rw [hQpos]
    simp only [sourceFiniteAffineSum, Finset.sum_product]
  rw [← hsumQ, hposEq]
  ring

end GuthMaynardS3MiddleNormalize

namespace GuthMaynardS3MiddleNormalize

open GuthMaynardJIteration
open GuthMaynardS3LiteralTruncation
open GuthMaynardS3BlockRectangle
open GuthMaynardEquation55Infinite

private lemma block_outer_neg_mem (Mcut k : ℕ) (m : ℤ) :
    m ∈ blockCoordinateRange Mcut k ↔
      -m ∈ blockCoordinateRange Mcut k := by
  unfold blockCoordinateRange
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨(GuthMaynardS3RectangleSignSymmetry.nonzeroPrefix_neg_mem).mp hm,
      by simpa using hb⟩
  · rintro ⟨hm, hb⟩
    have hnm := (GuthMaynardS3RectangleSignSymmetry.nonzeroPrefix_neg_mem
      (M := Mcut) (m := -m)).mp hm
    exact ⟨by simpa only [neg_neg] using hnm, by simpa using hb⟩

private lemma block_middle_neg_mem (Mcut k : ℕ) (m : ℤ) :
    m ∈ blockMiddleRange Mcut k ↔
      -m ∈ blockMiddleRange Mcut k := by
  unfold blockMiddleRange
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨(GuthMaynardS3RectangleSignSymmetry.nonzeroPrefix_neg_mem).mp hm,
      by simpa using hb⟩
  · rintro ⟨hm, hb⟩
    have hnm := (GuthMaynardS3RectangleSignSymmetry.nonzeroPrefix_neg_mem
      (M := Mcut) (m := -m)).mp hm
    exact ⟨by simpa only [neg_neg] using hnm, by simpa using hb⟩

/-- The actual middle shell is bounded by twice the canonical positive dyadic
source sum; the filtered positive part is enlarged only after exact signed
reindexing. -/
theorem block_sourceFiniteAffineSum_middle_le_two_positive
    (Mcut k : ℕ) (f : ℝ → ℝ) (u : ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    sourceFiniteAffineSum (blockCoordinateRange Mcut k)
      (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k) f u ≤
      2 * sourceFiniteAffineSum (blockCoordinateRange Mcut k)
        (sourcePositiveDyadicRange (2 ^ k))
        (blockCoordinateRange Mcut k) f u := by
  let R := blockCoordinateRange Mcut k
  let S := blockMiddleRange Mcut k
  let P := S.filter (fun m => 0 < m)
  have hR : ∀ m, m ∈ R ↔ -m ∈ R := block_outer_neg_mem Mcut k
  have hS : ∀ m, m ∈ S ↔ -m ∈ S := block_middle_neg_mem Mcut k
  have hSzero : ∀ m ∈ S, m ≠ 0 := by
    intro m hm
    exact GuthMaynardS3LiteralTruncation.nonzeroPrefix_ne_zero
      (Finset.mem_filter.mp hm).1
  have heq := signed_eq_two_positive_filtered hR hS hSzero f u
  have hPsub : P ⊆ sourcePositiveDyadicRange (2 ^ k) := by
    intro m hm
    have hmS := (Finset.mem_filter.mp hm).1
    have hmpos := (Finset.mem_filter.mp hm).2
    have hh := (Finset.mem_filter.mp hmS).2
    have hlow := hh.1
    have hhigh := hh.2
    rw [mem_sourcePositiveDyadicRange_iff]
    have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    rw [abs_of_pos hmposR] at hlow hhigh
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hhigh
  have hsub : (R ×ˢ P) ×ˢ R ⊆
      (R ×ˢ sourcePositiveDyadicRange (2 ^ k)) ×ˢ R := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp12, hp3⟩
    rcases Finset.mem_product.mp hp12 with ⟨hp1, hp2⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hp1, hPsub hp2⟩, hp3⟩
  have hmono : sourceFiniteAffineSum R P R f u ≤
      sourceFiniteAffineSum R (sourcePositiveDyadicRange (2 ^ k)) R f u := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun p : Frequency => f (((p.1.1 : ℝ) * u + (p.2 : ℝ)) /
        (p.1.2 : ℝ))) hsub
      (fun p _ _ => hf _)
    simpa [sourceFiniteAffineSum, Finset.sum_product] using hh
  dsimp [R, S, P] at heq hmono ⊢
  calc
    _ = 2 * sourceFiniteAffineSum (blockCoordinateRange Mcut k)
        (blockMiddleRange Mcut k |>.filter (fun m => 0 < m))
        (blockCoordinateRange Mcut k) f u := heq
    _ ≤ 2 * sourceFiniteAffineSum (blockCoordinateRange Mcut k)
        (sourcePositiveDyadicRange (2 ^ k))
        (blockCoordinateRange Mcut k) f u :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)

end GuthMaynardS3MiddleNormalize

#print axioms GuthMaynardS3MiddleNormalize.block_sourceFiniteAffineSum_middle_le_two_positive
