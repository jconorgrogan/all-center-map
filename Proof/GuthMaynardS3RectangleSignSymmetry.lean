import GuthMaynardS3BlockRectangle

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3RectangleSignSymmetry

open GuthMaynardJIteration
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralTruncation
open GuthMaynardS3LiteralBalancedGeometry
open GuthMaynardS3WideProfile
open GuthMaynardS3BlockRectangle

/-- One direction of signed-prefix negation invariance. -/
private theorem nonzeroPrefix_neg_mem_forward {M : ℕ} {m : ℤ}
    (hm : m ∈ nonzeroPrefix M) : -m ∈ nonzeroPrefix M := by
  unfold nonzeroPrefix at hm ⊢
  rcases Finset.mem_union.mp hm with h | h
  · rcases Finset.mem_image.mp h with ⟨n, hn, rfl⟩
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨n, hn, by simp⟩
  · rcases Finset.mem_image.mp h with ⟨n, hn, rfl⟩
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    exact ⟨n, hn, by simp⟩

/-- The signed nonzero prefix is invariant under negation. -/
theorem nonzeroPrefix_neg_mem {M : ℕ} {m : ℤ} :
    m ∈ nonzeroPrefix M ↔ -m ∈ nonzeroPrefix M := by
  constructor
  · exact nonzeroPrefix_neg_mem_forward
  · intro hm
    simpa only [neg_neg] using
      (nonzeroPrefix_neg_mem_forward (M := M) (m := -m) hm)

/-- Reindexing a finite signed prefix by negation. -/
theorem sum_neg_nonzeroPrefix
    {M : ℕ} (F : ℤ → ℝ) :
    (∑ m ∈ nonzeroPrefix M, F (-m)) = ∑ m ∈ nonzeroPrefix M, F m := by
  apply Finset.sum_bij (fun m _ => -m)
  · intro m hm
    exact (nonzeroPrefix_neg_mem).mp hm
  · intro a ha b hb hab
    exact neg_injective hab
  · intro b hb
    refine ⟨-b, ?_, ?_⟩
    · exact (nonzeroPrefix_neg_mem).mp hb
    · simp
  · intro m hm
    simp

private theorem range_neg_mem {R : Finset ℤ}
    (hR : ∀ m, m ∈ R ↔ -m ∈ R) (m : ℤ) :
    m ∈ R ↔ -m ∈ R := hR m

/-- The right rectangle can use the original wide profile: negating both outer
signed coordinates absorbs the minus sign in `affineCenter`. -/
theorem rectangleAffineSquareSumRight_eq_sourceFiniteAffineSum_wide
    (B : ℝ) (W : Finset ℝ) (Mcut k : ℕ) (v : ℝ) :
    rectangleAffineSquareSumRight B W Mcut k v =
      sourceFiniteAffineSum (blockCoordinateRange Mcut k)
        (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k)
        (wideProfile B W) v := by
  have hR : ∀ m, m ∈ blockCoordinateRange Mcut k ↔
      -m ∈ blockCoordinateRange Mcut k := by
    intro m
    unfold blockCoordinateRange
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hm, hb⟩
      exact ⟨(nonzeroPrefix_neg_mem).mp hm, by simpa using hb⟩
    · rintro ⟨hm, hb⟩
      have hnm : m ∈ nonzeroPrefix Mcut := by
        simpa only [neg_neg] using (nonzeroPrefix_neg_mem (M := Mcut) (m := -m)).mp hm
      exact ⟨hnm, by simpa using hb⟩
  unfold rectangleAffineSquareSumRight sourceFiniteAffineSum affineCenter
  let R := blockCoordinateRange Mcut k
  let M := blockMiddleRange Mcut k
  let Q := (R ×ˢ M) ×ˢ R
  have hsum :
      (∑ p ∈ Q, wideProfile B W
        (-((p.1.1 : ℝ) * v + (p.2 : ℝ)) / (p.1.2 : ℝ))) =
      ∑ p ∈ Q, wideProfile B W
        (((p.1.1 : ℝ) * v + (p.2 : ℝ)) / (p.1.2 : ℝ)) := by
    apply Finset.sum_bij (fun p _ => ((-p.1.1, p.1.2), -p.2))
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp12, hp3⟩
      rcases Finset.mem_product.mp hp12 with ⟨hp1, hp2⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨(hR p.1.1).mp hp1, hp2⟩, (hR p.2).mp hp3⟩
    · intro p hp q hq heq
      rcases p with ⟨⟨p1,p2⟩,p3⟩
      rcases q with ⟨⟨q1,q2⟩,q3⟩
      have hh : ((-p1, p2), -p3) = ((-q1, q2), -q3) := heq
      have h12 : p2 = q2 := congrArg (fun z => z.1.2) hh
      have h1 : p1 = q1 := by
        apply neg_injective
        exact congrArg (fun z => z.1.1) hh
      have h3 : p3 = q3 := by
        apply neg_injective
        exact congrArg (fun z => z.2) hh
      exact Prod.ext (Prod.ext h1 h12) h3
    · intro p hp
      rcases p with ⟨⟨p1,p2⟩,p3⟩
      refine ⟨((-p1,p2),-p3), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(hR p1).mp (Finset.mem_product.mp (Finset.mem_product.mp hp).1).1,
            (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2⟩,
          (hR p3).mp (Finset.mem_product.mp hp).2⟩
      · simp
    · intro p hp
      rcases p with ⟨⟨p1,p2⟩,p3⟩
      congr 1
      push_cast
      ring
  simpa [Q, R, M, Finset.sum_product] using hsum

end GuthMaynardS3RectangleSignSymmetry

#print axioms GuthMaynardS3RectangleSignSymmetry.rectangleAffineSquareSumRight_eq_sourceFiniteAffineSum_wide
