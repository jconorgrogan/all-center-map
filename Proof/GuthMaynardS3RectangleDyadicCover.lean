import GuthMaynardS3BlockRectangle
import GuthMaynardSourceDyadicRanges

open scoped BigOperators
noncomputable section
namespace GuthMaynardS3RectangleDyadicCover
open GuthMaynardJIteration GuthMaynardS3BlockRectangle
open GuthMaynardS3LiteralTruncation

/-- Every outer coordinate has a dyadic scale at most four above the middle
scale. This uses the literal `16*2^k` mask, not the global frequency cutoff. -/
theorem coordinate_mem_some_dyadic {Mcut k : ℕ} {m : ℤ}
    (hm : m ∈ blockCoordinateRange Mcut k) :
    ∃ j ∈ Finset.range (k+5), m ∈ sourceSignedDyadicRange (2^j) := by
  have hmne : m ≠ 0 := nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1
  have hnne : m.natAbs ≠ 0 := by simpa using hmne
  have ht : (16 : ℝ) * (2^k : ℝ) = ((2^(k+4) : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    norm_num
    ring
  have hreal : (m.natAbs : ℝ) ≤ ((2^(k+4) : ℕ) : ℝ) := by
    rw [← ht]
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Finset.mem_filter.mp hm).2
  have hnat : m.natAbs ≤ 2^(k+4) := by exact_mod_cast hreal
  let j := m.natAbs.log2
  have hlo : 2^j ≤ m.natAbs := Nat.log2_self_le hnne
  have hhi : m.natAbs ≤ 2*2^j := by
    have hh := Nat.lt_log2_self (n:=m.natAbs)
    simpa only [j, pow_succ, mul_comm] using hh.le
  have hj : j ≤ k+4 := by
    have hp : 2^j ≤ 2^(k+4) := hlo.trans hnat
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hp
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
  have hloI : ((2^j : ℕ) : ℤ) ≤ |m| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hlo
  have hhiI : |m| ≤ (2 : ℤ) * ((2^j : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hhi
  rw [mem_sourceSignedDyadicRange_iff]
  by_cases hm0 : 0 ≤ m
  · rw [abs_of_nonneg hm0] at hloI hhiI
    exact Or.inr ⟨hloI,hhiI⟩
  · have hm0' : m ≤ 0 := le_of_not_ge hm0
    rw [abs_of_nonpos hm0'] at hloI hhiI
    exact Or.inl ⟨by linarith,by linarith⟩

/-- Positive summands may be covered by these dyadic shells, allowing their
boundary overlaps. No extra factor is paid at this linear-sum step. -/
theorem coordinate_sum_le_dyadic (H : ℤ → ℝ) (hH : ∀ m, 0 ≤ H m)
    (Mcut k : ℕ) :
    (∑ m ∈ blockCoordinateRange Mcut k, H m) ≤
      ∑ j ∈ Finset.range (k+5), ∑ m ∈ sourceSignedDyadicRange (2^j), H m := by
  let Q : Finset (Sigma (fun _ : ℕ => ℤ)) :=
    (Finset.range (k+5)).sigma (fun j => sourceSignedDyadicRange (2^j))
  have hsub : blockCoordinateRange Mcut k ⊆ Q.image (fun p => p.2) := by
    intro m hm
    obtain ⟨j,hj,hmj⟩ := coordinate_mem_some_dyadic hm
    apply Finset.mem_image.mpr
    refine ⟨⟨j,m⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨hj,hmj⟩
  have hfirst := Finset.sum_le_sum_of_subset_of_nonneg (f:=H) hsub
    (fun m _ _ => hH m)
  have hsecond := Finset.sum_image_le_of_nonneg
    (s:=Q) (g:=fun p => p.2) (f:=H) (fun m _ => hH m)
  have hh := hfirst.trans hsecond
  simpa only [Q, Finset.sum_sigma] using hh

/-- The actual positive-middle rectangle is bounded by the dyadic first
coordinate family with the original third-coordinate mask. -/
theorem rectangle_positive_sum_le_dyadic
    (f : ℝ → ℝ) (hf0 : ∀ u, 0 ≤ f u) (Mcut k : ℕ) (u : ℝ) :
    sourceFiniteAffineSum (blockCoordinateRange Mcut k)
      (sourcePositiveDyadicRange (2^k)) (blockCoordinateRange Mcut k) f u ≤
      ∑ j ∈ Finset.range (k+5),
        sourceFiniteAffineSum (sourceSignedDyadicRange (2^j))
          (sourcePositiveDyadicRange (2^k)) (blockCoordinateRange Mcut k) f u := by
  apply coordinate_sum_le_dyadic
  intro m
  apply Finset.sum_nonneg
  intro m2 hm2
  apply Finset.sum_nonneg
  intro m3 hm3
  exact hf0 _

end GuthMaynardS3RectangleDyadicCover
#print axioms GuthMaynardS3RectangleDyadicCover.coordinate_mem_some_dyadic
#print axioms GuthMaynardS3RectangleDyadicCover.rectangle_positive_sum_le_dyadic
