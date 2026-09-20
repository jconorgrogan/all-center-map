import Mathlib

open scoped BigOperators

namespace FordDifferenceDominance

noncomputable section

/-- The size of a finite fiber of `f`; no finiteness assumption is imposed on
 the ambient additive group. -/
def fiberCount {X G : Type*} [Fintype X] [DecidableEq G]
    (f : X → G) (g : G) : ℕ :=
  (Finset.univ.filter fun x => f x = g).card

def support {X G : Type*} [Fintype X] [DecidableEq G]
    (f : X → G) : Finset G := Finset.univ.image f

/-- Literal ordered-pair representation count at a difference `d`. -/
def differencePairCount {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (d : G) : ℕ :=
  ∑ x : X, (Finset.univ.filter fun y => f x - f y = d).card

/-- The same representation count grouped by the value of `f x`. -/
def differenceCount {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (d : G) : ℕ :=
  ∑ g ∈ support f, fiberCount f g * fiberCount f (g - d)

lemma differencePairCount_eq_differenceCount
    {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (d : G) :
    differencePairCount f d = differenceCount f d := by
  classical
  unfold differencePairCount differenceCount support fiberCount
  have hfilter (x : X) :
      (Finset.univ.filter fun y => f x - f y = d) =
        (Finset.univ.filter fun y => f y = f x - d) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      apply (eq_sub_iff_add_eq).2
      have hh := (sub_eq_iff_eq_add).1 h
      simpa [add_comm] using hh.symm
    · intro h
      have hh := (eq_sub_iff_add_eq).1 h
      apply (sub_eq_iff_eq_add).2
      simpa [add_comm] using hh.symm
  simp_rw [hfilter]
  rw [← Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset X)) (t := (Finset.univ.image f)) (g := f)
      (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)]
  apply Finset.sum_congr rfl
  intro g hg
  have hconst : ∀ i ∈ (Finset.univ.filter (fun i : X => f i = g)),
      (Finset.univ.filter fun y => f y = f i - d).card =
        (Finset.univ.filter fun y => f y = g - d).card := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hi]
  rw [Finset.sum_eq_card_nsmul hconst]
  simp [nsmul_eq_mul]

lemma differenceCount_zero
    {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) :
    differenceCount f 0 = ∑ g ∈ support f, fiberCount f g ^ 2 := by
  unfold differenceCount
  simp [sub_zero, pow_two]

private lemma support_sum_extra_zero
    {X G : Type*} [Fintype X] [DecidableEq G]
    (f : X → G) (T : Finset G) (hT : support f ⊆ T) :
    (∑ g ∈ T, fiberCount f g ^ 2) =
      ∑ g ∈ support f, fiberCount f g ^ 2 := by
  apply le_antisymm
  · have heq : (∑ g ∈ support f, fiberCount f g ^ 2) =
        ∑ g ∈ T, fiberCount f g ^ 2 := Finset.sum_subset hT (by
      intro g hgT hgS
      have hz : fiberCount f g = 0 := by
        unfold fiberCount
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro x hx
        intro hfx
        exact hgS (Finset.mem_image.mpr ⟨x, hx, hfx⟩)
      simp [hz])
    exact le_of_eq heq.symm
  · exact Finset.sum_le_sum_of_subset_of_nonneg hT
      (fun _ _ _ => Nat.zero_le _)

/-- Every difference representation count is bounded by the zero moment, for
an arbitrary additive commutative group `G`, even when `G` is infinite. -/
theorem differenceCount_le_zeroMoment
    {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (d : G) :
    differenceCount f d ≤ differenceCount f 0 := by
  classical
  rw [differenceCount_zero]
  unfold differenceCount
  let S : Finset G := support f
  let T : Finset G := S ∪ S.image (fun g => g - d)
  have hterm : ∀ g ∈ S,
      2 * (fiberCount f g * fiberCount f (g - d)) ≤
        fiberCount f g ^ 2 + fiberCount f (g - d) ^ 2 := by
    intro g hg
    simpa [mul_assoc] using
      (two_mul_le_add_sq (R := ℕ) (fiberCount f g) (fiberCount f (g - d)))
  have hsum := Finset.sum_le_sum (s := S) (fun g hg => hterm g hg)
  have himage :
      (∑ g ∈ S.image (fun g => g - d), fiberCount f g ^ 2) =
        ∑ g ∈ S, fiberCount f (g - d) ^ 2 := by
    rw [Finset.sum_image (fun a ha b hb hab => sub_left_injective hab)]
  have hT : S ⊆ T := by intro g hg; exact Finset.mem_union_left _ hg
  have hsumT : (∑ g ∈ T, fiberCount f g ^ 2) =
      ∑ g ∈ S, fiberCount f g ^ 2 := by
    apply support_sum_extra_zero f T
    simpa [S] using hT
  have hshift : (∑ g ∈ S, fiberCount f (g - d) ^ 2) ≤
      ∑ g ∈ S, fiberCount f g ^ 2 := by
    calc
      _ = ∑ g ∈ S.image (fun g => g - d), fiberCount f g ^ 2 := himage.symm
      _ ≤ ∑ g ∈ T, fiberCount f g ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr
          (fun g hg => Finset.mem_union_right S (Finset.mem_image.mpr ⟨g, hg, rfl⟩)))
          (fun _ _ _ => Nat.zero_le _)
      _ = _ := hsumT
  have hdouble :
      2 * (∑ g ∈ S, fiberCount f g * fiberCount f (g - d)) ≤
        2 * (∑ g ∈ S, fiberCount f g ^ 2) := by
    have hsum' := Finset.sum_le_sum (s := S) (fun g hg => hterm g hg)
    have hsum'' :
        2 * (∑ g ∈ S, fiberCount f g * fiberCount f (g - d)) ≤
          (∑ g ∈ S, fiberCount f g ^ 2) +
            (∑ g ∈ S, fiberCount f (g - d) ^ 2) := by
      simpa [Finset.sum_add_distrib, Finset.mul_sum] using hsum'
    omega
  exact Nat.le_of_mul_le_mul_left hdouble (by omega)

/-- Literal ordered-pair version of the zero-moment dominance. -/
theorem differencePairCount_le_zeroMoment
    {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (d : G) :
    differencePairCount f d ≤ differencePairCount f 0 := by
  rw [differencePairCount_eq_differenceCount,
    differencePairCount_eq_differenceCount]
  exact differenceCount_le_zeroMoment f d

#print axioms FordDifferenceDominance.differencePairCount_le_zeroMoment
#print axioms FordDifferenceDominance.differenceCount_le_zeroMoment

end
end FordDifferenceDominance
