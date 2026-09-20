import FordDifferenceDominance

open scoped BigOperators

namespace FordDifferenceWeighted

open FordDifferenceDominance

noncomputable section

def differencePairCard {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (d : G) : ℕ :=
  (Finset.univ.filter fun p : X × X => f p.1 - f p.2 = d).card

lemma differencePairCount_eq_card
    {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (d : G) :
    differencePairCount f d = differencePairCard f d := by
  classical
  unfold differencePairCount differencePairCard
  let P : Finset (X × X) := Finset.univ.filter
    (fun p : X × X => f p.1 - f p.2 = d)
  have hmaps : ∀ p ∈ P, p.1 ∈ (Finset.univ : Finset X) :=
    by intro p hp; exact Finset.mem_univ _
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := P) (t := (Finset.univ : Finset X))
    (f := fun p : X × X => p.1) (fun p hp => Finset.mem_univ _)
  have hcardfiber : ∀ x : X,
      (P.filter fun p : X × X => p.1 = x).card =
        (Finset.univ.filter fun y : X => f x - f y = d).card := by
    intro x
    apply Finset.card_bij (fun p hp => p.2)
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [P, hp'.2] using hp'.1⟩
    · intro p hp p' hp' heq
      rcases p with ⟨xp, yp⟩
      rcases p' with ⟨xp', yp'⟩
      have hxp : xp = x := (Finset.mem_filter.mp hp).2
      have hxp' : xp' = x := (Finset.mem_filter.mp hp').2
      exact Prod.ext (hxp.trans hxp'.symm) heq
    · intro y hy
      refine ⟨(x, y), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      change (x, y) ∈ (Finset.univ.product Finset.univ).filter
        (fun p : X × X => f p.1 - f p.2 = d)
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hy⟩
  calc
    ∑ x : X, (Finset.univ.filter fun y => f x - f y = d).card =
        ∑ x : X, (P.filter fun p : X × X => p.1 = x).card := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (hcardfiber x).symm
    _ = P.card := hfib.symm

private lemma weighted_grouping_identity
    {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (S : Finset G)
    (hS : ∀ x y : X, f x - f y ∈ S) (F : G → ℝ) :
    (∑ x : X, ∑ y : X, F (f x - f y)) =
      ∑ d ∈ S, (differencePairCount f d : ℝ) * F d := by
  classical
  let P : Finset (X × X) := Finset.univ.product Finset.univ
  let q : X × X → G := fun p => f p.1 - f p.2
  have hmaps : ∀ p ∈ P, q p ∈ S := by
    intro p hp
    exact hS p.1 p.2
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := S) (g := q) hmaps (fun p : X × X => F (q p))
  have hconst : ∀ d ∈ S,
      ∀ p ∈ P.filter (fun p => q p = d), F (q p) = F d := by
    intro d hd p hp
    have hp' := Finset.mem_filter.mp hp
    exact congrArg F hp'.2
  have hleft :
      (∑ d ∈ S, ∑ p ∈ P with q p = d, F (q p)) =
        ∑ d ∈ S, (P.filter (fun p => q p = d)).card • F d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_eq_card_nsmul]
    intro p hp
    exact hconst d hd p hp
  have hsumP :
      (∑ x : X, ∑ y : X, F (f x - f y)) =
        ∑ p ∈ P, F (q p) := by
    simpa [P, q] using
      (Finset.sum_product (Finset.univ : Finset X) (Finset.univ : Finset X)
        (fun p : X × X => F (f p.1 - f p.2))).symm
  calc
    (∑ x : X, ∑ y : X, F (f x - f y)) = ∑ p ∈ P, F (q p) := hsumP
    _ = ∑ d ∈ S, ∑ p ∈ P with q p = d, F (q p) := hfiber.symm
    _ = ∑ d ∈ S, (P.filter (fun p => q p = d)).card • F d := hleft
    _ = ∑ d ∈ S, (differencePairCount f d : ℝ) * F d := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [nsmul_eq_mul]
      congr 1
      exact_mod_cast (differencePairCount_eq_card f d).symm
      

/-- Weighted finite difference grouping with nonnegative weights. The literal
zero-moment dominance is supplied by the proved finite-support theorem. -/
theorem weighted_difference_le_zeroMoment
    {X G : Type*} [Fintype X] [DecidableEq G]
    [AddCommGroup G] (f : X → G) (S : Finset G)
    (hS : ∀ x y : X, f x - f y ∈ S)
    (F : G → ℝ) (hF : ∀ d ∈ S, 0 ≤ F d) :
    (∑ x : X, ∑ y : X, F (f x - f y)) ≤
      (differencePairCount f 0 : ℝ) * ∑ d ∈ S, F d := by
  have hdom := FordDifferenceDominance.differencePairCount_le_zeroMoment f
  have hgroup := weighted_grouping_identity f S hS F
  rw [hgroup]
  have hterm : ∀ d ∈ S,
      (differencePairCount f d : ℝ) * F d ≤
        (differencePairCount f 0 : ℝ) * F d := by
    intro d hd
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdom d) (hF d hd)
  calc
    ∑ d ∈ S, (differencePairCount f d : ℝ) * F d ≤
        ∑ d ∈ S, (differencePairCount f 0 : ℝ) * F d :=
      Finset.sum_le_sum (fun d hd => hterm d hd)
    _ = (differencePairCount f 0 : ℝ) * ∑ d ∈ S, F d := by
      rw [Finset.mul_sum]

#print axioms FordDifferenceWeighted.differencePairCount_eq_card
#print axioms FordDifferenceWeighted.weighted_difference_le_zeroMoment

end
end FordDifferenceWeighted
