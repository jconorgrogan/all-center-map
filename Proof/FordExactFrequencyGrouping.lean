import Mathlib

open scoped BigOperators

namespace FordExactFrequencyGrouping

noncomputable section

private theorem card_subtype_eq_filter_card
    {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] :
    Fintype.card {x // p x} = (Finset.univ.filter p).card := by
  exact Fintype.card_ofFinset (Finset.univ.filter p) (by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl)

private theorem total_fiber_cauchy
    {X T R : Type*} [Fintype X] [DecidableEq T] [DecidableEq R]
    (total : X → T) (cls : X → R) (C : ℕ) (t : T)
    (hC : (((Finset.univ : Finset X).filter (fun x => total x = t)).image cls).card ≤ C) :
    ((Finset.univ : Finset X).filter (fun x => total x = t)).card ^ 2 ≤
      C * ((((Finset.univ : Finset X).filter (fun x => total x = t)).product
        ((Finset.univ : Finset X).filter (fun x => total x = t))).filter
          (fun p => cls p.1 = cls p.2)).card := by
  classical
  let S : Finset X := (Finset.univ : Finset X).filter (fun x => total x = t)
  let Rset : Finset R := S.image cls
  let Q : Finset (X × X) := (S.product S).filter (fun p => cls p.1 = cls p.2)
  have hS : S = (Finset.univ : Finset X).filter (fun x => total x = t) := rfl
  have hcount :
      (∑ r ∈ Rset, (S.filter (fun x => cls x = r)).card) = S.card := by
    have hfiber := Finset.sum_fiberwise_of_maps_to
      (s := S) (t := Rset)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (fun _ : X => (1 : ℕ))
    calc
      (∑ r ∈ Rset, (S.filter (fun x => cls x = r)).card) =
          ∑ r ∈ Rset, ∑ x ∈ S with cls x = r, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.card_eq_sum_ones _
      _ = ∑ x ∈ S, (1 : ℕ) := hfiber
      _ = S.card := (Finset.card_eq_sum_ones _).symm
  have hqfiber (r : R) (hr : r ∈ Rset) :
      Q.filter (fun p => cls p.1 = r) =
        (S.filter (fun x => cls x = r)).product
          (S.filter (fun x => cls x = r)) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpQ, hpr⟩
      rcases Finset.mem_filter.mp hpQ with ⟨hpProd, heq⟩
      rcases Finset.mem_product.mp hpProd with ⟨hpS, hqS⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hpS, hpr⟩,
          Finset.mem_filter.mpr ⟨hqS, heq ▸ hpr⟩⟩
    · intro hp
      have hpProd := Finset.mem_product.mp hp
      rcases hpProd with ⟨hpS, hqS⟩
      have hpS' := Finset.mem_filter.mp hpS
      have hqS' := Finset.mem_filter.mp hqS
      rcases hpS' with ⟨hpS, hpr⟩
      rcases hqS' with ⟨hqS, hqr⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨hpS, hqS⟩, hpr.trans hqr.symm⟩
      · exact hpr
  have hqcount :
      (∑ r ∈ Rset, (S.filter (fun x => cls x = r)).card ^ 2) = Q.card := by
    have hmapQ : ∀ p ∈ Q, cls p.1 ∈ Rset := by
      intro p hp
      have hpProd := (Finset.mem_filter.mp hp).1
      exact Finset.mem_image.mpr ⟨p.1, (Finset.mem_product.mp hpProd).1, rfl⟩
    have hfiber := Finset.sum_fiberwise_of_maps_to
      (s := Q) (t := Rset) hmapQ (fun _ : X × X => (1 : ℕ))
    calc
      (∑ r ∈ Rset, (S.filter (fun x => cls x = r)).card ^ 2) =
          ∑ r ∈ Rset, (Q.filter (fun p => cls p.1 = r)).card := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hqfiber r hr]
        simp [Finset.card_product, pow_two]
      _ = Q.card := by
        calc
          (∑ r ∈ Rset, (Q.filter (fun p => cls p.1 = r)).card) =
              ∑ r ∈ Rset, ∑ p ∈ Q with cls p.1 = r, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact Finset.card_eq_sum_ones _
          _ = ∑ p ∈ Q, (1 : ℕ) := hfiber
          _ = Q.card := (Finset.card_eq_sum_ones _).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    Rset (fun _ : R => (1 : ℕ))
      (fun r => (S.filter (fun x => cls x = r)).card)
  have hcs' : S.card ^ 2 ≤ Rset.card * Q.card := by
    calc
      S.card ^ 2 =
          (∑ r ∈ Rset, (S.filter (fun x => cls x = r)).card) ^ 2 := by
        rw [hcount]
      _ ≤ (∑ r ∈ Rset, (1 : ℕ) * 1) *
          (∑ r ∈ Rset, (S.filter (fun x => cls x = r)).card ^ 2) := by
        simpa using hcs
      _ = Rset.card * Q.card := by
        rw [hqcount]
        simp
  have hscale := Nat.mul_le_mul_right Q.card hC
  have hmain : S.card ^ 2 ≤ C * Q.card := by
    calc
      S.card ^ 2 ≤ Rset.card * Q.card := hcs'
      _ ≤ C * Q.card := by
        exact hscale
  change S.card ^ 2 ≤ C * Q.card
  exact hmain

theorem collision_card_le_class_collision_card
    {X T R : Type*} [Fintype X] [DecidableEq T] [DecidableEq R]
    (total : X → T) (cls : X → R) (C : ℕ)
    (hC : ∀ t : T,
      (((Finset.univ : Finset X).filter (fun x => total x = t)).image cls).card ≤ C) :
    Fintype.card {p : X × X // total p.1 = total p.2} ≤
      C * Fintype.card {p : X × X //
        total p.1 = total p.2 ∧ cls p.1 = cls p.2} := by
  classical
  let Xs : Finset X := Finset.univ
  let Ts : Finset T := Xs.image total
  let P : Finset (X × X) := (Xs.product Xs).filter
    (fun p => total p.1 = total p.2)
  let Q : Finset (X × X) := (Xs.product Xs).filter
    (fun p => total p.1 = total p.2 ∧ cls p.1 = cls p.2)
  have hmapP : ∀ p ∈ P, total p.1 ∈ Ts := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p.1,
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1, rfl⟩
  have hmapQ : ∀ p ∈ Q, total p.1 ∈ Ts := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p.1,
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1, rfl⟩
  have hP := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := Ts) hmapP (fun _ : X × X => (1 : ℕ))
  have hQ := Finset.sum_fiberwise_of_maps_to
    (s := Q) (t := Ts) hmapQ (fun _ : X × X => (1 : ℕ))
  have hper (t : T) (ht : t ∈ Ts) :
      (P.filter (fun p => total p.1 = t)).card ≤
        C * (Q.filter (fun p => total p.1 = t)).card := by
    have hlocal := total_fiber_cauchy total cls C t (hC t)
    have hPfiber :
        P.filter (fun p => total p.1 = t) =
          (((Finset.univ : Finset X).filter (fun x => total x = t)).product
            ((Finset.univ : Finset X).filter (fun x => total x = t))) := by
      ext p
      simp only [P, Xs, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hpProd, heq⟩, ht1⟩
        have hpProd' := Finset.mem_product.mp hpProd
        rcases hpProd' with ⟨hp, hq⟩
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hp, ht1⟩,
            Finset.mem_filter.mpr ⟨hq, heq ▸ ht1⟩⟩
      · intro hpProd
        have hpProd' := Finset.mem_product.mp hpProd
        rcases hpProd' with ⟨hpPair, hqPair⟩
        have hp' := Finset.mem_filter.mp hpPair
        have hq' := Finset.mem_filter.mp hqPair
        rcases hp' with ⟨hp, ht1⟩
        rcases hq' with ⟨hq, ht2⟩
        exact ⟨⟨Finset.mem_product.mpr
          ⟨hp, hq⟩, ht1.trans ht2.symm⟩, ht1⟩
    have hQfiber :
        Q.filter (fun p => total p.1 = t) =
          (((Finset.univ : Finset X).filter (fun x => total x = t)).product
            ((Finset.univ : Finset X).filter (fun x => total x = t))).filter
              (fun p => cls p.1 = cls p.2) := by
      ext p
      simp only [Q, Xs, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hpProd, ⟨heq, hcls⟩⟩, ht1⟩
        rcases Finset.mem_product.mp hpProd with ⟨hp, hq⟩
        exact ⟨Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨hp, ht1⟩,
              Finset.mem_filter.mpr ⟨hq, heq ▸ ht1⟩⟩, hcls⟩
      · intro hp
        rcases hp with ⟨hpProd, hcls⟩
        have hpProd' := Finset.mem_product.mp hpProd
        rcases hpProd' with ⟨hpPair, hqPair⟩
        have hp' := Finset.mem_filter.mp hpPair
        have hq' := Finset.mem_filter.mp hqPair
        rcases hp' with ⟨hp, ht1⟩
        rcases hq' with ⟨hq, ht2⟩
        exact ⟨⟨Finset.mem_product.mpr
          ⟨hp, hq⟩,
          ⟨ht1.trans ht2.symm, hcls⟩⟩, ht1⟩
    rw [hPfiber, hQfiber]
    simpa [Finset.card_product, pow_two] using hlocal
  have hsum : P.card ≤ C * Q.card := by
    calc
      P.card = ∑ t ∈ Ts, (P.filter (fun p => total p.1 = t)).card := by
        calc
          P.card = ∑ p ∈ P, (1 : ℕ) := Finset.card_eq_sum_ones _
          _ = ∑ t ∈ Ts, ∑ p ∈ P with total p.1 = t, (1 : ℕ) := hP.symm
          _ = ∑ t ∈ Ts, (P.filter (fun p => total p.1 = t)).card := by
            apply Finset.sum_congr rfl
            intro t ht
            exact (Finset.card_eq_sum_ones _).symm
      _ ≤ ∑ t ∈ Ts, C * (Q.filter (fun p => total p.1 = t)).card := by
        apply Finset.sum_le_sum
        intro t ht
        exact hper t ht
      _ = C * Q.card := by
        rw [← Finset.mul_sum]
        congr 1
        calc
          (∑ t ∈ Ts, (Q.filter (fun p => total p.1 = t)).card) =
              ∑ t ∈ Ts, ∑ p ∈ Q with total p.1 = t, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact Finset.card_eq_sum_ones _
          _ = ∑ p ∈ Q, (1 : ℕ) := hQ
          _ = Q.card := (Finset.card_eq_sum_ones _).symm
  have hPcard : Fintype.card {p : X × X // total p.1 = total p.2} = P.card := by
    simpa [P, Xs] using card_subtype_eq_filter_card (fun p : X × X => total p.1 = total p.2)
  have hQcard : Fintype.card {p : X × X //
      total p.1 = total p.2 ∧ cls p.1 = cls p.2} = Q.card := by
    simpa [Q, Xs] using card_subtype_eq_filter_card
      (fun p : X × X => total p.1 = total p.2 ∧ cls p.1 = cls p.2)
  rw [hPcard, hQcard]
  exact hsum

end
end FordExactFrequencyGrouping

#print axioms FordExactFrequencyGrouping.collision_card_le_class_collision_card
