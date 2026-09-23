import GuthMaynardLemma116ClassAlgebra
import GuthMaynardS3LiteralLemma83Energy

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy118ShellCount
open GuthMaynardLemma116 GuthMaynardS3LiteralLemma83Energy

private def fibre {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (j : β) : ℕ := (S.filter fun x => f x = j).card

private theorem cross_fibre_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f g : α → β) (U : Finset β)
    (hf : ∀ x ∈ S, f x ∈ U) :
    ((S.product S).filter fun p => f p.1 = g p.2).card =
      ∑ j ∈ U, fibre S f j * fibre S g j := by
  have hpart := Finset.sum_fiberwise_of_maps_to' hf (fibre S g)
  have hsum : (∑ j ∈ U, fibre S f j * fibre S g j) =
      ∑ x ∈ S, fibre S g (f x) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, fibre] using! hpart
  rw [hsum]
  simp only [fibre, Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [eq_comm]

private theorem fibre_sq_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (U : Finset β)
    (hf : S.image f ⊆ U) :
    (∑ j ∈ U, (fibre S f j)^2) =
      ((S.product S).filter fun p => f p.1 = f p.2).card := by
  rw [← sum_image_fiber_card_sq_eq_equalPair_card S f]
  symm
  apply Finset.sum_subset hf
  intro j hj hnot
  have hempty : S.filter (fun x => f x = j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hnot (Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩)
  simp [fibre,hempty]

/-- Cauchy for collisions of two finite maps, with exact multiplicity. -/
theorem two_cross_collisions_le_energies
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f g : α → β) :
    2*((S.product S).filter fun p => f p.1 = g p.2).card ≤
      ((S.product S).filter fun p => f p.1 = f p.2).card +
      ((S.product S).filter fun p => g p.1 = g p.2).card := by
  let U := S.image f ∪ S.image g
  have hf : S.image f ⊆ U := Finset.subset_union_left
  have hg : S.image g ⊆ U := Finset.subset_union_right
  rw [cross_fibre_sum S f g U (fun x hx => hf (Finset.mem_image.mpr ⟨x,hx,rfl⟩)),
    ← fibre_sq_sum S f U hf, ← fibre_sq_sum S g U hg,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  nlinarith [sq_nonneg ((fibre S f j : ℤ)-(fibre S g j : ℤ))]

/-- Every integer shift of a finite bin autocorrelation is bounded by its
zero-shift energy. This does not discard the multiplicities in each bin. -/
theorem shifted_floor_collisions_le_diagonal
    {α : Type*} [DecidableEq α] (S : Finset α) (x : α → ℝ) (m : ℤ) :
    ((S.product S).filter fun p => ⌊x p.1⌋ - ⌊x p.2⌋ = m).card ≤
      ((S.product S).filter fun p => ⌊x p.1⌋ = ⌊x p.2⌋).card := by
  have hh := two_cross_collisions_le_energies S (fun a => ⌊x a⌋) (fun a => ⌊x a⌋+m)
  have hcross : ((S.product S).filter fun p => ⌊x p.1⌋ = ⌊x p.2⌋+m) =
      ((S.product S).filter fun p => ⌊x p.1⌋-⌊x p.2⌋ = m) := by
    apply Finset.filter_congr
    intro p hp
    exact (sub_eq_iff_eq_add').symm
  have heqg : ((S.product S).filter fun p => ⌊x p.1⌋+m = ⌊x p.2⌋+m) =
      ((S.product S).filter fun p => ⌊x p.1⌋ = ⌊x p.2⌋) := by
    ext p
    simp only [Finset.mem_filter,add_left_inj]
  rw [hcross,heqg] at hh
  omega

private theorem shell_floor_alternatives (a b : ℝ) (m : ℤ)
    (hlo : (m : ℝ) ≤ a-b) (hhi : a-b < (m : ℝ)+1) :
    ⌊a⌋-⌊b⌋ = m ∨ ⌊a⌋-⌊b⌋ = m+1 := by
  have ha0 := Int.floor_le a
  have ha1 := Int.lt_floor_add_one a
  have hb0 := Int.floor_le b
  have hb1 := Int.lt_floor_add_one b
  have hlo' : m ≤ ⌊a⌋-⌊b⌋ := by
    by_contra hn
    have hh : ⌊a⌋-⌊b⌋ ≤ m-1 := by omega
    have hr : (⌊a⌋ : ℝ)-(⌊b⌋ : ℝ) ≤ (m : ℝ)-1 := by exact_mod_cast hh
    linarith
  have hhi' : ⌊a⌋-⌊b⌋ ≤ m+1 := by
    by_contra hn
    have hh : m+2 ≤ ⌊a⌋-⌊b⌋ := by omega
    have hr : (m : ℝ)+2 ≤ (⌊a⌋ : ℝ)-(⌊b⌋ : ℝ) := by exact_mod_cast hh
    linarith
  omega

/-- A half-open unit shell of an arbitrary finite difference multiset has at
most twice the zero-bin collision count. -/
theorem shell_card_le_two_floor_energy
    {α : Type*} [DecidableEq α] (S : Finset α) (x : α → ℝ) (m : ℤ) :
    ((S.product S).filter fun p => (m : ℝ) ≤ x p.1-x p.2 ∧
      x p.1-x p.2 < (m : ℝ)+1).card ≤
      2*((S.product S).filter fun p => ⌊x p.1⌋ = ⌊x p.2⌋).card := by
  let A := (S.product S).filter fun p => ⌊x p.1⌋-⌊x p.2⌋ = m
  let B := (S.product S).filter fun p => ⌊x p.1⌋-⌊x p.2⌋ = m+1
  have hsub : ((S.product S).filter fun p => (m : ℝ) ≤ x p.1-x p.2 ∧
      x p.1-x p.2 < (m : ℝ)+1) ⊆ A ∪ B := by
    intro p hp
    obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
    rcases shell_floor_alternatives (x p.1) (x p.2) m hlo hhi with h | h
    · exact Finset.mem_union_left B (Finset.mem_filter.mpr ⟨hp,h⟩)
    · exact Finset.mem_union_right A (Finset.mem_filter.mpr ⟨hp,h⟩)
  calc
    _ ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card+B.card := Finset.card_union_le _ _
    _ ≤ _ := by
      have ha := shifted_floor_collisions_le_diagonal S x m
      have hb := shifted_floor_collisions_le_diagonal S x (m+1)
      change A.card ≤ _ at ha
      change B.card ≤ _ at hb
      have h := Nat.add_le_add ha hb
      simpa only [two_mul] using h

/-- Literal additive-energy shell bound, valid without any separation of W. -/
theorem additive_shell_card_le_two_energy (W : Finset ℝ) (m : ℤ) :
    (((W.product W).product (W.product W)).filter fun p =>
      (m : ℝ) ≤ additivePhase p ∧ additivePhase p < (m : ℝ)+1).card ≤
        2*sourceApproximateAdditiveEnergy W := by
  have hh := shell_card_le_two_floor_energy (W.product W) (fun p => p.1+p.2) m
  have hdiag : (((W.product W).product (W.product W)).filter fun p =>
      ⌊p.1.1+p.1.2⌋ = ⌊p.2.1+p.2.2⌋).card ≤ sourceApproximateAdditiveEnergy W := by
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hp,?_⟩
    exact (abs_sub_lt_one_of_floor_eq he).le
  exact hh.trans (Nat.mul_le_mul_left 2 hdiag)

end GuthMaynardEnergy118ShellCount
#print axioms GuthMaynardEnergy118ShellCount.two_cross_collisions_le_energies
#print axioms GuthMaynardEnergy118ShellCount.shifted_floor_collisions_le_diagonal
#print axioms GuthMaynardEnergy118ShellCount.shell_card_le_two_floor_energy
#print axioms GuthMaynardEnergy118ShellCount.additive_shell_card_le_two_energy
