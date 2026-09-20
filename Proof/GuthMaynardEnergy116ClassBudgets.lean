import GuthMaynardEnergy118SecondShell

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy116ClassBudgets
open CGLProofDAG GuthMaynardLemma116 GuthMaynardS3LiteralLemma83Energy

theorem floorDifferenceMultiplicity_le_card
    (W : Finset ℝ) (hsep : OneSeparated W) (u : ℤ) :
    floorDifferenceMultiplicity W u ≤ W.card := by
  let S := (W.product W).filter fun p => floorDifference p = u
  have hinj : Set.InjOn Prod.fst (S : Set (ℝ × ℝ)) := by
    intro p hp q hq heq
    have hp0 := Finset.mem_filter.mp hp
    have hq0 := Finset.mem_filter.mp hq
    have hpW := Finset.mem_product.mp hp0.1
    have hqW := Finset.mem_product.mp hq0.1
    have hfloor : ⌊p.1-p.2⌋ = ⌊q.1-q.2⌋ := hp0.2.trans hq0.2.symm
    have hlt := abs_sub_lt_one_of_floor_eq hfloor
    have hsecond : p.2 = q.2 := by
      by_contra hn
      have hh := hsep p.2 hpW.2 q.2 hqW.2 hn
      have hid : (p.1-p.2)-(q.1-q.2) = -(p.2-q.2) := by
        change p.1 = q.1 at heq
        rw [heq]
        ring
      rw [hid,abs_neg] at hlt
      linarith
    exact Prod.ext heq hsecond
  have hsub : S.image Prod.fst ⊆ W := by
    intro t ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hh
  exact hh

theorem active_exponent_card_le_log_card (W : Finset ℝ) (hsep : OneSeparated W) :
    (activeDyadicExponents (floorDifferenceBins W) (floorDifferenceMultiplicity W)).card ≤
      Nat.log2 W.card+1 :=
  card_activeDyadicExponents_le_log2_add_one _ _ _
    (fun u hu => floorDifferenceMultiplicity_le_card W hsep u)

/-- The strict difference-energy convention in the baseline class algebra is
injected into the literal closed additive-energy convention by swapping the
second and fourth coordinates. -/
theorem approximateDifferenceEnergy_le_source (W : Finset ℝ) :
    approximateDifferenceEnergy W ≤ sourceApproximateAdditiveEnergy W := by
  let f : ((ℝ × ℝ) × (ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ)) :=
    fun p => ((p.1.1,p.2.2),(p.2.1,p.1.2))
  let S := ((W.product W).product (W.product W)).filter fun p =>
    |(p.1.1-p.1.2)-(p.2.1-p.2.2)| < 1
  let A := ((W.product W) ×ˢ (W.product W)).filter fun p =>
    |(p.1.1+p.1.2)-(p.2.1+p.2.2)| ≤ 1
  have hsub : S.image f ⊆ A := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
    have hp0 := Finset.mem_product.mp hp
    have h1 := Finset.mem_product.mp hp0.1
    have h2 := Finset.mem_product.mp hp0.2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h1.1,h2.2⟩,
        Finset.mem_product.mpr ⟨h2.1,h1.2⟩⟩
    · have hid : ((f p).1.1+(f p).1.2)-((f p).2.1+(f p).2.2) =
          (p.1.1-p.1.2)-(p.2.1-p.2.2) := by dsimp [f]; ring
      rw [hid]
      exact hlt.le
  have hinj : Function.Injective f := by
    intro p q he
    have hh := congrArg f he
    simpa only [f] using hh
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S hinj] at hh
  exact hh

/-- Both class budgets with the literal source energy on the right. -/
theorem floorDifference_source_class_budgets (W : Finset ℝ) (B : ℕ) :
    B*(dyadicMultiplicityClass (floorDifferenceBins W)
      (floorDifferenceMultiplicity W) B).card ≤ W.card^2 ∧
    B^2*(dyadicMultiplicityClass (floorDifferenceBins W)
      (floorDifferenceMultiplicity W) B).card ≤ sourceApproximateAdditiveEnergy W := by
  have hh := floorDifference_dyadic_class_source_budgets W B
  exact ⟨hh.1,hh.2.trans (approximateDifferenceEnergy_le_source W)⟩

end GuthMaynardEnergy116ClassBudgets
#print axioms GuthMaynardEnergy116ClassBudgets.floorDifferenceMultiplicity_le_card
#print axioms GuthMaynardEnergy116ClassBudgets.active_exponent_card_le_log_card
#print axioms GuthMaynardEnergy116ClassBudgets.approximateDifferenceEnergy_le_source
#print axioms GuthMaynardEnergy116ClassBudgets.floorDifference_source_class_budgets
