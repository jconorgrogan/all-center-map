import GuthMaynardEnergy114CollarReduction

open scoped BigOperators Real
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy114CollarReduction

noncomputable section
set_option maxHeartbeats 1200000
namespace GuthMaynardEnergyGeometry

/-- Every ordered pair contributes the diagonal quadruple `(a,b,a,b)`. -/
theorem sourceApproximateAdditiveEnergy_ge_card_sq (W : Finset ℝ) :
    (W.card : ℝ) ^ 2 ≤ sourceApproximateAdditiveEnergy W := by
  classical
  let S : Finset (ℝ × ℝ) := W.product W
  let f : (ℝ × ℝ) → ((ℝ × ℝ) × (ℝ × ℝ)) := fun p => (p, p)
  let Q : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (S.product S).filter fun pq =>
      |(pq.1.1 + pq.1.2) - (pq.2.1 + pq.2.2)| ≤ 1
  have hf : Function.Injective f := by
    intro p q hpq
    change (p, p) = (q, q) at hpq
    exact congrArg Prod.fst hpq
  have himage : S.image f ⊆ Q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    dsimp [f]
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨hp, hp⟩
    · norm_num
  have hcard : S.card ≤ Q.card := by
    calc
      S.card = (S.image f).card := by
        symm
        exact Finset.card_image_of_injective S hf
      _ ≤ Q.card := Finset.card_le_card himage
  have hcard' : (S.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
  have hS : (S.card : ℝ) = (W.card : ℝ)^2 := by
    simp [S, Finset.card_product]
    ring
  have hQ : (Q.card : ℝ) = sourceApproximateAdditiveEnergy W := by
    rfl
  rw [hS, hQ] at hcard'
  exact hcard'

/-- Under one-separation, each unit additive collar has at most three points. -/
theorem sourceApproximateAdditiveEnergy_le_three_card_cube
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y|) :
    (sourceApproximateAdditiveEnergy W : ℝ) ≤ 3 * (W.card : ℝ)^3 := by
  rw [energy_eq_sum_collar]
  calc
    ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        ((W.filter fun d => |a + b - c - d| ≤ 1).card : ℝ) ≤
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (3 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        apply Finset.sum_le_sum
        intro c hc
        exact unit_collar_card_le_three W hsep (a + b - c)
    _ = 3 * (W.card : ℝ)^3 := by
      simp
      ring

/-- At spacing three, every closed unit collar contains at most one point. -/
theorem sourceApproximateAdditiveEnergy_le_card_cube_of_three_separated
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 3 ≤ |x-y|) :
    (sourceApproximateAdditiveEnergy W : ℝ) ≤ (W.card : ℝ)^3 := by
  have hcollar : ∀ z : ℝ,
      ((W.filter fun t => |z-t| ≤ 1).card : ℝ) ≤ 1 := by
    intro z
    have hnat : (W.filter fun t => |z-t| ≤ 1).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      by_contra hxy
      have hxy3 := hsep x hx'.1 y hy'.1 hxy
      have hxy2 : |x-y| ≤ 2 := by
        have hzx := abs_le.mp hx'.2
        have hzy := abs_le.mp hy'.2
        rw [abs_le]
        constructor <;> nlinarith [hzx.1, hzx.2, hzy.1, hzy.2]
      linarith
    exact_mod_cast hnat
  rw [energy_eq_sum_collar]
  calc
    ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        ((W.filter fun d => |a + b - c - d| ≤ 1).card : ℝ) ≤
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        apply Finset.sum_le_sum
        intro c hc
        exact hcollar (a + b - c)
    _ = (W.card : ℝ)^3 := by
      simp
      ring

end GuthMaynardEnergyGeometry

#print axioms GuthMaynardEnergyGeometry.sourceApproximateAdditiveEnergy_ge_card_sq
#print axioms GuthMaynardEnergyGeometry.sourceApproximateAdditiveEnergy_le_three_card_cube
#print axioms GuthMaynardEnergyGeometry.sourceApproximateAdditiveEnergy_le_card_cube_of_three_separated
