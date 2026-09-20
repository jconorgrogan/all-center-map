import APTailToRemainderTransfer

/-!
# Height monotonicity available to the corrected AP contour route

Weighted zero mass is monotone in the divisor height.  The complex zero-field
energy is not asserted monotone: enlarging a complex sum can create
cancellation.  Its corrected consumer must instead apply the equation-(2.8)
pair bound directly at the selected common height, with the outer mass taken
at `H+1`.
-/

namespace MAPAPHeightMonotonicity

open Set
open scoped BigOperators ENNReal
open MAPFixedScaleAPZeroRoute APExplicitFormulaMajorantAdapter

noncomputable section

theorem primitiveWeightedZeroMass_mono_height
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X T T' : ℝ} (hX : 0 ≤ X) (hT : T ≤ T') :
    primitiveWeightedZeroMass chi X T ≤
      primitiveWeightedZeroMass chi X T' := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hsubset :
      DirichletZeros.zeroSupport chi.primitiveCharacter 0 T ⊆
        DirichletZeros.zeroSupport chi.primitiveCharacter 0 T' :=
    MAPMellinDetectorLeaf.zeroSupport_mono chi.primitiveCharacter le_rfl hT
  have hrewrite : primitiveWeightedZeroMass chi X T =
      ∑ rho ∈ DirichletZeros.zeroSupport chi.primitiveCharacter 0 T,
        (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T' rho : ℝ) *
          Real.rpow X (2 * (rho.re - 1)) := by
    unfold primitiveWeightedZeroMass
    apply Finset.sum_congr rfl
    intro rho hrho
    congr 2
    exact_mod_cast
      MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
        chi.primitiveCharacter
        ((DirichletZeros.zeroDivisor chi.primitiveCharacter 0 T).supportWithinDomain
          ((DirichletZeros.zeroSupport_mem_iff
            chi.primitiveCharacter 0 T rho).mp hrho))
        ((DirichletZeros.zeroDivisor chi.primitiveCharacter 0 T').supportWithinDomain
          ((DirichletZeros.zeroSupport_mem_iff
            chi.primitiveCharacter 0 T' rho).mp (hsubset hrho)))
  rw [hrewrite]
  unfold primitiveWeightedZeroMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun rho hrho hrho' => mul_nonneg (Nat.cast_nonneg _)
      (Real.rpow_nonneg hX _))

theorem weightedZeroMassAtLevel_mono_height
    (q : ℕ) {X T T' : ℝ} (hX : 0 ≤ X) (hT : T ≤ T') :
    weightedZeroMassAtLevel q X T ≤ weightedZeroMassAtLevel q X T' := by
  by_cases hq : q = 0
  · simp [weightedZeroMassAtLevel, hq]
  · letI : NeZero q := ⟨hq⟩
    simp only [weightedZeroMassAtLevel, hq, dite_false]
    apply Finset.sum_le_sum
    intro chi hchi
    exact primitiveWeightedZeroMass_mono_height chi hX hT

theorem apWeightedZeroMass_mono_height
    (Q : ℕ) {X T T' : ℝ} (hX : 0 ≤ X) (hT : T ≤ T') :
    apWeightedZeroMass Q X T ≤ apWeightedZeroMass Q X T' := by
  unfold apWeightedZeroMass
  apply Finset.sum_le_sum
  intro q hq
  exact weightedZeroMassAtLevel_mono_height q hX hT

/-- The exact monotone domination supplied by a selected common height
`T ∈ (H,H+1)`. -/
theorem apWeightedZeroMass_selectedHeight_le_add_one
    (Q : ℕ) {X H T : ℝ} (hX : 0 ≤ X) (hT : T ∈ Set.Ioo H (H + 1)) :
    apWeightedZeroMass Q X T ≤ apWeightedZeroMass Q X (H + 1) :=
  apWeightedZeroMass_mono_height Q hX hT.2.le

end
end MAPAPHeightMonotonicity

#print axioms MAPAPHeightMonotonicity.primitiveWeightedZeroMass_mono_height
#print axioms MAPAPHeightMonotonicity.weightedZeroMassAtLevel_mono_height
#print axioms MAPAPHeightMonotonicity.apWeightedZeroMass_mono_height
#print axioms MAPAPHeightMonotonicity.apWeightedZeroMass_selectedHeight_le_add_one
