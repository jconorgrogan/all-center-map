import MRTLemma215DynamicHighPacketCertificateV3

/-!
# Finite index for every literal dynamic high packet

This is the packet-indexed V3 wrapper.  Raw HB branch, shell bags, Type-d
witness, selected factor, complementary output cell, and every analytic
parameter remain packet-local.
-/

namespace MRTLemma215DynamicHighPacketIndexV3

open scoped ArithmeticFunction BigOperators
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicHighPacketsV3
open MRTLemma215ComplementDyadicV3
open MRTLemma215DynamicHighPacketCertificateV3

noncomputable section

/-- One component of the exact arbitrary-order preliminary expansion. -/
def DynamicRawComponentIndexV3 (X : ℝ) (K : ℕ) :=
  Σ branch : Fin K,
    Fin (sourceDyadicCount (hbFactorCutoff X)) ×
      Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ) ×
      Sym (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1)

def rawBranchV3 {X : ℝ} {K : ℕ}
    (c : DynamicRawComponentIndexV3 X K) : Fin K := c.1

def rawLogIndexV3 {X : ℝ} {K : ℕ}
    (c : DynamicRawComponentIndexV3 X K) :
    Fin (sourceDyadicCount (hbFactorCutoff X)) := c.2.1

def rawZetaBagV3 {X : ℝ} {K : ℕ}
    (c : DynamicRawComponentIndexV3 X K) :
    Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
      (rawBranchV3 c : ℕ) := c.2.2.1

def rawMoebiusBagV3 {X : ℝ} {K : ℕ}
    (c : DynamicRawComponentIndexV3 X K) :
    Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) ((rawBranchV3 c : ℕ) + 1) := c.2.2.2

def DynamicComponentIsHighV3
    {X : ℝ} {K : ℕ} (delta H₀ : ℝ)
    (c : DynamicRawComponentIndexV3 X K) : Prop :=
  ∃ j : Fin 8,
    dynamicComponentOutcome 8 delta H₀ (rawLogIndexV3 c)
      (rawZetaBagV3 c) (rawMoebiusBagV3 c) = .typeD j ∧
      3 ≤ (j : ℕ)

def DynamicHighComponentIndexV3
    (X delta H₀ : ℝ) (K : ℕ) :=
  {c : DynamicRawComponentIndexV3 X K //
    DynamicComponentIsHighV3 delta H₀ c}

instance (X : ℝ) (K : ℕ) : Fintype (DynamicRawComponentIndexV3 X K) := by
  classical
  unfold DynamicRawComponentIndexV3
  infer_instance

instance (X delta H₀ : ℝ) (K : ℕ) :
    Fintype (DynamicHighComponentIndexV3 X delta H₀ K) := by
  classical
  unfold DynamicHighComponentIndexV3
  infer_instance

def highTypeIndexV3
    {X delta H₀ : ℝ} {K : ℕ}
    (c : DynamicHighComponentIndexV3 X delta H₀ K) : Fin 8 :=
  Classical.choose c.property

theorem highTypeIndexV3_outcome
    {X delta H₀ : ℝ} {K : ℕ}
    (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    dynamicComponentOutcome 8 delta H₀ (rawLogIndexV3 c.1)
      (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1) =
        .typeD (highTypeIndexV3 c) :=
  (Classical.choose_spec c.property).1

theorem highTypeIndexV3_three
    {X delta H₀ : ℝ} {K : ℕ}
    (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    3 ≤ (highTypeIndexV3 c : ℕ) :=
  (Classical.choose_spec c.property).2

def highFactorsV3
    {X delta H₀ : ℝ} {K : ℕ}
    (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    List NatDyadicFactor :=
  sortedComponentFactorList (rawLogIndexV3 c.1)
    (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1)

def highScalesV3
    {X delta H₀ : ℝ} {K : ℕ}
    (c : DynamicHighComponentIndexV3 X delta H₀ K) : List ℝ :=
  dynamicPreliminaryScaleList (some (rawLogIndexV3 c.1))
    (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1)

def highSelectedIndexV3
    {X delta H₀ : ℝ} {K : ℕ}
    (c : DynamicHighComponentIndexV3 X delta H₀ K) : ℕ :=
  largestSmallPrefix (highScalesV3 c) (Real.rpow X delta)

theorem highGeometryV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    let s := highSelectedIndexV3 c
    let factors := highFactorsV3 c
    ∃ hs : s < factors.length,
      2 ≤ factors[s].length ∧
      factors[s].length ^ 2 ≤
        factorLowerProduct (complementFactorList factors s) ∧
      factorConvolution
          (dynamicComponentFactorList (rawLogIndexV3 c.1)
            (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1)) =
        factors[s].coeff *
          factorConvolution (complementFactorList factors s) := by
  simpa [highSelectedIndexV3, highScalesV3, highFactorsV3] using
    typeD_high_regrouping_geometry hX hdelta
      (rawLogIndexV3 c.1) (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1)
      (highTypeIndexV3 c) (highTypeIndexV3_three c)
      (highTypeIndexV3_outcome c)

def highSelectedIndexIsLtV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    highSelectedIndexV3 c < (highFactorsV3 c).length :=
  Classical.choose (highGeometryV3 hX hdelta c)

def highSelectedFactorV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    NatDyadicFactor :=
  (highFactorsV3 c)[highSelectedIndexV3 c]'(highSelectedIndexIsLtV3 hX hdelta c)

def highComplementV3
    {X delta H₀ : ℝ} {K : ℕ}
    (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    List NatDyadicFactor :=
  complementFactorList (highFactorsV3 c) (highSelectedIndexV3 c)

theorem highSelectedFactorV3_two
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    2 ≤ (highSelectedFactorV3 hX hdelta c).length :=
  (Classical.choose_spec (highGeometryV3 hX hdelta c)).1

theorem highSelectedFactorV3_square
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    (highSelectedFactorV3 hX hdelta c).length ^ 2 ≤
      factorLowerProduct (highComplementV3 c) :=
  (Classical.choose_spec (highGeometryV3 hX hdelta c)).2.1

theorem highComplementV3_length_one
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    1 ≤ (highComplementV3 c).length := by
  by_contra h
  have hnil : highComplementV3 c = [] := by
    apply List.eq_nil_of_length_eq_zero
    omega
  have hsquare := highSelectedFactorV3_square hX hdelta c
  have htwo := highSelectedFactorV3_two hX hdelta c
  rw [hnil] at hsquare
  simp [factorLowerProduct] at hsquare
  nlinarith

def DynamicHighPacketIndexV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (K : ℕ) :=
  Σ c : DynamicHighComponentIndexV3 X delta H₀ K,
    {cell : Fin (sourceDyadicCount (factorUpperProduct (highComplementV3 c))) //
      cell ∈ survivingComplementCells
        (highSelectedFactorV3 hX hdelta c).length (highComplementV3 c)}

instance {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (K : ℕ) : Fintype (DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) := by
  classical
  unfold DynamicHighPacketIndexV3
  infer_instance

def highPacketShortLengthV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) : ℕ :=
  (highSelectedFactorV3 hX hdelta packet.1).length

def highPacketLongLengthV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) : ℕ :=
  2 ^ (packet.2.1 : ℕ)

def highPacketShortCoeffV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    ArithmeticFunction ℂ :=
  scaledSelectedFactor (rawZetaBagV3 packet.1.1)
    (rawMoebiusBagV3 packet.1.1)
    (highSelectedFactorV3 hX hdelta packet.1) |>.coeff

def highPacketLongCoeffV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    ArithmeticFunction ℂ :=
  sourceDyadicArithmetic (factorUpperProduct (highComplementV3 packet.1))
    (factorConvolution (highComplementV3 packet.1)) packet.2.1

theorem highPacket_geometryV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    2 ≤ highPacketShortLengthV3 packet ∧
    2 ≤ highPacketLongLengthV3 packet ∧
    (1 / 2 : ℝ) * (highPacketShortLengthV3 packet : ℝ) ^ 2 ≤
      (highPacketLongLengthV3 packet : ℝ) := by
  exact ⟨highSelectedFactorV3_two hX hdelta packet.1,
    survivingComplementCell_longLength_two
      (highSelectedFactorV3_two hX hdelta packet.1) packet.2.2,
    survivingComplementCell_half_square_le packet.2.2⟩

theorem highPacket_supportV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    SupportedNatDyadic (highPacketShortLengthV3 packet)
        (highPacketShortCoeffV3 packet) ∧
      SupportedNatDyadic (highPacketLongLengthV3 packet)
        (highPacketLongCoeffV3 packet) := by
  exact ⟨(scaledSelectedFactor
      (rawZetaBagV3 packet.1.1) (rawMoebiusBagV3 packet.1.1)
      (highSelectedFactorV3 hX hdelta packet.1)).support,
    sourceDyadicArithmetic_supported _ _ packet.2.1⟩

theorem highPacket_exists_coefficientBoundsV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    ∃ a : ℕ,
      (∀ n ∈ DeterminantCountWeld.dyadic (highPacketShortLengthV3 packet),
        ‖highPacketShortCoeffV3 packet n‖ ≤
          Real.log (2 * (n : ℝ)) ^ a) ∧
      (∀ n ∈ DeterminantCountWeld.dyadic (highPacketLongLengthV3 packet),
        ‖highPacketLongCoeffV3 packet n‖ ≤
          (MixedMellinCert.tauAF (highComplementV3 packet.1).length n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ a) := by
  exact exists_highPacket_coefficientBounds
    (rawLogIndexV3 packet.1.1) (rawZetaBagV3 packet.1.1)
    (rawMoebiusBagV3 packet.1.1) (highSelectedIndexV3 packet.1)
    (highSelectedIndexIsLtV3 hX hdelta packet.1)
    (highSelectedFactorV3_two hX hdelta packet.1) packet.2.1 packet.2.2

end
end MRTLemma215DynamicHighPacketIndexV3

#print axioms MRTLemma215DynamicHighPacketIndexV3.highGeometryV3
#print axioms MRTLemma215DynamicHighPacketIndexV3.highPacket_geometryV3
#print axioms MRTLemma215DynamicHighPacketIndexV3.highComplementV3_length_one
#print axioms MRTLemma215DynamicHighPacketIndexV3.highPacket_exists_coefficientBoundsV3
