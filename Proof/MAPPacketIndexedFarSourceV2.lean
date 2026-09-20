import MAPFarSourceWeldScaffold

/-!
# Packet-indexed far-source certificate

The original padded-cell interface shares one short factor across every
dyadic block of a Heath--Brown branch.  A literal dyadic decomposition does
not have that restriction.  This V2 interface keeps the short length,
coefficient, character modulus, interval and window packet-indexed.
-/

namespace MAPPacketIndexedFarSourceV2

open scoped BigOperators
open MAPMRTCorollary25Instantiation
open MAPMRTCorollary53Source
open MAPFarAnnulusMRT
open MAPFarAnnulusSourceToModel
open MAPFarSourceWeldScaffold

noncomputable section

/-- Packetwise local source reduction with every factorization parameter
retained at its natural packet index. -/
def SourceToPacketIndexedPaddedCells
    (sourceMass error : CutoffBranch → ℝ)
    (blockCount : CutoffBranch → ℕ)
    (q shortLength longLength :
      (branch : CutoffBranch) → Fin (blockCount branch) → ℕ)
    (beta g : (branch : CutoffBranch) →
      (i : Fin (blockCount branch)) → Fin (q branch i) → ℕ → ℂ)
    (a b U : (branch : CutoffBranch) →
      Fin (blockCount branch) → ℝ) : Prop :=
  ∀ branch,
    sourceMass branch ≤ error branch +
      ∑ i : Fin (blockCount branch),
        literalFactoredTypeDCell (q branch i) (shortLength branch i)
          (longLength branch i) (beta branch i) (g branch i)
          (a branch i) (b branch i) (U branch i)

/-- The exact mixed-mass envelope of the packet-indexed cells. -/
def packetIndexedMixedMass
    {blockCount : CutoffBranch → ℕ}
    (q shortLength longLength :
      (branch : CutoffBranch) → Fin (blockCount branch) → ℕ)
    (beta g : (branch : CutoffBranch) →
      (i : Fin (blockCount branch)) → Fin (q branch i) → ℕ → ℂ)
    (a b U : (branch : CutoffBranch) →
      Fin (blockCount branch) → ℝ) : ℝ :=
  ∑ branch : CutoffBranch, ∑ i : Fin (blockCount branch),
    2 * characterPairMixedMass (q branch i) (shortLength branch i)
      (longLength branch i) (pairShortFamily (beta branch i))
      (pairLongFamily (g branch i))
      ((a branch i + b branch i) / 2)
      ((b branch i - a branch i) + 2 * U branch i) (U branch i)

theorem sourceToPacketIndexedPaddedCells_implies_mixedMassMajorant
    {sourceMass error : CutoffBranch → ℝ}
    {blockCount : CutoffBranch → ℕ}
    {q shortLength longLength :
      (branch : CutoffBranch) → Fin (blockCount branch) → ℕ}
    {beta g : (branch : CutoffBranch) →
      (i : Fin (blockCount branch)) → Fin (q branch i) → ℕ → ℂ}
    {a b U : (branch : CutoffBranch) →
      Fin (blockCount branch) → ℝ}
    (hsource : SourceToPacketIndexedPaddedCells sourceMass error blockCount
      q shortLength longLength beta g a b U)
    (hab : ∀ branch i, a branch i ≤ b branch i)
    (hU : ∀ branch i, 0 ≤ U branch i) :
    (∑ branch : CutoffBranch, sourceMass branch) ≤
      ∑ branch : CutoffBranch,
        (error branch + ∑ i : Fin (blockCount branch),
          2 * characterPairMixedMass (q branch i) (shortLength branch i)
            (longLength branch i) (pairShortFamily (beta branch i))
            (pairLongFamily (g branch i))
            ((a branch i + b branch i) / 2)
            ((b branch i - a branch i) + 2 * U branch i) (U branch i)) := by
  apply Finset.sum_le_sum
  intro branch hbranch
  calc
    sourceMass branch ≤ error branch +
        ∑ i : Fin (blockCount branch),
          literalFactoredTypeDCell (q branch i) (shortLength branch i)
            (longLength branch i) (beta branch i) (g branch i)
            (a branch i) (b branch i) (U branch i) := hsource branch
    _ ≤ error branch + ∑ i : Fin (blockCount branch),
        2 * characterPairMixedMass (q branch i) (shortLength branch i)
          (longLength branch i) (pairShortFamily (beta branch i))
          (pairLongFamily (g branch i))
          ((a branch i + b branch i) / 2)
          ((b branch i - a branch i) + 2 * U branch i) (U branch i) := by
      exact add_le_add le_rfl <| Finset.sum_le_sum fun i hi =>
        literalFactoredTypeDCell_le_two_characterPairMixedMass
          (q branch i) (shortLength branch i) (longLength branch i)
          (beta branch i) (g branch i) (hab branch i) (hU branch i)

structure PacketIndexedPaddedSourceData (p : Corollary53Input) where
  decompositionError : OuterComponent → ℝ
  sourceMass : OuterComponent → FarSourceBranch → ℝ
  cellError : OuterComponent → CutoffBranch → ℝ
  blockCount : OuterComponent → CutoffBranch → ℕ
  q : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℕ
  shortLength : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℕ
  longLength : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℕ
  beta : (component : OuterComponent) → (branch : CutoffBranch) →
    (i : Fin (blockCount component branch)) → Fin (q component branch i) → ℕ → ℂ
  g : (component : OuterComponent) → (branch : CutoffBranch) →
    (i : Fin (blockCount component branch)) → Fin (q component branch i) → ℕ → ℂ
  a : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℝ
  b : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℝ
  U : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℝ

def expandedPacketIndexedSourceRHS
    (p : Corollary53Input) (d : PacketIndexedPaddedSourceData p) : ℝ :=
  (divisorCount p.q : ℝ) ^ 4 /
      (p.q * stationaryWidth p.beta p.H ^ 2) *
    (nonCellSourceTotal d.decompositionError d.sourceMass +
      ∑ component : OuterComponent, ∑ branch : CutoffBranch,
        (d.cellError component branch +
          ∑ i : Fin (d.blockCount component branch),
            2 * characterPairMixedMass
              (d.q component branch i) (d.shortLength component branch i)
              (d.longLength component branch i)
              (pairShortFamily (d.beta component branch i))
              (pairLongFamily (d.g component branch i))
              ((d.a component branch i + d.b component branch i) / 2)
              ((d.b component branch i - d.a component branch i) +
                2 * d.U component branch i) (d.U component branch i))) +
    ordinaryError p.X p.H p.f p.beta p.eta

structure PacketIndexedPaddedSourceCertificate
    (p : Corollary53Input) (budget : ℝ) where
  data : PacketIndexedPaddedSourceData p
  sourceDecomposition :
    SourceBranchDecomposition p data.decompositionError data.sourceMass
  paddedCells : ∀ component,
    SourceToPacketIndexedPaddedCells
      (fun branch => data.sourceMass component (.cutoff branch))
      (data.cellError component) (data.blockCount component)
      (data.q component) (data.shortLength component) (data.longLength component)
      (data.beta component) (data.g component)
      (data.a component) (data.b component) (data.U component)
  intervalOrder : ∀ component branch i,
    data.a component branch i ≤ data.b component branch i
  widthNonneg : ∀ component branch i, 0 ≤ data.U component branch i
  expandedBudget : expandedPacketIndexedSourceRHS p data ≤ budget

theorem factorizationSup_le_packetIndexedCells
    {p : Corollary53Input} {hq : 1 ≤ p.q}
    (d : PacketIndexedPaddedSourceData p)
    (hsource : SourceBranchDecomposition p d.decompositionError d.sourceMass)
    (hcells : ∀ component,
      SourceToPacketIndexedPaddedCells
        (fun branch => d.sourceMass component (.cutoff branch))
        (d.cellError component) (d.blockCount component)
        (d.q component) (d.shortLength component) (d.longLength component)
        (d.beta component) (d.g component)
        (d.a component) (d.b component) (d.U component))
    (hab : ∀ component branch i,
      d.a component branch i ≤ d.b component branch i)
    (hU : ∀ component branch i, 0 ≤ d.U component branch i) :
    factorizationSup p.X p.H p.q p.f p.beta p.eta hq ≤
      nonCellSourceTotal d.decompositionError d.sourceMass +
      ∑ component : OuterComponent, ∑ branch : CutoffBranch,
        (d.cellError component branch +
          ∑ i : Fin (d.blockCount component branch),
            2 * characterPairMixedMass
              (d.q component branch i) (d.shortLength component branch i)
              (d.longLength component branch i)
              (pairShortFamily (d.beta component branch i))
              (pairLongFamily (d.g component branch i))
              ((d.a component branch i + d.b component branch i) / 2)
              ((d.b component branch i - d.a component branch i) +
                2 * d.U component branch i) (d.U component branch i)) := by
  calc
    factorizationSup p.X p.H p.q p.f p.beta p.eta hq ≤
        nonCellSourceTotal d.decompositionError d.sourceMass +
          cutoffSourceTotal d.sourceMass :=
      factorizationSup_le_nonCell_add_cutoff hsource
    _ ≤ nonCellSourceTotal d.decompositionError d.sourceMass +
        ∑ component : OuterComponent, ∑ branch : CutoffBranch,
          (d.cellError component branch +
            ∑ i : Fin (d.blockCount component branch),
              2 * characterPairMixedMass
                (d.q component branch i) (d.shortLength component branch i)
                (d.longLength component branch i)
                (pairShortFamily (d.beta component branch i))
                (pairLongFamily (d.g component branch i))
                ((d.a component branch i + d.b component branch i) / 2)
                ((d.b component branch i - d.a component branch i) +
                  2 * d.U component branch i) (d.U component branch i)) := by
      apply add_le_add le_rfl
      unfold cutoffSourceTotal
      apply Finset.sum_le_sum
      intro component hcomponent
      exact sourceToPacketIndexedPaddedCells_implies_mixedMassMajorant
        (hcells component) (hab component) (hU component)

theorem sourceRHS_le_of_packetIndexedCertificate
    {p : Corollary53Input} {hq : 1 ≤ p.q} {budget : ℝ}
    (cert : PacketIndexedPaddedSourceCertificate p budget) :
    stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
        ordinaryError p.X p.H p.f p.beta p.eta ≤ budget := by
  rw [stationaryMainTerm_eq_U]
  apply le_trans _ cert.expandedBudget
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left
    (factorizationSup_le_packetIndexedCells cert.data
      cert.sourceDecomposition cert.paddedCells cert.intervalOrder cert.widthNonneg)
  positivity

/-- Embed an old shared-short certificate into the packet-indexed interface. -/
def packetIndexedDataOfShared
    {p : Corollary53Input} (d : LiteralPaddedSourceData p) :
    PacketIndexedPaddedSourceData p where
  decompositionError := d.decompositionError
  sourceMass := d.sourceMass
  cellError := d.cellError
  blockCount := d.blockCount
  q := fun component branch _ => d.q component branch
  shortLength := fun component branch _ => d.shortLength component branch
  longLength := d.longLength
  beta := fun component branch _ => d.beta component branch
  g := d.g
  a := fun component branch _ => d.a component branch
  b := fun component branch _ => d.b component branch
  U := fun component branch _ => d.U component branch

theorem expandedPacketIndexedSourceRHS_of_shared
    {p : Corollary53Input} (d : LiteralPaddedSourceData p) :
    expandedPacketIndexedSourceRHS p (packetIndexedDataOfShared d) =
      expandedPaddedSourceRHS p d := by
  unfold expandedPacketIndexedSourceRHS expandedPaddedSourceRHS
    packetIndexedDataOfShared blockwiseCharacterPairMixedMass
  simp only
  congr 2
  simp_rw [Finset.mul_sum]

def packetIndexedCertificateOfShared
    {p : Corollary53Input} {budget : ℝ}
    (cert : LiteralPaddedSourceCertificate p budget) :
    PacketIndexedPaddedSourceCertificate p budget where
  data := packetIndexedDataOfShared cert.data
  sourceDecomposition := cert.sourceDecomposition
  paddedCells := cert.paddedCells
  intervalOrder := fun component branch i => cert.intervalOrder component branch
  widthNonneg := fun component branch i => cert.widthNonneg component branch
  expandedBudget := by
    rw [expandedPacketIndexedSourceRHS_of_shared]
    exact cert.expandedBudget

end
end MAPPacketIndexedFarSourceV2

#print axioms MAPPacketIndexedFarSourceV2.sourceToPacketIndexedPaddedCells_implies_mixedMassMajorant
#print axioms MAPPacketIndexedFarSourceV2.sourceRHS_le_of_packetIndexedCertificate
#print axioms MAPPacketIndexedFarSourceV2.packetIndexedCertificateOfShared
