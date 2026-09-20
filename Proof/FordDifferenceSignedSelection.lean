import FordSignedMixedSelectionActual
import FordCompleteMomentBridge
import FordDifferenceEnergyK
import FordDifferencePointBlockNorm
import FordPositiveHeightFamily
import FordKPointEnergy
import FordDifferencePairs

open scoped BigOperators ZMod ComplexConjugate
open FordBoundaryCountGeometry
open FordSignedMixedCount
open FordSignedMixedSelectionActual
open MAPFordDifferenceEnergyK
open MAPFordDifferencePointBlockNorm
open FordPositiveHeightFamily
open MAPFordDifferenceFamily
open MAPFordLemma32LiteralContract
open FordDifferencePairs
open FordKPointEnergy
open MAPFordCompleteSystemMoment

noncomputable section
namespace FordDifferenceSignedSelection

 theorem difference_signed_selection
    {s k P Q p q r : ℕ}
    (phi : Fin k → Polynomial ℤ)
    (hp : 0 < p) (hq : 0 < q) (hk : 1 ≤ k)
    (hm : 0 < p ^ r) (hH : 0 < P / (p ^ r)) :
    ∃ h0 : PositiveHeight P (p ^ r),
      ∀ (hs : Fin k → PositiveHeight P (p ^ r))
        (sign : Fin k → Bool),
      (Fintype.card (SignedZero
        (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
          FordKPointEnergy.baseFreq (q := p * q) x)
        (fun h : PositiveHeight P (p ^ r) =>
          fun z : FordKPointEnergy.SourcePoint (P := P) =>
            pointTranslatedDifferenceFrequency phi (shift h) z)
        hs sign) : ℝ)^2 ≤
        (completeMoment s k Q : ℝ) *
          (Fintype.card (KPoint s k P Q
            (differencePsi phi (shift h0)) (p * q)) : ℝ) := by
  let hbase : PositiveHeight P (p ^ r) :=
    ⟨⟨1, by omega⟩, by norm_num⟩
  letI : Nonempty (PositiveHeight P (p ^ r)) := ⟨hbase⟩
  obtain ⟨h0, hsel⟩ :=
    signed_zero_card_selection
      (f := fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := p * q) x)
      (g := fun h : PositiveHeight P (p ^ r) =>
          fun z : FordKPointEnergy.SourcePoint (P := P) =>
            pointTranslatedDifferenceFrequency phi (shift h) z)
      hk
  refine ⟨h0, ?_⟩
  intro hs sign
  have hbound := hsel hs sign
  have hmoment := FordCompleteMomentBridge.completeMoment_eq_baseZero_card
    (s := s) (k := k) (Q := Q) (q := p * q)
    (Nat.mul_pos hp hq)
  have henergy := kpoint_card_eq_translated_difference_energy
    (s := s) (k := k) (P := P) (Q := Q) (q := p * q)
    phi (shift h0)
  rw [← hmoment, ← henergy] at hbound
  exact hbound

end FordDifferenceSignedSelection

#print axioms FordDifferenceSignedSelection.difference_signed_selection
