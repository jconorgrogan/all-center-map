import FordClassEnergyInjective
import FordLPointClassEnergy
import FordMaxEnergyInput

open FordBoundaryCountGeometry FordLPointClassEnergy
open MAPFordLemma32LiteralContract

noncomputable section
namespace FordLPointLargeModulus

theorem positiveResidueClass_injective
    {P p r : ℕ} (hm : P < p ^ r) :
    Function.Injective (positiveResidueClass (P := P) (p := p) (r := r)) := by
  intro z w he
  apply Subtype.ext
  apply Fin.ext
  have hval := congrArg Fin.val he
  change z.1.val % (p ^ r) = w.1.val % (p ^ r) at hval
  have hz : z.1.val < p ^ r := by have := z.1.isLt; omega
  have hw : w.1.val < p ^ r := by have := w.1.isLt; omega
  simpa [Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hw] using hval

/-- Exact H=0 count before identifying the base count with the complete moment.
No positivity or primality hypotheses are needed for this combinatorial fact. -/
theorem lPoint_card_large_modulus
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) (hm : P < p ^ r) :
    Fintype.card (LPoint s k P Q p q r phi) =
      Fintype.card (BaseZero (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (k := k) (q := p * q) x)) * P ^ k := by
  rw [lPoint_card_eq_classEnergy]
  change Fintype.card (FordClassEnergyMoment.ClassEnergyZero _ _ _ k) = _
  have hh := FordClassEnergyInjective.card_classEnergy_of_injective
    (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
      FordKPointEnergy.baseFreq (k := k) (q := p * q) x)
    (fun z : FordKPointEnergy.SourcePoint (P := P) => FordKPointEnergy.sourceFreq phi z)
    (positiveResidueClass (P := P) (p := p) (r := r))
    (positiveResidueClass_injective (p := p) (r := r) hm) k
  simpa only [FordMaxEnergyInput.sourcePoint_card] using hh

end FordLPointLargeModulus

#print axioms FordLPointLargeModulus.positiveResidueClass_injective
#print axioms FordLPointLargeModulus.lPoint_card_large_modulus
