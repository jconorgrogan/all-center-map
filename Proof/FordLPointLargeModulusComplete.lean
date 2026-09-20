import FordLPointLargeModulus
import FordCompleteMomentBridge

open MAPFordLemma32LiteralContract MAPFordCompleteSystemMoment
open FordLPointLargeModulus FordCompleteMomentBridge

noncomputable section
namespace FordLPointLargeModulusComplete

/-- The exact H=0 formula in terms of the pre-existing literal complete moment. -/
theorem lPoint_card_eq_completeMoment
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (hp : 0 < p) (hq : 0 < q) (hm : P < p ^ r) :
    Fintype.card (LPoint s k P Q p q r phi) =
      P ^ k * completeMoment s k Q := by
  rw [lPoint_card_large_modulus phi hm]
  have hbase := completeMoment_eq_baseZero_card
    (s := s) (k := k) (Q := Q) (Nat.mul_pos hp hq)
  change _ = _ at hbase
  rw [← hbase]
  exact Nat.mul_comm _ _

end FordLPointLargeModulusComplete

#print axioms FordLPointLargeModulusComplete.lPoint_card_eq_completeMoment
