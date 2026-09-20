import FordSource36InteriorCore
open MAPFordSource36InteriorCarrier MAPFordP16FiniteFourierBridge MAPFordP16Source35Triangular MAPFordP16LiteralResidueBridge
set_option maxHeartbeats 100000
namespace MAPFordSource36TransportLight
private def submap {α : Type*} {a b : α → Prop} (h : ∀ x, a x → b x) (z : Subtype a) : Subtype b := ⟨z.val,h z.val z.property⟩
private theorem submap_val {α : Type*} {a b : α → Prop} (h : ∀ x, a x → b x) (z : Subtype a) : (submap h z).val = z.val := rfl
def transportF {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi) :
    fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp (phiRow psi q c) :=
  submap (fun x => (fordPolynomialMask_phiRow_iff hdk hp psi q c hzero x).mpr) z
lemma transportF_val {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi) :
    (transportF hdk hp psi q c hzero z).val = z.val :=
  submap_val (fun x => (fordPolynomialMask_phiRow_iff hdk hp psi q c hzero x).mpr) z
end MAPFordSource36TransportLight
#print axioms MAPFordSource36TransportLight.transportF_val
