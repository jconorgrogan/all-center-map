import FordRawCongruenceToL

open scoped BigOperators
open MAPFordLemma32LiteralContract
noncomputable section
set_option autoImplicit false
namespace FordLPointMonotone

private def intervalCast {Q₁ Q₂ : ℕ} (hQ : Q₁ ≤ Q₂) :
    interval Q₁ → interval Q₂ :=
  Fin.castLE (Nat.add_le_add_right hQ 1)

def lPointCast {s k P Q₁ Q₂ p q r : ℕ} (hQ : Q₁ ≤ Q₂)
    (phi : Fin k → Polynomial ℤ) :
    LPoint s k P Q₁ p q r phi → LPoint s k P Q₂ p q r phi := by
  intro a
  refine {
    z := a.z
    w := a.w
    u := fun i => intervalCast hQ (a.u i)
    v := fun i => intervalCast hQ (a.v i)
    z_pos := a.z_pos
    w_pos := a.w_pos
    u_pos := ?_
    v_pos := ?_
    congruence := a.congruence
    equation := ?_ }
  · intro i
    exact a.u_pos i
  · intro i
    exact a.v_pos i
  · intro j
    simpa [intervalCast] using a.equation j

lemma lPointCast_injective {s k P Q₁ Q₂ p q r : ℕ}
    (hQ : Q₁ ≤ Q₂) (phi : Fin k → Polynomial ℤ) :
    Function.Injective (lPointCast (s := s) (k := k) (P := P) (Q₁ := Q₁)
      (Q₂ := Q₂) (p := p) (q := q) (r := r) hQ phi) := by
  intro a b hab
  have hz : a.z = b.z := by
    simpa [lPointCast] using congrArg (fun t => t.z) hab
  have hw : a.w = b.w := by
    simpa [lPointCast] using congrArg (fun t => t.w) hab
  have hu0 : (fun i => intervalCast hQ (a.u i)) =
      (fun i => intervalCast hQ (b.u i)) := by
    simpa [lPointCast] using congrArg (fun t => t.u) hab
  have hv0 : (fun i => intervalCast hQ (a.v i)) =
      (fun i => intervalCast hQ (b.v i)) := by
    simpa [lPointCast] using congrArg (fun t => t.v) hab
  have hu : a.u = b.u := by
    funext i
    apply Fin.ext
    simpa [intervalCast] using congrArg Fin.val (congrFun hu0 i)
  have hv : a.v = b.v := by
    funext i
    apply Fin.ext
    simpa [intervalCast] using congrArg Fin.val (congrFun hv0 i)
  cases a with
  | mk az aw au av azpos awpos aupos avpos acong aeq =>
    cases b with
    | mk bz bw bu bv bzpos bwpos bupos bvpos bcong beq =>
      dsimp at hz hw hu hv
      cases hz
      cases hw
      cases hu
      cases hv
      rfl

theorem lPoint_card_mono {s k P Q₁ Q₂ p q r : ℕ}
    (hQ : Q₁ ≤ Q₂) (phi : Fin k → Polynomial ℤ) :
    Fintype.card (LPoint s k P Q₁ p q r phi) ≤
      Fintype.card (LPoint s k P Q₂ p q r phi) :=
  Fintype.card_le_of_injective
    (lPointCast (s := s) (k := k) (P := P) (Q₁ := Q₁) (Q₂ := Q₂)
      (p := p) (q := q) (r := r) hQ phi)
    (lPointCast_injective (s := s) (k := k) (P := P) (Q₁ := Q₁)
      (Q₂ := Q₂) (p := p) (q := q) (r := r) hQ phi)

end FordLPointMonotone

#print axioms FordLPointMonotone.lPointCast_injective
#print axioms FordLPointMonotone.lPoint_card_mono
