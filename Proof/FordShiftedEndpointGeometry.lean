import FordP16Source35Reparam

open scoped BigOperators ZMod

namespace MAPFordShiftedEndpointGeometry
noncomputable section
set_option maxHeartbeats 1000000

open MAPFordP16Source35Reparam

/-- The full shifted-U upper endpoint. -/
def shiftedUFullCap {p Q : ℕ} [NeZero p] (c : Fin p) : ℕ :=
  (Q + c.val) / p

def shiftedU_equiv_fin
    {p Q : ℕ} [NeZero p] (c : Fin p) :
    shiftedU (p := p) (Q := Q) c ≃
      Fin (shiftedUFullCap (p := p) (Q := Q) c) := by
  let toFun : shiftedU (p := p) (Q := Q) c →
      Fin (shiftedUFullCap (p := p) (Q := Q) c) := fun u =>
    ⟨u.1.val - 1, by
      have hu := u.1.isLt
      change u.1.val < shiftedUFullCap (p := p) (Q := Q) c + 1 at hu
      have hpos := u.2
      omega⟩
  let invFun : Fin (shiftedUFullCap (p := p) (Q := Q) c) →
      shiftedU (p := p) (Q := Q) c := fun n =>
    ⟨⟨n.val + 1, by
        have hn := n.isLt
        change n.val < shiftedUFullCap (p := p) (Q := Q) c at hn
        change n.val + 1 < shiftedUFullCap (p := p) (Q := Q) c + 1
        omega⟩, by exact Nat.succ_le_succ (Nat.zero_le _ )⟩
  refine Equiv.mk toFun invFun ?_ ?_
  · intro u
    apply Subtype.ext
    apply Fin.ext
    have hpos := u.2
    change u.1.val - 1 + 1 = u.1.val
    omega
  · intro n
    apply Fin.ext
    change (n.val + 1) - 1 = n.val
    omega

theorem shiftedU_card
    {p Q : ℕ} [NeZero p] (c : Fin p) :
    Fintype.card (shiftedU (p := p) (Q := Q) c) =
      shiftedUFullCap (p := p) (Q := Q) c := by
  rw [Fintype.card_congr (shiftedU_equiv_fin (p := p) (Q := Q) c)]
  simp

lemma shiftedUFullCap_lower
    {p Q : ℕ} [NeZero p] (c : Fin p) :
    Q / p ≤ shiftedUFullCap (p := p) (Q := Q) c := by
  dsimp [shiftedUFullCap]
  exact Nat.div_le_div_right (Nat.le_add_right Q c.val)

lemma shiftedUFullCap_upper
    {p Q : ℕ} [NeZero p] (c : Fin p) :
    shiftedUFullCap (p := p) (Q := Q) c ≤ Q / p + 1 := by
  dsimp [shiftedUFullCap]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  apply (Nat.div_le_iff_le_mul hp).2
  have hc : c.val < p := c.isLt
  have hrem : Q % p < p := Nat.mod_lt Q hp
  have hdecomp := Nat.mod_add_div Q p
  simp only [Nat.add_mul, Nat.one_mul]
  have hdecomp' : (Q / p) * p + Q % p = Q := by
    simpa [Nat.add_comm, Nat.mul_comm] using hdecomp
  omega

lemma shiftedUFullCap_eq_succ_of_boundary
    {p Q : ℕ} [NeZero p] (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c) :
    shiftedUFullCap (p := p) (Q := Q) c = Q / p + 1 := by
  have hu := shiftedUFullCap_upper (p := p) (Q := Q) c
  omega

def shiftedUEndpoint
    {p Q : ℕ} [NeZero p] (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c) :
    shiftedU (p := p) (Q := Q) c := by
  let cap := shiftedUFullCap (p := p) (Q := Q) c
  have hcapEq := shiftedUFullCap_eq_succ_of_boundary (p := p) (Q := Q) c hboundary
  have hcap' : cap = Q / p + 1 := by
    simpa [cap] using hcapEq
  have hcap : 0 < cap := by
    rw [hcap']
    exact Nat.zero_lt_succ _
  refine ⟨⟨cap, ?_⟩, ?_⟩
  · dsimp [cap, shiftedUFullCap]
    exact Nat.lt_succ_of_le (Nat.le_refl _)
  · exact hcap

lemma shiftedU_boundary_iff
    {p Q : ℕ} [NeZero p] (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c)
    (u : shiftedU (p := p) (Q := Q) c) :
    Q / p < u.1.val ↔
      u.1.val = shiftedUFullCap (p := p) (Q := Q) c := by
  have hcap := shiftedUFullCap_eq_succ_of_boundary (p := p) (Q := Q) c hboundary
  constructor
  · intro hu
    have hupper : u.1.val ≤ shiftedUFullCap (p := p) (Q := Q) c := by
      have := u.1.isLt
      change u.1.val < shiftedUFullCap (p := p) (Q := Q) c + 1 at this
      omega
    omega
  · intro hu
    rw [hu]
    exact hboundary

lemma shiftedU_endpoint_val
    {p Q : ℕ} [NeZero p] (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c) :
    (shiftedUEndpoint (p := p) (Q := Q) c hboundary).1.val =
      shiftedUFullCap (p := p) (Q := Q) c := by
  rfl

lemma shiftedU_ne_endpoint_iff_le
    {p Q : ℕ} [NeZero p] (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c)
    (u : shiftedU (p := p) (Q := Q) c) :
    u ≠ shiftedUEndpoint (p := p) (Q := Q) c hboundary ↔
      u.1.val ≤ Q / p := by
  constructor
  · intro hne
    by_contra hnot
    have hgt : Q / p < u.1.val := Nat.lt_of_not_ge hnot
    have huval := (shiftedU_boundary_iff (p := p) (Q := Q) c hboundary u).1 hgt
    apply hne
    apply Subtype.ext
    apply Fin.ext
    exact huval
  · intro hle heq
    have heqval := congrArg (fun z : shiftedU (p := p) (Q := Q) c => z.1.val) heq
    have hcap := shiftedUFullCap_eq_succ_of_boundary (p := p) (Q := Q) c hboundary
    dsimp [shiftedUEndpoint] at heqval
    omega

theorem shiftedU_fullCap_gt_threshold_of_mul_lt
    {p Q s : ℕ} [NeZero p] (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c)
    (hQ : (4 * s) ^ 2 * p < Q) :
    (4 * s) ^ 2 < shiftedUFullCap (p := p) (Q := Q) c := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hT : (4 * s) ^ 2 ≤ Q / p := by
    apply (Nat.le_div_iff_mul_le hp).2
    omega
  have hcap := shiftedUFullCap_eq_succ_of_boundary (p := p) (Q := Q) c hboundary
  omega

end
end MAPFordShiftedEndpointGeometry

#print axioms MAPFordShiftedEndpointGeometry.shiftedU_card
#print axioms MAPFordShiftedEndpointGeometry.shiftedU_boundary_iff
#print axioms MAPFordShiftedEndpointGeometry.shiftedU_ne_endpoint_iff_le
#print axioms MAPFordShiftedEndpointGeometry.shiftedU_fullCap_gt_threshold_of_mul_lt
