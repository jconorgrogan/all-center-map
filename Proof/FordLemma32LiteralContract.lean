import FordP18FixedTargetInjection

open scoped BigOperators

/-!
# Literal finite carriers for Ford's Lemma 3.2

The rendered source, printed pp.13--18, defines `K_s` by (3.1), `L_s` by
(3.2), and the p.18 set `B*(m)` used in (3.7).  This file records those
finite carriers without asserting either analytic estimate.  The final
theorem is the exact finite cardinality identity for the grouped p.18
carrier; the separate source-to-grouped map is exposed with its checked
left-inverse.
-/

namespace MAPFordLemma32LiteralContract
noncomputable section
set_option autoImplicit false

open MAPFordP18FixedTargetInjection

abbrev interval (N : ℕ) := Fin (N + 1)

structure KPoint (s k P Q : ℕ) (psi : Fin k → Polynomial ℤ) (q : ℕ) where
  z : Fin k → interval P
  w : Fin k → interval P
  x : Fin s → interval Q
  y : Fin s → interval Q
  z_pos : ∀ i, 1 ≤ (z i).val
  w_pos : ∀ i, 1 ≤ (w i).val
  x_pos : ∀ i, 1 ≤ (x i).val
  y_pos : ∀ i, 1 ≤ (y i).val
  equation : ∀ j : Fin k,
    (∑ i : Fin k, ((psi j).eval ((z i).val : ℤ) - (psi j).eval ((w i).val : ℤ))) +
      (q ^ (j.val + 1)) *
        (∑ i : Fin s, (((x i).val : ℤ) ^ (j.val + 1) - ((y i).val : ℤ) ^ (j.val + 1))) = 0

abbrev KCarrier (s k P Q : ℕ) (psi : Fin k → Polynomial ℤ) (q : ℕ) :=
  KPoint s k P Q psi q

structure LPoint (s k P Q p q r : ℕ) (phi : Fin k → Polynomial ℤ) where
  z : Fin k → interval P
  w : Fin k → interval P
  u : Fin s → interval Q
  v : Fin s → interval Q
  z_pos : ∀ i, 1 ≤ (z i).val
  w_pos : ∀ i, 1 ≤ (w i).val
  u_pos : ∀ i, 1 ≤ (u i).val
  v_pos : ∀ i, 1 ≤ (v i).val
  congruence : ∀ i : Fin k, (z i).val ≡ (w i).val [MOD p ^ r]
  equation : ∀ j : Fin k,
    (∑ i : Fin k, ((phi j).eval ((z i).val : ℤ) - (phi j).eval ((w i).val : ℤ))) +
      ((p * q) ^ (j.val + 1)) *
        (∑ i : Fin s, (((u i).val : ℤ) ^ (j.val + 1) - ((v i).val : ℤ) ^ (j.val + 1))) = 0

abbrev LCarrier (s k P Q p q r : ℕ) (phi : Fin k → Polynomial ℤ) :=
  LPoint s k P Q p q r phi

def sourceBstarAll {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) : Type :=
  {z : sourcePoint p r n d //
    MAPFordCoarseP18Fiber.intervalPositive z.1 ∧
    MAPFordCoarseP18Fiber.intervalPositive z.2 ∧
    p.Coprime (MAPFordCoarseP18Jacobian.sourceJacobian phi z.1).det.natAbs}

instance sourceBstarAllFintype {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) :
    Fintype (sourceBstarAll (d := d) hp hR phi) := by
  classical
  dsimp [sourceBstarAll, sourcePoint]
  infer_instance

def sourceBstarAllTarget {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (z : sourceBstarAll (d := d) hp hR phi) :
    Fin n → Fin (p ^ r) :=
  fun i => intResidue (p ^ r) (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
    (freeSum phi z.1 i + fixedSum phi z.1 i)

def sourceBstarAllToGrouped {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) :
    sourceBstarAll (d := d) hp hR phi →
      Sigma (fun m : Fin n → Fin (p ^ r) =>
        sourceBstarAt (d := d) hp hR phi (fun i => (m i).val)) := by
  intro z
  let m : Fin n → Fin (p ^ r) := sourceBstarAllTarget hp hR phi z
  refine ⟨m, ?_⟩
  refine ⟨z.1, z.2.1, z.2.2.1, ?_, z.2.2.2⟩
  intro i
  exact (intResidue_modEq (p ^ r)
    (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) _).symm

def groupedToSourceBstarAll {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) :
    Sigma (fun m : Fin n → Fin (p ^ r) =>
      sourceBstarAt (d := d) hp hR phi (fun i => (m i).val)) →
      sourceBstarAll (d := d) hp hR phi := by
  rintro ⟨m, z⟩
  exact ⟨z.1, ⟨z.2.1, z.2.2.1, z.2.2.2.2⟩⟩

lemma groupedToSourceBstarAll_left_inverse {p r n d : ℕ}
    (hp : p.Prime) (hR : 1 ≤ r) (phi : Fin n → Polynomial ℤ)
    (z : sourceBstarAll (d := d) hp hR phi) :
    groupedToSourceBstarAll hp hR phi
      (sourceBstarAllToGrouped hp hR phi z) = z := by
  apply Subtype.ext
  rfl

def p18GroupedSource {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) : Type :=
  Sigma (fun m : Fin n → Fin (p ^ r) =>
    sourceBstarAt (d := d) hp hR phi (fun i => (m i).val))

instance p18GroupedSourceFintype {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) :
    Fintype (p18GroupedSource (d := d) hp hR phi) := by
  classical
  dsimp [p18GroupedSource]
  infer_instance

theorem card_p18GroupedSource_eq_grouped_sum {p r n d : ℕ}
    (hp : p.Prime) (hR : 1 ≤ r) (phi : Fin n → Polynomial ℤ) :
    Fintype.card (p18GroupedSource (d := d) hp hR phi) =
      ∑ m : Fin n → Fin (p ^ r),
        Fintype.card (sourceBstarAt (d := d) hp hR phi (fun i => (m i).val)) := by
  change Fintype.card
      (Sigma (fun m : Fin n → Fin (p ^ r) =>
        sourceBstarAt (d := d) hp hR phi (fun i => (m i).val))) = _
  rw [Fintype.card_sigma]

end
end MAPFordLemma32LiteralContract

#print axioms MAPFordLemma32LiteralContract.card_p18GroupedSource_eq_grouped_sum

#check @MAPFordLemma32LiteralContract.KPoint.equation
#check @MAPFordLemma32LiteralContract.LPoint.equation
