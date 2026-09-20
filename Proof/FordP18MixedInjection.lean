import FordP18FixedTargetInjection

namespace MAPFordP18MixedInjection
noncomputable section

open MAPFordP18FixedTargetInjection

def equationExponent (r d : ℕ) (i : Fin n) : ℕ :=
  min (d + i.val + 1) r

def mixedTarget (p r n d : ℕ) : Type :=
  ∀ i : Fin n, Fin (p ^ equationExponent r d i)

def mixedSourceBstar {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : mixedTarget p r n d) : Type :=
  {z : sourcePoint p r n d //
    MAPFordCoarseP18Fiber.intervalPositive z.1 ∧
    MAPFordCoarseP18Fiber.intervalPositive z.2 ∧
    (∀ i, freeSum phi z i + fixedSum phi z i ≡
      (m i).val [ZMOD (p ^ equationExponent r d i : ℕ)]) ∧
    p.Coprime (MAPFordCoarseP18Jacobian.sourceJacobian phi z.1).det.natAbs}

instance mixedSourceBstarFintype {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : mixedTarget p r n d) :
    Fintype (mixedSourceBstar hp hR phi m) := by
  classical
  dsimp [mixedSourceBstar, sourcePoint]
  infer_instance

def actualResidueVector {p r n d : ℕ} (hp : p.Prime)
    (phi : Fin n → Polynomial ℤ) (z : sourcePoint p r n d) :
    Fin n → Fin (p ^ r) := fun i =>
  intResidue (p ^ r) (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
    (freeSum phi z i + fixedSum phi z i)

def residueVector {p r n : ℕ} (a : Fin n → ℕ)
    (m : (i : Fin n) → Fin (p ^ a i)) : Type :=
  (i : Fin n) → residueFiber p (r := r) (a i) (m i)

lemma equationExponent_le (p r n d : ℕ) (i : Fin n) :
    equationExponent r d i ≤ r := by
  exact min_le_right _ _

def actualResidueVector_mem {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : mixedTarget p r n d)
    (z : mixedSourceBstar hp hR phi m) :
    residueVector (r := r)
      (fun i => equationExponent r d i) m := by
  intro i
  let a := equationExponent r d i
  let t := actualResidueVector hp phi z.1 i
  have hpow : p ^ a ∣ p ^ r := by
    exact Nat.pow_dvd_pow p (equationExponent_le p r n d i)
  have hpowInt : (p ^ a : ℤ) ∣ (p ^ r : ℤ) := by
    exact_mod_cast hpow
  have htotal : t.val ≡
      (freeSum phi z.1 i + fixedSum phi z.1 i)
      [ZMOD (p ^ r : ℕ)] := by
    exact intResidue_modEq (p ^ r)
      (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) _
  have hsmall := Int.ModEq.of_dvd hpowInt htotal
  have hmixed := z.2.2.2.1 i
  have hmod : (t.val : ℤ) ≡ (m i).val [ZMOD (p ^ a : ℕ)] :=
    hsmall.trans hmixed
  have hnat : t.val % p ^ a = (m i).val := by
    rw [Int.ModEq] at hmod
    have hcast : ((t.val % p ^ a : ℕ) : ℤ) =
        (((m i).val % p ^ a : ℕ) : ℤ) := by
      simpa [Int.natCast_mod] using hmod
    have hcastNat : t.val % p ^ a = (m i).val % p ^ a := by
      exact_mod_cast hcast
    rw [Nat.mod_eq_of_lt (m i).isLt] at hcastNat
    exact hcastNat
  exact ⟨t, hnat⟩

def mixedToResidueVector {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : mixedTarget p r n d) :
    mixedSourceBstar hp hR phi m →
      residueVector (r := r) (fun i => equationExponent r d i) m := fun z =>
  actualResidueVector_mem hp hR phi m z

end
end MAPFordP18MixedInjection

#print axioms MAPFordP18MixedInjection.mixedToResidueVector
