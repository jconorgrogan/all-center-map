import FordCoarseP18Jacobian

open scoped BigOperators
open Finset

namespace MAPFordP18FixedTargetInjection
noncomputable section

def sourcePoint (p r n d : ℕ) : Type :=
  (Fin n → Fin (p ^ r + 1)) × (Fin d → Fin (p ^ r + 1))

def fixedInterval (p r d : ℕ) : Type :=
  {h : Fin d → Fin (p ^ r + 1) //
    MAPFordCoarseP18Fiber.intervalPositive h}

instance fixedIntervalFintype (p r d : ℕ) : Fintype (fixedInterval p r d) := by
  dsimp [fixedInterval]
  infer_instance

/- A single mixed-congruence coordinate has exactly the expected quotient
   injection.  This is the elementary lift map needed to pass from Ford's
   mod `p^min(j,r)` targets to a common mod `p^r` target. -/
def residueFiber (p r a : ℕ) (m : Fin (p ^ a)) : Type :=
  {t : Fin (p ^ r) // t.val % p ^ a = m.val}

def intResidue (q : ℕ) (hq : 0 < q) (a : ℤ) : Fin q :=
  ⟨(a % (q : ℤ)).toNat, by
    rw [Int.toNat_lt]
    · exact_mod_cast Int.emod_lt_of_pos a (by exact_mod_cast hq : (0 : ℤ) < q)
    · exact Int.emod_nonneg a
        (by exact_mod_cast (Nat.ne_of_gt hq) : (q : ℤ) ≠ 0)⟩

lemma intResidue_modEq (q : ℕ) (hq : 0 < q) (a : ℤ) :
    (intResidue q hq a).val ≡ a [ZMOD (q : ℕ)] := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hnon : 0 ≤ a % (q : ℤ) := Int.emod_nonneg a hqz.ne'
  change ((a % (q : ℤ)).toNat : ℤ) % (q : ℤ) = a % (q : ℤ)
  rw [Int.toNat_of_nonneg hnon]
  exact Int.emod_emod a (q : ℤ)

instance residueFiberFintype (p r a : ℕ) (m : Fin (p ^ a)) :
    Fintype (residueFiber p r a m) := by
  dsimp [residueFiber]
  infer_instance

def residueQuot {p r a : ℕ} (hp : 0 < p) (ha : a ≤ r)
    (m : Fin (p ^ a)) : residueFiber p r a m → Fin (p ^ (r-a)) := fun t =>
  ⟨t.1.val / p ^ a, by
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (n := a) hp)).2
    calc
      t.1.val < p ^ r := t.1.isLt
      _ = p ^ (r-a) * p ^ a := by
        rw [Nat.mul_comm, ← pow_add, Nat.add_sub_of_le ha]
  ⟩

lemma residueQuot_injective {p r a : ℕ} (hp : 0 < p) (ha : a ≤ r)
    (m : Fin (p ^ a)) : Function.Injective (residueQuot hp ha m) := by
  intro x y hxy
  apply Subtype.ext
  apply Fin.ext
  have hq : x.1.val / p ^ a = y.1.val / p ^ a := congrArg Fin.val hxy
  have hx := x.2
  have hy := y.2
  rw [← Nat.mod_add_div x.1.val (p ^ a), ← Nat.mod_add_div y.1.val (p ^ a)]
  rw [hx, hy, hq]

theorem card_residueFiber_le {p r a : ℕ} (hp : 0 < p) (ha : a ≤ r)
    (m : Fin (p ^ a)) :
    Fintype.card (residueFiber p r a m) ≤ p ^ (r-a) := by
  simpa using Fintype.card_le_of_injective (residueQuot hp ha m)
    (residueQuot_injective hp ha m)

def freeSum {p r n d : ℕ} (phi : Fin n → Polynomial ℤ)
    (z : sourcePoint p r n d) (i : Fin n) : ℤ :=
  ∑ j : Fin n, (phi i).eval ((z.1 j).val : ℤ)

def fixedSum {p r n d : ℕ} (phi : Fin n → Polynomial ℤ)
    (z : sourcePoint p r n d) (i : Fin n) : ℤ :=
  ∑ j : Fin d, (phi i).eval ((z.2 j).val : ℤ)

def freeTarget {p r n d : ℕ} (phi : Fin n → Polynomial ℤ)
    (m : Fin n → ℤ) (h : fixedInterval p r d) : Fin n → ℤ :=
  fun i => m i - ∑ j : Fin d, (phi i).eval ((h.1 j).val : ℤ)

/-- The fixed-target source fiber after the `d` high coordinates are separated.
The source congruence is the sum over free plus fixed coordinates, while the
Jacobian is Ford's `(k-d)`-variable source Jacobian on the free block. -/
def sourceBstarAt {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : Fin n → ℤ) : Type :=
  {z : sourcePoint p r n d //
    MAPFordCoarseP18Fiber.intervalPositive z.1 ∧
    MAPFordCoarseP18Fiber.intervalPositive z.2 ∧
    (∀ i, freeSum phi z i + fixedSum phi z i ≡ m i
      [ZMOD (p ^ r : ℕ)]) ∧
    p.Coprime (MAPFordCoarseP18Jacobian.sourceJacobian phi z.1).det.natAbs}

instance sourceBstarAtFintype {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : Fin n → ℤ) :
    Fintype (sourceBstarAt (p := p) (r := r) (n := n) (d := d) hp hR phi m) := by
  classical
  dsimp [sourceBstarAt, sourcePoint]
  infer_instance

def sourceToSigma {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : Fin n → ℤ) :
    sourceBstarAt (p := p) (r := r) (n := n) (d := d) hp hR phi m →
      Σ h : fixedInterval p r d,
        MAPFordCoarseP18Fiber.intervalFiber
          (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) phi
          (freeTarget phi m h) := by
  intro z
  let hfixed : fixedInterval p r d := ⟨z.1.2, z.2.2.1⟩
  let htarget : Fin n → ℤ := freeTarget phi m hfixed
  have hfree : MAPFordCoarseP18Fiber.intervalPositive z.1.1 := z.2.1
  have heq : ∀ i, (freeSum phi z.1 i - htarget i) ≡ 0
      [ZMOD (p ^ r : ℕ)] := by
    intro i
    change freeSum phi z.1 i -
        (m i - fixedSum phi z.1 i) ≡ 0 [ZMOD (p ^ r : ℕ)]
    have hs := z.2.2.2.1 i
    have hsub := hs.sub_right (fixedSum phi z.1 i)
    have hsub2 := hsub.sub_right (m i - fixedSum phi z.1 i)
    convert hsub2 using 1 <;> ring
  have hsource : p.Coprime
      (MAPFordCoarseP18Jacobian.sourceJacobian phi z.1.1).det.natAbs := z.2.2.2.2
  have hshift := (MAPFordCoarseP18Jacobian.source_nonsingularity_iff_shifted
      (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) phi htarget z.1.1 hfree).1 hsource
  exact ⟨hfixed, ⟨⟨z.1.1, hfree⟩, ⟨heq, hshift⟩⟩⟩

lemma sourceToSigma_injective {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : Fin n → ℤ) :
    Function.Injective (sourceToSigma (p := p) (r := r) (n := n) (d := d)
      hp hR phi m) := by
  intro a b hab
  apply Subtype.ext
  have hfixed : a.1.2 = b.1.2 := by
    have h := congrArg (fun x => (x.1).1) hab
    simpa [sourceToSigma] using h
  have hfree : a.1.1 = b.1.1 := by
    have h := congrArg (fun x => (x.2).1.1) hab
    simpa [sourceToSigma] using h
  exact Prod.ext hfree hfixed

lemma card_fixedInterval_le (p r d : ℕ) (hp : 0 < p) :
    Fintype.card (fixedInterval p r d) ≤ (p ^ r) ^ d := by
  classical
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let f : fixedInterval p r d → (Fin d → Fin (p ^ r)) := fun h =>
    MAPFordCoarseP18Fiber.intervalToFin
      (Nat.pow_pos (n := r) hp) h.1 h.2
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact MAPFordCoarseP18Fiber.finToInterval_intervalToFin
      (Nat.pow_pos (n := r) hp) a.1 a.2 |>.symm.trans
      ((congrArg (MAPFordCoarseP18Fiber.finToInterval) hab).trans
        (MAPFordCoarseP18Fiber.finToInterval_intervalToFin
          (Nat.pow_pos (n := r) hp) b.1 b.2))
  have hc := Fintype.card_le_of_injective f hinj
  have hcard_fun : Fintype.card (Fin d → Fin (p ^ r)) = (p ^ r) ^ d := by
    rw [Fintype.card_fun]
    simp
  exact hc.trans_eq hcard_fun

theorem card_sourceBstarAt_le
    {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : Fin n → ℤ) :
    Fintype.card (sourceBstarAt (p := p) (r := r) (n := n) (d := d)
      hp hR phi m) ≤
      p ^ (r*d + n) := by
  classical
  let qpos : 0 < p ^ r := Nat.pow_pos (n := r) (Nat.Prime.pos hp)
  letI := sourceBstarAtFintype (p := p) (r := r) (n := n) (d := d)
    hp hR phi m
  let sigma := Σ h : fixedInterval p r d,
    MAPFordCoarseP18Fiber.intervalFiber qpos phi (freeTarget phi m h)
  have hinj := sourceToSigma_injective (p := p) (r := r) (n := n) (d := d)
    hp hR phi m
  have hsource : Fintype.card
      (sourceBstarAt (p := p) (r := r) (n := n) (d := d) hp hR phi m) ≤
      Fintype.card sigma :=
    Fintype.card_le_of_injective
      (sourceToSigma (p := p) (r := r) (n := n) (d := d) hp hR phi m) hinj
  rw [Fintype.card_sigma] at hsource
  have hsum : (∑ h : fixedInterval p r d,
      Fintype.card (MAPFordCoarseP18Fiber.intervalFiber qpos phi
        (freeTarget phi m h))) ≤
      ∑ _h : fixedInterval p r d, p ^ n := by
    apply Finset.sum_le_sum
    intro h hh
    exact MAPFordCoarseP18Fiber.card_intervalFiber_le_p_pow_n hp hR phi
      (freeTarget phi m h)
  have hfixed := card_fixedInterval_le p r d hp.pos
  calc
    Fintype.card (sourceBstarAt hp hR phi m) ≤
        ∑ h : fixedInterval p r d,
          Fintype.card (MAPFordCoarseP18Fiber.intervalFiber qpos phi
            (freeTarget phi m h)) := hsource
    _ ≤ Fintype.card (fixedInterval p r d) * p ^ n := by
      exact hsum.trans_eq (by simp)
    _ ≤ (p ^ r) ^ d * p ^ n := Nat.mul_le_mul_right _ hfixed
    _ = p ^ (r*d + n) := by
      rw [← pow_mul, ← pow_add]

end
end MAPFordP18FixedTargetInjection

#print axioms MAPFordP18FixedTargetInjection.card_sourceBstarAt_le
