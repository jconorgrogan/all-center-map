import FordMixedSourceCount
import FordScaledPowerCongruence
import FordP16LiteralResidueBridge
import FordHenselFiber

open scoped BigOperators
open MAPFordP18FixedTargetInjection MAPFordP18MixedInjection
open MAPFordMixedSourceCount MAPFordScaledPowerCongruence
open MAPFordP16FiniteFourierBridge
open MAPFordP16LiteralResidueBridge

noncomputable section
namespace FordRealizedClassBound

/-- The positive representative of an integer residue modulo `p^r`.  The
zero residue is represented by `p^r`, so the source interval remains
`1,...,p^r` and never acquires a zero-padded coordinate. -/
def positiveResidue {p r P : ℕ} (hp : p.Prime) (x : Fin (P + 1)) :
    Fin (p ^ r + 1) := by
  let a := intResidue (p ^ r) (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
    (x.val : ℤ)
  exact ⟨if a.val = 0 then p ^ r else a.val, by
    split_ifs with h
    · omega
    · exact Nat.lt_succ_of_lt a.isLt⟩

lemma positiveResidue_modEq {p r P : ℕ} (hp : p.Prime)
    (x : Fin (P + 1)) :
    ((positiveResidue (p := p) (r := r) hp x).val : ℤ) ≡ (x.val : ℤ)
      [ZMOD (p ^ r : ℕ)] := by
  let a := intResidue (p ^ r) (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
    (x.val : ℤ)
  have ha : (a.val : ℤ) ≡ (x.val : ℤ) [ZMOD (p ^ r : ℕ)] :=
    intResidue_modEq (p ^ r) (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) _
  dsimp [positiveResidue, a]
  split_ifs with h
  · have hzero : ((p ^ r : ℕ) : ℤ) ≡ 0 [ZMOD (p ^ r : ℕ)] := by
      apply Int.modEq_iff_dvd.mpr
      simpa using (show (p ^ r : ℤ) ∣ (p ^ r : ℤ) from dvd_rfl)
    have ha' : (0 : ℤ) ≡ (x.val : ℤ) [ZMOD (p ^ r : ℕ)] := by
      have hval : a.val = 0 := h
      have ha'' := ha
      rw [hval] at ha''
      exact ha''
    exact hzero.trans ha'
  · simpa [h] using ha

lemma positiveResidue_modEq_prime {p r P : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (x : Fin (P + 1)) :
    ((positiveResidue (p := p) (r := r) hp x).val : ℤ) ≡ (x.val : ℤ) [ZMOD (p : ℕ)] := by
  have hpow := positiveResidue_modEq (r := r) hp x
  have hdvd : (p : ℤ) ∣ (p ^ r : ℤ) := by
    simpa using (dvd_pow_self (p : ℤ) (Nat.ne_of_gt hR))
  exact Int.ModEq.of_dvd (show (p : ℤ) ∣ (p ^ r : ℤ) by exact hdvd) hpow

/-- Split the full source tuple into the first `k-d` free coordinates and
last `d` fixed coordinates, exactly as the p.18 source point does. -/
def canonicalSourcePoint {p r k d P : ℕ} (hdk : d ≤ k)
    (hp : p.Prime) (z : Fin k → Fin (P + 1)) :
    sourcePoint p r (k - d) d :=
  (fun i => positiveResidue (p := p) (r := r) hp (z ⟨i.val, by omega⟩),
    fun i => positiveResidue (p := p) (r := r) hp
      (z ⟨(k - d) + i.val, by omega⟩))

lemma canonicalSourcePoint_positive {p r k d P : ℕ} (hdk : d ≤ k)
    (hp : p.Prime) (z : Fin k → Fin (P + 1)) :
    MAPFordCoarseP18Fiber.intervalPositive (q := p ^ r)
      (canonicalSourcePoint hdk hp z).1 ∧
    MAPFordCoarseP18Fiber.intervalPositive (q := p ^ r)
      (canonicalSourcePoint hdk hp z).2 := by
  have hpos : ∀ x : Fin (P + 1),
      1 ≤ (positiveResidue (p := p) (r := r) hp x).val := by
    intro x
    dsimp [positiveResidue]
    split_ifs <;> omega
  constructor
  · intro i
    exact hpos _
  · intro i
    exact hpos _

private lemma polynomial_eval_modEq {p : ℕ} (f : Polynomial ℤ) {a b : ℤ}
    (hab : a ≡ b [ZMOD (p : ℤ)]) :
    f.eval a ≡ f.eval b [ZMOD (p : ℤ)] := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simpa only [Polynomial.eval_add] using hf.add hg
  | monomial n c =>
      simpa [Polynomial.eval_monomial] using (Int.ModEq.refl c).mul (hab.pow n)

private lemma sourceJacobian_coprime_of_prime_residue
    {p r n P : ℕ} (hp : p.Prime) (phi : Fin n → Polynomial ℤ)
    (x : Fin n → Fin (P + 1)) (y : Fin n → Fin (p ^ r + 1))
    (hxy : ∀ i, (y i).val ≡ (x i).val [ZMOD (p : ℕ)])
    (hcop : p.Coprime
      (MAPFordCoarseP18Jacobian.sourceJacobian phi x).det.natAbs) :
    p.Coprime
      (MAPFordCoarseP18Jacobian.sourceJacobian phi y).det.natAbs := by
  have hpoly : ∀ (f : Polynomial ℤ) (a b : ℤ),
      a ≡ b [ZMOD (p : ℤ)] → f.eval a ≡ f.eval b [ZMOD (p : ℤ)] := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
        intro a b hab
        simpa only [Polynomial.eval_add] using (hf a b hab).add (hg a b hab)
    | monomial n c =>
        intro a b hab
        simpa [Polynomial.eval_monomial] using
          (Int.ModEq.refl c).mul (hab.pow n)
  let A : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    (phi j).derivative.eval ((x i).val : ℤ)
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    (phi j).derivative.eval ((y i).val : ℤ)
  change p.Coprime A.det.natAbs at hcop
  change p.Coprime B.det.natAbs
  have hentry : ∀ i j, (A i j : ZMod p) = (B i j : ZMod p) := by
    intro i j
    have hm := hpoly (phi j).derivative ((x i).val : ℤ) ((y i).val : ℤ)
      (hxy i).symm
    exact (ZMod.intCast_eq_intCast_iff _ _ p).2 hm
  have hdet : (A.det : ZMod p) = (B.det : ZMod p) := by
    rw [← MAPFordHenselStep.det_cast_zmod A,
      ← MAPFordHenselStep.det_cast_zmod B]
    congr 1
    ext i j
    exact hentry i j
  have hAunitNat : IsUnit (A.det.natAbs : ZMod p) :=
    (ZMod.isUnit_iff_coprime _ _).2 hcop.symm
  have hAunit : IsUnit (A.det : ZMod p) := by
    cases hD : A.det with
    | ofNat n => simpa [hD] using hAunitNat
    | negSucc n =>
        have hu : IsUnit ((n + 1 : ℕ) : ZMod p) := by
          simpa [Int.natAbs, hD] using hAunitNat
        simpa only [hD, Int.cast_negSucc] using hu.neg
  have hBunit : IsUnit (B.det : ZMod p) := by
    rw [← hdet]
    exact hAunit
  have hBunitNat : IsUnit (B.det.natAbs : ZMod p) := by
    cases hD : B.det with
    | ofNat n => simpa [hD] using hBunit
    | negSucc n =>
        have hb := hBunit
        rw [hD, Int.cast_negSucc] at hb
        simpa only [neg_neg, Int.natAbs_negSucc] using hb.neg
  exact (ZMod.isUnit_iff_coprime _ _).1 hBunitNat |>.symm

lemma canonicalSourcePoint_mask
    {p r k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime) (hR : 1 ≤ r)
    (psi : Fin k → Polynomial ℤ)
    (z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P)
      hdk hp psi) :
    p.Coprime
      (MAPFordCoarseP18Jacobian.sourceJacobian (q := p ^ r)
        (fordTailPolynomials hdk psi)
        (canonicalSourcePoint (r := r) hdk hp z.1).1).det.natAbs := by
  have hz := z.2
  have hxy : ∀ i : Fin (k - d),
      ((canonicalSourcePoint (r := r) hdk hp z.1).1 i).val ≡
        ((fordTailCoordinates hdk z.1) i).val [ZMOD (p : ℕ)] := by
    intro i
    dsimp [canonicalSourcePoint, fordTailCoordinates]
    exact positiveResidue_modEq_prime hp (by omega) (z.1 ⟨i.val, by omega⟩)
  apply sourceJacobian_coprime_of_prime_residue hp
    (fordTailPolynomials hdk psi) (fordTailCoordinates hdk z.1)
    (canonicalSourcePoint (r := r) hdk hp z.1).1 hxy
  simpa [fordPolynomialMask] using hz.2

/-- For a fixed exact transformed total, every realized full source residue
class injects into the literal mixed p.18 source fiber.  The word block is
scaled by `p*q`; no coprimality condition on `q` is used. -/
theorem realized_class_card_le
    {p r k d P Q s q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (hR : 1 ≤ r) (hr : r ≤ k)
    (psi : Fin k → Polynomial ℤ) (t : Fin k → ℤ) :
    Fintype.card {c : Fin k → Fin (p ^ r) //
      ∃ z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P)
          hdk hp psi,
        ∃ u : Fin s → Fin (Q + 1),
          (∀ j, fordSourceFrequencyAt psi z.1 j +
            fordQFrequencyAt (q := p * q) u j = t j) ∧
          (∀ j, c j = intResidue (p ^ r)
            (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
            (z.1 j).val)} ≤
      p ^ ((r - d) * (r - d - 1) / 2 + r * d + (k - d)) := by
  classical
  let n := k - d
  let phi : Fin n → Polynomial ℤ := fordTailPolynomials hdk psi
  let a : Fin n → ℕ := equationExponent r d
  let m : (i : Fin n) → Fin (p ^ a i) := fun i =>
    intResidue (p ^ a i) (Nat.pow_pos (n := a i) (Nat.Prime.pos hp))
      (t ⟨d + i.val, by omega⟩)
  let F : Type := fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P)
      hdk hp psi
  let X : Type := F × (Fin s → Fin (Q + 1))
  let cls : X → (Fin k → Fin (p ^ r)) := fun x j =>
    intResidue (p ^ r) (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
      (x.1.1 j).val
  let realized : Type := {c : Fin k → Fin (p ^ r) //
      ∃ x : X, (∀ j, fordSourceFrequencyAt psi x.1.1 j +
        fordQFrequencyAt (q := p * q) x.2 j = t j) ∧
        ∀ j, c j = cls x j}
  let inject : realized → mixedSourceBstar hp hR phi m := by
    intro c
    let x := Classical.choose c.2
    have hx := Classical.choose_spec c.2
    let zbar := canonicalSourcePoint (r := r) hdk hp x.1.1
    have hpos := canonicalSourcePoint_positive (r := r) hdk hp x.1.1
    have hmask := canonicalSourcePoint_mask (r := r) hdk hp hR psi x.1
    have hcong : ∀ i : Fin n,
        freeSum phi zbar i + fixedSum phi zbar i ≡
          (m i).val [ZMOD (p ^ a i : ℕ)] := by
      intro i
      have hj := MAPFordScaledPowerCongruence.source_modEq_total p q r psi
        x.1.1 x.2 ⟨d + i.val, by omega⟩
      have hjt := hj
      rw [hx.1 ⟨d + i.val, by omega⟩] at hjt
      have hfree : freeSum phi zbar i ≡
          (∑ j : Fin n, (phi i).eval
            ((x.1.1 ⟨j.val, by omega⟩).val : ℤ))
            [ZMOD (p ^ a i : ℕ)] := by
        dsimp [freeSum, zbar, canonicalSourcePoint]
        apply Int.ModEq.sum
        intro j hj
        have hmodr := positiveResidue_modEq (r := r) hp
          (x.1.1 ⟨j.val, by omega⟩)
        have hdvd : (p ^ a i : ℤ) ∣ (p ^ r : ℤ) := by
          exact_mod_cast Nat.pow_dvd_pow p
            (MAPFordP18MixedInjection.equationExponent_le p r n d i)
        apply polynomial_eval_modEq
        exact Int.ModEq.of_dvd hdvd hmodr
      have hfixed : fixedSum phi zbar i ≡
          (∑ j : Fin d, (phi i).eval
            ((x.1.1 ⟨n + j.val, by omega⟩).val : ℤ))
            [ZMOD (p ^ a i : ℕ)] := by
        dsimp [fixedSum, zbar, canonicalSourcePoint]
        apply Int.ModEq.sum
        intro j hj
        have hmodr := positiveResidue_modEq (r := r) hp
          (x.1.1 ⟨n + j.val, by omega⟩)
        have hdvd : (p ^ a i : ℤ) ∣ (p ^ r : ℤ) := by
          exact_mod_cast Nat.pow_dvd_pow p
            (MAPFordP18MixedInjection.equationExponent_le p r n d i)
        apply polynomial_eval_modEq
        exact Int.ModEq.of_dvd hdvd hmodr
      have hsource : fordSourceFrequencyAt psi x.1.1 ⟨d + i.val, by omega⟩ ≡
          freeSum phi zbar i + fixedSum phi zbar i
            [ZMOD (p ^ a i : ℕ)] := by
        have hsum := hfree.add hfixed
        have hsplit : fordSourceFrequencyAt psi x.1.1 ⟨d + i.val, by omega⟩ =
            (∑ j : Fin n, (phi i).eval
              ((x.1.1 ⟨j.val, by omega⟩).val : ℤ)) +
            (∑ j : Fin d, (phi i).eval
              ((x.1.1 ⟨n + j.val, by omega⟩).val : ℤ)) := by
          change (∑ j : Fin k, (psi ⟨d + i.val, by omega⟩).eval
              ((x.1.1 j).val : ℤ)) = _
          have hk' : n + d = k := by
            dsimp [n]
            omega
          let e : Fin (n + d) ≃ Fin k := Fin.castOrderIso hk'
          calc
            (∑ j : Fin k, (psi ⟨d + i.val, by omega⟩).eval
                ((x.1.1 j).val : ℤ)) =
                ∑ j : Fin (n + d), (psi ⟨d + i.val, by omega⟩).eval
                  ((x.1.1 (e j)).val : ℤ) := by
              symm
              exact Equiv.sum_comp e
                (fun j : Fin k => (psi ⟨d + i.val, by omega⟩).eval
                  ((x.1.1 j).val : ℤ))
            _ = _ := by
              rw [Fin.sum_univ_add]
              simp [e, Fin.castOrderIso, Fin.cast, phi, fordTailPolynomials]
        rw [hsplit]
        exact hsum.symm
      have hmixed := intResidue_modEq (p ^ a i)
        (Nat.pow_pos (n := a i) (Nat.Prime.pos hp))
        (t ⟨d + i.val, by omega⟩)
      exact hsource.symm.trans hjt |>.trans hmixed.symm
    exact ⟨zbar, hpos.1, hpos.2, hcong, hmask⟩
  have hinj : Function.Injective inject := by
    intro c c' hcc
    apply Subtype.ext
    have hz := congrArg (fun w : mixedSourceBstar hp hR phi m => w.1) hcc
    have hcoordF : ∀ j : Fin (k - d), (canonicalSourcePoint (r := r) hdk hp
        (Classical.choose c.2).1.1).1 j =
        (canonicalSourcePoint (r := r) hdk hp
          (Classical.choose c'.2).1.1).1 j := by
      intro j
      have := congrArg (fun w : sourcePoint p r (k - d) d => w.1 j) hz
      exact this
    have hcoordD : ∀ j : Fin d, (canonicalSourcePoint (r := r) hdk hp
        (Classical.choose c.2).1.1).2 j =
        (canonicalSourcePoint (r := r) hdk hp
          (Classical.choose c'.2).1.1).2 j := by
      intro j
      have := congrArg (fun w : sourcePoint p r (k - d) d => w.2 j) hz
      exact this
    funext j
    have hc := (Classical.choose_spec c.2).2 j
    have hc' := (Classical.choose_spec c'.2).2 j
    rw [hc, hc']
    change intResidue (p ^ r)
        (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
        ((Classical.choose c.2).1.1 j).val =
      intResidue (p ^ r)
        (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
        ((Classical.choose c'.2).1.1 j).val
    by_cases hj : j.val < k - d
    · have h := hcoordF ⟨j.val, hj⟩
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [canonicalSourcePoint, positiveResidue] at hv
      split_ifs at hv <;> omega
    · have hj' : k - d ≤ j.val := Nat.le_of_not_gt hj
      have h := hcoordD ⟨j.val - (k - d), by omega⟩
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [canonicalSourcePoint, positiveResidue] at hv
      simp [Nat.add_sub_of_le hj'] at hv
      split_ifs at hv <;> omega
  have hcard := Fintype.card_le_of_injective inject hinj
  simpa [realized, X, cls, n, phi, a, m] using
    hcard.trans (MAPFordMixedSourceCount.card_sourceBstar_kd_le
      hp hR hdk hr phi m)

end FordRealizedClassBound

#print axioms FordRealizedClassBound.realized_class_card_le
