import FordP16ResidueHolder

open scoped BigOperators

namespace MAPFordP16ResidueAggregation
noncomputable section

open MAPFordP16PowerFiber MAPFordP16ResidueHolder

def powerTarget {p s d : ℕ} [NeZero p] (c : Fin s → ZMod p) : Fin d → ZMod p :=
  fun j => ∑ i : Fin s, c i ^ (j.val + 1)

def allTargetSigma {p s d : ℕ} [NeZero p] : Type :=
  Sigma (fun t : Fin d → ZMod p =>
    powerFiberTruncated (p := p) (s := s) (d := d) t)

instance allTargetSigmaFintype {p s d : ℕ} [NeZero p] : Fintype (allTargetSigma (p := p) (s := s) (d := d)) := by
  classical
  dsimp [allTargetSigma]
  infer_instance

def targetFiber {p s d : ℕ} [NeZero p] (t : Fin d → ZMod p) : Type :=
  {c : Fin s → ZMod p // powerTarget c = t}

def targetFiberEquiv {p s d : ℕ} [NeZero p] (t : Fin d → ZMod p) :
    targetFiber (p := p) (s := s) (d := d) t ≃
      powerFiberTruncated (p := p) (s := s) (d := d) t where
  toFun c := ⟨c.1, by
    intro j
    exact congrFun c.2 j⟩
  invFun c := ⟨c.1, by
    funext j
    exact c.2 j⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; rfl

def allTargetSigmaEquiv {p s d : ℕ} [NeZero p] :
    allTargetSigma (p := p) (s := s) (d := d) ≃ (Fin s → ZMod p) :=
  (Equiv.sigmaCongrRight (fun t => targetFiberEquiv (p := p) (s := s) (d := d) t)).symm.trans
    (Equiv.sigmaFiberEquiv (powerTarget (p := p) (s := s) (d := d)))

lemma sum_over_targets_eq_sum_over_tuples {p s d : ℕ} [NeZero p]
    (f : (Fin s → ZMod p) → ℝ) :
    ∑ t : Fin d → ZMod p,
      ∑ c : powerFiberTruncated (p := p) (s := s) (d := d) t, f c.1 =
      ∑ c : Fin s → ZMod p, f c := by
  let e := allTargetSigmaEquiv (p := p) (s := s) (d := d)
  have hsigma :
      (∑ x : allTargetSigma (p := p) (s := s) (d := d), f x.2.1) =
        ∑ t : Fin d → ZMod p,
          ∑ c : powerFiberTruncated (p := p) (s := s) (d := d) t, f c.1 := by
    simpa using!
      (Fintype.sum_sigma (fun x : allTargetSigma (p := p) (s := s) (d := d) => f x.2.1))
  rw [← hsigma]
  simpa [e] using! (Equiv.sum_comp e f)

lemma sum_coordinate_weights {p s : ℕ} [NeZero p] (hs : 0 < s) (h : ZMod p → ℝ) :
    ∑ c : Fin s → ZMod p, ∑ i : Fin s, h (c i) =
      (s : ℝ) * p ^ (s-1) * ∑ a : ZMod p, h a := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst s
        simp only [Nat.zero_add, Nat.cast_one, Nat.add_sub_cancel, pow_zero, one_mul]
        let E := Fin.consEquiv (fun _ : Fin 1 => ZMod p)
        rw [← E.sum_comp]
        simpa [E] using! (Fintype.sum_prod_type'
          (fun x : ZMod p => fun _y : Fin 0 → ZMod p => h x))
      · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
        have htail := ih hspos
        let E := Fin.consEquiv (fun _ : Fin (s+1) => ZMod p)
        have hrewrite :
            (∑ c : Fin (s+1) → ZMod p, ∑ i : Fin (s+1), h (c i)) =
              ∑ x : (ZMod p) × (Fin s → ZMod p),
                (h x.1 + ∑ i : Fin s, h (x.2 i)) := by
          rw [← E.sum_comp]
          apply Finset.sum_congr rfl
          intro x hx
          simp [E, Fin.sum_univ_succ, Fin.consEquiv_apply]
        rw [hrewrite]
        have hprod :
            (∑ x : (ZMod p) × (Fin s → ZMod p),
              (h x.1 + ∑ i : Fin s, h (x.2 i))) =
              ∑ x : ZMod p, ∑ y : Fin s → ZMod p,
                (h x + ∑ i : Fin s, h (y i)) := by
          simpa using (Fintype.sum_prod_type'
            (fun x : ZMod p => fun y : Fin s → ZMod p =>
              h x + ∑ i : Fin s, h (y i)))
        rw [hprod]
        simp only [Finset.sum_add_distrib, Finset.sum_const_zero]
        have hsumA : (∑ x : ZMod p, ∑ _y : Fin s → ZMod p, h x) =
            (p ^ s : ℕ) * ∑ x : ZMod p, h x := by
          simp [Fintype.card_pi_const, ZMod.card, Finset.mul_sum]
        have hsumTail : (∑ x : ZMod p, ∑ y : Fin s → ZMod p,
            ∑ i : Fin s, h (y i)) =
            p * ∑ y : Fin s → ZMod p, ∑ i : Fin s, h (y i) := by
          simp [ZMod.card]
        rw [hsumA, hsumTail]
        have houter : s + 1 - 1 = s := by omega
        rw [houter, htail]
        have hpows : (p : ℝ) ^ s = (p : ℝ) * (p : ℝ) ^ (s-1) := by
          calc
            (p : ℝ) ^ s = (p : ℝ) ^ ((s-1) + 1) := by congr 1 <;> omega
            _ = (p : ℝ) * (p : ℝ) ^ (s-1) := by rw [pow_succ']
        push_cast
        rw [hpows]
        ring

theorem residueSum_targets_holder {p s d : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (g : ZMod p → ℂ) :
    ∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
      (Nat.factorial d * p ^ (2*s-d-1) : ℝ) *
        ∑ a : ZMod p, ‖g a‖ ^ (2*s) := by
  let h : ZMod p → ℝ := fun a => ‖g a‖ ^ (2*s)
  let F : ℝ := (Nat.factorial d * p ^ (s-d) : ℝ)
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum_holder :
      ∑ target : Fin d → ZMod p,
        (s : ℝ) * ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
      ∑ target : Fin d → ZMod p,
        F * (∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
          ∑ i : Fin s, h (c.1 i)) := by
    exact Finset.sum_le_sum (fun target _ => by
      simpa [F, h] using
        (residueSum_holder hp hd hds hs g target))
  have hleft :
      ∑ target : Fin d → ZMod p,
        (s : ℝ) * ‖residueSum (s := s) (d := d) g target‖ ^ 2 =
      (s : ℝ) * ∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) g target‖ ^ 2 := by
    rw [Finset.mul_sum]
  have hright_sum :
      (∑ target : Fin d → ZMod p,
        F * (∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
          ∑ i : Fin s, h (c.1 i))) =
      F * ((s : ℝ) * p ^ (s-1) * ∑ a : ZMod p, h a) := by
    calc
      (∑ target : Fin d → ZMod p,
        F * (∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
          ∑ i : Fin s, h (c.1 i))) =
          F * (∑ target : Fin d → ZMod p,
            ∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
              ∑ i : Fin s, h (c.1 i)) := by rw [Finset.mul_sum]
      _ = F * (∑ c : Fin s → ZMod p, ∑ i : Fin s, h (c i)) := by
        congr 1
        exact sum_over_targets_eq_sum_over_tuples (f := fun c => ∑ i : Fin s, h (c i))
      _ = F * ((s : ℝ) * p ^ (s-1) * ∑ a : ZMod p, h a) := by
        rw [sum_coordinate_weights hs h]
  have hmain :
      (s : ℝ) * ∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
      F * ((s : ℝ) * p ^ (s-1) * ∑ a : ZMod p, h a) := by
    rw [← hleft]
    rw [← hright_sum]
    exact hsum_holder
  have hcancel :
      ∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
      (F * p ^ (s-1)) * ∑ a : ZMod p, h a := by
    exact le_of_mul_le_mul_left
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmain) hsreal
  calc
    ∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
      (F * p ^ (s-1)) * ∑ a : ZMod p, h a := hcancel
    _ = (Nat.factorial d * p ^ (2*s-d-1) : ℝ) *
        ∑ a : ZMod p, ‖g a‖ ^ (2*s) := by
      dsimp [F, h]
      have hexp : (s-d) + (s-1) = 2*s-d-1 := by omega
      calc
        (↑d.factorial * ↑p ^ (s-d) * ↑p ^ (s-1)) *
            ∑ a : ZMod p, ‖g a‖ ^ (2*s) =
            ↑d.factorial * (↑p ^ (s-d) * ↑p ^ (s-1)) *
              ∑ a : ZMod p, ‖g a‖ ^ (2*s) := by ring
        _ = (↑d.factorial * ↑p ^ ((s-d) + (s-1))) *
              ∑ a : ZMod p, ‖g a‖ ^ (2*s) := by rw [← pow_add]
        _ = (↑d.factorial * ↑p ^ (2*s-d-1)) *
              ∑ a : ZMod p, ‖g a‖ ^ (2*s) := by rw [hexp]

end
end MAPFordP16ResidueAggregation

#print axioms MAPFordP16ResidueAggregation.residueSum_targets_holder
