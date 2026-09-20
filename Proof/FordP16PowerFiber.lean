import FordFiniteFieldBase

open scoped BigOperators

/-!
# Ford p.16 consecutive-power residue fiber

The source p.16 carrier fixes the last `s-d` residues and uses Newton's
identities on the first `d` residues.  This file records the literal carrier
and the finite encoding into a tail tuple and a permutation.  The resulting
`d! * p^(s-d)` count is independent of the analytic Lemma 3.2 estimates.
-/

namespace MAPFordP16PowerFiber
noncomputable section

open MAPFordFiniteFieldBase

def powerFiberTruncated {p s d : ℕ} [NeZero p] (target : Fin d → ZMod p) : Type :=
  {c : Fin s → ZMod p //
    ∀ j : Fin d, (∑ i : Fin s, c i ^ (j.val + 1)) = target j}

instance powerFiberTruncatedFintype {p s d : ℕ} [NeZero p]
    (target : Fin d → ZMod p) :
    Fintype (powerFiberTruncated (p := p) (s := s) (d := d) target) := by
  classical
  dsimp [powerFiberTruncated]
  infer_instance

def prefixOf {p s d : ℕ} (hds : d ≤ s) (c : Fin s → ZMod p) : Fin d → ZMod p :=
  fun i => c (Fin.cast (by omega : d + (s-d) = s) (Fin.castAdd (s-d) i))

def tailOf {p s d : ℕ} (hds : d ≤ s) (c : Fin s → ZMod p) :
    Fin (s-d) → ZMod p :=
  fun i => c (Fin.cast (by omega : d + (s-d) = s) (Fin.natAdd d i))

lemma power_sum_split {p s d : ℕ} [NeZero p] (hds : d ≤ s)
    (c : Fin s → ZMod p) (j : Fin d) :
    (∑ i : Fin s, c i ^ (j.val + 1)) =
      (∑ i : Fin d, prefixOf hds c i ^ (j.val + 1)) +
        ∑ i : Fin (s-d), tailOf hds c i ^ (j.val + 1) := by
  let e : d + (s-d) = s := by omega
  let g : Fin s → ZMod p := fun i => c i ^ (j.val + 1)
  have h := Fin.sum_univ_add
    (fun i : Fin (d + (s-d)) => c (Fin.cast e i) ^ (j.val + 1))
  have heq : (∑ i : Fin (d + (s-d)), g (Fin.cast e i)) = ∑ i : Fin s, g i :=
    Equiv.sum_comp (finCongr e) g
  rw [heq] at h
  simpa [prefixOf, tailOf, e, g] using h

def truncatedEncode {p s d : ℕ} [NeZero p] {target : Fin d → ZMod p} (hds : d ≤ s)
    (c : powerFiberTruncated (p := p) (s := s) (d := d) target) :
    (Fin (s-d) → ZMod p) × Equiv.Perm (Fin d) :=
  (tailOf hds c.1, zmodSort (prefixOf hds c.1))

lemma prefix_power_eq_of_same_tail {p s d : ℕ} [NeZero p]
    (hds : d ≤ s) (target : Fin d → ZMod p)
    {a b : powerFiberTruncated (p := p) (s := s) (d := d) target}
    (htail : tailOf hds a.1 = tailOf hds b.1) :
    ∀ j : Fin d, (∑ i : Fin d, prefixOf hds a.1 i ^ (j.val + 1)) =
      ∑ i : Fin d, prefixOf hds b.1 i ^ (j.val + 1) := by
  intro j
  have ha := a.2 j
  have hb := b.2 j
  rw [power_sum_split hds a.1 j] at ha
  rw [power_sum_split hds b.1 j] at hb
  calc
    (∑ i : Fin d, prefixOf hds a.1 i ^ (j.val + 1)) =
        target j - ∑ i : Fin (s-d), tailOf hds a.1 i ^ (j.val + 1) := by
          rw [← ha]
          ring
    _ = target j - ∑ i : Fin (s-d), tailOf hds b.1 i ^ (j.val + 1) := by
          rw [htail]
    _ = ∑ i : Fin d, prefixOf hds b.1 i ^ (j.val + 1) := by
          rw [← hb]
          ring

lemma prefix_tail_ext {p s d : ℕ} (hds : d ≤ s)
    {a b : Fin s → ZMod p}
    (hpref : prefixOf hds a = prefixOf hds b)
    (htail : tailOf hds a = tailOf hds b) : a = b := by
  funext i
  let e : d + (s-d) = s := by omega
  have hi : Fin.cast e (Fin.cast e.symm i) = i := by
    apply Fin.ext
    rfl
  rw [← hi]
  refine Fin.addCases ?_ ?_ (Fin.cast e.symm i)
  · intro k
    exact congrFun hpref k
  · intro k
    exact congrFun htail k

lemma truncatedEncode_injective {p s d : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (target : Fin d → ZMod p) :
    Function.Injective (truncatedEncode (target := target) hds) := by
  intro a b hab
  have htail : tailOf hds a.1 = tailOf hds b.1 := congrArg Prod.fst hab
  have hsort : zmodSort (prefixOf hds a.1) =
      zmodSort (prefixOf hds b.1) := congrArg Prod.snd hab
  have hpow : ∀ j, 1 ≤ j → j ≤ d →
      (∑ i : Fin d, prefixOf hds a.1 i ^ j) =
        ∑ i : Fin d, prefixOf hds b.1 i ^ j := by
    intro j hj1 hjd
    have h := prefix_power_eq_of_same_tail hds target htail
    let jj : Fin d := ⟨j-1, by omega⟩
    have hjj : jj.val + 1 = j := by dsimp [jj]; omega
    simpa [hjj] using h jj
  have hpref : prefixOf hds a.1 = prefixOf hds b.1 :=
    tuple_eq_of_power_eq_and_sort_eq hp hd hpow hsort
  apply Subtype.ext
  exact prefix_tail_ext hds hpref htail

theorem card_powerFiberTruncated_le {p s d : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (target : Fin d → ZMod p) :
    Fintype.card (powerFiberTruncated (p := p) (s := s) (d := d) target) ≤
      Nat.factorial d * p ^ (s-d) := by
  let f := truncatedEncode (target := target) hds
  have hc := Fintype.card_le_of_injective f
    (truncatedEncode_injective hp hd hds target)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_perm] at hc
  rw [ZMod.card] at hc
  simpa [Nat.mul_comm] using hc

end
end MAPFordP16PowerFiber

#print axioms MAPFordP16PowerFiber.card_powerFiberTruncated_le
