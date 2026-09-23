import Mathlib

/-!
# Ford consecutive-power finite-field base

Ford p. 16 applies Newton reconstruction to the first `d` power sums and
gets a `d!` fiber bound.  This module formalizes the consecutive-power case
over `ZMod p` under the explicit restriction `k < p`, which makes the Newton
coefficients `1,...,k` units.  It does not assert Ford Lemma 2.4 for arbitrary
degree tuples; those require the separate Jacobian/non-singular hypotheses.
-/
open scoped BigOperators
open Finset
noncomputable section
namespace MAPFordFiniteFieldBase

section Generic
variable {R : Type*} [Field R]

def eVal {k : ℕ} (x : Fin k → R) (n : ℕ) : R :=
  MvPolynomial.aeval x (MvPolynomial.esymm (Fin k) R n)
def pVal {k : ℕ} (x : Fin k → R) (n : ℕ) : R :=
  MvPolynomial.aeval x (MvPolynomial.psum (Fin k) R n)
def xMulti {k : ℕ} (x : Fin k → R) : Multiset R :=
  (List.ofFn x : Multiset R)

theorem psum_eval {k : ℕ} (x : Fin k → R) (j : ℕ) :
    pVal x j = ∑ i : Fin k, x i ^ j := by
  simp [pVal, MvPolynomial.psum]

theorem esymm_eval {k : ℕ} (x : Fin k → R) (n : ℕ) :
    eVal x n = (xMulti x).esymm n := by
  rw [eVal, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  congr 1
  simp [xMulti, List.ofFn_eq_map]

lemma eval_mul_esymm {k : ℕ} (x : Fin k → R) (n : ℕ) :
    (n : R) * eVal x n =
      (-1 : R) ^ (n+1) *
       ∑ a ∈ antidiagonal n with a.1 < n,
         (-1 : R)^a.1 * eVal x a.1 * pVal x a.2 := by
  have h := congrArg (MvPolynomial.aeval x)
    (MvPolynomial.mul_esymm_eq_sum (Fin k) R n)
  simpa [eVal, pVal, map_sum, map_mul, map_pow, map_natCast] using h

lemma xMulti_eq_of_pVal_eq {k : ℕ} {x y : Fin k → R}
    (hcast : ∀ n, 1 ≤ n → n ≤ k → (n : R) ≠ 0)
    (hp : ∀ j, 1 ≤ j → j ≤ k → pVal x j = pVal y j) :
    xMulti x = xMulti y := by
  have aux : ∀ n, n ≤ k → (∀ m, m < n → eVal x m = eVal y m) →
      eVal x n = eVal y n := by
    intro n hn hprev
    cases n with
    | zero => simp [eVal]
    | succ n =>
      have hx := eval_mul_esymm x (n+1)
      have hy := eval_mul_esymm y (n+1)
      have hsum :
          ∑ a ∈ antidiagonal (n+1) with a.1 < (n+1),
            (-1 : R)^a.1 * eVal x a.1 * pVal x a.2 =
          ∑ a ∈ antidiagonal (n+1) with a.1 < (n+1),
            (-1 : R)^a.1 * eVal y a.1 * pVal y a.2 := by
        apply sum_congr rfl
        intro a ha
        have hsum' := mem_antidiagonal.mp (mem_filter.mp ha).1
        have halt := (mem_filter.mp ha).2
        have hpos : 1 ≤ a.2 := by omega
        have hale : a.2 ≤ k := by omega
        have heq := hprev a.1 halt
        rw [heq, hp a.2 hpos hale]
      rw [hsum] at hx
      apply (mul_left_cancel₀ (hcast (n+1) (by omega) hn))
      exact hx.trans hy.symm
  have he : ∀ n, n ≤ k → eVal x n = eVal y n := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      apply aux n hn
      intro m hm
      exact ih m hm (by omega)
  have hpoly :
      ((xMulti x).map (fun a => Polynomial.X - Polynomial.C a)).prod =
      ((xMulti y).map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    have hcardx : (xMulti x).card = k := by simp [xMulti]
    have hcardy : (xMulti y).card = k := by simp [xMulti]
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,
      Multiset.prod_X_sub_X_eq_sum_esymm, hcardx, hcardy]
    apply sum_congr rfl
    intro j hj
    have hjk : j ≤ k := by simpa using (mem_range.mp hj)
    rw [← esymm_eval x j, ← esymm_eval y j, he j hjk]
  have hxroots :
      (((xMulti x).map (fun a => Polynomial.X - Polynomial.C a)).prod).roots = xMulti x :=
    Polynomial.roots_multiset_prod_X_sub_C _
  have hyroots :
      (((xMulti y).map (fun a => Polynomial.X - Polynomial.C a)).prod).roots = xMulti y :=
    Polynomial.roots_multiset_prod_X_sub_C _
  rw [← hxroots, ← hyroots, hpoly]

lemma sorted_val_eq_of_xMulti_eq {k : ℕ} {x y : Fin k → R}
    {val : R → ℕ} (hval_inj : Function.Injective val)
    (hm : xMulti x = xMulti y) :
    (fun i => val (x i)) ∘ Tuple.sort (fun i => val (x i)) =
      (fun i => val (y i)) ∘ Tuple.sort (fun i => val (y i)) := by
  have hmval := congrArg (Multiset.map val) hm
  have hxy : List.Perm (List.ofFn (fun i => val (x i)))
      (List.ofFn (fun i => val (y i))) := by
    apply Multiset.coe_eq_coe.mp
    convert hmval
    · simp [xMulti, List.map_ofFn]
      rfl
    · simp [xMulti, List.map_ofFn]
      rfl
  have hpx := Equiv.Perm.ofFn_comp_perm (Tuple.sort (fun i => val (x i)))
    (fun i => val (x i))
  have hpy := Equiv.Perm.ofFn_comp_perm (Tuple.sort (fun i => val (y i)))
    (fun i => val (y i))
  have hs : List.ofFn ((fun i => val (x i)) ∘ Tuple.sort (fun i => val (x i))) =
      List.ofFn ((fun i => val (y i)) ∘ Tuple.sort (fun i => val (y i))) :=
    List.Perm.eq_of_sortedLE
      (Tuple.monotone_sort (fun i => val (x i))).sortedLE_ofFn
      (Tuple.monotone_sort (fun i => val (y i))).sortedLE_ofFn
      (hpx.trans (hxy.trans hpy.symm))
  exact List.ofFn_injective hs
end Generic

section ZMod

def valTuple {p k : ℕ} (x : Fin k → ZMod p) : Fin k → ℕ := fun i => (x i).val

def zmodSort {p k : ℕ} (x : Fin k → ZMod p) : Equiv.Perm (Fin k) :=
  Tuple.sort (valTuple x)

lemma zmod_natCast_ne_zero {p k n : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hnk : n ≤ k) (hk : k < p) :
    (n : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hdiv
  have : p ≤ n := Nat.le_of_dvd (by omega) hdiv
  omega

lemma zmod_multiset_eq_of_power_eq {p k : ℕ} (hp : p.Prime) (hk : k < p)
    {x y : Fin k → ZMod p}
    (hpow : ∀ j, 1 ≤ j → j ≤ k → (∑ i, x i ^ j) = ∑ i, y i ^ j) :
    xMulti x = xMulti y := by
  letI : Fact p.Prime := ⟨hp⟩
  apply xMulti_eq_of_pVal_eq (fun n hn hnk => zmod_natCast_ne_zero hp hn hnk hk)
  simpa [psum_eval] using hpow

lemma sorted_val_eq_of_power_eq {p k : ℕ} [NeZero p] (hp : p.Prime) (hk : k < p)
    {x y : Fin k → ZMod p}
    (hpow : ∀ j, 1 ≤ j → j ≤ k → (∑ i, x i ^ j) = ∑ i, y i ^ j) :
    valTuple x ∘ zmodSort x = valTuple y ∘ zmodSort y := by
  letI : Fact p.Prime := ⟨hp⟩
  apply sorted_val_eq_of_xMulti_eq (val := ZMod.val)
    (ZMod.val_injective p)
  exact zmod_multiset_eq_of_power_eq hp hk hpow

lemma tuple_eq_of_power_eq_and_sort_eq {p k : ℕ} [NeZero p] (hp : p.Prime) (hk : k < p)
    {x y : Fin k → ZMod p}
    (hpow : ∀ j, 1 ≤ j → j ≤ k → (∑ i, x i ^ j) = ∑ i, y i ^ j)
    (hsort : zmodSort x = zmodSort y) : x = y := by
  letI : NeZero p := ‹NeZero p›
  have hs := sorted_val_eq_of_power_eq hp hk hpow
  have hs' : valTuple x ∘ zmodSort x = valTuple y ∘ zmodSort y := hs
  rw [hsort] at hs'
  have hv : valTuple x = valTuple y := by
    funext i
    have hh := congrFun hs' ((zmodSort y).symm i)
    simpa [Function.comp_apply] using hh
  funext i
  exact ZMod.val_injective p (by simpa [valTuple] using congrFun hv i)

def powerFiber (p k : ℕ) [NeZero p] (target : ℕ → ZMod p) :
    Finset (Fin k → ZMod p) := by
  classical
  exact Finset.univ.filter (fun x => ∀ j ∈ Icc 1 k,
    (∑ i : Fin k, x i ^ j) = target j)

lemma powerFiber_sort_injective {p k : ℕ} [NeZero p] (hp : p.Prime) (hk : k < p)
    (target : ℕ → ZMod p) :
    Function.Injective (fun z : powerFiber p k target => zmodSort z.1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro a b hab
  apply Subtype.ext
  have ha : ∀ j ∈ Icc 1 k,
      (∑ i : Fin k, a.1 i ^ j) = target j := by
    simpa [powerFiber] using a.2
  have hb : ∀ j ∈ Icc 1 k,
      (∑ i : Fin k, b.1 i ^ j) = target j := by
    simpa [powerFiber] using b.2
  have hpow : ∀ j, 1 ≤ j → j ≤ k →
      (∑ i : Fin k, a.1 i ^ j) = ∑ i : Fin k, b.1 i ^ j := by
    intro j hj1 hjk
    rw [ha j (mem_Icc.mpr ⟨hj1, hjk⟩), hb j (mem_Icc.mpr ⟨hj1, hjk⟩)]
  apply tuple_eq_of_power_eq_and_sort_eq hp hk hpow hab

theorem card_powerFiber_le_factorial {p k : ℕ} [NeZero p] (hp : p.Prime) (hk : k < p)
    (target : ℕ → ZMod p) :
    Fintype.card (powerFiber p k target) ≤ Nat.factorial k := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let f : powerFiber p k target → Equiv.Perm (Fin k) := fun z => zmodSort z.1
  have hf : Function.Injective f := by
    dsimp [f]
    exact powerFiber_sort_injective hp hk target
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_perm] at hc
  simpa using hc

end ZMod
end MAPFordFiniteFieldBase

#print axioms MAPFordFiniteFieldBase.card_powerFiber_le_factorial
#print axioms MAPFordFiniteFieldBase.zmod_multiset_eq_of_power_eq
