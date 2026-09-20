import FordCompleteSystemMoment
import FordKPointEnergy

open scoped BigOperators
open MAPFordCompleteSystemMoment
open FordBoundaryCountGeometry
open MAPFordP16SourceCountBridge
open MAPFordP16FiniteFourierBridge
open FordKPointEnergy
namespace FordCompleteMomentBridge
noncomputable section

abbrev PowerWord {s Q : ℕ} := FordKPointEnergy.PowerWord (s := s) (Q := Q)
abbrev PairQ {s Q : ℕ} := (Fin s → Fin Q) × (Fin s → Fin Q)

/-- The positive interval `{1,...,Q}` is equivalent to `Fin Q` by subtracting one. -/
def positiveFinEquiv (Q : ℕ) : fordFinitePositiveX (Q := Q) ≃ Fin Q :=
  { toFun := fun x => ⟨x.1.val - 1, by
        have hx := x.1.isLt
        have hxpos := x.2
        omega⟩
    invFun := fun x => ⟨⟨x.val + 1, by
        have hx := x.isLt
        exact Nat.succ_lt_succ hx⟩,
      Nat.succ_le_succ (Nat.zero_le _)⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Fin.ext
      dsimp
      have hxpos := x.2
      exact Nat.sub_add_cancel hxpos
    right_inv := by
      intro x
      apply Fin.ext
      dsimp
      }

lemma positiveFinEquiv_val_add_one {Q : ℕ} (x : fordFinitePositiveX (Q := Q)) :
    (positiveFinEquiv Q x).val + 1 = x.val := by
  dsimp [positiveFinEquiv]
  have hxpos := x.2
  exact Nat.sub_add_cancel hxpos

def wordToFin {s Q : ℕ} : PowerWord (s := s) (Q := Q) → (Fin s → Fin Q) :=
  fun x i => positiveFinEquiv Q (x i)

def wordFromFin {s Q : ℕ} : (Fin s → Fin Q) → PowerWord (s := s) (Q := Q) :=
  fun x i => (positiveFinEquiv Q).symm (x i)

lemma wordFromFin_toFin {s Q : ℕ} (x : PowerWord (s := s) (Q := Q)) :
    wordFromFin (wordToFin x) = x := by
  funext i
  exact (positiveFinEquiv Q).left_inv (x i)

lemma wordToFin_fromFin {s Q : ℕ} (x : Fin s → Fin Q) :
    wordToFin (wordFromFin x) = x := by
  funext i
  exact (positiveFinEquiv Q).right_inv (x i)

def pairToFin {s Q : ℕ} : PowerWord (s := s) (Q := Q) × PowerWord (s := s) (Q := Q) → PairQ (s := s) (Q := Q) :=
  fun xy => (wordToFin xy.1, wordToFin xy.2)

def pairFromFin {s Q : ℕ} : PairQ (s := s) (Q := Q) → PowerWord (s := s) (Q := Q) × PowerWord (s := s) (Q := Q) :=
  fun xy => (wordFromFin xy.1, wordFromFin xy.2)

lemma pairFromFin_toFin {s Q : ℕ} (x : PowerWord (s := s) (Q := Q) × PowerWord (s := s) (Q := Q)) :
    pairFromFin (pairToFin x) = x := by
  exact Prod.ext (wordFromFin_toFin x.1) (wordFromFin_toFin x.2)

lemma pairToFin_fromFin {s Q : ℕ} (x : PairQ (s := s) (Q := Q)) :
    pairToFin (pairFromFin x) = x := by
  exact Prod.ext (wordToFin_fromFin x.1) (wordToFin_fromFin x.2)

def allPowerEq {s k Q : ℕ} (xy : PairQ (s := s) (Q := Q)) : Prop :=
  ∀ j : Fin k,
    (∑ i : Fin s, ((xy.1 i).val + 1) ^ (j.val + 1)) =
      ∑ i : Fin s, ((xy.2 i).val + 1) ^ (j.val + 1)

lemma allPowerEq_pairToFin_iff
    {s Q : ℕ} (k : ℕ) (q : ℕ) (hq : 0 < q)
    (x y : PowerWord (s := s) (Q := Q)) :
    FordKPointEnergy.baseFreq (k := k) (q := q) x =
        FordKPointEnergy.baseFreq (k := k) (q := q) y ↔
      allPowerEq (k := k) (pairToFin (x, y)) := by
  constructor
  · intro h j
    have hj := congrFun h j
    simp only [FordKPointEnergy.baseFreq, MAPFordP16FiniteFourierBridge.fordQFrequencyAt,
      MAPFordP16FiniteFourierBridge.fordQScalarFrequency] at hj
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hj
    have hqpow : (q : ℤ) ^ (j.val + 1) ≠ 0 := by
      apply pow_ne_zero
      exact_mod_cast (Nat.ne_of_gt hq)
    have hpow := mul_left_cancel₀ hqpow hj
    have hnat :
        (∑ i : Fin s, (x i).1.val ^ (j.val + 1)) =
          ∑ i : Fin s, (y i).1.val ^ (j.val + 1) := by
      exact_mod_cast hpow
    have hpow' :
        (∑ i : Fin s, ((x i).1.val : ℤ) ^ (j.val + 1)) =
          ∑ i : Fin s, ((y i).1.val : ℤ) ^ (j.val + 1) := by
      exact_mod_cast hnat
    simpa [allPowerEq, pairToFin, wordToFin,
      positiveFinEquiv_val_add_one] using hnat
  · intro h
    funext j
    have hj := h j
    have hpow :
        (∑ i : Fin s, (((x i).1 : ℤ)) ^ (j.val + 1)) =
          ∑ i : Fin s, (((y i).1 : ℤ)) ^ (j.val + 1) := by
      have hj' := hj
      simp [allPowerEq, pairToFin, wordToFin,
        positiveFinEquiv_val_add_one] at hj'
      have hnat :
          (∑ i : Fin s, (x i).1.val ^ (j.val + 1)) =
            ∑ i : Fin s, (y i).1.val ^ (j.val + 1) := by
        simpa [pairToFin, wordToFin,
          positiveFinEquiv_val_add_one] using hj'
      exact_mod_cast hnat
    simp only [FordKPointEnergy.baseFreq, MAPFordP16FiniteFourierBridge.fordQFrequencyAt,
      MAPFordP16FiniteFourierBridge.fordQScalarFrequency]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hpow]

lemma powersFin_iff_Icc
    {s k Q : ℕ} (xy : PairQ (s := s) (Q := Q)) :
    allPowerEq (k := k) xy ↔
      ∀ j ∈ Finset.Icc 1 k,
        (∑ i : Fin s, ((xy.1 i).val + 1) ^ j) =
          ∑ i : Fin s, ((xy.2 i).val + 1) ^ j := by
  constructor
  · intro h j hj
    have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjle : j ≤ k := (Finset.mem_Icc.mp hj).2
    let jj : Fin k := ⟨j - 1, by omega⟩
    have hh := h jj
    have hsub : j - 1 + 1 = j := by omega
    simpa [jj, hsub] using hh
  · intro h jj
    have hjmem : jj.val + 1 ∈ Finset.Icc 1 k := by
      apply Finset.mem_Icc.mpr
      omega
    have hh := h (jj.val + 1) hjmem
    simpa [Nat.sub_add_cancel (show 1 ≤ jj.val + 1 by omega)] using hh

def completeSolutions {s k Q : ℕ} : Type :=
  {xy : PairQ (s := s) (Q := Q) // allPowerEq (k := k) xy}

instance completeSolutionsFintype {s k Q : ℕ} : Fintype (completeSolutions (s := s) (k := k) (Q := Q)) := by
  classical
  dsimp [completeSolutions]
  infer_instance

lemma completeMoment_eq_card_completeSolutions (s k Q : ℕ) :
    completeMoment s k Q = Fintype.card (completeSolutions (s := s) (k := k) (Q := Q)) := by
  classical
  unfold completeMoment
  symm
  change Fintype.card {xy : PairQ (s := s) (Q := Q) // allPowerEq (k := k) xy} =
    (Finset.univ.filter (fun xy : PairQ (s := s) (Q := Q) =>
    ∀ j ∈ Finset.Icc 1 k,
      (∑ i : Fin s, ((xy.1 i).val + 1) ^ j) =
        ∑ i : Fin s, ((xy.2 i).val + 1) ^ j)).card
  let e :
      {xy : PairQ (s := s) (Q := Q) // allPowerEq (k := k) xy} ≃
        {xy : PairQ (s := s) (Q := Q) // ∀ j ∈ Finset.Icc 1 k,
          (∑ i : Fin s, ((xy.1 i).val + 1) ^ j) =
            ∑ i : Fin s, ((xy.2 i).val + 1) ^ j} :=
    { toFun := fun r => ⟨r.1, (powersFin_iff_Icc r.1).mp r.2⟩
      invFun := fun r => ⟨r.1, (powersFin_iff_Icc r.1).mpr r.2⟩
      left_inv := by intro r; rfl
      right_inv := by intro r; rfl }
  have hc := Fintype.card_congr e
  rw [hc]
  let fset := Finset.univ.filter (fun xy : PairQ (s := s) (Q := Q) =>
    ∀ j ∈ Finset.Icc 1 k,
      (∑ i : Fin s, ((xy.1 i).val + 1) ^ j) =
        ∑ i : Fin s, ((xy.2 i).val + 1) ^ j)
  let ef :
      {xy : PairQ (s := s) (Q := Q) // ∀ j ∈ Finset.Icc 1 k,
        (∑ i : Fin s, ((xy.1 i).val + 1) ^ j) =
          ∑ i : Fin s, ((xy.2 i).val + 1) ^ j} ≃
        ↥fset :=
    { toFun := fun r => ⟨r.1, by
          simp only [fset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact r.2⟩
      invFun := fun r => ⟨r.1, by
          simpa only [fset, Finset.mem_filter, Finset.mem_univ, true_and] using r.2⟩
      left_inv := by intro r; rfl
      right_inv := by intro r; rfl }
  exact (Fintype.card_congr ef).trans (Fintype.card_coe fset)

/-- The complete-system moment is exactly the zero-base-frequency count after
identifying positive words with `Fin Q`; cancellation is over `ℤ` and only
uses `q > 0`. -/
theorem completeMoment_eq_baseZero_card
    {s k Q q : ℕ} (hq : 0 < q) :
    completeMoment s k Q =
      Fintype.card (BaseZero
        (FordKPointEnergy.baseFreq (s := s) (k := k) (Q := Q) (q := q))) := by
  classical
  rw [completeMoment_eq_card_completeSolutions]
  let e :
      BaseZero (FordKPointEnergy.baseFreq (s := s) (k := k) (Q := Q) (q := q)) ≃
        completeSolutions (s := s) (k := k) (Q := Q) :=
    { toFun := fun r =>
        ⟨pairToFin r.1, (allPowerEq_pairToFin_iff k q hq r.1.1 r.1.2).mp r.2⟩
      invFun := fun r =>
        ⟨pairFromFin r.1, (allPowerEq_pairToFin_iff k q hq _ _).mpr r.2⟩
      left_inv := by
        intro r
        apply Subtype.ext
        exact pairFromFin_toFin r.1
      right_inv := by
        intro r
        apply Subtype.ext
        exact pairToFin_fromFin r.1 }
  exact (Fintype.card_congr e).symm

end
end FordCompleteMomentBridge

#print axioms FordCompleteMomentBridge.completeMoment_eq_baseZero_card
