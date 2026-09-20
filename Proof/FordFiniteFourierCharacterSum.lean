import FordFiniteFourierOrthogonality

open scoped BigOperators ZMod
open Finset

namespace MAPFordFiniteFourierCharacterSum
noncomputable section
open MAPFordFiniteFourierOrthogonality

lemma sum_prod_stdAddChar {L k : ℕ} [NeZero L]
    (freq : Fin k → ZMod L) :
    (∑ alpha : Fin k → ZMod L,
      ∏ j : Fin k, ZMod.stdAddChar (alpha j * freq j)) =
      ∏ j : Fin k, ∑ a : ZMod L, ZMod.stdAddChar (a * freq j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      let E := Fin.consEquiv (fun _ : Fin (k + 1) => ZMod L)
      rw [← E.sum_comp]
      rw [show
        (∑ x : (ZMod L) × (Fin k → ZMod L),
          ∏ j : Fin (k + 1),
            ZMod.stdAddChar ((E x) j * freq j)) =
          ∑ a : ZMod L, ∑ tail : Fin k → ZMod L,
            ∏ j : Fin (k + 1),
              ZMod.stdAddChar ((E (a, tail)) j * freq j) by
          simpa using (Fintype.sum_prod_type'
            (fun a : ZMod L => fun tail : Fin k → ZMod L =>
              ∏ j : Fin (k + 1),
                ZMod.stdAddChar ((E (a, tail)) j * freq j)))]
      simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero,
        Fin.cons_succ]
      calc
        (∑ a : ZMod L, ∑ tail : Fin k → ZMod L,
            ZMod.stdAddChar (a * freq 0) *
              ∏ i : Fin k, ZMod.stdAddChar (tail i * freq i.succ)) =
            ∑ a : ZMod L, ZMod.stdAddChar (a * freq 0) *
              (∑ tail : Fin k → ZMod L,
                ∏ i : Fin k, ZMod.stdAddChar (tail i * freq i.succ)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = (∑ a : ZMod L, ZMod.stdAddChar (a * freq 0)) *
              ∏ i : Fin k, ∑ a : ZMod L,
                ZMod.stdAddChar (a * freq i.succ) := by
          rw [ih (fun i => freq i.succ)]
          rw [Finset.sum_mul]

lemma prod_stdAddChar_sum {L k : ℕ} [NeZero L]
    (freq : Fin k → ZMod L) :
    (∏ j : Fin k, ∑ a : ZMod L, ZMod.stdAddChar (a * freq j)) =
      if (∀ j, freq j = 0) then (L : ℂ) ^ k else 0 := by
  classical
  by_cases hzero : ∀ j, freq j = 0
  · simp [hzero]
  · obtain ⟨j, hj⟩ := not_forall.mp hzero
    have hfactor : (∑ a : ZMod L, ZMod.stdAddChar (a * freq j)) = 0 := by
      rw [stdAddChar_sum_mul]
      simp [hj]
    rw [Finset.prod_eq_zero (mem_univ j) hfactor]
    simp [hzero]

/-- Exact vector additive-character orthogonality on `(ZMod L)^k`. -/
theorem vector_character_sum {L k : ℕ} [NeZero L]
    (freq : Fin k → ZMod L) :
    (∑ alpha : Fin k → ZMod L,
      ∏ j : Fin k, ZMod.stdAddChar (alpha j * freq j)) =
      if (∀ j, freq j = 0) then (L : ℂ) ^ k else 0 := by
  exact (sum_prod_stdAddChar freq).trans (prod_stdAddChar_sum freq)

/-- Summing the vector character over an arbitrary finite masked carrier gives
`L^k` times the exact zero-frequency cardinality. -/
theorem finite_masked_character_count
    {L k : ℕ} [NeZero L] {R : Type*} [Fintype R]
    (freq : R → Fin k → ZMod L) :
    (∑ alpha : Fin k → ZMod L,
      ∑ r : R, ∏ j : Fin k,
        ZMod.stdAddChar (alpha j * freq r j)) =
      (L : ℂ) ^ k * Fintype.card {r : R // ∀ j, freq r j = 0} := by
  rw [Finset.sum_comm]
  simp_rw [vector_character_sum]
  have hsum :
      (∑ r : R, if ∀ j, freq r j = 0 then (L : ℂ) ^ k else 0) =
        (L : ℂ) ^ k * Fintype.card {r : R // ∀ j, freq r j = 0} := by
    calc
      (∑ r : R, if ∀ j, freq r j = 0 then (L : ℂ) ^ k else 0) =
          ∑ r : R, (L : ℂ) ^ k *
            (if ∀ j, freq r j = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        split_ifs <;> ring
      _ = (L : ℂ) ^ k *
            ∑ r : R, (if ∀ j, freq r j = 0 then 1 else 0) := by
        rw [Finset.mul_sum]
      _ = (L : ℂ) ^ k * Fintype.card {r : R // ∀ j, freq r j = 0} := by
        rw [Finset.sum_boole, Fintype.card_subtype]
  exact hsum

/-- Integer-frequency form: under the literal no-aliasing bound, the finite
character sum counts the original integer zero system, with normalization
exactly `L^k`. -/
theorem finite_masked_integer_character_count
    {L k : ℕ} [NeZero L] {R : Type*} [Fintype R]
    (freq : R → Fin k → ℤ)
    (hbound : ∀ r j, |freq r j| < (L : ℤ)) :
    (∑ alpha : Fin k → ZMod L,
      ∑ r : R, ∏ j : Fin k,
        ZMod.stdAddChar (alpha j * (freq r j : ZMod L))) =
      (L : ℂ) ^ k * Fintype.card {r : R // ∀ j, freq r j = 0} := by
  let fmod : R → Fin k → ZMod L := fun r j => freq r j
  have hmod := finite_masked_character_count (L := L) (k := k) fmod
  let e : {r : R // ∀ j, fmod r j = 0} ≃
      {r : R // ∀ j, freq r j = 0} :=
    { toFun := fun r =>
        ⟨r.1, (frequency_mod_zero_iff (L := L) (freq := freq r)
          (fun j => hbound r j)).1 r.2⟩
      invFun := fun r =>
        ⟨r.1, (frequency_mod_zero_iff (L := L) (freq := freq r)
          (fun j => hbound r j)).2 r.2⟩
      left_inv := by intro r; rfl
      right_inv := by intro r; rfl }
  have hcard := Fintype.card_congr e
  rw [hcard] at hmod
  simpa [fmod] using hmod

end
end MAPFordFiniteFourierCharacterSum

#print axioms MAPFordFiniteFourierCharacterSum.vector_character_sum
#print axioms MAPFordFiniteFourierCharacterSum.finite_masked_character_count
#print axioms MAPFordFiniteFourierCharacterSum.finite_masked_integer_character_count
