import MRTLemma29Coefficient
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace MAPMRTLemma29Proof
open scoped BigOperators
open Complex
noncomputable section
set_option maxHeartbeats 800000

lemma character_expansion_unit {q : ℕ} [NeZero q]
    (a n : ZMod q) (ha : IsUnit a) (hn : IsUnit n) :
    ZMod.stdAddChar (a * n) =
      (q.totient : ℂ)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          chi a * gaussSum chi⁻¹ ZMod.stdAddChar * chi n := by
  rw [show (∑ chi : DirichletCharacter ℂ q,
          chi a * gaussSum chi⁻¹ ZMod.stdAddChar * chi n) =
      (q.totient : ℂ) * ZMod.stdAddChar (a * n) by
    simp_rw [gaussSum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hinner (l : ZMod q) :
        (∑ chi : DirichletCharacter ℂ q,
          chi a * (chi⁻¹ l * ZMod.stdAddChar l) * chi n) =
        ZMod.stdAddChar l *
          (if l = a * n then (q.totient : ℂ) else 0) := by
      rw [mul_comm (ZMod.stdAddChar l)]
      simp_rw [show ∀ chi : DirichletCharacter ℂ q,
          chi a * (chi⁻¹ l * ZMod.stdAddChar l) * chi n =
            ZMod.stdAddChar l * (chi (Ring.inverse l) * chi (a * n)) by
        intro chi
        rw [MulChar.inv_apply, map_mul]
        ring]
      rw [← Finset.mul_sum]
      simp_rw [← map_mul]
      rw [DirichletCharacter.sum_characters_eq]
      have hinv : Ring.inverse l * (a * n) = 1 ↔ l = a * n := by
        by_cases hl : IsUnit l
        · simpa [eq_comm] using
            (Ring.inverse_mul_eq_iff_eq_mul l (a * n) 1 hl)
        · rw [Ring.inverse_non_unit l hl]
          constructor
          · intro hzero
            have hz : (0 : ZMod q) = 1 := by simpa using hzero
            letI : Subsingleton (ZMod q) := subsingleton_of_zero_eq_one hz
            exact (hl (isUnit_of_subsingleton l)).elim
          · intro heq
            exact (hl (heq ▸ (ha.mul hn))).elim
      simp only [hinv]
      split_ifs <;> ring
    simp_rw [hinner]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (a * n)]
    simp
    ring]
  have hphi : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (NeZero.pos q)))
  field_simp [hphi]

lemma finite_unit_character_expansion {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (s : Finset ℕ) (c : ℕ → ℂ)
    (hs : ∀ n ∈ s, IsUnit (n : ZMod q)) :
    (∑ n ∈ s, c n * ZMod.stdAddChar (a * (n : ZMod q))) =
      (q.totient : ℂ)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          (chi a * gaussSum chi⁻¹ ZMod.stdAddChar) *
            ∑ n ∈ s, c n * chi n := by
  have hexp (n : ℕ) (hn : n ∈ s) :=
    character_expansion_unit a (n : ZMod q) ha (hs n hn)
  calc
    (∑ n ∈ s, c n * ZMod.stdAddChar (a * (n : ZMod q))) =
        ∑ n ∈ s, c n * ((q.totient : ℂ)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            chi a * gaussSum chi⁻¹ ZMod.stdAddChar * chi n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hexp n hn]
    _ = _ := by
      have hterm (n : ℕ) :
          c n * ((q.totient : ℂ)⁻¹ *
            ∑ chi : DirichletCharacter ℂ q,
              chi a * gaussSum chi⁻¹ ZMod.stdAddChar * chi n) =
          (q.totient : ℂ)⁻¹ *
            ∑ chi : DirichletCharacter ℂ q,
              (chi a * gaussSum chi⁻¹ ZMod.stdAddChar) *
                (c n * chi n) := by
        simp_rw [Finset.mul_sum]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]

lemma finite_unit_character_bound {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (s : Finset ℕ) (c : ℕ → ℂ)
    (hs : ∀ n ∈ s, IsUnit (n : ZMod q)) :
    ‖∑ n ∈ s, c n * ZMod.stdAddChar (a * (n : ZMod q))‖ ≤
      Real.sqrt q / q.totient *
        ∑ chi : DirichletCharacter ℂ q,
          ‖∑ n ∈ s, c n * chi n‖ := by
  rw [finite_unit_character_expansion a ha s c hs]
  rw [norm_mul]
  calc
    ‖(q.totient : ℂ)⁻¹‖ *
        ‖∑ chi : DirichletCharacter ℂ q,
          (chi a * gaussSum chi⁻¹ ZMod.stdAddChar) *
            ∑ n ∈ s, c n * chi n‖ ≤
        ‖(q.totient : ℂ)⁻¹‖ *
          ∑ chi : DirichletCharacter ℂ q,
            ‖(chi a * gaussSum chi⁻¹ ZMod.stdAddChar) *
              ∑ n ∈ s, c n * chi n‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ Real.sqrt q / q.totient *
        ∑ chi : DirichletCharacter ℂ q,
          ‖∑ n ∈ s, c n * chi n‖ := by
      have hphi : 0 < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
      have hnormInv : ‖(q.totient : ℂ)⁻¹‖ = (q.totient : ℝ)⁻¹ := by
        simp
      rw [hnormInv, div_eq_mul_inv, mul_comm (Real.sqrt q)]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ chi : DirichletCharacter ℂ q,
            ‖(chi a * gaussSum chi⁻¹ ZMod.stdAddChar) *
              ∑ n ∈ s, c n * chi n‖) ≤
            ∑ chi : DirichletCharacter ℂ q,
              Real.sqrt q * ‖∑ n ∈ s, c n * chi n‖ := by
          apply Finset.sum_le_sum
          intro chi hchi
          rw [norm_mul, norm_mul]
          have haNorm : ‖chi a‖ = 1 := by
            rw [← ha.unit_spec]
            exact chi.unit_norm_eq_one ha.unit
          rw [haNorm, one_mul]
          exact mul_le_mul_of_nonneg_right
            (gaussSum_norm_le_sqrt (chi⁻¹)) (norm_nonneg _)
        _ = Real.sqrt q * ∑ chi : DirichletCharacter ℂ q,
              ‖∑ n ∈ s, c n * chi n‖ := by
          rw [Finset.mul_sum]

end
end MAPMRTLemma29Proof
