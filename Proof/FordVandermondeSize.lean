import Mathlib

open scoped BigOperators
noncomputable section
namespace MAPFordVandermondeSize

lemma finite_difference_natAbs_le {P : ℕ} (a b : Fin (P+1)) :
    ((a.val : ℤ) - (b.val : ℤ)).natAbs ≤ P := by
  have ha : (a.val : ℤ) ≤ P := by exact_mod_cast Nat.le_of_lt_succ a.isLt
  have hb : (b.val : ℤ) ≤ P := by exact_mod_cast Nat.le_of_lt_succ b.isLt
  have h : |(a.val : ℤ) - (b.val : ℤ)| ≤ (P : ℤ) := abs_le.mpr (by constructor <;> omega)
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

lemma sum_card_Ioi (n : ℕ) :
    ∑ i : Fin n, (Finset.Ioi i).card = ∑ i : Fin n, i.val := by
  simp only [Fin.card_Ioi]
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun i : Fin n => i.val)
  calc
    _ = ∑ i : Fin n, (Fin.revPerm i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Fin.revPerm, Fin.rev]
      omega
    _ = _ := h

lemma vandermonde_natAbs_le {n P : ℕ} (z : Fin n → Fin (P+1)) :
    (Matrix.vandermonde (fun i => ((z i).val : ℤ))).det.natAbs ≤
      P ^ (∑ i : Fin n, i.val) := by
  rw [Matrix.det_vandermonde]
  change Int.natAbsHom (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
    (((z j).val : ℤ) - ((z i).val : ℤ))) ≤ _
  rw [map_prod]
  simp_rw [map_prod]
  calc
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        Int.natAbsHom (((z j).val : ℤ) - ((z i).val : ℤ))) ≤
        ∏ i : Fin n, P ^ (Finset.Ioi i).card := by
      apply Finset.prod_le_prod'
      intro i hi
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod'
      intro j hj
      exact finite_difference_natAbs_le (z j) (z i)
    _ = P ^ (∑ i : Fin n, i.val) := by
      rw [Finset.prod_pow_eq_pow_sum, sum_card_Ioi]

/-- Size of the literal bad-prime product, without powers of T or 2^m
that belong to Jacobian coefficients rather than the avoidance object. -/
theorem bad_product_natAbs_le {n P d : ℕ} (T : ℤ)
    (hT : T.natAbs ≤ P^d) (z w : Fin n → Fin (P+1)) :
    (T * (Matrix.vandermonde (fun i => ((z i).val : ℤ))).det *
      (Matrix.vandermonde (fun i => ((w i).val : ℤ))).det).natAbs ≤
      P ^ (d + n*(n-1)) := by
  rw [Int.natAbs_mul, Int.natAbs_mul]
  have h := Nat.mul_le_mul (Nat.mul_le_mul hT (vandermonde_natAbs_le z))
    (vandermonde_natAbs_le w)
  have he : (∑ i : Fin n, i.val) * 2 = n*(n-1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
    exact Finset.sum_range_id_mul_two n
  calc
    _ ≤ P^d * P^(∑ i : Fin n, i.val) * P^(∑ i : Fin n, i.val) := h
    _ = P^(d+n*(n-1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

end MAPFordVandermondeSize
#print axioms MAPFordVandermondeSize.vandermonde_natAbs_le
#print axioms MAPFordVandermondeSize.bad_product_natAbs_le
