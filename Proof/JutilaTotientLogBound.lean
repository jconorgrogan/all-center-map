import Mathlib

/-! # Elementary logarithmic bound for the reciprocal totient ratio -/
namespace MAPJutilaTotientLogBound
open scoped BigOperators
noncomputable section

/-- Among distinct integers at least two, the product `p/(p-1)` is at most
one plus their number. Maximal-element induction implements the sorted bound. -/
theorem prod_div_pred_le_card_add_one (A : Finset ℕ)
    (hA : ∀ p ∈ A, 2 ≤ p) :
    (∏ p ∈ A, (p : ℝ) / ((p : ℝ)-1)) ≤ (A.card : ℝ)+1 := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | insert p A hmax ih =>
    have hp : 2 ≤ p := hA p (Finset.mem_insert_self _ _)
    have hA' : ∀ x ∈ A, 2 ≤ x := fun x hx => hA x (Finset.mem_insert_of_mem hx)
    have hpnot : p ∉ A := fun hpA => (lt_irrefl p) (hmax p hpA)
    have hcard : A.card ≤ p-2 := by
      calc
        A.card ≤ (Finset.Ico 2 p).card := Finset.card_le_card (by
          intro x hx
          exact Finset.mem_Ico.mpr ⟨hA' x hx, hmax x hx⟩)
        _ = p-2 := Nat.card_Ico 2 p
    have hcard' : (A.card : ℝ)+2 ≤ (p : ℝ) := by
      exact_mod_cast (show A.card+2 ≤ p by omega)
    have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1<p by omega)
    rw [Finset.prod_insert hpnot, Finset.card_insert_of_notMem hpnot]
    push_cast
    calc
      _ ≤ ((p : ℝ)/((p : ℝ)-1))*((A.card : ℝ)+1) :=
        mul_le_mul_of_nonneg_left (ih hA') (by positivity)
      _ ≤ (A.card : ℝ)+1+1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < (p : ℝ)-1)]
        nlinarith

theorem div_totient_eq_prod (q : ℕ) (hq : 0 < q) :
    (q : ℝ)/(Nat.totient q : ℝ) =
      ∏ p ∈ q.primeFactors, (p : ℝ)/((p : ℝ)-1) := by
  have hphi : (0 : ℝ) < Nat.totient q := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hden : (∏ p ∈ q.primeFactors, ((p : ℝ)-1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => by
      have hpR : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hphi.ne' hden).mpr
  have heq := Nat.totient_mul_prod_primeFactors q
  have heqR := congrArg (fun n : ℕ => (n : ℝ)) heq
  push_cast at heqR
  have hpred : (∏ p ∈ q.primeFactors, ((p-1 : ℕ) : ℝ)) =
      ∏ p ∈ q.primeFactors, ((p : ℝ)-1) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    norm_num
  rw [hpred] at heqR
  nlinarith [heqR]

theorem div_totient_le_one_add_log_div_log_two (q : ℕ) (hq : 0 < q) :
    (q : ℝ)/(Nat.totient q : ℝ) ≤ 1 + Real.log (q : ℝ)/Real.log 2 := by
  have hpowNat : 2^q.primeFactors.card ≤ q :=
    (Finset.pow_card_le_prod _ id 2 (fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le)).trans
        (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
  have hpow : (2 : ℝ)^q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<(2 : ℝ)^q.primeFactors.card) hpow
  rw [Real.log_pow] at hlog
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ)/Real.log 2 :=
    (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog
  rw [div_totient_eq_prod q hq]
  exact (prod_div_pred_le_card_add_one q.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans (by linarith)

/-- A single absolute constant times `1+log q`, uniform in positive `q`. -/
theorem div_totient_le_log (q : ℕ) (hq : 0 < q) :
    (q : ℝ)/(Nat.totient q : ℝ) ≤
      (1 + (Real.log 2)⁻¹) * (1 + Real.log (q : ℝ)) := by
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hinv : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hbase := div_totient_le_one_add_log_div_log_two q hq
  simp only [div_eq_mul_inv] at hbase ⊢
  nlinarith

/-- Detector normalization loses only two logarithmic powers at any larger
ambient scale. -/
theorem inverse_totient_ratio_sq_le_logScale
    (q : ℕ) (hq : 0 < q) {D : ℝ} (hqD : (q : ℝ) ≤ D) :
    (((Nat.totient q : ℝ)/(q : ℝ))⁻¹)^2 ≤
      (1 + (Real.log 2)⁻¹)^2 * (1 + Real.log D)^2 := by
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hq) hqD
  have hC : 0 ≤ 1 + (Real.log 2)⁻¹ := by
    have h := (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
    positivity
  have hbound : (q : ℝ)/(Nat.totient q : ℝ) ≤
      (1+(Real.log 2)⁻¹)*(1+Real.log D) :=
    (div_totient_le_log q hq).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hlog) hC)
  rw [inv_div]
  calc
    _ ≤ ((1+(Real.log 2)⁻¹)*(1+Real.log D))^2 :=
      pow_le_pow_left₀ (by positivity) hbound 2
    _ = _ := by ring

end
end MAPJutilaTotientLogBound
#print axioms MAPJutilaTotientLogBound.div_totient_le_log

#print axioms MAPJutilaTotientLogBound.inverse_totient_ratio_sq_le_logScale
