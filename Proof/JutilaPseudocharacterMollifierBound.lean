import JutilaGappedGrahamBypass
import JutilaPseudocharacterAlgebra

/-!
# Finite pseudocharacter factor in Jutila Lemma 6

This module certifies the elementary estimate following equation (2.11).
For `f(n)=mu(n)phi(n)`, the coefficient at a fixed squarefree `r` is bounded
by `r^2/phi(r)`.  After the external `r^-1` weight, only `r/phi(r)` remains.
-/

namespace MAPJutilaPseudocharacterMollifierBound

open scoped BigOperators
open MAPJutilaGappedGrahamBypass MAPJutilaPseudocharacterAlgebra

noncomputable section

def pseudocharacterEulerProduct (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, ((p : ℝ) + 1)

private theorem prod_prime_sub_one_real
    {n : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) :
    (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) =
      (Nat.totient n : ℝ) := by
  have hq := prod_prime_sub_one_eq_totient hn hsq
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
  simpa using hr

theorem pseudocharacterEulerProduct_le_sq_div_totient
    {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) :
    pseudocharacterEulerProduct n ≤
      (n : ℝ) ^ 2 / (Nat.totient n : ℝ) := by
  have hlocal : ∀ p ∈ n.primeFactors,
      ((p : ℝ) + 1) ≤ (p : ℝ) ^ 2 / ((p : ℝ) - 1) := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
    apply (le_div_iff₀ (by linarith)).2
    nlinarith
  have hprod :
      (∏ p ∈ n.primeFactors, ((p : ℝ) + 1)) ≤
        ∏ p ∈ n.primeFactors,
          ((p : ℝ) ^ 2 / ((p : ℝ) - 1)) := by
    apply Finset.prod_le_prod
    · intro p hp
      exact add_nonneg (Nat.cast_nonneg p) (by norm_num)
    · exact hlocal
  have hnprod : (∏ p ∈ n.primeFactors, (p : ℝ)) = (n : ℝ) := by
    calc
      (∏ p ∈ n.primeFactors, (p : ℝ)) =
          ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) :=
        (Nat.cast_prod (R := ℝ) (fun p : ℕ => p) n.primeFactors).symm
      _ = (n : ℝ) :=
        congrArg (fun m : ℕ => (m : ℝ))
          (Nat.prod_primeFactors_of_squarefree hsq)
  have hphiprod := prod_prime_sub_one_real hn.ne' hsq
  unfold pseudocharacterEulerProduct
  calc
    (∏ p ∈ n.primeFactors, ((p : ℝ) + 1)) ≤
        ∏ p ∈ n.primeFactors,
          ((p : ℝ) ^ 2 / ((p : ℝ) - 1)) := hprod
    _ = (n : ℝ) ^ 2 / (Nat.totient n : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_pow, hnprod, hphiprod]

/-- Absolute local factor in (2.1), after using `|lambda_d|≤1`,
`|chi(d)|≤1`, and `|d^{-it}|=1`. -/
def pseudocharacterLocalEnvelope (r d : ℕ) : ℝ :=
  (Nat.totient (r.gcd d) : ℝ) *
    pseudocharacterEulerProduct (r / r.gcd d)

theorem pseudocharacterLocalEnvelope_le
    {r d : ℕ} (hr : 0 < r) (hrsq : Squarefree r) :
    pseudocharacterLocalEnvelope r d ≤
      (r : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
  let g : ℕ := r.gcd d
  let n : ℕ := r / g
  have hgdiv : g ∣ r := by dsimp [g]; exact Nat.gcd_dvd_left r d
  have hg : 0 < g := by dsimp [g]; exact Nat.gcd_pos_of_pos_left d hr
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hr hgdiv) hg
  have hnsq : Squarefree n :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hgdiv) hrsq
  have hcop : n.Coprime g := by
    have hc := Nat.coprime_div_gcd_of_squarefree hrsq hg.ne'
    rw [Nat.gcd_eq_right_iff_dvd.mpr hgdiv] at hc
    simpa only [n] using hc
  have hrprod : n * g = r := by
    dsimp [n]
    exact Nat.div_mul_cancel hgdiv
  have hphi : Nat.totient r = Nat.totient n * Nat.totient g := by
    rw [← hrprod, Nat.totient_mul hcop]
  have hphiG : (Nat.totient g : ℝ) ≤ g := by
    exact_mod_cast Nat.totient_le g
  have hphiGpos : 0 < (Nat.totient g : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hg)
  have hphiNpos : 0 < (Nat.totient n : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hEuler := pseudocharacterEulerProduct_le_sq_div_totient hn hnsq
  unfold pseudocharacterLocalEnvelope
  change (Nat.totient g : ℝ) * pseudocharacterEulerProduct n ≤ _
  calc
    (Nat.totient g : ℝ) * pseudocharacterEulerProduct n ≤
        (Nat.totient g : ℝ) *
          ((n : ℝ) ^ 2 / (Nat.totient n : ℝ)) :=
      mul_le_mul_of_nonneg_left hEuler hphiGpos.le
    _ ≤ (r : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
      rw [hphi]
      push_cast
      rw [← hrprod]
      push_cast
      have hphiSq : (Nat.totient g : ℝ) ^ 2 ≤ (g : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((g : ℝ) - (Nat.totient g : ℝ))]
      have hphiRatio : (Nat.totient g : ℝ) ≤
          (g : ℝ) ^ 2 / (Nat.totient g : ℝ) :=
        (le_div_iff₀ hphiGpos).2 (by simpa [pow_two] using hphiSq)
      have hbase0 : 0 ≤ (n : ℝ) ^ 2 / (Nat.totient n : ℝ) := by
        positivity
      calc
        (Nat.totient g : ℝ) * ((n : ℝ) ^ 2 / (Nat.totient n : ℝ)) =
            ((n : ℝ) ^ 2 / (Nat.totient n : ℝ)) *
              (Nat.totient g : ℝ) := by ring
        _ ≤ ((n : ℝ) ^ 2 / (Nat.totient n : ℝ)) *
              ((g : ℝ) ^ 2 / (Nat.totient g : ℝ)) :=
          mul_le_mul_of_nonneg_left hphiRatio hbase0
        _ = ((n : ℝ) * (g : ℝ)) ^ 2 /
              ((Nat.totient n : ℝ) * (Nat.totient g : ℝ)) := by
          field_simp [hphiNpos.ne', hphiGpos.ne']

end

end MAPJutilaPseudocharacterMollifierBound

#print axioms MAPJutilaPseudocharacterMollifierBound.pseudocharacterLocalEnvelope_le
