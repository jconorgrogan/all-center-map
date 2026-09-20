import JutilaPseudocharacterMollifierBound

/-!
# Summed pseudocharacter mollifier bound in Jutila Lemma 6

This file finishes the finite summation following the local Euler-factor
estimate.  A mollifier with at most `z2` coefficients has norm at most
`z2 * r^2 / phi(r)` at a squarefree modulus `r`.  After Jutila's external
`1/r` weight and summation over `r ≤ R`, the total cost is bounded by
`z2 * R * harmonic(R)^4`.

The fourth harmonic power is deliberately elementary.  The weak zero-free
gap on the live MAP collar absorbs this fixed polylogarithmic loss, so no
sharp average order for `r/phi(r)` is needed here.
-/

namespace MAPJutilaPseudocharacterMollifierSum

open scoped BigOperators
open MAPJutilaPseudocharacterMollifierBound
open RamachandraShiftedCoefficientEnergy
open FixedCharacterPoweredBridge

noncomputable section

def totientQuotient (r : ℕ) : ℝ :=
  (r : ℝ) / (Nat.totient r : ℝ)

private theorem nat_le_totient_mul_divisorCount
    {n : ℕ} (hn : 1 ≤ n) :
    n ≤ n.totient * n.divisors.card := by
  calc
    n = n.divisors.sum Nat.totient := (Nat.sum_totient n).symm
    _ ≤ n.divisors.sum (fun _ => n.totient) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = n.totient * n.divisors.card := by
      simp [mul_comm]

theorem totientQuotient_le_divisorCount
    {r : ℕ} (hr : 1 ≤ r) :
    totientQuotient r ≤ (r.divisors.card : ℝ) := by
  have hphi : 0 < (Nat.totient r : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  apply (div_le_iff₀ hphi).2
  exact_mod_cast (show r ≤ r.divisors.card * r.totient by
    simpa [mul_comm] using nat_le_totient_mul_divisorCount hr)

private theorem divisorCount_one_le {r : ℕ} (hr : 1 ≤ r) :
    (1 : ℝ) ≤ r.divisors.card := by
  have honeDiv : 1 ∣ r := one_dvd r
  have hr0 : r ≠ 0 := by omega
  have honeMem : 1 ∈ r.divisors := Nat.mem_divisors.mpr ⟨honeDiv, hr0⟩
  have hcard : 1 ≤ r.divisors.card := Finset.one_le_card.mpr ⟨1, honeMem⟩
  exact_mod_cast hcard

/-- Elementary average bound sufficient on the gapped collar. -/
theorem sum_totientQuotient_Icc_le (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, totientQuotient r) ≤
      (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  have hpoint : ∀ r ∈ Finset.Icc 1 R,
      totientQuotient r ≤
        (R : ℝ) * ((CGLProofDAG.orderedDivisorCount 2 r : ℝ) ^ 2 / (r : ℝ)) := by
    intro r hrmem
    have hrI := Finset.mem_Icc.mp hrmem
    have hrpos : 0 < r := by omega
    have hrR : (r : ℝ) ≤ R := by exact_mod_cast hrI.2
    have hdivCount : CGLProofDAG.orderedDivisorCount 2 r = r.divisors.card := by
      exact orderedDivisorCount_two_eq_card_divisors (Nat.ne_of_gt hrpos)
    have hquot := totientQuotient_le_divisorCount hrI.1
    have hcountOne : (1 : ℝ) ≤ r.divisors.card := divisorCount_one_le hrI.1
    have hcount0 : 0 ≤ (r.divisors.card : ℝ) := by positivity
    have hcountSq : (r.divisors.card : ℝ) ≤ (r.divisors.card : ℝ) ^ 2 := by
      nlinarith [mul_nonneg hcount0 (sub_nonneg.mpr hcountOne)]
    have hrRscale : (1 : ℝ) ≤ (R : ℝ) / (r : ℝ) := by
      exact (one_le_div (by exact_mod_cast hrpos)).2 hrR
    have hsq0 : 0 ≤ (r.divisors.card : ℝ) ^ 2 := sq_nonneg _
    calc
      totientQuotient r ≤ (r.divisors.card : ℝ) := hquot
      _ ≤ (r.divisors.card : ℝ) ^ 2 := hcountSq
      _ ≤ ((R : ℝ) / (r : ℝ)) * (r.divisors.card : ℝ) ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hrRscale hsq0
      _ = (R : ℝ) *
          ((CGLProofDAG.orderedDivisorCount 2 r : ℝ) ^ 2 / (r : ℝ)) := by
        rw [hdivCount]
        ring
  calc
    (∑ r ∈ Finset.Icc 1 R, totientQuotient r) ≤
        ∑ r ∈ Finset.Icc 1 R,
          (R : ℝ) * ((CGLProofDAG.orderedDivisorCount 2 r : ℝ) ^ 2 / (r : ℝ)) := by
      exact Finset.sum_le_sum hpoint
    _ = (R : ℝ) * ∑ r ∈ Finset.Ioc 0 R,
          ((CGLProofDAG.orderedDivisorCount 2 r : ℝ) ^ 2 / (r : ℝ)) := by
      rw [Finset.mul_sum]
      congr 2
    _ ≤ (R : ℝ) * (harmonic R : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left
        (sum_orderedDivisorCount_two_sq_div_le R) (Nat.cast_nonneg R)

/-- An abstract finite mollifier with the exact local envelope from (2.1).
The next source adapter instantiates `term` by Jutila's literal coefficient. -/
def finitePseudocharacterMollifier
    (D : Finset ℕ) (term : ℕ → ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ d ∈ D, term r d

theorem norm_finitePseudocharacterMollifier_le
    {D : Finset ℕ} {term : ℕ → ℕ → ℂ} {z2 r : ℕ}
    (hD : D.card ≤ z2) (hr : 0 < r) (hrsq : Squarefree r)
    (hterm : ∀ d ∈ D,
      ‖term r d‖ ≤ pseudocharacterLocalEnvelope r d) :
    ‖finitePseudocharacterMollifier D term r‖ ≤
      (z2 : ℝ) * ((r : ℝ) ^ 2 / (Nat.totient r : ℝ)) := by
  have hlocal : ∀ d ∈ D,
      ‖term r d‖ ≤ (r : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
    intro d hd
    exact (hterm d hd).trans (pseudocharacterLocalEnvelope_le hr hrsq)
  calc
    ‖finitePseudocharacterMollifier D term r‖ ≤
        ∑ d ∈ D, ‖term r d‖ := by
      unfold finitePseudocharacterMollifier
      exact norm_sum_le _ _
    _ ≤ ∑ _d ∈ D, ((r : ℝ) ^ 2 / (Nat.totient r : ℝ)) := by
      exact Finset.sum_le_sum hlocal
    _ = (D.card : ℝ) * ((r : ℝ) ^ 2 / (Nat.totient r : ℝ)) := by simp
    _ ≤ (z2 : ℝ) * ((r : ℝ) ^ 2 / (Nat.totient r : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (by positivity)

/-- Summed version after the external `1/r` weight in Jutila (2.11). -/
theorem sum_inv_mul_norm_finitePseudocharacterMollifier_le
    {D : Finset ℕ} {term : ℕ → ℕ → ℂ} {z2 R : ℕ}
    (hD : D.card ≤ z2)
    (hrsq : ∀ r ∈ Finset.Icc 1 R, Squarefree r)
    (hterm : ∀ r ∈ Finset.Icc 1 R, ∀ d ∈ D,
      ‖term r d‖ ≤ pseudocharacterLocalEnvelope r d) :
    (∑ r ∈ Finset.Icc 1 R,
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖) ≤
      (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  have hpoint : ∀ r ∈ Finset.Icc 1 R,
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖ ≤
        (z2 : ℝ) * totientQuotient r := by
    intro r hrmem
    have hrI := Finset.mem_Icc.mp hrmem
    have hrpos : 0 < r := by omega
    have hnorm := norm_finitePseudocharacterMollifier_le
      hD hrpos (hrsq r hrmem) (hterm r hrmem)
    have hinv0 : 0 ≤ (r : ℝ)⁻¹ := by positivity
    calc
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖ ≤
          (r : ℝ)⁻¹ *
            ((z2 : ℝ) * ((r : ℝ) ^ 2 / (Nat.totient r : ℝ))) :=
        mul_le_mul_of_nonneg_left hnorm hinv0
      _ = (z2 : ℝ) * totientQuotient r := by
        unfold totientQuotient
        field_simp [show (r : ℝ) ≠ 0 by exact_mod_cast hrpos.ne']
  calc
    (∑ r ∈ Finset.Icc 1 R,
        (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖) ≤
      ∑ r ∈ Finset.Icc 1 R, (z2 : ℝ) * totientQuotient r := by
        exact Finset.sum_le_sum hpoint
    _ = (z2 : ℝ) * ∑ r ∈ Finset.Icc 1 R, totientQuotient r := by
      rw [Finset.mul_sum]
    _ ≤ (z2 : ℝ) * ((R : ℝ) * (harmonic R : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left (sum_totientQuotient_Icc_le R)
        (Nat.cast_nonneg z2)
    _ = (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by ring

/-- The source-faithful selected version of the summed mollifier bound.
Jutila's prime on the `r`-sum restricts to squarefree integers coprime to the
character modulus.  The coprimality condition is part of the selected-system
interface even though this upper bound only uses squarefreeness and the range
restriction. -/
theorem sum_inv_mul_norm_finitePseudocharacterMollifier_selected_le
    {D S : Finset ℕ} {term : ℕ → ℕ → ℂ} {z2 R q : ℕ}
    (hD : D.card ≤ z2) (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (_hrcop : ∀ r ∈ S, r.Coprime q)
    (hterm : ∀ r ∈ S, ∀ d ∈ D,
      ‖term r d‖ ≤ pseudocharacterLocalEnvelope r d) :
    (∑ r ∈ S,
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖) ≤
      (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  have hpoint : ∀ r ∈ S,
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖ ≤
        (z2 : ℝ) * totientQuotient r := by
    intro r hrmem
    have hrI := Finset.mem_Icc.mp (hS hrmem)
    have hrpos : 0 < r := by omega
    have hnorm := norm_finitePseudocharacterMollifier_le
      hD hrpos (hrsq r hrmem) (hterm r hrmem)
    have hinv0 : 0 ≤ (r : ℝ)⁻¹ := by positivity
    calc
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖ ≤
          (r : ℝ)⁻¹ *
            ((z2 : ℝ) * ((r : ℝ) ^ 2 / (Nat.totient r : ℝ))) :=
        mul_le_mul_of_nonneg_left hnorm hinv0
      _ = (z2 : ℝ) * totientQuotient r := by
        unfold totientQuotient
        field_simp [show (r : ℝ) ≠ 0 by exact_mod_cast hrpos.ne']
  calc
    (∑ r ∈ S,
        (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D term r‖) ≤
      ∑ r ∈ S, (z2 : ℝ) * totientQuotient r :=
        Finset.sum_le_sum hpoint
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (z2 : ℝ) * totientQuotient r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro r hrI hrS
      apply mul_nonneg (Nat.cast_nonneg z2)
      unfold totientQuotient
      exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg (Nat.totient r))
    _ = (z2 : ℝ) * ∑ r ∈ Finset.Icc 1 R, totientQuotient r := by
      rw [Finset.mul_sum]
    _ ≤ (z2 : ℝ) * ((R : ℝ) * (harmonic R : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left (sum_totientQuotient_Icc_le R)
        (Nat.cast_nonneg z2)
    _ = (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by ring

end

end MAPJutilaPseudocharacterMollifierSum

#print axioms MAPJutilaPseudocharacterMollifierSum.sum_totientQuotient_Icc_le
#print axioms MAPJutilaPseudocharacterMollifierSum.norm_finitePseudocharacterMollifier_le
#print axioms MAPJutilaPseudocharacterMollifierSum.sum_inv_mul_norm_finitePseudocharacterMollifier_le
#print axioms MAPJutilaPseudocharacterMollifierSum.sum_inv_mul_norm_finitePseudocharacterMollifier_selected_le
