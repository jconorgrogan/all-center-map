import FordNextDegreeEnvelope
import FordDecayExponent

noncomputable section
namespace FordDegreeScaleBounds

open FordWEnvelopeScalar FordNextDegreeEnvelope FordDecayExponent

theorem degree_le_four_lam {lam : ℝ} (hlam : 2000 * b ≤ lam) :
    let k := Nat.floor (lam / b) + 1
    (k : ℝ) ≤ 4 * lam := by
  have hb : (1 : ℝ) / 2 ≤ b := by norm_num [b]
  have hbpos : 0 < b := by norm_num [b]
  have hlampos : 0 < lam := by
    have : 0 < (2000 : ℝ) * b := by positivity
    linarith
  have hratio1 : (1 : ℝ) ≤ lam / b := by
    apply (le_div_iff₀ hbpos).2
    nlinarith
  have hfloor : (Nat.floor (lam / b) : ℝ) ≤ lam / b :=
    Nat.floor_le (by linarith)
  have hkupper :
      ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ≤ 2 * (lam / b) := by
    push_cast
    nlinarith
  have hfour : 2 * (lam / b) ≤ 4 * lam := by
    rw [show 2 * (lam / b) = (2 * lam) / b by ring]
    apply (div_le_iff₀ hbpos).2
    have hmul : 0 ≤ (b - (1 : ℝ) / 2) * lam :=
      mul_nonneg (sub_nonneg.mpr hb) (le_of_lt hlampos)
    ring_nf at hmul ⊢
    nlinarith
  dsimp
  exact hkupper.trans hfour

theorem decay_lower_bound {lam : ℝ} (hlam : 2000 * b ≤ lam) :
    let k := Nat.floor (lam / b) + 1
    (1 : ℝ) / (10000000000 * lam ^ 2) ≤ decay k := by
  have hbpos : 0 < b := by norm_num [b]
  have hlampos : 0 < lam := by
    have : 0 < (2000 : ℝ) * b := by positivity
    linarith
  have hk : 2000 ≤ Nat.floor (lam / b) + 1 := by
    have hh := (FordNextDegreeEnvelope.floor_next_degree_slab hlam).1
    omega
  have hkpos : (0 : ℝ) < (Nat.floor (lam / b) + 1 : ℕ) := by
    exact_mod_cast (show 0 < Nat.floor (lam / b) + 1 by omega)
  have hdeg :
      ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ≤ 4 * lam := by
    exact degree_le_four_lam hlam
  have hsq :
      ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ^ 2 ≤ 16 * lam ^ 2 := by
    calc
      ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ^ 2 ≤
          (4 * lam) ^ 2 := pow_le_pow_left₀ (by positivity) hdeg 2
      _ = 16 * lam ^ 2 := by ring
  have hden :
      (400 : ℝ) * (1003 : ℝ) ^ 2 *
          ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ^ 2 ≤
        10000000000 * lam ^ 2 := by
    calc
      (400 : ℝ) * (1003 : ℝ) ^ 2 *
          ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ^ 2 ≤
          (400 : ℝ) * (1003 : ℝ) ^ 2 * (16 * lam ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 10000000000 * lam ^ 2 := by
        have hl2 : 0 ≤ lam ^ 2 := sq_nonneg lam
        have hc : (400 : ℝ) * (1003 : ℝ) ^ 2 * 16 ≤ 10000000000 := by
          norm_num
        simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hc hl2)
  have hleft : 0 < (10000000000 : ℝ) * lam ^ 2 := by positivity
  have hright : 0 < (400 : ℝ) * (1003 : ℝ) ^ 2 *
      ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ^ 2 := by positivity
  apply (div_le_div_iff₀ hleft hright).2
  simpa [decay]
    using hden

theorem quartic_degree_bound {lam : ℝ} (hlam : 2000 * b ≤ lam) :
    let k := Nat.floor (lam / b) + 1
    (1000000000000 : ℝ) * (k : ℝ) ^ 4 ≤
      256000000000000 * lam ^ 4 := by
  have hdeg := degree_le_four_lam hlam
  dsimp
  have hpow :
      ((Nat.floor (lam / b) + 1 : ℕ) : ℝ) ^ 4 ≤ (4 * lam) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) hdeg 4
  nlinarith [hpow]

end FordDegreeScaleBounds

#print axioms FordDegreeScaleBounds.degree_le_four_lam
#print axioms FordDegreeScaleBounds.decay_lower_bound
#print axioms FordDegreeScaleBounds.quartic_degree_bound
