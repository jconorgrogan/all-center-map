import FordUniformEnvelope

open scoped BigOperators
noncomputable section
namespace FordNextDegreeEnvelope

open FordWEnvelopeScalar FordUniformEnvelope

lemma envelope_next_term_le {K : ℕ} {lam : ℝ}
    (hpos : 0 < lam) :
    lam * envelope (((K + 1 : ℕ) : ℝ) / lam) ≤
      mu2 * ((K + 1 : ℕ) : ℝ) := by
  have henv : envelope (((K + 1 : ℕ) : ℝ) / lam) ≤
      mu2 * (((K + 1 : ℕ) : ℝ) / lam) := by
    unfold envelope
    exact min_le_left _ _
  have hm := mul_le_mul_of_nonneg_left henv hpos.le
  field_simp at hm ⊢
  nlinarith

lemma envelope_sum_succ_le {K : ℕ} {lam : ℝ}
    (hpos : 0 < lam) :
    envelopeSum (K + 1) lam ≤ envelopeSum K lam +
      mu2 * ((K + 1 : ℕ) : ℝ) := by
  unfold envelopeSum
  rw [Finset.sum_range_succ]
  have hterm := envelope_next_term_le (K := K) hpos
  exact add_le_add le_rfl hterm

theorem raw_saving_succ_ge_target {K : ℕ} {lam : ℝ}
    (hK : 2000 ≤ K)
    (hlow : b * (K : ℝ) ≤ lam)
    (hupp : lam ≤ b * (K : ℝ) + 1) :
    ((K + 1 : ℕ) : ℝ) ^ 2 / 51 ≤
      rawSaving (K + 1) lam := by
  have hb : 0 < b := by norm_num [b]
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hpos : 0 < lam := (mul_pos hb hKpos).trans_le hlow
  have hsum := envelope_sum_succ_le (K := K) hpos
  have hold := raw_saving_ge_target hK hlow hupp
  have hstep : rawSaving (K + 1) lam ≥
      rawSaving K lam - eps * (mu1 + mu2) * (2 * (K : ℝ) + 1) := by
    unfold rawSaving at hsum ⊢
    norm_num [Nat.cast_add] at hsum ⊢
    ring_nf at hsum ⊢
    nlinarith [hsum]
  have hmargin : (K : ℝ) ^ 2 / 50 -
      eps * (mu1 + mu2) * (2 * (K : ℝ) + 1) ≥
      ((K + 1 : ℕ) : ℝ) ^ 2 / 51 := by
    norm_num [mu1, mu2, eps, Nat.cast_add]
    ring_nf
    have hKR : (2000 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [sq_nonneg ((K : ℝ) - 2000)]
  have hraw : ((K + 1 : ℕ) : ℝ) ^ 2 / 51 ≤
      rawSaving K lam - eps * (mu1 + mu2) * (2 * (K : ℝ) + 1) := by
    linarith
  exact hraw.trans hstep

theorem floor_next_degree_slab {lam : ℝ}
    (hlam : 2000 * b ≤ lam) :
    let k := Nat.floor (lam / b) + 1
    2001 ≤ k ∧
      b * ((k : ℝ) - 1) ≤ lam ∧
      lam < b * (k : ℝ) := by
  have hb : 0 < b := by norm_num [b]
  have hb1 : b ≤ 1 := by norm_num [b]
  have hratio : (2000 : ℝ) ≤ lam / b :=
    (le_div_iff₀ hb).mpr (by nlinarith)
  have hratio0 : 0 ≤ lam / b := by linarith
  let K : ℕ := Nat.floor (lam / b)
  have hK : 2000 ≤ K := by
    dsimp [K]
    apply (Nat.le_floor_iff hratio0).mpr
    simpa using hratio
  have hfl := Nat.floor_le hratio0
  have hfu := Nat.lt_floor_add_one (lam / b)
  have hlo : b * (K : ℝ) ≤ lam := by
    have h := (le_div_iff₀ hb).mp (by simpa [K] using hfl)
    simpa [K, mul_comm] using h
  have hup : lam < b * ((K + 1 : ℕ) : ℝ) := by
    have h := (div_lt_iff₀ hb).mp (by simpa [K] using hfu)
    simpa [K, Nat.cast_add, mul_comm] using h
  dsimp [K]
  constructor
  · omega
  constructor
  · have hh := hlo
    dsimp [K] at hh
    have heq :
        (((Nat.floor (lam / b) + 1 : ℕ) : ℝ) - 1) =
          (Nat.floor (lam / b) : ℝ) := by
      push_cast
      ring
    rw [heq]
    exact hh
  · have hh := hup
    dsimp [K] at hh
    have heq :
        (((Nat.floor (lam / b) + 1 : ℕ) : ℝ)) =
          (Nat.floor (lam / b) : ℝ) + 1 := by
      push_cast
      ring
    rw [heq] at hh ⊢
    exact hh

theorem raw_saving_floor_next_degree {lam : ℝ}
    (hlam : 2000 * b ≤ lam) :
    let k := Nat.floor (lam / b) + 1
    (k : ℝ) ^ 2 / 51 ≤ rawSaving k lam := by
  obtain ⟨hk, hlo, hup⟩ := floor_next_degree_slab hlam
  have hlo' : b * (Nat.floor (lam / b) : ℝ) ≤ lam := by
    have hh := hlo
    have heq :
        (((Nat.floor (lam / b) + 1 : ℕ) : ℝ) - 1) =
          (Nat.floor (lam / b) : ℝ) := by
      push_cast
      ring
    rw [heq] at hh
    exact hh
  have hup' : lam ≤ b * (Nat.floor (lam / b) : ℝ) + 1 := by
    have hb1 : b ≤ 1 := by norm_num [b]
    have h : lam < b * ((Nat.floor (lam / b) : ℝ) + 1) := by
      have hh := hup
      have heq :
          (((Nat.floor (lam / b) + 1 : ℕ) : ℝ)) =
            (Nat.floor (lam / b) : ℝ) + 1 := by
        push_cast
        ring
      rw [heq] at hh
      exact hh
    have hstep : b * ((Nat.floor (lam / b) : ℝ) + 1) ≤
        b * (Nat.floor (lam / b) : ℝ) + 1 := by
      calc
        b * ((Nat.floor (lam / b) : ℝ) + 1) =
            b * (Nat.floor (lam / b) : ℝ) + b := by ring
        _ ≤ b * (Nat.floor (lam / b) : ℝ) + 1 :=
          by simpa [add_comm] using
            (add_le_add_left hb1 (b * (Nat.floor (lam / b) : ℝ)))
    exact (le_of_lt h).trans hstep
  exact raw_saving_succ_ge_target (K := Nat.floor (lam / b))
    (by omega) hlo' hup'

theorem floor_next_degree_taylor_exponent {lam : ℝ}
    (hlam : 2000 * b ≤ lam) :
    let k := Nat.floor (lam / b) + 1
    lam - b * ((k : ℝ) + 1) < -b := by
  obtain ⟨_, _, hup⟩ := floor_next_degree_slab hlam
  dsimp
  have heq :
      (((Nat.floor (lam / b) + 1 : ℕ) : ℝ)) =
        (Nat.floor (lam / b) : ℝ) + 1 := by
    push_cast
    ring
  rw [heq] at hup ⊢
  calc
    lam - b * ((Nat.floor (lam / b) : ℝ) + 1 + 1) <
        b * ((Nat.floor (lam / b) : ℝ) + 1) -
          b * ((Nat.floor (lam / b) : ℝ) + 1 + 1) :=
      sub_lt_sub_right hup _
    _ = -b := by ring

end FordNextDegreeEnvelope

#print axioms FordNextDegreeEnvelope.raw_saving_succ_ge_target
#print axioms FordNextDegreeEnvelope.floor_next_degree_slab
#print axioms FordNextDegreeEnvelope.raw_saving_floor_next_degree
#print axioms FordNextDegreeEnvelope.floor_next_degree_taylor_exponent
