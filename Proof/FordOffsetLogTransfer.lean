import FordShiftApproximation
import FordLogPhaseTaylor

open scoped BigOperators
noncomputable section

namespace FordOffsetLogTransfer

open FordPolynomialPhase FordUnitPhaseLipschitz FordSourceWeakBilinear

/-- The unshifted logarithmic phase at a natural argument. -/
def offsetPhase (t u : ℝ) (n : ℕ) : ℂ :=
  unitPhase (-t * Real.log ((n : ℝ) + u))

/-- The Taylor corrected phase at base point `n` and natural shift `u`. -/
def correctedOffsetPhase (k : ℕ) (t u : ℝ) (n h : ℕ) : ℂ :=
  unitPhase (-t * Real.log ((n : ℝ) + u)) *
    FordPolynomialPhase.e
      (∑ j : Fin k,
        sourceGamma t ((n : ℝ) + u) j.val * (h : ℝ) ^ (j.val + 1))

lemma corrected_offset_norm_strip (k : ℕ) (t u : ℝ) (n h : ℕ) :
    ‖correctedOffsetPhase k t u n h‖ =
      ‖FordPolynomialPhase.e
        (∑ j : Fin k,
          sourceGamma t ((n : ℝ) + u) j.val * (h : ℝ) ^ (j.val + 1))‖ := by
  unfold correctedOffsetPhase
  rw [norm_mul, unitPhase_norm, one_mul]

/-- Uniform Taylor transfer for an arbitrary finite shift set. -/
theorem offset_shifted_log_transfer {ι : Type*} (S : Finset ι) (shift : ι → ℕ)
    (N H D k : ℕ) (t u : ℝ) (hN : 1 ≤ N) (ht : 0 ≤ t)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hd : ∀ i ∈ S, shift i ≤ D) :
    (S.card : ℝ) *
        ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
      (S.card : ℝ) * (2 * (D : ℝ)) +
        (∑ n ∈ Finset.range H,
          ‖∑ i ∈ S,
            FordPolynomialPhase.e
              (∑ j : Fin k,
                sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                  (shift i : ℝ) ^ (j.val + 1))‖) +
        (S.card : ℝ) * (H : ℝ) *
          (t * ((D : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)) := by
  let f : ℕ → ℂ := offsetPhase t u
  let g : ℕ → ι → ℂ := fun n i =>
    correctedOffsetPhase k t u (N + n) (shift i)
  let E : ℝ := t * ((D : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hf : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    dsimp [f, offsetPhase]
    rw [unitPhase_norm]
  have he : ∀ n ∈ Finset.range H, ∀ i ∈ S,
      ‖f (N + n + shift i) - g n i‖ ≤ E := by
    intro n hn i hi
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hz : 0 < ((N + n : ℕ) : ℝ) + u := by
      have hbase : 0 < ((N + n : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_lt_of_lt
          (lt_of_lt_of_le (Nat.zero_lt_of_lt hN) (Nat.le_add_right N n))
      linarith
    have hh : 0 ≤ (shift i : ℝ) := by positivity
    have hphase := FordLogPhaseTaylor.shifted_log_phase_bound_source
      (k := k) (t := t) (z := ((N + n : ℕ) : ℝ) + u)
      (h := (shift i : ℝ)) ht hz hh
    have hratio :
        (shift i : ℝ) / (((N + n : ℕ) : ℝ) + u) ≤ (D : ℝ) / (N : ℝ) := by
      apply div_le_div₀
      · positivity
      · exact_mod_cast hd i hi
      · exact hNpos
      · have hbase : (N : ℝ) ≤ ((N + n : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_add_right N n
        linarith
    have hpow :
        ((shift i : ℝ) / (((N + n : ℕ) : ℝ) + u)) ^ (k + 1) ≤
          ((D : ℝ) / (N : ℝ)) ^ (k + 1) := by
      apply pow_le_pow_left₀
      · positivity
      · exact hratio
    have hscaled :
        t * ((shift i : ℝ) / (((N + n : ℕ) : ℝ) + u)) ^ (k + 1) / (k + 1) ≤ E := by
      dsimp [E]
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hpow ht
      · positivity
    dsimp [f, g, offsetPhase, correctedOffsetPhase]
    have hcast :
        (((N + n + shift i : ℕ) : ℝ)) + u =
          (((N + n : ℕ) : ℝ) + u) + (shift i : ℝ) := by
      push_cast
      ring
    rw [hcast]
    exact hphase.trans hscaled
  have htrans := FordShiftApproximation.transfer S shift f g N H D E hf hd he
  have hstrip (n : ℕ) :
      ‖∑ i ∈ S, g n i‖ =
        ‖∑ i ∈ S,
          FordPolynomialPhase.e
            (∑ j : Fin k,
              sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                (shift i : ℝ) ^ (j.val + 1))‖ := by
    dsimp [g, correctedOffsetPhase]
    rw [← Finset.mul_sum, norm_mul, unitPhase_norm, one_mul]
  dsimp [f, offsetPhase] at htrans
  rw [show E = t * ((D : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1) by rfl] at htrans
  simp_rw [hstrip] at htrans
  simpa [offsetPhase] using htrans

/-- Bilinear specialization for the logarithmic phase with a real offset in
`[0,1]`; the Taylor shifts remain the product `(b+1)(a+1)`. -/
theorem offset_bilinear_shift_transfer (M1 M2 N H k : ℕ) (t u : ℝ)
    (hN : 1 ≤ N) (ht : 0 ≤ t) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (M1 * M2 : ℝ) *
        ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
      (M1 * M2 : ℝ) * (2 * ((M1 * M2 : ℕ) : ℝ)) +
        (∑ n ∈ Finset.range H,
          ‖∑ b : Fin M2, ∑ a : Fin M1,
            FordPolynomialPhase.e
              (∑ j : Fin k,
                sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                  (((b.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
                  (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖) +
        (M1 * M2 : ℝ) * (H : ℝ) *
          (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)) := by
  let P := Fin M2 × Fin M1
  let sh : P → ℕ := fun p => (p.1.val + 1) * (p.2.val + 1)
  have hsh : ∀ p ∈ (Finset.univ : Finset P), sh p ≤ M1 * M2 := by
    intro p hp
    have hb : p.1.val + 1 ≤ M2 := by omega
    have ha : p.2.val + 1 ≤ M1 := by omega
    have hprod := Nat.mul_le_mul hb ha
    simpa [sh, Nat.mul_comm] using hprod
  have htr := offset_shifted_log_transfer
    (S := (Finset.univ : Finset P)) (shift := sh)
    (N := N) (H := H) (D := M1 * M2) (k := k) (t := t) (u := u)
    hN ht hu hu1 hsh
  have hcard : ((Finset.univ : Finset P).card : ℝ) = (M1 * M2 : ℝ) := by
    simp [P, Fintype.card_prod]
    ring
  rw [hcard] at htr
  have hsum (n : ℕ) :
      ‖∑ i ∈ (Finset.univ : Finset P),
          FordPolynomialPhase.e
            (∑ j : Fin k,
              sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                (sh i : ℝ) ^ (j.val + 1))‖ =
        ‖∑ b : Fin M2, ∑ a : Fin M1,
            FordPolynomialPhase.e
              (∑ j : Fin k,
                sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                  (((b.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
                  (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖ := by
    change ‖∑ i : P,
          FordPolynomialPhase.e
            (∑ j : Fin k,
              sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                (sh i : ℝ) ^ (j.val + 1))‖ = _
    rw [Fintype.sum_prod_type]
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [sh]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hsum] at htr
  simpa [P, sh, Nat.cast_mul] using htr

end FordOffsetLogTransfer

#print axioms FordOffsetLogTransfer.offset_shifted_log_transfer
#print axioms FordOffsetLogTransfer.offset_bilinear_shift_transfer
