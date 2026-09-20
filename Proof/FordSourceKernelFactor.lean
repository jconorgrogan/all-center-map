import FordBilinearFinite

open scoped BigOperators
open FordBilinearFinite

namespace FordSourceKernelFactor
noncomputable section

lemma sfd_le_factor_C {L K q : ℕ} {gamma : ℝ}
    (hL : 2 ≤ L) (hq1 : 1 ≤ q) (hgamma : gamma ≠ 0) :
    6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
        6 * (K : ℝ) * |gamma| +
        (4 * (q : ℝ) + 2) / ((L : ℝ) * |gamma|) ≤
      (2 * (q : ℝ) + 1) *
        (2 * (K : ℝ) / L + 2 * (K : ℝ) * |gamma| +
          2 / ((L : ℝ) * |gamma|) + 2) := by
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hL0 : 0 < (L : ℝ) := by positivity
  have hg0 : 0 < |gamma| := abs_pos.mpr hgamma
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have hA : 0 ≤ (K : ℝ) / L := by positivity
  have hB : 0 ≤ (K : ℝ) * |gamma| := by positivity
  have hD : 0 ≤ 1 / ((L : ℝ) * |gamma|) := by positivity
  have hq4 : 0 ≤ 4 * (q : ℝ) - 4 := by linarith
  have hrem : 0 ≤ (4 * (q : ℝ) - 4) * ((K : ℝ) * |gamma| + 1) :=
    mul_nonneg hq4 (by positivity)
  calc
    6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
          6 * (K : ℝ) * |gamma| +
          (4 * (q : ℝ) + 2) / ((L : ℝ) * |gamma|) =
        (2 * (q : ℝ) + 1) *
          (2 * (K : ℝ) / L + 2 * (K : ℝ) * |gamma| +
            2 / ((L : ℝ) * |gamma|) + 2) -
          (4 * (q : ℝ) - 4) * ((K : ℝ) * |gamma| + 1) := by ring
    _ ≤ _ := by linarith

lemma min_factor_le_mul_min {A C n : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hn : 1 ≤ n) :
    min A (n * C) ≤ n * min A C := by
  by_cases h : A ≤ C
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by
      simpa [mul_comm] using (le_mul_of_one_le_right hA hn))
  · have h' : C ≤ A := le_of_not_ge h
    rw [min_eq_right h']
    exact min_le_right _ _

theorem kernelFactor_le_mul_C_min
    {L K q : ℕ} {gamma : ℝ} (hL : 2 ≤ L) (hq1 : 1 ≤ q)
    (hgamma : gamma ≠ 0) :
    kernelFactor L K q gamma ≤
      (L : ℝ) * (2 * (q : ℝ) + 1) *
        min (2 * (K : ℝ))
          (2 * (K : ℝ) / L + 2 * (K : ℝ) * |gamma| +
            2 / ((L : ℝ) * |gamma|) + 2) := by
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hq0 : 1 ≤ (2 * (q : ℝ) + 1) := by
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith
  have hC0 : 0 ≤ (2 * (K : ℝ) / L + 2 * (K : ℝ) * |gamma| +
      2 / ((L : ℝ) * |gamma|) + 2) := by positivity
  have hA0 : 0 ≤ 2 * (K : ℝ) := by positivity
  have hsfd := sfd_le_factor_C (K := K) hL hq1 hgamma
  have hmin : min (2 * (K : ℝ))
      (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
        6 * (K : ℝ) * |gamma| +
        (4 * (q : ℝ) + 2) / ((L : ℝ) * |gamma|)) ≤
      (2 * (q : ℝ) + 1) * min (2 * (K : ℝ))
        (2 * (K : ℝ) / L + 2 * (K : ℝ) * |gamma| +
          2 / ((L : ℝ) * |gamma|) + 2) := by
    apply le_trans (min_le_min_left _ hsfd)
    exact min_factor_le_mul_min hA0 hC0 hq0
  unfold kernelFactor
  calc
    (L : ℝ) * min (2 * (K : ℝ))
        (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
          6 * (K : ℝ) * |gamma| +
          (4 * (q : ℝ) + 2) / ((L : ℝ) * |gamma|)) ≤
        (L : ℝ) * ((2 * (q : ℝ) + 1) * min (2 * (K : ℝ))
          (2 * (K : ℝ) / L + 2 * (K : ℝ) * |gamma| +
            2 / ((L : ℝ) * |gamma|) + 2)) :=
      mul_le_mul_of_nonneg_left hmin hL0
    _ = (L : ℝ) * (2 * (q : ℝ) + 1) * min (2 * (K : ℝ))
          (2 * (K : ℝ) / L + 2 * (K : ℝ) * |gamma| +
            2 / ((L : ℝ) * |gamma|) + 2) := by ring

def sourceC (r s M M2 j N : ℕ) (t : ℝ) : ℝ :=
  2 * (s * M2 ^ j : ℝ) / (r * M ^ j : ℝ) +
    (s * M2 ^ j : ℝ) * t /
      (Real.pi * (j : ℝ) * (N : ℝ) ^ j) +
    4 * Real.pi * (j : ℝ) * (2 * (N : ℝ)) ^ j /
      ((r * M ^ j : ℝ) * t) + 2

def sourceW (r s M M2 j N : ℕ) (t : ℝ) : ℝ :=
  min (2 * (s * M2 ^ j : ℝ)) (sourceC r s M M2 j N t)

theorem kernelFactor_le_source
    {r s M M2 j N q : ℕ} {t z : ℝ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hM : 1 ≤ M) (hM2 : 1 ≤ M2)
    (hj : 1 ≤ j) (hN : 0 < N) (ht : 0 < t)
    (hzlo : (N : ℝ) ≤ z) (hzhi : z ≤ 2 * N)
    (hL : 2 ≤ r * M ^ j) (hq : r * M ^ j < 2 ^ q) :
    kernelFactor (r * M ^ j) (s * M2 ^ j) q
        ((-1 : ℝ) ^ j * t /
          (2 * Real.pi * (j : ℝ) * z ^ j)) ≤
      (r * M ^ j : ℝ) * (2 * (q : ℝ) + 1) * sourceW r s M M2 j N t := by
  have hr0 : 0 < (r : ℝ) := by positivity
  have hs0 : 0 < (s : ℝ) := by positivity
  have hM0 : 0 < (M : ℝ) := by positivity
  have hM20 : 0 < (M2 : ℝ) := by positivity
  have hN0 : 0 < (N : ℝ) := by positivity
  have hj0 : 0 < (j : ℝ) := by positivity
  have hz0 : 0 < z := lt_of_lt_of_le hN0 hzlo
  have hpi : 0 < Real.pi := Real.pi_pos
  have hzp : 0 < z ^ j := by positivity
  have hNp : 0 < (N : ℝ) ^ j := by positivity
  have h2Np : 0 < (2 * (N : ℝ)) ^ j := by positivity
  have hgamma0 : ((-1 : ℝ) ^ j * t /
      (2 * Real.pi * (j : ℝ) * z ^ j)) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt ht)
    · positivity
  have habsgamma :
      |((-1 : ℝ) ^ j * t /
        (2 * Real.pi * (j : ℝ) * z ^ j))| =
        t / (2 * Real.pi * (j : ℝ) * z ^ j) := by
    rw [abs_div, abs_mul, abs_mul]
    simp [abs_pow, abs_of_pos ht, abs_of_pos hpi, abs_of_pos hz0]
  have hNpow : (N : ℝ) ^ j ≤ z ^ j := by
    gcongr
  have hz2pow : z ^ j ≤ (2 * (N : ℝ)) ^ j := by
    gcongr
  have hC :
      2 * (s * M2 ^ j : ℝ) / (r * M ^ j) +
          2 * (s * M2 ^ j : ℝ) *
            |((-1 : ℝ) ^ j * t /
              (2 * Real.pi * (j : ℝ) * z ^ j))| +
          2 / ((r * M ^ j : ℝ) *
            |((-1 : ℝ) ^ j * t /
              (2 * Real.pi * (j : ℝ) * z ^ j))|) + 2 ≤
        sourceC r s M M2 j N t := by
    rw [habsgamma]
    unfold sourceC
    have hterm2 :
        2 * (s * M2 ^ j : ℝ) *
            (t / (2 * Real.pi * (j : ℝ) * z ^ j)) ≤
          (s : ℝ) * t * (M2 : ℝ) ^ j /
            (Real.pi * (j : ℝ) * (N : ℝ) ^ j) := by
      have heq :
          2 * (s * M2 ^ j : ℝ) *
              (t / (2 * Real.pi * (j : ℝ) * z ^ j)) =
            (s : ℝ) * t * (M2 : ℝ) ^ j /
              (Real.pi * (j : ℝ) * z ^ j) := by
        field_simp
      rw [heq]
      have hNpow' : Real.pi * (j : ℝ) * (N : ℝ) ^ j ≤
          Real.pi * (j : ℝ) * z ^ j :=
        mul_le_mul_of_nonneg_left hNpow (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hNpow'
    have hterm3 :
        2 / ((r * M ^ j : ℝ) *
            (t / (2 * Real.pi * (j : ℝ) * z ^ j))) ≤
          4 * Real.pi * (j : ℝ) * (2 * (N : ℝ)) ^ j /
            ((r : ℝ) * t * (M : ℝ) ^ j) := by
      have heq :
          2 / ((r * M ^ j : ℝ) *
              (t / (2 * Real.pi * (j : ℝ) * z ^ j))) =
            4 * Real.pi * (j : ℝ) * z ^ j /
              ((r : ℝ) * t * (M : ℝ) ^ j) := by
        field_simp
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hz2pow (by positivity)) (by positivity)
    calc
      2 * (s * M2 ^ j : ℝ) / (r * M ^ j) +
            2 * (s * M2 ^ j : ℝ) *
              (t / (2 * Real.pi * (j : ℝ) * z ^ j)) +
            2 / ((r * M ^ j : ℝ) *
              (t / (2 * Real.pi * (j : ℝ) * z ^ j))) + 2 ≤
          2 * (s * M2 ^ j : ℝ) / (r * M ^ j) +
            (s : ℝ) * t * (M2 : ℝ) ^ j /
              (Real.pi * (j : ℝ) * (N : ℝ) ^ j) +
            4 * Real.pi * (j : ℝ) * (2 * (N : ℝ)) ^ j /
              ((r : ℝ) * t * (M : ℝ) ^ j) + 2 := by
                linarith [hterm2, hterm3]
      _ = sourceC r s M M2 j N t := by
        unfold sourceC
        ring
  have hq1 : 1 ≤ q := by
    by_contra hqnot
    have hq0 : q = 0 := by omega
    subst q
    norm_num at hq
    omega
  have hcap := kernelFactor_le_mul_C_min (L := r * M ^ j)
    (K := s * M2 ^ j) (q := q)
    (gamma := (-1 : ℝ) ^ j * t /
      (2 * Real.pi * (j : ℝ) * z ^ j)) hL hq1 hgamma0
  have hcap' :
      kernelFactor (r * M ^ j) (s * M2 ^ j) q
        ((-1 : ℝ) ^ j * t /
          (2 * Real.pi * (j : ℝ) * z ^ j)) ≤
      (r * M ^ j : ℝ) * (2 * (q : ℝ) + 1) *
        min (2 * (s * M2 ^ j : ℝ))
          (2 * (s * M2 ^ j : ℝ) / (r * M ^ j) +
            2 * (s * M2 ^ j : ℝ) *
              |((-1 : ℝ) ^ j * t /
                (2 * Real.pi * (j : ℝ) * z ^ j))| +
            2 / ((r * M ^ j : ℝ) *
              |((-1 : ℝ) ^ j * t /
                (2 * Real.pi * (j : ℝ) * z ^ j))|) + 2) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hcap
  unfold sourceW
  calc
    kernelFactor (r * M ^ j) (s * M2 ^ j) q
        ((-1 : ℝ) ^ j * t /
          (2 * Real.pi * (j : ℝ) * z ^ j)) ≤
      (r * M ^ j : ℝ) * (2 * (q : ℝ) + 1) *
        min (2 * (s * M2 ^ j : ℝ))
          (2 * (s * M2 ^ j : ℝ) / (r * M ^ j) +
            2 * (s * M2 ^ j : ℝ) *
              |((-1 : ℝ) ^ j * t /
                (2 * Real.pi * (j : ℝ) * z ^ j))| +
            2 / ((r * M ^ j : ℝ) *
              |((-1 : ℝ) ^ j * t /
                (2 * Real.pi * (j : ℝ) * z ^ j))|) + 2) := hcap'
    _ ≤ (r * M ^ j : ℝ) * (2 * (q : ℝ) + 1) *
        min (2 * (s * M2 ^ j : ℝ)) (sourceC r s M M2 j N t) := by
      have hminC : min (2 * (s * M2 ^ j : ℝ))
          (2 * (s * M2 ^ j : ℝ) / (r * M ^ j) +
            2 * (s * M2 ^ j : ℝ) *
              |((-1 : ℝ) ^ j * t /
                (2 * Real.pi * (j : ℝ) * z ^ j))| +
            2 / ((r * M ^ j : ℝ) *
              |((-1 : ℝ) ^ j * t /
                (2 * Real.pi * (j : ℝ) * z ^ j))|) + 2) ≤
          min (2 * (s * M2 ^ j : ℝ)) (sourceC r s M M2 j N t) :=
        min_le_min_left _ hC
      have hfac : 0 ≤ (r * M ^ j : ℝ) * (2 * (q : ℝ) + 1) := by positivity
      exact mul_le_mul_of_nonneg_left hminC hfac

end
end FordSourceKernelFactor

#print axioms FordSourceKernelFactor.kernelFactor_le_mul_C_min
#print axioms FordSourceKernelFactor.kernelFactor_le_source
