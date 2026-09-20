import GoldfeldPolyaVinogradov
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The interval Fourier-kernel bound in Pólya--Vinogradov

This file removes the zero Fourier mode and proves the geometric-series and
chord estimates underlying the `O(N log N)` interval-kernel `L¹` bound.
-/

namespace MAPGoldfeldSiegel

open Complex
open scoped ZMod BigOperators

noncomputable section
set_option maxHeartbeats 1000000

/-- For a nontrivial modulus the zero Fourier coefficient in the primitive
character expansion vanishes. -/
theorem primitive_partialSum_eq_fourier_ne_zero
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (A M : ℕ) :
    (∑ n ∈ Finset.range M, chi ((A + n : ℕ) : ZMod N)) =
      (N : ℂ)⁻¹ * ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
          additiveIntervalKernel N A M k := by
  rw [primitive_partialSum_eq_fourier chi hprim]
  congr 1
  symm
  apply Finset.sum_erase
  haveI : Fact (1 < N) := ⟨lt_of_lt_of_le Nat.one_lt_two hN⟩
  simp only [neg_zero, MulChar.map_zero, zero_mul]

/-- A unit-circle geometric sum is uniformly bounded by the reciprocal chord. -/
theorem norm_geometric_sum_le_two_div_norm_one_sub
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, z ^ n‖ ≤ 2 / ‖1 - z‖ := by
  have hgeom := geom_sum_mul_neg z M
  have hden : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
  have hn := congrArg norm hgeom
  rw [norm_mul] at hn
  apply (le_div_iff₀ hden).2
  rw [hn]
  calc
    ‖1 - z ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ M‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, norm_pow, hz, one_pow]; norm_num

/-- The standard additive character at a nonzero frequency is not one. -/
theorem stdAddChar_ne_one {N : ℕ} [NeZero N] {k : ZMod N} (hk : k ≠ 0) :
    ZMod.stdAddChar k ≠ 1 := by
  intro h
  have h0 : ZMod.stdAddChar k = ZMod.stdAddChar (0 : ZMod N) := by simpa using h
  exact hk (ZMod.injective_stdAddChar h0)

/-- Exact chord length for a standard additive character. -/
theorem norm_one_sub_stdAddChar_eq
    {N : ℕ} [NeZero N] (k : ZMod N) :
    ‖1 - ZMod.stdAddChar k‖ =
      ‖2 * Real.sin (Real.pi * (k.val : ℝ) / N)‖ := by
  rw [norm_sub_rev]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change ‖Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / N) - 1‖ = _
  convert Complex.norm_exp_I_mul_ofReal_sub_one
      (2 * Real.pi * (k.val : ℝ) / N) using 2 <;>
    push_cast <;> ring

/-- The interval kernel is a harmless phase times a geometric sum. -/
theorem additiveIntervalKernel_eq_phase_mul_geom
    {N : ℕ} [NeZero N] (A M : ℕ) (k : ZMod N) :
    additiveIntervalKernel N A M k =
      ZMod.stdAddChar (k * (A : ZMod N)) *
        ∑ n ∈ Finset.range M, (ZMod.stdAddChar k) ^ n := by
  simp only [additiveIntervalKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← AddChar.map_nsmul_eq_pow]
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  push_cast
  simp [mul_add, mul_comm, nsmul_eq_mul]

/-- Pointwise geometric bound for every nonzero interval frequency. -/
theorem norm_additiveIntervalKernel_le_chord
    {N : ℕ} [NeZero N] (A M : ℕ) {k : ZMod N} (hk : k ≠ 0) :
    ‖additiveIntervalKernel N A M k‖ ≤
      2 / ‖1 - ZMod.stdAddChar k‖ := by
  rw [additiveIntervalKernel_eq_phase_mul_geom]
  rw [norm_mul, show ‖ZMod.stdAddChar (k * (A : ZMod N))‖ = 1 by
    simpa [ZMod.stdAddChar_apply] using (ZMod.toCircle (k * (A : ZMod N))).property, one_mul]
  exact norm_geometric_sum_le_two_div_norm_one_sub _
    (by simpa [ZMod.stdAddChar_apply] using (ZMod.toCircle k).property)
    (stdAddChar_ne_one hk) M

/-- On the lower half of the frequency range, the chord is bounded below by
four times the normalized frequency. -/
theorem four_mul_nat_div_le_norm_one_sub_stdAddChar
    {N k : ℕ} [NeZero N] (hk : 2 * k ≤ N) :
    4 * (k : ℝ) / N ≤
      ‖1 - ZMod.stdAddChar (k : ZMod N)‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.ne N).bot_lt
  have hklt : k < N := by
    by_cases hk0 : k = 0
    · subst k
      exact Nat.zero_lt_of_ne_zero (NeZero.ne N)
    · omega
  rw [norm_one_sub_stdAddChar_eq]
  rw [ZMod.val_natCast_of_lt hklt]
  have hx0 : 0 ≤ Real.pi * (k : ℝ) / N := by positivity
  have hxhalf : Real.pi * (k : ℝ) / N ≤ Real.pi / 2 := by
    have hkR : 2 * (k : ℝ) ≤ N := by exact_mod_cast hk
    rw [div_le_div_iff₀ hN (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_left hkR Real.pi_pos.le]
  have hsin := Real.mul_le_sin hx0 hxhalf
  have hbase : 2 * (k : ℝ) / N ≤
      Real.sin (Real.pi * (k : ℝ) / N) := by
    calc
      2 * (k : ℝ) / N =
          2 / Real.pi * (Real.pi * (k : ℝ) / N) := by
            field_simp [Real.pi_ne_zero, hN.ne']
      _ ≤ _ := hsin
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi hx0 (hxhalf.trans (by linarith [Real.pi_pos]))))]
  calc
    4 * (k : ℝ) / N = 2 * (2 * (k : ℝ) / N) := by ring
    _ ≤ 2 * Real.sin (Real.pi * (k : ℝ) / N) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)

/-- Distance of a residue frequency to the nearest endpoint of the standard
frequency interval. -/
def frequencyDistance {N : ℕ} [NeZero N] (k : ZMod N) : ℕ :=
  min k.val (N - k.val)

theorem frequencyDistance_pos {N : ℕ} [NeZero N] {k : ZMod N} (hk : k ≠ 0) :
    0 < frequencyDistance k := by
  have hv0 : 0 < k.val := by
    exact Nat.pos_of_ne_zero (by
      intro hv
      apply hk
      apply ZMod.val_injective
      simpa [hv])
  exact lt_min hv0 (Nat.sub_pos_of_lt k.val_lt)

/-- Uniform lower chord bound in terms of centered frequency distance. -/
theorem four_mul_frequencyDistance_div_le_norm_one_sub_stdAddChar
    {N : ℕ} [NeZero N] {k : ZMod N} (hk : k ≠ 0) :
    4 * (frequencyDistance k : ℝ) / N ≤
      ‖1 - ZMod.stdAddChar k‖ := by
  have hv0 : 0 < k.val := by
    exact Nat.pos_of_ne_zero (by
      intro hv
      apply hk
      apply ZMod.val_injective
      simpa [hv])
  by_cases hlo : 2 * k.val ≤ N
  · have hmin : min k.val (N - k.val) = k.val := by
      rw [min_eq_left]
      omega
    rw [frequencyDistance, hmin]
    simpa only [ZMod.natCast_zmod_val] using
      (four_mul_nat_div_le_norm_one_sub_stdAddChar (N := N) hlo)
  · have htwo : 2 * (N - k.val) ≤ N := by omega
    have hjlt : N - k.val < N := Nat.sub_lt
      (Nat.zero_lt_of_ne_zero (NeZero.ne N)) hv0
    have hmin : min k.val (N - k.val) = N - k.val := by
      rw [min_eq_right]
      simp only [not_le] at hlo
      omega
    rw [frequencyDistance, hmin]
    have hj := four_mul_nat_div_le_norm_one_sub_stdAddChar (N := N) htwo
    have hchord :
        ‖1 - ZMod.stdAddChar ((N - k.val : ℕ) : ZMod N)‖ =
          ‖1 - ZMod.stdAddChar k‖ := by
      rw [norm_one_sub_stdAddChar_eq, norm_one_sub_stdAddChar_eq]
      rw [ZMod.val_natCast_of_lt hjlt]
      congr 2
      have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.ne N).bot_lt
      have hang : Real.pi * ((N - k.val : ℕ) : ℝ) / N =
          Real.pi - Real.pi * (k.val : ℝ) / N := by
        rw [Nat.cast_sub k.val_le]
        field_simp [hN.ne']
      rw [hang, Real.sin_pi_sub]
    exact hj.trans_eq hchord

/-- Pointwise interval-kernel estimate in centered frequency coordinates. -/
theorem norm_additiveIntervalKernel_le_level_div_two_distance
    {N : ℕ} [NeZero N] (A M : ℕ) {k : ZMod N} (hk : k ≠ 0) :
    ‖additiveIntervalKernel N A M k‖ ≤
      (N : ℝ) / (2 * frequencyDistance k) := by
  have hd : (0 : ℝ) < frequencyDistance k := by
    exact_mod_cast frequencyDistance_pos hk
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.ne N).bot_lt
  have hchord := four_mul_frequencyDistance_div_le_norm_one_sub_stdAddChar hk
  have hsmall : 0 < 4 * (frequencyDistance k : ℝ) / N := by positivity
  have hden : 0 < ‖1 - ZMod.stdAddChar k‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (stdAddChar_ne_one hk).symm)
  calc
    ‖additiveIntervalKernel N A M k‖
        ≤ 2 / ‖1 - ZMod.stdAddChar k‖ :=
          norm_additiveIntervalKernel_le_chord A M hk
    _ ≤ 2 / (4 * (frequencyDistance k : ℝ) / N) :=
      div_le_div_of_nonneg_left (by norm_num) hsmall hchord
    _ = (N : ℝ) / (2 * frequencyDistance k) := by
      field_simp [hN.ne', hd.ne']
      ring

/-- Re-indexing nonzero residues by their standard representatives. -/
theorem sum_zmod_erase_zero_eq_sum_Icc_val
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (f : ZMod N → ℝ) :
    (∑ k ∈ (Finset.univ.erase (0 : ZMod N)), f k) =
      ∑ v ∈ Finset.Icc 1 (N - 1), f (v : ZMod N) := by
  apply Finset.sum_bij (fun k _ ↦ k.val)
  · intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by
      intro hv
      apply hk
      apply ZMod.val_injective
      simpa [hv]), by
        have hvlt := k.val_lt
        omega⟩
  · intro a ha b hb hab
    apply ZMod.val_injective
    exact hab
  · intro v hv
    have hvI := Finset.mem_Icc.mp hv
    have hvlt : v < N := by omega
    refine ⟨(v : ZMod N), ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hv0
      have := congrArg ZMod.val hv0
      rw [ZMod.val_natCast_of_lt hvlt] at this
      simp at this
      omega
    · exact ZMod.val_natCast_of_lt hvlt
  · intro k hk
    rw [ZMod.natCast_zmod_val]

theorem inv_frequencyDistance_natCast_le
    {N v : ℕ} [NeZero N] (hv : v ∈ Finset.Icc 1 (N - 1)) :
    ((frequencyDistance (v : ZMod N) : ℕ) : ℝ)⁻¹ ≤
      (v : ℝ)⁻¹ + ((N - v : ℕ) : ℝ)⁻¹ := by
  have hvI := Finset.mem_Icc.mp hv
  have hvlt : v < N := by omega
  rw [frequencyDistance, ZMod.val_natCast_of_lt hvlt]
  by_cases hle : v ≤ N - v
  · rw [min_eq_left hle]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (by positivity))
  · rw [min_eq_right (le_of_not_ge hle)]
    exact le_add_of_nonneg_left (inv_nonneg.mpr (by positivity))

theorem sum_Icc_reflected_inv
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ v ∈ Finset.Icc 1 (N - 1), (((N - v : ℕ) : ℝ)⁻¹)) =
      ∑ v ∈ Finset.Icc 1 (N - 1), ((v : ℝ)⁻¹) := by
  apply Finset.sum_bij (fun v _ ↦ N - v)
  · intro v hv
    have hvI := Finset.mem_Icc.mp hv
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb hab
    have haI := Finset.mem_Icc.mp ha
    have hbI := Finset.mem_Icc.mp hb
    omega
  · intro v hv
    have hvI := Finset.mem_Icc.mp hv
    refine ⟨N - v, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · omega
  · intro v hv
    have hvI := Finset.mem_Icc.mp hv
    congr 2

theorem sum_Icc_inv_eq_harmonic_real (n : ℕ) :
    (∑ v ∈ Finset.Icc 1 n, ((v : ℝ)⁻¹)) = (harmonic n : ℝ) := by
  have h := congrArg (fun x : ℚ ↦ (x : ℝ))
    (harmonic_eq_sum_Icc (n := n))
  change (harmonic n : ℝ) =
    ((∑ i ∈ Finset.Icc 1 n, (i : ℚ)⁻¹ : ℚ) : ℝ) at h
  rw [Rat.cast_sum] at h
  simpa using h.symm

/-- The centered reciprocal frequencies have the expected harmonic mass. -/
theorem sum_inv_frequencyDistance_le
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        (((frequencyDistance k : ℕ) : ℝ)⁻¹)) ≤
      2 * (1 + Real.log N) := by
  rw [sum_zmod_erase_zero_eq_sum_Icc_val hN]
  calc
    (∑ v ∈ Finset.Icc 1 (N - 1),
        (((frequencyDistance (v : ZMod N) : ℕ) : ℝ)⁻¹))
        ≤ ∑ v ∈ Finset.Icc 1 (N - 1),
            ((v : ℝ)⁻¹ + (((N - v : ℕ) : ℝ)⁻¹)) := by
          apply Finset.sum_le_sum
          intro v hv
          exact inv_frequencyDistance_natCast_le hv
    _ = 2 * (harmonic (N - 1) : ℝ) := by
      rw [Finset.sum_add_distrib, sum_Icc_reflected_inv hN,
        sum_Icc_inv_eq_harmonic_real]
      ring
    _ ≤ 2 * (1 + Real.log N) := by
      gcongr
      calc
        (harmonic (N - 1) : ℝ) ≤
            1 + Real.log ((N - 1 : ℕ) : ℝ) :=
          harmonic_le_one_add_log _
        _ ≤ 1 + Real.log (N : ℝ) := by
          have hlog := Real.log_le_log
            (x := ((N - 1 : ℕ) : ℝ)) (y := (N : ℝ))
            (by exact_mod_cast (show 0 < N - 1 by omega))
            (by exact_mod_cast (Nat.sub_le N 1))
          linarith

/-- Character-free `L¹` bound for every integer interval Fourier kernel. -/
theorem sum_norm_additiveIntervalKernel_le
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (A M : ℕ) :
    (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        ‖additiveIntervalKernel N A M k‖) ≤
      (N : ℝ) * (1 + Real.log N) := by
  calc
    (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        ‖additiveIntervalKernel N A M k‖)
        ≤ ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
            (N : ℝ) / (2 * frequencyDistance k) := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
          exact norm_additiveIntervalKernel_le_level_div_two_distance A M hk
    _ = ((N : ℝ) / 2) *
          ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
            (((frequencyDistance k : ℕ) : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [div_eq_mul_inv]
      ring
    _ ≤ ((N : ℝ) / 2) * (2 * (1 + Real.log N)) := by
      exact mul_le_mul_of_nonneg_left (sum_inv_frequencyDistance_le hN)
        (by positivity)
    _ = (N : ℝ) * (1 + Real.log N) := by ring

/-- Pólya--Vinogradov for the primitive quadratic characters needed in the
Goldfeld comparison and in the specialized Jutila collar argument.  The bound
is uniform in the starting point and interval length. -/
theorem primitive_quadratic_polyaVinogradov
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hreal : chi ^ 2 = 1) (A M : ℕ) :
    ‖∑ n ∈ Finset.range M, chi ((A + n : ℕ) : ZMod N)‖ ≤
      Real.sqrt N * (1 + Real.log N) := by
  rw [primitive_partialSum_eq_fourier_ne_zero hN chi hprim]
  have hsum :
      ‖∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
          (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
            additiveIntervalKernel N A M k‖ ≤
        Real.sqrt N *
          ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
            ‖additiveIntervalKernel N A M k‖ := by
    calc
      ‖∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
          (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
            additiveIntervalKernel N A M k‖
          ≤ ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
              ‖(chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
                additiveIntervalKernel N A M k‖ := norm_sum_le _ _
      _ ≤ Real.sqrt N *
            ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
              ‖additiveIntervalKernel N A M k‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul, norm_mul,
            norm_gaussSum_stdAddChar_eq_sqrt chi hprim hreal]
          gcongr 1
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right ((chi⁻¹).norm_le_one (-k))
              (Real.sqrt_nonneg (N : ℝ)))
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (NeZero.ne N).bot_lt
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNreal).ne'
  calc
    ‖(N : ℂ)⁻¹ * ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
          additiveIntervalKernel N A M k‖
        = (N : ℝ)⁻¹ *
            ‖∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
              (chi⁻¹ (-k) * gaussSum chi ZMod.stdAddChar) *
                additiveIntervalKernel N A M k‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (N : ℝ)⁻¹ * (Real.sqrt N *
          ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
            ‖additiveIntervalKernel N A M k‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (N : ℝ)⁻¹ * (Real.sqrt N *
          ((N : ℝ) * (1 + Real.log N))) := by
      gcongr
      exact sum_norm_additiveIntervalKernel_le hN A M
    _ = Real.sqrt N * (1 + Real.log N) := by
      field_simp [hNreal.ne', hsqrt]

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.primitive_partialSum_eq_fourier_ne_zero
#print axioms MAPGoldfeldSiegel.norm_geometric_sum_le_two_div_norm_one_sub
#print axioms MAPGoldfeldSiegel.norm_one_sub_stdAddChar_eq
