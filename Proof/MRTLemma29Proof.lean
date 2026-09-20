import MRTLemma29GCDPartition

namespace MAPMRTLemma29Proof
open scoped BigOperators ZMod
open MAPMRTProposition51Source MAPMRTCorollary53Source
open MAPMRTLemma29Corrected MixedMeanFrontend MAPFarAnnulusSourceToModel
noncomputable section
set_option maxHeartbeats 1600000

lemma stdAddChar_factorization
    {q q0 q1 a n : ℕ} [NeZero q] [NeZero q1]
    (hq1 : 1 ≤ q1) (hfac : q0 * q1 = q) :
    ZMod.stdAddChar ((a * (q0 * n) : ℕ) : ZMod q) =
      ZMod.stdAddChar ((a * n : ℕ) : ZMod q1) := by
  rw [show ((a * (q0 * n) : ℕ) : ZMod q) =
      ((a * (q0 * n) : ℤ) : ZMod q) by norm_num,
    show ((a * n : ℕ) : ZMod q1) = ((a * n : ℤ) : ZMod q1) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hq0pos : 0 < q0 := by
    by_contra h
    have : q0 = 0 := by omega
    subst q0
    simp at hfac
    exact (NeZero.ne q) hfac.symm
  rw [← hfac]
  have hq0C : (q0 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq0pos)
  have hq1C : (q1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < q1))
  field_simp [hq0C, hq1C]
  push_cast
  ring

lemma norm_mellinPhase (n : ℕ) (t : ℝ) :
    ‖mellinPhase n t‖ = 1 := by
  unfold mellinPhase
  rw [show -(((t * Real.log n : ℝ) : ℂ)) * Complex.I =
      ((-(t * Real.log n) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma factorized_term
    {q q0 q1 a n : ℕ} [NeZero q] [NeZero q1]
    (hq0 : 1 ≤ q0) (hn : 1 ≤ n)
    (hq1 : 1 ≤ q1) (hfac : q0 * q1 = q)
    (f : ℕ → ℂ) (t : ℝ) :
    f (q0 * n) * (Real.sqrt (q0 * n) : ℂ)⁻¹ *
        mellinPhase (q0 * n) t *
        ZMod.stdAddChar ((a * (q0 * n) : ℕ) : ZMod q) =
      ((Real.sqrt q0 : ℂ)⁻¹ * mellinPhase q0 t) *
        ((f (q0 * n) * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t) *
          ZMod.stdAddChar ((a * n : ℕ) : ZMod q1)) := by
  rw [stdAddChar_factorization hq1 hfac]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ q0), Complex.ofReal_mul,
    mul_inv_rev]
  rw [mellinPhase_mul (by omega) (by omega)]
  ring

lemma character_polynomial_filter
    {N q0 q1 : ℕ} [NeZero q1] (f : ℕ → ℂ) (t : ℝ)
    (chi : DirichletCharacter ℂ q1) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q1),
      (f (q0 * n) * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t) * chi n) =
    ∑ n ∈ Finset.Icc 1 N,
      f (q0 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcop : n.Coprime q1
  · rw [if_pos hcop]
    ring
  · rw [if_neg hcop]
    have hnonunit : ¬ IsUnit (n : ZMod q1) := by
      simpa [ZMod.isUnit_iff_coprime] using hcop
    rw [chi.map_nonunit hnonunit]
    ring

lemma factor_component_bound
    {N q q0 q1 a : ℕ} [NeZero q]
    (hq0 : 1 ≤ q0) (hq1 : 1 ≤ q1) (hfac : q0 * q1 = q)
    (haq : a.Coprime q) (f : ℕ → ℂ) (t : ℝ) :
    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q1),
      f (q0 * n) * (Real.sqrt (q0 * n) : ℂ)⁻¹ *
        mellinPhase (q0 * n) t *
          ZMod.stdAddChar ((a * (q0 * n) : ℕ) : ZMod q)‖ ≤
      Real.sqrt q1 / (Real.sqrt q0 * q1.totient) *
        ∑ chi : DirichletCharacter ℂ q1,
          ‖∑ n ∈ Finset.Icc 1 N,
            f (q0 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
              mellinPhase n t‖ := by
  letI : NeZero q1 := ⟨by omega⟩
  let s := (Finset.Icc 1 N).filter (fun n => n.Coprime q1)
  let c : ℕ → ℂ := fun n =>
    f (q0 * n) * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t
  have hq1div : q1 ∣ q := ⟨q0, by simpa [mul_comm] using hfac.symm⟩
  have hacop : a.Coprime q1 := Nat.Coprime.of_dvd_right hq1div haq
  have haunit : IsUnit (a : ZMod q1) := by
    simpa [ZMod.isUnit_iff_coprime] using hacop
  have hsunit : ∀ n ∈ s, IsUnit (n : ZMod q1) := by
    intro n hn
    have hcop := (Finset.mem_filter.mp hn).2
    simpa [ZMod.isUnit_iff_coprime] using hcop
  have heq :
      (∑ n ∈ s,
        f (q0 * n) * (Real.sqrt (q0 * n) : ℂ)⁻¹ *
          mellinPhase (q0 * n) t *
            ZMod.stdAddChar ((a * (q0 * n) : ℕ) : ZMod q)) =
      ((Real.sqrt q0 : ℂ)⁻¹ * mellinPhase q0 t) *
        ∑ n ∈ s, c n *
          ZMod.stdAddChar ((a : ZMod q1) * (n : ZMod q1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hnmem
    have hn : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnmem).1).1
    rw [show ((a : ZMod q1) * (n : ZMod q1)) =
        ((a * n : ℕ) : ZMod q1) by norm_num]
    exact factorized_term hq0 hn hq1 hfac f t
  change ‖∑ n ∈ s,
      f (q0 * n) * (Real.sqrt (q0 * n) : ℂ)⁻¹ *
        mellinPhase (q0 * n) t *
          ZMod.stdAddChar ((a * (q0 * n) : ℕ) : ZMod q)‖ ≤ _
  rw [heq, norm_mul]
  have hconst :
      ‖(Real.sqrt q0 : ℂ)⁻¹ * mellinPhase q0 t‖ =
        (Real.sqrt q0)⁻¹ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity)), norm_mellinPhase, mul_one]
  rw [hconst]
  have hbound := finite_unit_character_bound
    (a : ZMod q1) haunit s c hsunit
  have hfilter (chi : DirichletCharacter ℂ q1) :
      (∑ n ∈ s, c n * chi n) =
        ∑ n ∈ Finset.Icc 1 N,
          f (q0 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
            mellinPhase n t := by
    exact character_polynomial_filter f t chi
  simp_rw [hfilter] at hbound
  have hsqrt0 : 0 < Real.sqrt q0 := Real.sqrt_pos.2 (by positivity)
  have hphi : 0 < (q1.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  calc
    (Real.sqrt q0)⁻¹ * ‖∑ n ∈ s, c n *
        ZMod.stdAddChar ((a : ZMod q1) * (n : ZMod q1))‖ ≤
      (Real.sqrt q0)⁻¹ * (Real.sqrt q1 / q1.totient *
        ∑ chi : DirichletCharacter ℂ q1,
          ‖∑ n ∈ Finset.Icc 1 N,
            f (q0 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
              mellinPhase n t‖) := by
        gcongr
    _ = Real.sqrt q1 / (Real.sqrt q0 * q1.totient) *
        ∑ chi : DirichletCharacter ℂ q1,
          ‖∑ n ∈ Finset.Icc 1 N,
            f (q0 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
              mellinPhase n t‖ := by
      field_simp

theorem mrtLemma29Supported_proof : MRTLemma29Supported := by
  intro N q a f t hq haq hsupport
  letI : NeZero q := ⟨by omega⟩
  let g : ℕ → ℂ := fun n =>
    f n * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t *
      ZMod.stdAddChar ((a * n : ℕ) : ZMod q)
  have hgsupport : ∀ n, N < n → g n = 0 := by
    intro n hn
    simp [g, hsupport n hn]
  have hlhs :
      finiteCriticalPolynomial N (additiveTwist q a f) t =
        ∑ n ∈ Finset.Icc 1 N, g n := by
    unfold finiteCriticalPolynomial additiveTwist
    apply Finset.sum_congr rfl
    intro n hn
    rw [additive_phase_eq_stdAddChar a n]
    dsimp [g]
    ring
  rw [hlhs, gcd_coordinate_partition_supported hq g hgsupport]
  calc
    ‖∑ z ∈ modulusFactorizations q,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime z.2),
          g (z.1 * n)‖ ≤
      ∑ z ∈ modulusFactorizations q,
        ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime z.2),
          g (z.1 * n)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ z ∈ modulusFactorizations q,
        ((divisorCount q : ℝ) / Real.sqrt q) *
          ∑ chi : DirichletCharacter ℂ z.2,
            ‖∑ n ∈ Finset.Icc 1 N,
              f (z.1 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
                mellinPhase n t‖ := by
      apply Finset.sum_le_sum
      intro z hz
      have hzmem := Finset.mem_filter.mp hz
      have hzprod := Finset.mem_product.mp hzmem.1
      have hq0 : 1 ≤ z.1 := (Finset.mem_Icc.mp hzprod.1).1
      have hq1 : 1 ≤ z.2 := (Finset.mem_Icc.mp hzprod.2).1
      have hfac : z.1 * z.2 = q := hzmem.2
      have hcomp := factor_component_bound
        (N := N) hq0 hq1 hfac haq f t
      have hcharsNonneg : 0 ≤
          ∑ chi : DirichletCharacter ℂ z.2,
            ‖∑ n ∈ Finset.Icc 1 N,
              f (z.1 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
                mellinPhase n t‖ := by positivity
      have hfinal := hcomp.trans (mul_le_mul_of_nonneg_right
        (factor_coefficient_le hq0 hq1 hfac) hcharsNonneg)
      simpa only [g, Nat.cast_mul] using hfinal
    _ = (divisorCount q : ℝ) / Real.sqrt q *
        ∑ z ∈ modulusFactorizations q,
          ∑ chi : DirichletCharacter ℂ z.2,
            ‖∑ n ∈ Finset.Icc 1 N,
              f (z.1 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
                mellinPhase n t‖ := by
      rw [Finset.mul_sum]

end
end MAPMRTLemma29Proof
