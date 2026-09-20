import MRTCorollary25TransitionBand
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The finite `min`-sum in the MRT truncated Perron error
-/

namespace MAPMRTCorollary25MinSum

open scoped BigOperators
open Set MeasureTheory
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- A reciprocal harmonic tail is controlled by its first term plus the
literal logarithm of the endpoint ratio. -/
theorem sum_Icc_inv_le_inv_add_log_ratio
    {L M : ℕ} (hL : 1 ≤ L) (hLM : L ≤ M) :
    (∑ k ∈ Finset.Icc L M, 1 / (k : ℝ)) ≤
      1 / (L : ℝ) + Real.log ((M : ℝ) / (L : ℝ)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hL.trans hLM
  have htail :
      (∑ k ∈ Finset.Ico (L + 1) (M + 1), 1 / (k : ℝ)) ≤
        ∫ x in (L : ℝ)..(M : ℝ), x⁻¹ := by
    have hanti : AntitoneOn (fun x : ℝ => x⁻¹)
        (Set.Icc (L : ℝ) (M : ℝ)) :=
      inv_antitoneOn_Icc_right hLpos
    have hbase := hanti.sum_le_integral_Ico hLM
    rw [← Finset.sum_Ico_add'
      (fun k : ℕ => 1 / (k : ℝ)) L M 1]
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using hbase
  have hint : (∫ x in (L : ℝ)..(M : ℝ), x⁻¹) =
      Real.log ((M : ℝ) / (L : ℝ)) := by
    exact integral_inv (by
      rw [Set.uIcc_of_le (by exact_mod_cast hLM)]
      simp [not_le_of_gt hLpos])
  rw [hint] at htail
  have hsplit :
      (∑ k ∈ Finset.Icc L M, 1 / (k : ℝ)) =
        1 / (L : ℝ) +
          ∑ k ∈ Finset.Ico (L + 1) (M + 1), 1 / (k : ℝ) := by
    rw [Finset.Icc_eq_cons_Ioc hLM]
    rw [Finset.sum_cons]
    rw [← Finset.Ico_add_one_add_one_eq_Ioc L M]
  rw [hsplit]
  gcongr


/-- Half-integer distance on the inside of a natural prefix. -/
theorem abs_halfInteger_sub_nat_eq_inside
    {N n : ℕ} (hn : n ≤ N) :
    |halfIntegerPoint N - (n : ℝ)| = (N - n : ℕ) + (1 / 2 : ℝ) := by
  have hcast : (n : ℝ) ≤ N := by exact_mod_cast hn
  rw [abs_of_nonneg]
  · unfold halfIntegerPoint
    rw [Nat.cast_sub hn]
    push_cast
    ring
  · unfold halfIntegerPoint
    linarith

/-- Half-integer distance on the outside of a natural prefix. -/
theorem abs_halfInteger_sub_nat_eq_outside
    {N n : ℕ} (hn : N < n) :
    |halfIntegerPoint N - (n : ℝ)| = (n - N - 1 : ℕ) + (1 / 2 : ℝ) := by
  have hcast : (N + 1 : ℕ) ≤ n := Nat.add_one_le_iff.mpr hn
  have hreal : (N : ℝ) + 1 ≤ n := by exact_mod_cast hcast
  rw [abs_of_nonpos]
  · unfold halfIntegerPoint
    have hsub : n - N - 1 = n - (N + 1) := by omega
    rw [hsub, Nat.cast_sub hcast]
    push_cast
    ring
  · unfold halfIntegerPoint
    linarith

private def insideIndices (M N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun n => n ≤ N)

private def outsideIndices (M N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun n => ¬ n ≤ N)

private def insideDistances (M N : ℕ) : Finset ℕ :=
  (insideIndices M N).image (fun n => N - n)

private def outsideDistances (M N : ℕ) : Finset ℕ :=
  (outsideIndices M N).image (fun n => n - N - 1)

private theorem insideDistances_subset (M N : ℕ) (hNM : N ≤ M) :
    insideDistances M N ⊆ Finset.Icc 0 M := by
  intro k hk
  simp only [insideDistances, Finset.mem_image] at hk
  rcases hk with ⟨n, hn, rfl⟩
  simp only [insideIndices, Finset.mem_filter, Finset.mem_Icc] at hn
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.sub_le N n).trans hNM⟩

private theorem outsideDistances_subset (M N : ℕ) :
    outsideDistances M N ⊆ Finset.Icc 0 M := by
  intro k hk
  simp only [outsideDistances, Finset.mem_image] at hk
  rcases hk with ⟨n, hn, rfl⟩
  simp only [outsideIndices, Finset.mem_filter, Finset.mem_Icc] at hn
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.sub_le n (N + 1)).trans hn.1.2⟩

/-- A half-integer has at most two natural indices at each distance shell. -/
theorem halfInteger_minSum_le_two_shellSums
    (M N : ℕ) (hNM : N ≤ M) (A : ℝ) (hA : 0 ≤ A) :
    (∑ n ∈ Finset.Icc 1 M,
        min 1 (A / |halfIntegerPoint N - (n : ℝ)|)) ≤
      2 * ∑ k ∈ Finset.Icc 0 M,
        min 1 (A / ((k : ℝ) + 1 / 2)) := by
  let g : ℕ → ℝ := fun k => min 1 (A / ((k : ℝ) + 1 / 2))
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    exact le_min (by norm_num) (div_nonneg hA (by positivity))
  have hpartition :
      (∑ n ∈ Finset.Icc 1 M,
          min 1 (A / |halfIntegerPoint N - (n : ℝ)|)) =
        ∑ n ∈ insideIndices M N,
          min 1 (A / |halfIntegerPoint N - (n : ℝ)|) +
        ∑ n ∈ outsideIndices M N,
          min 1 (A / |halfIntegerPoint N - (n : ℝ)|) := by
    exact (Finset.sum_filter_add_sum_filter_not
      (Finset.Icc 1 M) (fun n => n ≤ N)
      (fun n => min 1 (A / |halfIntegerPoint N - (n : ℝ)|))).symm
  rw [hpartition]
  have hinj : Set.InjOn (fun n : ℕ => N - n) (insideIndices M N : Set ℕ) := by
    intro a ha b hb hab
    simp only [insideIndices, Finset.coe_filter, Finset.coe_Icc,
      Set.mem_setOf_eq, Set.mem_Icc] at ha hb
    change N - a = N - b at hab
    calc
      a = N - (N - a) := by omega
      _ = N - (N - b) := by rw [hab]
      _ = b := by omega
  have houtinj : Set.InjOn (fun n : ℕ => n - N - 1) (outsideIndices M N : Set ℕ) := by
    intro a ha b hb hab
    simp only [outsideIndices, Finset.coe_filter, Finset.coe_Icc,
      Set.mem_setOf_eq, Set.mem_Icc] at ha hb
    change a - N - 1 = b - N - 1 at hab
    have haN : N + 1 ≤ a := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge ha.2)
    have hbN : N + 1 ≤ b := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hb.2)
    calc
      a = (a - N - 1) + (N + 1) := by omega
      _ = (b - N - 1) + (N + 1) := by rw [hab]
      _ = b := by omega
  have hinsum :
      (∑ n ∈ insideIndices M N,
          min 1 (A / |halfIntegerPoint N - (n : ℝ)|)) =
        ∑ k ∈ insideDistances M N, g k := by
    unfold insideDistances
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [insideIndices, Finset.mem_filter] at hn
    rw [abs_halfInteger_sub_nat_eq_inside hn.2]
  have houtsum :
      (∑ n ∈ outsideIndices M N,
          min 1 (A / |halfIntegerPoint N - (n : ℝ)|)) =
        ∑ k ∈ outsideDistances M N, g k := by
    unfold outsideDistances
    rw [Finset.sum_image houtinj]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [outsideIndices, Finset.mem_filter] at hn
    rw [abs_halfInteger_sub_nat_eq_outside (Nat.lt_of_not_ge hn.2)]
  rw [hinsum, houtsum]
  have hi := Finset.sum_le_sum_of_subset_of_nonneg
    (insideDistances_subset M N hNM)
    (fun i hi hnot => hg0 i)
  have ho := Finset.sum_le_sum_of_subset_of_nonneg
    (outsideDistances_subset M N)
    (fun i hi hnot => hg0 i)
  nlinarith


/-- Shifting the zero-based reciprocal sum gives the ordinary harmonic
number. -/
theorem sum_Icc_zero_inv_add_one_eq_harmonic (M : ℕ) :
    (∑ k ∈ Finset.Icc 0 M, 1 / ((k : ℝ) + 1)) =
      ((harmonic (M + 1) : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro a ha b hb hab
    omega
  · intro j hj
    refine ⟨j - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hj ⊢
      omega
    · change (j - 1) + 1 = j
      simp only [Finset.mem_Icc] at hj
      omega
  · intro k hk
    push_cast
    ring

/-- The complete half-integer shell sum has the exact source scale
`A log(2+T)` whenever the ambient length is at most `A*T`. -/
theorem halfInteger_shellMinSum_le
    {A T : ℝ} {M : ℕ} (hA : 0 < A) (hT : 1 ≤ T)
    (hM : (M : ℝ) ≤ A * T) :
    (∑ k ∈ Finset.Icc 0 M,
        min 1 (A / ((k : ℝ) + 1 / 2))) ≤
      4 * A * (1 + Real.log (2 + T)) := by
  have hlog0 : 0 ≤ Real.log (2 + T) := by
    exact Real.log_nonneg (by linarith)
  have hT0 : 0 ≤ T := by linarith
  by_cases hAsmall : A < 1
  · have hpoint : ∀ k : ℕ,
        min 1 (A / ((k : ℝ) + 1 / 2)) ≤
          2 * A * (1 / ((k : ℝ) + 1)) := by
      intro k
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hd1 : 0 < (k : ℝ) + 1 / 2 := by positivity
      have hd2 : 0 < (k : ℝ) + 1 := by positivity
      calc
        min 1 (A / ((k : ℝ) + 1 / 2)) ≤
            A / ((k : ℝ) + 1 / 2) := min_le_right _ _
        _ ≤ 2 * A * (1 / ((k : ℝ) + 1)) := by
          rw [div_eq_mul_inv]
          have hcomp : ((k : ℝ) + 1) ≤
              2 * ((k : ℝ) + 1 / 2) := by linarith
          have hinv : (((k : ℝ) + 1 / 2)⁻¹) ≤
              2 * (((k : ℝ) + 1)⁻¹) := by
            apply (le_div_iff₀ hd2).2
            rw [inv_mul_eq_div, div_le_iff₀ hd1]
            nlinarith
          calc
            A * (((k : ℝ) + 1 / 2)⁻¹) ≤
                A * (2 * (((k : ℝ) + 1)⁻¹)) :=
              mul_le_mul_of_nonneg_left hinv hA.le
            _ = 2 * A * (1 / ((k : ℝ) + 1)) := by ring
    calc
      (∑ k ∈ Finset.Icc 0 M,
          min 1 (A / ((k : ℝ) + 1 / 2))) ≤
        ∑ k ∈ Finset.Icc 0 M,
          2 * A * (1 / ((k : ℝ) + 1)) :=
        Finset.sum_le_sum fun k hk => hpoint k
      _ = 2 * A * ((harmonic (M + 1) : ℚ) : ℝ) := by
        rw [← Finset.mul_sum, sum_Icc_zero_inv_add_one_eq_harmonic]
      _ ≤ 2 * A * (1 + Real.log (M + 1 : ℕ)) := by
        gcongr
        exact harmonic_le_one_add_log (M + 1)
      _ ≤ 2 * A * (1 + Real.log (2 + T)) := by
        gcongr
        have hMlt : (M : ℝ) < T := lt_of_le_of_lt hM (by
          nlinarith [mul_lt_mul_of_pos_right hAsmall
            (lt_of_lt_of_le zero_lt_one hT)])
        norm_num at *
        linarith
      _ ≤ 4 * A * (1 + Real.log (2 + T)) := by
        nlinarith [mul_nonneg hA.le (by linarith : 0 ≤ 1 + Real.log (2 + T))]
  · have hA1 : 1 ≤ A := le_of_not_gt hAsmall
    let L : ℕ := Nat.ceil A
    have hLpos : 1 ≤ L := by
      dsimp only [L]
      exact_mod_cast (show (1 : ℝ) ≤ Nat.ceil A by
        exact hA1.trans (Nat.le_ceil A))
    have hAL : A ≤ (L : ℝ) := by
      dsimp only [L]
      exact Nat.le_ceil A
    have hLle : (L : ℝ) ≤ A + 1 := by
      dsimp only [L]
      exact (Nat.ceil_lt_add_one hA.le).le
    by_cases hLM : L ≤ M
    · have hnearSet :
          (Finset.Icc 0 M).filter (fun k => k < L) = Finset.Ico 0 L := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
        omega
      have hfarSet :
          (Finset.Icc 0 M).filter (fun k => ¬ k < L) = Finset.Icc L M := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (Finset.Icc 0 M) (fun k => k < L)
        (fun k => min 1 (A / ((k : ℝ) + 1 / 2)))
      rw [hnearSet, hfarSet] at hsplit
      rw [← hsplit]
      have hnearCard :
          (∑ k ∈ Finset.Ico 0 L,
              min 1 (A / ((k : ℝ) + 1 / 2))) ≤ (L : ℝ) := by
        calc
          _ ≤ ∑ k ∈ Finset.Ico 0 L, (1 : ℝ) :=
            Finset.sum_le_sum fun k hk => min_le_left _ _
          _ = (L : ℝ) := by simp
      have hfarPoint : ∀ k ∈ Finset.Icc L M,
          min 1 (A / ((k : ℝ) + 1 / 2)) ≤ A * (1 / (k : ℝ)) := by
        intro k hk
        have hkpos : (0 : ℝ) < k := by
          exact_mod_cast hLpos.trans (Finset.mem_Icc.mp hk).1
        calc
          min 1 (A / ((k : ℝ) + 1 / 2)) ≤
              A / ((k : ℝ) + 1 / 2) := min_le_right _ _
          _ ≤ A * (1 / (k : ℝ)) := by
            rw [div_eq_mul_inv]
            have hkle : (k : ℝ) ≤ (k : ℝ) + 1 / 2 := by norm_num
            have hinv : (((k : ℝ) + 1 / 2)⁻¹) ≤ ((k : ℝ)⁻¹) :=
              inv_anti₀ hkpos hkle
            simpa only [one_div] using
              (mul_le_mul_of_nonneg_left hinv hA.le)
      have htailBase := sum_Icc_inv_le_inv_add_log_ratio hLpos hLM
      have hfarSum :
          (∑ k ∈ Finset.Icc L M,
              min 1 (A / ((k : ℝ) + 1 / 2))) ≤
            A * (1 / (L : ℝ) +
              Real.log ((M : ℝ) / (L : ℝ))) := by
        calc
          _ ≤ ∑ k ∈ Finset.Icc L M, A * (1 / (k : ℝ)) :=
            Finset.sum_le_sum hfarPoint
          _ = A * ∑ k ∈ Finset.Icc L M, 1 / (k : ℝ) := by
            rw [Finset.mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left htailBase hA.le
      have hratio : (M : ℝ) / (L : ℝ) ≤ T := by
        apply (div_le_iff₀ (by exact_mod_cast hLpos : (0 : ℝ) < L)).2
        calc
          (M : ℝ) ≤ A * T := hM
          _ ≤ (L : ℝ) * T :=
            mul_le_mul_of_nonneg_right hAL hT0
          _ = T * (L : ℝ) := by ring
      have hlogRatio : Real.log ((M : ℝ) / (L : ℝ)) ≤
          Real.log (2 + T) := by
        apply Real.log_le_log
        · exact div_pos (by exact_mod_cast hLpos.trans hLM)
            (by exact_mod_cast hLpos)
        · exact hratio.trans (by linarith)
      have hinvL : 1 / (L : ℝ) ≤ 1 := by
        exact (div_le_one (by exact_mod_cast hLpos : (0 : ℝ) < L)).2
          (by exact_mod_cast hLpos)
      calc
        (∑ k ∈ Finset.Ico 0 L,
            min 1 (A / ((k : ℝ) + 1 / 2))) +
          ∑ k ∈ Finset.Icc L M,
            min 1 (A / ((k : ℝ) + 1 / 2)) ≤
          (L : ℝ) + A * (1 / (L : ℝ) +
            Real.log ((M : ℝ) / (L : ℝ))) :=
          add_le_add hnearCard hfarSum
        _ ≤ (A + 1) + A * (1 + Real.log (2 + T)) := by
          gcongr
        _ ≤ 4 * A * (1 + Real.log (2 + T)) := by
          nlinarith [hA1, hlog0, mul_nonneg hA.le hlog0]
    · have hML : M < L := Nat.lt_of_not_ge hLM
      calc
        (∑ k ∈ Finset.Icc 0 M,
            min 1 (A / ((k : ℝ) + 1 / 2))) ≤
          ∑ k ∈ Finset.Icc 0 M, (1 : ℝ) :=
            Finset.sum_le_sum fun k hk => min_le_left _ _
        _ = (M + 1 : ℕ) := by simp
        _ ≤ (L : ℝ) := by exact_mod_cast hML
        _ ≤ A + 1 := hLle
        _ ≤ 4 * A * (1 + Real.log (2 + T)) := by
          nlinarith [hA1, hlog0, mul_nonneg hA.le hlog0]

end
end MAPMRTCorollary25MinSum

#print axioms MAPMRTCorollary25MinSum.sum_Icc_inv_le_inv_add_log_ratio
#print axioms MAPMRTCorollary25MinSum.halfInteger_minSum_le_two_shellSums
#print axioms MAPMRTCorollary25MinSum.halfInteger_shellMinSum_le
