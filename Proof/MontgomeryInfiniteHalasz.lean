import MontgomeryEquation30Halasz

/-!
# Infinite smooth-kernel Halasz weld

Montgomery's Lemma 1 applies Cauchy--Schwarz on the finite hard coefficient
block and then extends the positive quadratic sum to every positive integer,
where the smooth pair kernels are available.  This file certifies that exact
finite-to-infinite passage and the pairwise `K` absorption.
-/

namespace MAPMontgomeryInfiniteHalasz

open scoped BigOperators ComplexConjugate
open Complex
open MAPJutilaDeterministicCore MAPHuxleyHalaszFront

noncomputable section

private theorem summable_finset_sum
    {I K E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E]
    (s : Finset I) (f : I → K → E)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun k => ∑ i ∈ s, f i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (summable_zero : Summable (fun _ : K => (0 : E)))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem tsum_finset_sum
    {I K E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [T2Space E] [ContinuousAdd E]
    (s : Finset I) (f : I → K → E)
    (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' k, ∑ i ∈ s, f i k) = ∑ i ∈ s, ∑' k, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs : Summable (fun k => ∑ j ∈ s, f j k) :=
        summable_finset_sum s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simp only [Finset.sum_insert hi]
      rw [hfi.tsum_add hfs, ih]
      intro j hj
      exact hf j (Finset.mem_insert_of_mem hj)

/-- The infinite positive correlation energy introduced after extending the
finite hard coefficient block by the smooth weight. -/
def infiniteCorrelationEnergy
    {I K : Type*} [DecidableEq I]
    (rows : Finset I) (b : K → ℝ)
    (eta : I → ℂ) (v : I → K → ℂ) : ℝ :=
  ∑' k : K, b k * ‖∑ i ∈ rows, eta i * v i k‖ ^ 2

/-- One entry of the infinite smooth Gram matrix. -/
def infiniteKernel
    {I K : Type*} (b : K → ℝ) (v : I → K → ℂ)
    (i j : I) : ℂ :=
  ∑' k : K, (b k : ℂ) * conj (v i k) * v j k

theorem summable_infiniteKernel
    {I K : Type*} (b : K → ℝ) (v : I → K → ℂ)
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hv : ∀ i k, ‖v i k‖ ≤ 1) (i j : I) :
    Summable (fun k : K => (b k : ℂ) * conj (v i k) * v j k) := by
  apply Summable.of_norm_bounded hbsum
  intro k
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hb k), Complex.norm_conj]
  have hvi := hv i k
  have hvj := hv j k
  have hb0 := hb k
  have hni := norm_nonneg (v i k)
  have hnj := norm_nonneg (v j k)
  have hprod : ‖v i k‖ * ‖v j k‖ ≤ 1 := by nlinarith
  calc
    b k * ‖v i k‖ * ‖v j k‖ = b k * (‖v i k‖ * ‖v j k‖) := by ring
    _ ≤ b k * 1 := mul_le_mul_of_nonneg_left hprod hb0
    _ = b k := by ring

theorem summable_infiniteCorrelationEnergy
    {I K : Type*} [DecidableEq I]
    (rows : Finset I) (b : K → ℝ)
    (eta : I → ℂ) (v : I → K → ℂ)
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (heta : ∀ i ∈ rows, ‖eta i‖ = 1)
    (hv : ∀ i k, ‖v i k‖ ≤ 1) :
    Summable (fun k : K =>
      b k * ‖∑ i ∈ rows, eta i * v i k‖ ^ 2) := by
  let R : ℝ := rows.card
  apply Summable.of_nonneg_of_le
    (f := fun k : K => b k * R ^ 2)
  · intro k
    exact mul_nonneg (hb k) (sq_nonneg _)
  · intro k
    have hsum : ‖∑ i ∈ rows, eta i * v i k‖ ≤ R := by
      calc
        ‖∑ i ∈ rows, eta i * v i k‖ ≤
            ∑ i ∈ rows, ‖eta i * v i k‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ rows, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul, heta i hi, one_mul]
          exact hv i k
        _ = R := by simp [R]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
    exact mul_le_mul_of_nonneg_left hsq (hb k)
  · exact hbsum.mul_right (R ^ 2)

/-- Infinite analogue of `correlationEnergy_eq_doubleSum`.  All
sum-interchanges are justified by the summable positive majorant. -/
theorem infiniteCorrelationEnergy_eq_doubleSum
    {I K : Type*} [DecidableEq I]
    (rows : Finset I) (b : K → ℝ)
    (eta : I → ℂ) (v : I → K → ℂ)
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (heta : ∀ i ∈ rows, ‖eta i‖ = 1)
    (hv : ∀ i k, ‖v i k‖ ≤ 1) :
    (infiniteCorrelationEnergy rows b eta v : ℂ) =
      ∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j * infiniteKernel b v i j := by
  have henergy := summable_infiniteCorrelationEnergy
    rows b eta v hb hbsum heta hv
  rw [infiniteCorrelationEnergy, Complex.ofReal_tsum]
  calc
    (∑' k : K,
        ((b k * ‖∑ i ∈ rows, eta i * v i k‖ ^ 2 : ℝ) : ℂ)) =
      ∑' k : K, ∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j *
          ((b k : ℂ) * conj (v i k) * v j k) := by
        apply tsum_congr
        intro k
        push_cast
        let S : ℂ := ∑ i ∈ rows, eta i * v i k
        have hnorm : ((‖S‖ : ℝ) : ℂ) ^ 2 = S * conj S := by
          rw [Complex.mul_conj, ← Complex.sq_norm]
          norm_cast
        rw [show (∑ i ∈ rows, eta i * v i k) = S by rfl, hnorm]
        dsimp [S]
        simp_rw [map_sum, map_mul]
        calc
          (b k : ℂ) * ((∑ i ∈ rows, eta i * v i k) *
              (∑ j ∈ rows, conj (eta j) * conj (v j k))) =
            ((b k : ℂ) * (∑ i ∈ rows, eta i * v i k)) *
              (∑ j ∈ rows, conj (eta j) * conj (v j k)) := by ring
          _ =
            ∑ j ∈ rows, ∑ i ∈ rows,
              conj (eta j) * eta i *
                ((b k : ℂ) * conj (v j k) * v i k) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = ∑ i ∈ rows, ∑ j ∈ rows,
              conj (eta i) * eta j *
                ((b k : ℂ) * conj (v i k) * v j k) := by
              rw [Finset.sum_comm]
    _ = ∑ i ∈ rows, ∑ j ∈ rows,
        ∑' k : K, conj (eta i) * eta j *
          ((b k : ℂ) * conj (v i k) * v j k) := by
      rw [tsum_finset_sum rows]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [tsum_finset_sum rows]
        intro j hj
        exact (summable_infiniteKernel b v hb hbsum hv i j).mul_left
          (conj (eta i) * eta j)
      · intro i hi
        exact summable_finset_sum rows
          (fun j k => conj (eta i) * eta j *
            ((b k : ℂ) * conj (v i k) * v j k))
          (fun j hj =>
            (summable_infiniteKernel b v hb hbsum hv i j).mul_left
              (conj (eta i) * eta j))
    _ = ∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j * infiniteKernel b v i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [infiniteKernel, tsum_mul_left]

/-- Pairwise smooth-kernel bounds imply Montgomery's `FJ + KJ²` energy
bound, with no absolute row estimate at unit spacing. -/
theorem infiniteCorrelationEnergy_le_of_pairwise
    {I K : Type*} [DecidableEq I]
    (rows : Finset I) (b : K → ℝ)
    (eta : I → ℂ) (v : I → K → ℂ)
    {F K₀ : ℝ}
    (hF : 0 ≤ F) (hK₀ : 0 ≤ K₀)
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (heta : ∀ i ∈ rows, ‖eta i‖ = 1)
    (hv : ∀ i k, ‖v i k‖ ≤ 1)
    (hdiag : ∀ i ∈ rows, ‖infiniteKernel b v i i‖ ≤ F)
    (hoff : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j →
      ‖infiniteKernel b v i j‖ ≤ K₀) :
    infiniteCorrelationEnergy rows b eta v ≤
      (rows.card : ℝ) * (F + (rows.card : ℝ) * K₀) := by
  have hexpand := infiniteCorrelationEnergy_eq_doubleSum
    rows b eta v hb hbsum heta hv
  have henergy0 : 0 ≤ infiniteCorrelationEnergy rows b eta v := by
    unfold infiniteCorrelationEnergy
    exact tsum_nonneg (fun k => mul_nonneg (hb k) (sq_nonneg _))
  calc
    infiniteCorrelationEnergy rows b eta v =
        ‖(infiniteCorrelationEnergy rows b eta v : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy0]
    _ = ‖∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j * infiniteKernel b v i j‖ := by rw [hexpand]
    _ ≤ ∑ i ∈ rows, ∑ j ∈ rows,
        ‖conj (eta i) * eta j * infiniteKernel b v i j‖ := by
      exact (norm_sum_le _ _).trans <| Finset.sum_le_sum (fun i hi => norm_sum_le _ _)
    _ = ∑ i ∈ rows, ∑ j ∈ rows, ‖infiniteKernel b v i j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_mul, Complex.norm_conj, heta i hi, heta j hj]
    _ ≤ ∑ _i ∈ rows, (F + (rows.card : ℝ) * K₀) := by
      apply Finset.sum_le_sum
      intro i hi
      let B : I → ℝ := fun j => ‖infiniteKernel b v i j‖
      have hsplit : (∑ j ∈ rows, B j) =
          B i + ∑ j ∈ rows.erase i, B j := by
        rw [add_comm]
        exact (Finset.sum_erase_add rows B hi).symm
      rw [hsplit]
      apply add_le_add (hdiag i hi)
      calc
        (∑ j ∈ rows.erase i, B j) ≤
            ∑ _j ∈ rows.erase i, K₀ := by
          apply Finset.sum_le_sum
          intro j hj
          exact hoff i hi j (Finset.mem_of_mem_erase hj)
            (fun h => (Finset.mem_erase.mp hj).1 h.symm)
        _ = ((rows.erase i).card : ℝ) * K₀ := by simp
        _ ≤ (rows.card : ℝ) * K₀ := by
          have hcard : ((rows.erase i).card : ℝ) ≤ rows.card := by
            exact_mod_cast (Finset.card_erase_le : (rows.erase i).card ≤ rows.card)
          exact mul_le_mul_of_nonneg_right hcard hK₀
    _ = (rows.card : ℝ) * (F + (rows.card : ℝ) * K₀) := by
      simp
      ring

/-- Montgomery's exact infinite-kernel Halasz corollary.  The hard
coefficient columns may be any finite subset of the positive integers; the
smooth kernel and its pairwise bound live on all positive integers. -/
theorem finite_large_values_of_infinite_pairwise
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (b : K → ℝ) (v : I → K → ℂ)
    {V E F K₀ : ℝ}
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hF : 0 ≤ F) (hK₀ : 0 ≤ K₀)
    (hb : ∀ k ∈ cols, 0 < b k)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hv : ∀ i k, ‖v i k‖ ≤ 1)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hcoeff : (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) ≤ E)
    (hdiag : ∀ i ∈ rows, ‖infiniteKernel b v i i‖ ≤ F)
    (hoff : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j →
      ‖infiniteKernel b v i j‖ ≤ K₀)
    (hthreshold : 2 * E * K₀ ≤ V ^ 2) :
    (rows.card : ℝ) * V ^ 2 ≤ 2 * E * F := by
  obtain ⟨eta, heta, hfront⟩ :=
    finite_halasz_inequality rows cols a b v hb
  have hfiniteToInfinite :
      correlationEnergy rows cols b eta v ≤
        infiniteCorrelationEnergy rows b eta v := by
    exact (summable_infiniteCorrelationEnergy rows b eta v
      hb0 hbsum heta hv).sum_le_tsum cols
        (fun k hk => mul_nonneg (hb0 k) (sq_nonneg _))
  have hpair := infiniteCorrelationEnergy_le_of_pairwise
    rows b eta v hF hK₀ hb0 hbsum heta hv hdiag hoff
  have hcard : (rows.card : ℝ) * V ≤
      ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ := by
    calc
      (rows.card : ℝ) * V = ∑ _i ∈ rows, V := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hlarge i hi)
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) hV) hcard 2
  let R : ℝ := rows.card
  have hpre : (R * V) ^ 2 ≤ E * (R * (F + R * K₀)) := by
    calc
      (R * V) ^ 2 ≤
          (∑ i ∈ rows, ‖finitePolynomial cols a v i‖) ^ 2 := hsquare
      _ ≤ (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) *
          correlationEnergy rows cols b eta v := hfront
      _ ≤ E * (R * (F + R * K₀)) := by
        have hcorr0 : 0 ≤ correlationEnergy rows cols b eta v := by
          unfold correlationEnergy
          exact Finset.sum_nonneg (fun k hk =>
            mul_nonneg (hb0 k) (sq_nonneg _))
        exact mul_le_mul hcoeff (hfiniteToInfinite.trans hpair)
          hcorr0 hE
  have hR : 0 ≤ R := by positivity
  by_cases hRzero : R = 0
  · rw [show (rows.card : ℝ) = R by rfl, hRzero, zero_mul]
    positivity
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    change R * V ^ 2 ≤ 2 * E * F
    have hcancel : R * V ^ 2 ≤ E * F + R * E * K₀ := by
      apply (mul_le_mul_iff_of_pos_left hRpos).mp
      calc
        R * (R * V ^ 2) = (R * V) ^ 2 := by ring
        _ ≤ E * (R * (F + R * K₀)) := hpre
        _ = R * (E * F + R * E * K₀) := by ring
    have habs : 2 * R * E * K₀ ≤ R * V ^ 2 := by
      have := mul_le_mul_of_nonneg_left hthreshold hR
      nlinarith
    linarith

end
end MAPMontgomeryInfiniteHalasz

#print axioms MAPMontgomeryInfiniteHalasz.infiniteCorrelationEnergy_eq_doubleSum
#print axioms MAPMontgomeryInfiniteHalasz.infiniteCorrelationEnergy_le_of_pairwise
#print axioms MAPMontgomeryInfiniteHalasz.finite_large_values_of_infinite_pairwise
