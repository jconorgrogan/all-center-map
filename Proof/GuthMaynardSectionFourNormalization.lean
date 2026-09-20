import GuthMaynardLemma42Scalar

/-!
# Raw-to-normalized Section 4 trace bridge

The source matrix uses `n^{it}`, while Poisson summation naturally acts on
`(n/N)^{it}`.  Their row phases are unitary and cancel around every cubic
closed walk.  This file makes that normalization exact.
-/
namespace GuthMaynardSectionFourNormalization

open scoped BigOperators
open GuthMaynardSectionFourTrace
open GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

def sourceRowPhase (N : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((t * Real.log (N : ℝ) : ℝ) * Complex.I)

def sourceNormalizedPhase (n N : ℕ) (t : ℝ) : ℂ :=
  (Complex.ofReal ((n : ℝ) / (N : ℝ))) ^ (Complex.I * (t : ℂ))

def sourceNormalizedMatrix (W : Finset ℝ) (N : ℕ) :
    Matrix (SourceRow W) (SourceColumn N) ℂ :=
  fun t n =>
    (sectionThreeCutoffReal ((n : ℝ) / (N : ℝ)) : ℂ) *
      sourceNormalizedPhase n N t

def sourceNormalizedGram (W : Finset ℝ) (N : ℕ) :
    Matrix (SourceRow W) (SourceRow W) ℂ :=
  sourceNormalizedMatrix W N * Matrix.conjTranspose (sourceNormalizedMatrix W N)

def sourceNormalizedMatrixTraceCube (W : Finset ℝ) (N : ℕ) : ℂ :=
  Matrix.trace ((sourceNormalizedGram W N) ^ 3)

theorem sourcePhase_eq_rowPhase_mul_normalized
    {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (t : ℝ) :
    sourcePhase n t = sourceRowPhase N t * sourceNormalizedPhase n N t := by
  unfold sourcePhase sourceRowPhase sourceNormalizedPhase
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Complex.cpow_def_of_ne_zero]
  · rw [← Complex.ofReal_log (div_nonneg hnR.le hNR.le)]
    rw [Real.log_div hnR.ne' hNR.ne']
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · exact Complex.ofReal_ne_zero.mpr (div_ne_zero hnR.ne' hNR.ne')

theorem sourceMatrix_eq_rowPhase_mul_normalized
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ)
    (t : SourceRow W) (n : SourceColumn N) :
    sourceMatrix W N t n =
      sourceRowPhase N t * sourceNormalizedMatrix W N t n := by
  have hnN : N < (n : ℕ) :=
    (Finset.mem_Ioc.mp (show (n : ℕ) ∈ Finset.Ioc N (2 * N) from n.property)).1
  have hn : 0 < (n : ℕ) := lt_trans hN hnN
  rw [sourceMatrix, sourceNormalizedMatrix,
    sourcePhase_eq_rowPhase_mul_normalized hn hN]
  ring

theorem sourceRowPhase_mul_star (N : ℕ) (t : ℝ) :
    sourceRowPhase N t * star (sourceRowPhase N t) = 1 := by
  unfold sourceRowPhase
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem sourceGram_eq_rowPhases_mul_normalized
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ)
    (t u : SourceRow W) :
    sourceGram W N t u = sourceRowPhase N t * star (sourceRowPhase N u) *
      sourceNormalizedGram W N t u := by
  rw [sourceGram_apply]
  change (∑ n : SourceColumn N,
      sourceMatrix W N t n * star (sourceMatrix W N u n)) =
    sourceRowPhase N t * star (sourceRowPhase N u) *
      (∑ n : SourceColumn N,
        sourceNormalizedMatrix W N t n * star (sourceNormalizedMatrix W N u n))
  simp_rw [sourceMatrix_eq_rowPhase_mul_normalized hN W]
  simp_rw [star_mul]
  calc
    _ = ∑ n : SourceColumn N,
        (sourceRowPhase N t * star (sourceRowPhase N u)) *
          (sourceNormalizedMatrix W N t n * star (sourceNormalizedMatrix W N u n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by rw [Finset.mul_sum]

theorem sourceNormalizedMatrix_product_eq_oscillatory {n N : ℕ} (hN : 0 < N) (W : Finset ℝ) (t u : ℝ)
    (ht : t ∈ W) (hu : u ∈ W) (hncol : n ∈ Finset.Ioc N (2 * N)) :
 sourceNormalizedMatrix W N ⟨t, ht⟩ ⟨n, hncol⟩ *
 star (sourceNormalizedMatrix W N ⟨u, hu⟩ ⟨n, hncol⟩) =
 sectionThreeOscillatory (t-u) ((n:ℝ)/(N:ℝ)) := by
 have hnN : N < n := (Finset.mem_Ioc.mp hncol).1
 have hn : 0 < n := lt_trans hN hnN
 have hnR : (0:ℝ)<n := by exact_mod_cast hn
 have hNR : (0:ℝ)<N := by exact_mod_cast hN
 have hx : Complex.ofReal ((n:ℝ)/(N:ℝ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (div_ne_zero hnR.ne' hNR.ne')
 unfold sourceNormalizedMatrix sourceNormalizedPhase sectionThreeOscillatory GuthMaynardSectionThreeCutoff.sectionThreeCutoff
 rw [Complex.cpow_def_of_ne_zero hx, Complex.cpow_def_of_ne_zero hx,
   Complex.cpow_def_of_ne_zero hx]
 rw [← Complex.ofReal_log (div_nonneg hnR.le hNR.le)]
 let a : ℂ := GuthMaynardSectionThreeCutoff.sectionThreeCutoffReal ((n:ℝ)/(N:ℝ))
 let L : ℂ := Real.log ((n:ℝ)/(N:ℝ))
 change a * Complex.exp (L * (Complex.I * (t:ℂ))) *
   star (a * Complex.exp (L * (Complex.I * (u:ℂ)))) =
   a^2 * Complex.exp (L * (Complex.I * ((t-u:ℝ):ℂ)))
 rw [star_mul]
 simp only [Complex.star_def]
 rw [← Complex.exp_conj]
 simp
 have hstarA : (starRingEnd ℂ) a = a := by dsimp [a]; simp
 have hstarL : (starRingEnd ℂ) L = L := by dsimp [L]; simp
 rw [hstarA, hstarL]
 rw [show a * Complex.exp (L * (Complex.I * (t:ℂ))) *
   (Complex.exp (-(L * (Complex.I * (u:ℂ)))) * a) =
   a^2 * (Complex.exp (L * (Complex.I * (t:ℂ))) *
     Complex.exp (-(L * (Complex.I * (u:ℂ))))) by ring]
 rw [← Complex.exp_add]
 congr 1
 push_cast
 ring

theorem sourceNormalizedGram_apply_oscillatory
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) (t u : SourceRow W) :
    sourceNormalizedGram W N t u =
      ∑ n : SourceColumn N,
        sectionThreeOscillatory ((t : ℝ) - (u : ℝ))
          (((n : ℕ) : ℝ) / (N : ℝ)) := by
  change (∑ n : SourceColumn N,
      sourceNormalizedMatrix W N t n * star (sourceNormalizedMatrix W N u n)) = _
  apply Finset.sum_congr rfl
  intro n hn
  exact sourceNormalizedMatrix_product_eq_oscillatory hN W t u t.property u.property n.property

private theorem sectionThreeCutoff_one : sectionThreeCutoff (1 : ℝ) = 0 := by
  unfold sectionThreeCutoff sectionThreeCutoffReal
  rw [GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
      (1 / 5) fifth_pos (by norm_num : 2 * (1 / 5 : ℝ) ≤ |(1 : ℝ) - 7 / 5|),
    GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
      (1 / 5) fifth_pos (by norm_num : 2 * (1 / 5 : ℝ) ≤ |(1 : ℝ) - 8 / 5|)]
  norm_num

private theorem sectionThreeCutoff_two : sectionThreeCutoff (2 : ℝ) = 0 := by
  unfold sectionThreeCutoff sectionThreeCutoffReal
  rw [GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
      (1 / 5) fifth_pos (by norm_num : 2 * (1 / 5 : ℝ) ≤ |(2 : ℝ) - 7 / 5|),
    GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
      (1 / 5) fifth_pos (by norm_num : 2 * (1 / 5 : ℝ) ≤ |(2 : ℝ) - 8 / 5|)]
  norm_num

/-- The integer Poisson sum is exactly the finite dyadic column sum.  Endpoint
terms vanish for the concrete Section 3 cutoff. -/
theorem tsum_oscillatory_eq_columnSum
    (v : ℝ) {N : ℕ} (hN : 0 < N) :
    (∑' z : ℤ, sectionThreeOscillatory v ((z : ℝ) / (N : ℝ))) =
      ∑ n : SourceColumn N,
        sectionThreeOscillatory v (((n : ℕ) : ℝ) / (N : ℝ)) := by
  let e : ℕ ↪ ℤ := ⟨fun n => (n : ℤ), by
    intro a b h
    exact Int.ofNat.inj h⟩
  let s : Finset ℤ := (Finset.Ioc N (2 * N)).map e
  rw [tsum_eq_sum (s := s)]
  · rw [Finset.sum_map]
    exact Finset.sum_subtype (Finset.Ioc N (2 * N)) (by simp) _
  · intro z hz
    unfold s e at hz
    cases z with
    | ofNat k =>
        have hnot : k ∉ Finset.Ioc N (2 * N) := by
          intro hk
          exact hz (Finset.mem_map.mpr ⟨k, hk, rfl⟩)
        simp only [Finset.mem_Ioc, not_and_or, not_le] at hnot
        rcases hnot with hk | hk
        · by_cases heq : k = N
          · subst k
            change sectionThreeOscillatory v ((N : ℝ) / (N : ℝ)) = 0
            rw [show ((N : ℝ) / (N : ℝ)) = 1 by
              exact div_self (by exact_mod_cast hN.ne')]
            simp [sectionThreeOscillatory, sectionThreeCutoff_one]
          · apply sectionThreeOscillatory_supported
            simp only [Set.mem_Icc, not_and_or, not_le]
            left
            have hklt : k < N := lt_of_le_of_ne (Nat.le_of_not_gt hk) heq
            change (k : ℝ) / (N : ℝ) < 1
            exact (div_lt_one (by exact_mod_cast hN)).2 (by exact_mod_cast hklt)
        · apply sectionThreeOscillatory_supported
          simp only [Set.mem_Icc, not_and_or, not_le]
          right
          have hNR : (0 : ℝ) < N := by exact_mod_cast hN
          change 2 < (k : ℝ) / (N : ℝ)
          rw [lt_div_iff₀ hNR]
          exact_mod_cast hk
    | negSucc k =>
        apply sectionThreeOscillatory_supported
        simp only [Set.mem_Icc, not_and_or, not_le]
        left
        have hNR : (0 : ℝ) < N := by exact_mod_cast hN
        have hzneg : ((Int.negSucc k : ℤ) : ℝ) < 0 := by exact_mod_cast Int.negSucc_lt_zero k
        exact (div_neg_of_neg_of_pos hzneg hNR).trans (by norm_num)


private theorem normalizedTraceCube_expand (W : Finset ℝ) (N : ℕ) :
    sourceNormalizedMatrixTraceCube W N =
      ∑ t₁ : SourceRow W, ∑ t₂ : SourceRow W, ∑ t₃ : SourceRow W,
        sourceNormalizedGram W N t₁ t₂ * sourceNormalizedGram W N t₂ t₃ *
          sourceNormalizedGram W N t₃ t₁ := by
  unfold sourceNormalizedMatrixTraceCube Matrix.trace
  rw [show sourceNormalizedGram W N ^ 3 =
      sourceNormalizedGram W N *
        (sourceNormalizedGram W N * sourceNormalizedGram W N) by noncomm_ring]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro t₁ ht₁
  apply Finset.sum_congr rfl
  intro t₂ ht₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t₃ ht₃
  ring

/-- The row normalization cancels exactly in the cubic trace. -/
theorem sourceTraceCube_eq_normalized
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceTraceCube W N = sourceNormalizedMatrixTraceCube W N := by
  rw [sourceTraceCube_expand, normalizedTraceCube_expand]
  apply Finset.sum_congr rfl
  intro t₁ ht₁
  apply Finset.sum_congr rfl
  intro t₂ ht₂
  apply Finset.sum_congr rfl
  intro t₃ ht₃
  simp_rw [sourceGram_eq_rowPhases_mul_normalized hN W]
  have h₁ := sourceRowPhase_mul_star N (t₁ : ℝ)
  have h₂ := sourceRowPhase_mul_star N (t₂ : ℝ)
  have h₃ := sourceRowPhase_mul_star N (t₃ : ℝ)
  calc
    _ = (sourceRowPhase N t₁ * star (sourceRowPhase N t₁)) *
        (sourceRowPhase N t₂ * star (sourceRowPhase N t₂)) *
        (sourceRowPhase N t₃ * star (sourceRowPhase N t₃)) *
        (sourceNormalizedGram W N t₁ t₂ *
          sourceNormalizedGram W N t₂ t₃ * sourceNormalizedGram W N t₃ t₁) := by ring
    _ = _ := by rw [h₁, h₂, h₃]; simp

/-- The normalized finite matrix trace is the normalized Poisson-side trace
defined in `GuthMaynardSectionFourPoisson`. -/
theorem sourceNormalizedMatrixTraceCube_eq_poissonTrace
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceNormalizedMatrixTraceCube W N =
      GuthMaynardSectionFourPoisson.sourceNormalizedTraceCube N W := by
  rw [normalizedTraceCube_expand]
  unfold GuthMaynardSectionFourPoisson.sourceNormalizedTraceCube
  rw [Finset.sum_subtype W (fun _ => Iff.rfl)
    (fun t₁ => ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      (∑' n₁ : ℤ, sectionThreeOscillatory (t₁ - t₂) ((n₁ : ℝ) / (N : ℝ))) *
      (∑' n₂ : ℤ, sectionThreeOscillatory (t₂ - t₃) ((n₂ : ℝ) / (N : ℝ))) *
      (∑' n₃ : ℤ, sectionThreeOscillatory (t₃ - t₁) ((n₃ : ℝ) / (N : ℝ))))]
  apply Finset.sum_congr rfl
  intro t₁ ht₁
  rw [Finset.sum_subtype W (fun _ => Iff.rfl)
    (fun t₂ => ∑ t₃ ∈ W,
      (∑' n₁ : ℤ, sectionThreeOscillatory ((t₁ : ℝ) - t₂) ((n₁ : ℝ) / (N : ℝ))) *
      (∑' n₂ : ℤ, sectionThreeOscillatory (t₂ - t₃) ((n₂ : ℝ) / (N : ℝ))) *
      (∑' n₃ : ℤ, sectionThreeOscillatory (t₃ - (t₁ : ℝ)) ((n₃ : ℝ) / (N : ℝ))))]
  apply Finset.sum_congr rfl
  intro t₂ ht₂
  rw [Finset.sum_subtype W (fun _ => Iff.rfl)
    (fun t₃ =>
      (∑' n₁ : ℤ, sectionThreeOscillatory ((t₁ : ℝ) - (t₂ : ℝ)) ((n₁ : ℝ) / (N : ℝ))) *
      (∑' n₂ : ℤ, sectionThreeOscillatory ((t₂ : ℝ) - t₃) ((n₂ : ℝ) / (N : ℝ))) *
      (∑' n₃ : ℤ, sectionThreeOscillatory (t₃ - (t₁ : ℝ)) ((n₃ : ℝ) / (N : ℝ))))]
  apply Finset.sum_congr rfl
  intro t₃ ht₃
  rw [sourceNormalizedGram_apply_oscillatory hN,
    sourceNormalizedGram_apply_oscillatory hN,
    sourceNormalizedGram_apply_oscillatory hN,
    ← tsum_oscillatory_eq_columnSum (t₁ - t₂) hN,
    ← tsum_oscillatory_eq_columnSum (t₂ - t₃) hN,
    ← tsum_oscillatory_eq_columnSum (t₃ - t₁) hN]

/-- Exact Section 4 cubic trace identity, from the literal source matrix to
the literal absolutely convergent `I_m` sum. -/
theorem sourceTraceCube_eq_tsum_sourceIm
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceTraceCube W N =
      ∑' p : (ℤ × ℤ) × ℤ,
        GuthMaynardEquation55Split.sourceIm N W p.1.1 p.1.2 p.2 := by
  rw [sourceTraceCube_eq_normalized hN W,
    sourceNormalizedMatrixTraceCube_eq_poissonTrace hN W,
    GuthMaynardSectionFourPoisson.sourceNormalizedTraceCube_eq_tsum_sourceIm hN W]

end
end GuthMaynardSectionFourNormalization

#print axioms GuthMaynardSectionFourNormalization.sourcePhase_eq_rowPhase_mul_normalized
#print axioms GuthMaynardSectionFourNormalization.sourceTraceCube_eq_normalized
#print axioms GuthMaynardSectionFourNormalization.sourceTraceCube_eq_tsum_sourceIm
