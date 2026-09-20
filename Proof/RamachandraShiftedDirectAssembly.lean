import RamachandraShiftedDirectSeries
import MRTLemma215DyadicPartition

namespace RamachandraShiftedDirectAssembly
open scoped BigOperators
open CGLProofDAG
open RamachandraShiftedDirectSeries
open RamachandraShiftedCoefficientEnergy
open MRTLemma215DyadicPartition
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction
open BHPAllCharacterDyadicBudget

noncomputable section

def directSourceShellCoeff (M : ℕ) (sigma X : ℝ)
    (j : Fin (sourceDyadicCount M)) : ℕ → ℂ :=
  sourceDyadicCoeff M (shiftedSmoothedDivisorBlockCoeff sigma X) j

def directSourceUnitCoeff (M : ℕ) (sigma X : ℝ) : ℕ → ℂ :=
  sourceUnitCoeff M (shiftedSmoothedDivisorBlockCoeff sigma X)

theorem directSourceShellPolynomial_eq_dyadicBlock
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (M : ℕ) (sigma X t : ℝ) (j : Fin (sourceDyadicCount M)) :
    twistedFinitePolynomial d (Finset.Icc 1 M)
        (directSourceShellCoeff M sigma X j) psi t =
      twistedFinitePolynomial d (dyadicSupport (2 ^ (j : ℕ)))
        (directSourceShellCoeff M sigma X j) psi t := by
  let S := Finset.Icc 1 M
  let D := dyadicSupport (2 ^ (j : ℕ))
  let U := S ∪ D
  let F : ℕ → ℂ := fun n =>
    (directSourceShellCoeff M sigma X j n * psi n) * twistedPhase n t
  have hSU : S ⊆ U := Finset.subset_union_left
  have hDU : D ⊆ U := Finset.subset_union_right
  have houtS : ∀ n ∈ U, n ∉ S → F n = 0 := by
    intro n hnU hnS
    have hnD : n ∈ D := by
      rcases Finset.mem_union.mp hnU with hn | hn
      · exact (hnS hn).elim
      · exact hn
    have hnpos : 1 ≤ n := by
      have h := Finset.mem_Ioc.mp hnD
      omega
    have hnM : ¬ n ≤ M := by
      intro h
      exact hnS (Finset.mem_Icc.mpr ⟨hnpos, h⟩)
    unfold F directSourceShellCoeff sourceDyadicCoeff
    rw [if_neg]
    · simp
    · intro h
      exact hnM h.2.1
  have houtD : ∀ n ∈ U, n ∉ D → F n = 0 := by
    intro n hnU hnD
    have hsupp := sourceDyadicCoeff_supported M
      (shiftedSmoothedDivisorBlockCoeff sigma X) j n hnD
    unfold F directSourceShellCoeff
    rw [hsupp]
    simp
  unfold twistedFinitePolynomial
  change (∑ n ∈ S, F n) = ∑ n ∈ D, F n
  calc
    (∑ n ∈ S, F n) = ∑ n ∈ U, F n :=
      Finset.sum_subset hSU houtS
    _ = ∑ n ∈ D, F n := (Finset.sum_subset hDU houtD).symm

theorem shiftedDirectPrefix_eq_unit_add_shells
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (M : ℕ) (sigma X t : ℝ) :
    twistedFinitePolynomial d (Finset.Icc 1 M)
        (shiftedSmoothedDivisorBlockCoeff sigma X) psi t =
      twistedFinitePolynomial d (Finset.Icc 1 M)
          (directSourceUnitCoeff M sigma X) psi t +
        ∑ j : Fin (sourceDyadicCount M),
          ramachandraDyadicBlock d (2 ^ (j : ℕ))
            (directSourceShellCoeff M sigma X j) false psi t := by
  have hshell (j : Fin (sourceDyadicCount M)) :
      ramachandraDyadicBlock d (2 ^ (j : ℕ))
          (directSourceShellCoeff M sigma X j) false psi t =
        twistedFinitePolynomial d (Finset.Icc 1 M)
          (directSourceShellCoeff M sigma X j) psi t := by
    rw [ramachandraDyadicBlock]
    simp only [Bool.false_eq_true, if_false]
    exact (directSourceShellPolynomial_eq_dyadicBlock
      psi M sigma X t j).symm
  simp_rw [hshell]
  unfold twistedFinitePolynomial
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnrange : 1 ≤ n ∧ n ≤ M := Finset.mem_Icc.mp hn
  have hcoeff := unit_add_sum_sourceDyadicCoeff_eq_truncation
    M (shiftedSmoothedDivisorBlockCoeff sigma X) n
  rw [if_pos hnrange] at hcoeff
  unfold directSourceUnitCoeff directSourceShellCoeff
  rw [← hcoeff]
  rw [add_mul, add_mul]
  simp only [Finset.sum_mul]

end
end RamachandraShiftedDirectAssembly

namespace RamachandraShiftedDirectAssembly
open scoped BigOperators
open CGLProofDAG
open RamachandraShiftedDirectSeries
open RamachandraShiftedCoefficientEnergy
open MAPMRTLemma210OrthogonalityReduction

noncomputable section

theorem sum_range_shiftedDirectTerm_eq_prefixPolynomial
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (M : ℕ) (sigma X t : ℝ) :
    (∑ n ∈ Finset.range (M + 1), shiftedDirectTerm psi sigma X t n) =
      twistedFinitePolynomial d (Finset.Icc 1 M)
        (shiftedSmoothedDivisorBlockCoeff sigma X) psi t := by
  let R := Finset.range (M + 1)
  let S := Finset.Icc 1 M
  have hSR : S ⊆ R := by
    intro n hn
    exact Finset.mem_range.mpr (by
      have h := Finset.mem_Icc.mp hn
      omega)
  have hout : ∀ n ∈ R, n ∉ S →
      shiftedDirectTerm psi sigma X t n = 0 := by
    intro n hnR hnS
    have hnle : n ≤ M := by
      have := Finset.mem_range.mp hnR
      omega
    have hn0 : n = 0 := by
      by_contra hn0
      exact hnS (Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnle⟩)
    subst n
    simp [shiftedDirectTerm, LSeries.term_zero]
  change (∑ n ∈ R, shiftedDirectTerm psi sigma X t n) = _
  rw [← Finset.sum_subset hSR hout]
  change (∑ n ∈ Finset.Icc 1 M,
    shiftedDirectTerm psi sigma X t n) = _
  unfold twistedFinitePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  exact shiftedDirectTerm_eq_blockTerm psi
    (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1) sigma X t

end
end RamachandraShiftedDirectAssembly

#print axioms RamachandraShiftedDirectAssembly.shiftedDirectPrefix_eq_unit_add_shells
#print axioms RamachandraShiftedDirectAssembly.sum_range_shiftedDirectTerm_eq_prefixPolynomial

namespace RamachandraShiftedDirectAssembly

open scoped BigOperators Interval
open CGLProofDAG MeasureTheory
open RamachandraShiftedCoefficientEnergy
open MRTLemma215DyadicPartition
open MontgomeryVaughanFiniteReduction
open BHPAllCharacterDyadicBudget

noncomputable section

/-- Truncating the last source shell can only reduce its coefficient energy. -/
theorem coefficientEnergy_directSourceShellCoeff_le
    (M : ℕ) (j : Fin (sourceDyadicCount M))
    {X Y sigma delta : ℝ}
    (hX : 0 < X) (hNY : (2 * 2 ^ (j : ℕ) : ℕ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    coefficientEnergy (directSourceShellCoeff M sigma X j)
        (2 ^ (j : ℕ)) ≤
      Real.exp (2 * delta * Real.log Y) *
        (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _
    (Real.exp_nonneg _)
  intro n hn
  unfold directSourceShellCoeff sourceDyadicCoeff
  split_ifs with hkeep
  · apply norm_shiftedSmoothedDivisorBlockCoeff_sq_le_envelope
      hX (by omega) _ hdelta hsigma
    have hnle : (n : ℝ) ≤ (2 * 2 ^ (j : ℕ) : ℕ) := by
      exact_mod_cast (Finset.mem_Ioc.mp hn).2
    exact hnle.trans hNY
  · simp
    positivity

/-- Complete-character continuous mean square for one exact truncated source
shell. -/
theorem integral_sum_norm_directSourceShell_sq_le
    (d M : ℕ) [NeZero d] (j : Fin (sourceDyadicCount M))
    {T X Y sigma delta : ℝ}
    (hT : 0 ≤ T) (hX : 0 < X)
    (hNY : (2 * 2 ^ (j : ℕ) : ℕ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖ramachandraDyadicBlock d (2 ^ (j : ℕ))
          (directSourceShellCoeff M sigma X j) false psi t‖ ^ 2) ≤
      (((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
        Real.exp (2 * delta * Real.log Y) *
          (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4) := by
  have hmean := integral_sum_norm_ramachandraDyadicBlock_sq_le
    d (2 ^ (j : ℕ)) Nat.one_le_two_pow
      (directSourceShellCoeff M sigma X j) false hT
  apply hmean.trans
  unfold ramachandraDyadicCost
  have hfactor : 0 ≤ (d : ℝ) * (2 * T) +
      8 * Real.pi * (2 ^ (j : ℕ) : ℕ) := by positivity
  have henergy := coefficientEnergy_directSourceShellCoeff_le
    M j hX hNY hdelta hsigma
  calc
    ((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
        coefficientEnergy (directSourceShellCoeff M sigma X j)
          (2 ^ (j : ℕ)) ≤
      ((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
        (Real.exp (2 * delta * Real.log Y) *
          (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left henergy hfactor
    _ = _ := by ring

end
end RamachandraShiftedDirectAssembly

#print axioms RamachandraShiftedDirectAssembly.coefficientEnergy_directSourceShellCoeff_le
#print axioms RamachandraShiftedDirectAssembly.integral_sum_norm_directSourceShell_sq_le


namespace RamachandraShiftedDirectAssembly

open scoped BigOperators Interval
open CGLProofDAG MeasureTheory
open RamachandraShiftedCoefficientEnergy
open MRTLemma215DyadicPartition
open MAPMRTLemma210OrthogonalityReduction

noncomputable section

theorem norm_directSourceUnitPolynomial_le_one
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {M : ℕ} (hM : 1 ≤ M) {sigma X t : ℝ} (hX : 0 < X) :
    ‖twistedFinitePolynomial d (Finset.Icc 1 M)
      (directSourceUnitCoeff M sigma X) psi t‖ ≤ 1 := by
  unfold twistedFinitePolynomial
  rw [Finset.sum_eq_single 1]
  · have hc := norm_shiftedSmoothedDivisorBlockCoeff_one_le
      (sigma := sigma) hX
    simpa [directSourceUnitCoeff, sourceUnitCoeff, hM,
      norm_mul, norm_twistedPhase] using hc
  · intro n hn hn1
    unfold directSourceUnitCoeff sourceUnitCoeff
    simp [hn1]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩)).elim


end
end RamachandraShiftedDirectAssembly

#print axioms RamachandraShiftedDirectAssembly.norm_directSourceUnitPolynomial_le_one


namespace RamachandraShiftedDirectAssembly

open scoped BigOperators Interval
open CGLProofDAG MeasureTheory
open MRTLemma215DyadicPartition
open MAPMRTLemma210OrthogonalityReduction

noncomputable section

theorem integral_sum_norm_directSourceUnitPolynomial_sq_le
    (d M : ℕ) [NeZero d] (hM : 1 ≤ M)
    {T X sigma : ℝ} (hT : 0 ≤ T) (hX : 0 < X) :
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖twistedFinitePolynomial d (Finset.Icc 1 M)
          (directSourceUnitCoeff M sigma X) psi t‖ ^ 2) ≤
      2 * (d : ℝ) * T := by
  have hcont : Continuous (fun t : ℝ =>
      ∑ psi : DirichletCharacter ℂ d,
        ‖twistedFinitePolynomial d (Finset.Icc 1 M)
          (directSourceUnitCoeff M sigma X) psi t‖ ^ 2) := by
    apply continuous_finsetSum
    intro psi hpsi
    apply Continuous.pow
    apply Continuous.norm
    unfold twistedFinitePolynomial twistedPhase
    fun_prop
  calc
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖twistedFinitePolynomial d (Finset.Icc 1 M)
          (directSourceUnitCoeff M sigma X) psi t‖ ^ 2) ≤
        ∫ _t in (-T)..T,
          (Fintype.card (DirichletCharacter ℂ d) : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hcont.intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro t ht
        calc
          (∑ psi : DirichletCharacter ℂ d,
            ‖twistedFinitePolynomial d (Finset.Icc 1 M)
              (directSourceUnitCoeff M sigma X) psi t‖ ^ 2) ≤
              ∑ _psi : DirichletCharacter ℂ d, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro psi hpsi
            have h := norm_directSourceUnitPolynomial_le_one
              psi hM (sigma := sigma) (t := t) hX
            exact pow_le_one₀ (norm_nonneg _) h
          _ = (Fintype.card (DirichletCharacter ℂ d) : ℝ) := by simp
    _ = 2 * T * (Fintype.card (DirichletCharacter ℂ d) : ℝ) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ 2 * T * (d : ℝ) := by
      have hcard : (Fintype.card (DirichletCharacter ℂ d) : ℝ) ≤ d := by
        exact_mod_cast MAPMRTCorollary53Source.card_dirichletCharacters_le_modulus d
      exact mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = 2 * (d : ℝ) * T := by ring


end
end RamachandraShiftedDirectAssembly

#print axioms RamachandraShiftedDirectAssembly.integral_sum_norm_directSourceUnitPolynomial_sq_le


namespace RamachandraShiftedDirectAssembly
open scoped BigOperators Interval
open CGLProofDAG MeasureTheory
open RamachandraShiftedDirectAssembly
open RamachandraShiftedCoefficientEnergy
open MRTLemma215DyadicPartition
open MAPMRTLemma210OrthogonalityReduction
open BHPAllCharacterDyadicBudget

noncomputable section

theorem norm_fin_sum_sq_le_card_mul_sum_norm_sq
    {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (F : ι → E) :
    ‖∑ i ∈ s, F i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 := by
  have htriangle : ‖∑ i ∈ s, F i‖ ≤ ∑ i ∈ s, ‖F i‖ := norm_sum_le _ _
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, ‖F i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcs : (∑ i ∈ s, ‖F i‖) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  nlinarith [norm_nonneg (∑ i ∈ s, F i)]

def directSourceShellCost (d M : ℕ) (T Y delta : ℝ)
    (j : Fin (sourceDyadicCount M)) : ℝ :=
  ((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
    Real.exp (2 * delta * Real.log Y) *
      (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4

theorem integral_sum_norm_shiftedDirectPrefix_sq_le
    (d M : ℕ) [NeZero d] (hM : 1 ≤ M)
    {T X Y sigma delta : ℝ}
    (hT : 0 ≤ T) (hX : 0 < X)
    (hNY : ∀ j : Fin (sourceDyadicCount M),
      (2 * 2 ^ (j : ℕ) : ℕ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖twistedFinitePolynomial d (Finset.Icc 1 M)
          (shiftedSmoothedDivisorBlockCoeff sigma X) psi t‖ ^ 2) ≤
      4 * (d : ℝ) * T +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            directSourceShellCost d M T Y delta j := by
  let U : DirichletCharacter ℂ d → ℝ → ℂ := fun psi t =>
    twistedFinitePolynomial d (Finset.Icc 1 M)
      (directSourceUnitCoeff M sigma X) psi t
  let S : Fin (sourceDyadicCount M) → DirichletCharacter ℂ d → ℝ → ℂ :=
    fun j psi t => ramachandraDyadicBlock d (2 ^ (j : ℕ))
      (directSourceShellCoeff M sigma X j) false psi t
  have hpoint (psi : DirichletCharacter ℂ d) (t : ℝ) :
      ‖twistedFinitePolynomial d (Finset.Icc 1 M)
          (shiftedSmoothedDivisorBlockCoeff sigma X) psi t‖ ^ 2 ≤
        2 * ‖U psi t‖ ^ 2 +
          2 * (sourceDyadicCount M : ℝ) *
            ∑ j : Fin (sourceDyadicCount M), ‖S j psi t‖ ^ 2 := by
    rw [shiftedDirectPrefix_eq_unit_add_shells]
    have hsum := norm_fin_sum_sq_le_card_mul_sum_norm_sq
      (Finset.univ : Finset (Fin (sourceDyadicCount M)))
      (fun j => S j psi t)
    have htri := norm_add_le (U psi t) (∑ j, S j psi t)
    have hsq : ‖U psi t + ∑ j, S j psi t‖ ^ 2 ≤
        (‖U psi t‖ + ‖∑ j, S j psi t‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
    have hadd : ‖U psi t + ∑ j, S j psi t‖ ^ 2 ≤
        2 * ‖U psi t‖ ^ 2 + 2 * ‖∑ j, S j psi t‖ ^ 2 := by
      have hdiff : 0 ≤
          (‖U psi t‖ - ‖∑ j, S j psi t‖) ^ 2 := sq_nonneg _
      calc
        _ ≤ (‖U psi t‖ + ‖∑ j, S j psi t‖) ^ 2 := hsq
        _ ≤ _ := by nlinarith
    have hcard : ((Finset.univ : Finset (Fin (sourceDyadicCount M))).card : ℝ) =
        sourceDyadicCount M := by simp
    rw [hcard] at hsum
    have hscaled : 2 * ‖∑ j, S j psi t‖ ^ 2 ≤
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M), ‖S j psi t‖ ^ 2 :=
      by
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
    have hfinal := hadd.trans (add_le_add_right hscaled _)
    simpa [U, S] using hfinal
  have hprefixCont : Continuous (fun t : ℝ =>
      ∑ psi : DirichletCharacter ℂ d,
        ‖twistedFinitePolynomial d (Finset.Icc 1 M)
          (shiftedSmoothedDivisorBlockCoeff sigma X) psi t‖ ^ 2) := by
    unfold twistedFinitePolynomial twistedPhase
    fun_prop
  have hrightCont : Continuous (fun t : ℝ =>
      2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2 +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
    apply Continuous.add
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro psi hpsi
      exact (by
        dsimp [U]
        unfold twistedFinitePolynomial twistedPhase
        fun_prop : Continuous (fun t => ‖U psi t‖ ^ 2))
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro j hj
      apply continuous_finsetSum
      intro psi hpsi
      exact (continuous_ramachandraDyadicBlock d (2 ^ (j : ℕ))
        (directSourceShellCoeff M sigma X j) false psi).norm.pow 2
  calc
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖twistedFinitePolynomial d (Finset.Icc 1 M)
          (shiftedSmoothedDivisorBlockCoeff sigma X) psi t‖ ^ 2) ≤
      ∫ t in (-T)..T,
        (2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2 +
          2 * (sourceDyadicCount M : ℝ) *
            ∑ j : Fin (sourceDyadicCount M),
              ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hprefixCont.intervalIntegrable _ _
      · exact hrightCont.intervalIntegrable _ _
      · intro t ht
        calc
          (∑ psi : DirichletCharacter ℂ d,
            ‖twistedFinitePolynomial d (Finset.Icc 1 M)
              (shiftedSmoothedDivisorBlockCoeff sigma X) psi t‖ ^ 2) ≤
            ∑ psi : DirichletCharacter ℂ d,
              (2 * ‖U psi t‖ ^ 2 +
                2 * (sourceDyadicCount M : ℝ) *
                  ∑ j : Fin (sourceDyadicCount M), ‖S j psi t‖ ^ 2) :=
            Finset.sum_le_sum fun psi hpsi => hpoint psi t
          _ = 2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2 +
              2 * (sourceDyadicCount M : ℝ) *
                ∑ j : Fin (sourceDyadicCount M),
                  ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_comm]
            simp_rw [← Finset.mul_sum]
    _ = 2 * (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            (∫ t in (-T)..T,
              ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
      have hUfun : Continuous (fun t : ℝ =>
          ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) := by
        apply continuous_finsetSum
        intro psi hpsi
        dsimp [U]
        unfold twistedFinitePolynomial twistedPhase
        fun_prop
      have hSfun (j : Fin (sourceDyadicCount M)) : Continuous (fun t : ℝ =>
          ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
        apply continuous_finsetSum
        intro psi hpsi
        dsimp [S]
        exact (continuous_ramachandraDyadicBlock d (2 ^ (j : ℕ))
          (directSourceShellCoeff M sigma X j) false psi).norm.pow 2
      have hSsum : Continuous (fun t : ℝ =>
          ∑ j : Fin (sourceDyadicCount M),
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
        apply continuous_finsetSum
        intro j hj
        exact hSfun j
      rw [intervalIntegral.integral_add
        (f := fun t => 2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2)
        (g := fun t => 2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2)
        ((continuous_const.mul hUfun).intervalIntegrable _ _)
        ((continuous_const.mul hSsum).intervalIntegrable _ _)]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro j hj
      exact (hSfun j).intervalIntegrable _ _
    _ ≤ 2 * (2 * (d : ℝ) * T) +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            directSourceShellCost d M T Y delta j := by
      have hunit : (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) ≤
          2 * (d : ℝ) * T := by
        dsimp [U]
        exact integral_sum_norm_directSourceUnitPolynomial_sq_le
          d M hM hT hX
      have hshell : (∑ j : Fin (sourceDyadicCount M),
          (∫ t in (-T)..T,
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2)) ≤
          ∑ j : Fin (sourceDyadicCount M),
            directSourceShellCost d M T Y delta j := by
        apply Finset.sum_le_sum
        intro j hj
        dsimp [S, directSourceShellCost]
        exact integral_sum_norm_directSourceShell_sq_le
          d M j hT hX (hNY j) hdelta hsigma
      have hJ : 0 ≤ (2 : ℝ) * sourceDyadicCount M := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hshell hJ]
    _ = _ := by ring

end
end RamachandraShiftedDirectAssembly

#print axioms RamachandraShiftedDirectAssembly.norm_fin_sum_sq_le_card_mul_sum_norm_sq
#print axioms RamachandraShiftedDirectAssembly.integral_sum_norm_shiftedDirectPrefix_sq_le
