import MontgomeryTheorem12SourceDAG
import PostA5LongSpacingAssembly
import PostA5TypeIFourierAssembly
import MontgomeryLowStripTypeIHalaszAssembly

/-!
# Simultaneous nonprincipal selection for Montgomery's low strip

This module performs the family-level choice that precedes the detector
partition.  Every nonprincipal ambient character receives one `3B`-separated
set of distinct zeros.  The certified A.5 multiplicity and unit-bin crowding
losses are kept explicit, and the principal row is exactly empty rather than
silently discarded.
-/

namespace MAPMontgomeryLowStripNonprincipalSelection

open scoped BigOperators FourierTransform SchwartzMap
open Set Complex CGLProofDAG DirichletZeros MAPAPZeroDensityCert
open PostA5LongSpacingAssembly PostA5CrowdingDeterministic
open PostA5TypeIFourierAssembly MAPAppendixA4PostA5SetAdapter
open MAPMontgomeryTheorem12SourceDAG
open MAPMontgomeryCharacterShellGrouping MAPMontgomeryLowStripTypeIHalaszAssembly

noncomputable section

/-- Simultaneous family form of the certified per-character crowding
extraction.  Its last inequality controls the complete multiplicity-weighted
nonprincipal ambient count by the total selected cardinality. -/
theorem exists_simultaneous_nonprincipal_threeBSeparated
    {q : ℕ} [NeZero q] {sigma T B : ℝ}
    (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∃ W : DirichletCharacter ℂ q → Finset ℂ,
      W (1 : DirichletCharacter ℂ q) = ∅ ∧
      (∀ chi, chi ≠ 1 → W chi ⊆ zeroSupport chi sigma T) ∧
      (∀ chi, ∀ rho ∈ W chi, ∀ rho' ∈ W chi, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      (nonprincipalAmbientZeroCountAtLevel q sigma T : ℝ) ≤
        certifiedA5CrowdingEnvelope q T *
          (longSpacingColorCount B * certifiedA5CrowdingNatCap q T) *
            ∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ) := by
  classical
  have hexists : ∀ chi : DirichletCharacter ℂ q, chi ≠ 1 →
      ∃ S : Finset ℂ,
        S ⊆ zeroSupport chi sigma T ∧
        (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
          3 * B ≤ |rho.im - rho'.im|) ∧
        (dirichletZeroCount chi sigma T : ℝ) ≤
          certifiedA5CrowdingEnvelope q T *
            (longSpacingColorCount B * certifiedA5CrowdingNatCap q T) *
              S.card := by
    intro chi hchi
    exact exists_threeBSeparated_zeroSupport_weighted
      chi hchi hsigma hT hB
  let W : DirichletCharacter ℂ q → Finset ℂ := fun chi =>
    if hchi : chi = 1 then ∅ else Classical.choose (hexists chi hchi)
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · simp [W]
  · intro chi hchi
    simp only [W, dif_neg hchi]
    exact (Classical.choose_spec (hexists chi hchi)).1
  · intro chi rho hrho rho' hrho' hne
    by_cases hchi : chi = 1
    · subst chi
      simp [W] at hrho
    · exact (Classical.choose_spec (hexists chi hchi)).2.1
        rho (by simpa [W, hchi] using hrho)
        rho' (by simpa [W, hchi] using hrho') hne
  · unfold nonprincipalAmbientZeroCountAtLevel
    push_cast
    have henvelope0 : 0 ≤ certifiedA5CrowdingEnvelope q T := by
      have hqone : (1 : ℝ) ≤ q := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      have hscale : 1 ≤ (q : ℝ) * (T + 3) := by
        exact one_le_mul_of_one_le_of_one_le hqone (by linarith)
      unfold certifiedA5CrowdingEnvelope
      exact div_nonneg (by
        have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
        have h3200 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3200)
        have hs := Real.log_nonneg hscale
        linarith) (Real.log_nonneg (by norm_num))
    calc
      (∑ chi ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
          (dirichletZeroCount chi sigma T : ℝ)) ≤
          ∑ chi ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
            certifiedA5CrowdingEnvelope q T *
              (longSpacingColorCount B * certifiedA5CrowdingNatCap q T) *
                ((W chi).card : ℝ) := by
        apply Finset.sum_le_sum
        intro chi hchi
        have hne : chi ≠ 1 := (Finset.mem_erase.mp hchi).1
        simpa only [W, dif_neg hne] using
          (Classical.choose_spec (hexists chi hne)).2.2
      _ ≤ ∑ chi : DirichletCharacter ℂ q,
            certifiedA5CrowdingEnvelope q T *
              (longSpacingColorCount B * certifiedA5CrowdingNatCap q T) *
                ((W chi).card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro chi _hchi _hnot
        exact mul_nonneg
          (mul_nonneg henvelope0 (by positivity)) (Nat.cast_nonneg _)
      _ = certifiedA5CrowdingEnvelope q T *
            (longSpacingColorCount B * certifiedA5CrowdingNatCap q T) *
              ∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ) := by
        rw [Finset.mul_sum]

/-! ## Long spacing survives the Type-I Fourier shift -/

/-- If source ordinates are separated by `2C+1`, arbitrary individual
Fourier shifts of size at most `C` preserve one-spacing.  The image also has
exactly the source cardinality. -/
theorem oneSeparated_image_neg_im_add_of_longSeparated
    (S : Finset ℂ) (shift : ℂ → ℝ) {C : ℝ}
    (hshift : ∀ rho ∈ S, |shift rho| ≤ C)
    (hsep : ∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
      2 * C + 1 ≤ |rho.im - rho'.im|) :
    OneSeparated (S.image fun rho => -rho.im + shift rho) ∧
      (S.image fun rho => -rho.im + shift rho).card = S.card := by
  classical
  let f : ℂ → ℝ := fun rho => -rho.im + shift rho
  have hinj : Set.InjOn f (↑S : Set ℂ) := by
    intro rho hrho rho' hrho' heq
    by_contra hne
    have hgap := hsep rho hrho rho' hrho' hne
    have hsdiff : |shift rho - shift rho'| ≤ 2 * C := by
      calc
        |shift rho - shift rho'| ≤ |shift rho| + |shift rho'| := abs_sub _ _
        _ ≤ C + C := add_le_add (hshift rho hrho) (hshift rho' hrho')
        _ = 2 * C := by ring
    have hzero : -rho.im + shift rho - (-rho'.im + shift rho') = 0 := by
      exact sub_eq_zero.mpr heq
    have him : rho.im - rho'.im = shift rho - shift rho' := by
      linarith
    rw [him] at hgap
    linarith
  have hcard : (S.image f).card = S.card :=
    Finset.card_image_iff.mpr (fun rho hrho rho' hrho' h => hinj hrho hrho' h)
  refine ⟨?_, hcard⟩
  intro t ht u hu htu
  rcases Finset.mem_image.mp ht with ⟨rho, hrho, rfl⟩
  rcases Finset.mem_image.mp hu with ⟨rho', hrho', rfl⟩
  have hne : rho ≠ rho' := by
    intro heq
    subst rho'
    exact htu rfl
  have hgap := hsep rho hrho rho' hrho' hne
  have hsdiff : |shift rho - shift rho'| ≤ 2 * C := by
    calc
      |shift rho - shift rho'| ≤ |shift rho| + |shift rho'| := abs_sub _ _
      _ ≤ C + C := add_le_add (hshift rho hrho) (hshift rho' hrho')
      _ = 2 * C := by ring
  have htriangle : |rho.im - rho'.im| ≤
      |(-rho.im + shift rho) - (-rho'.im + shift rho')| +
        |shift rho - shift rho'| := by
    calc
      |rho.im - rho'.im| =
          |-((-rho.im + shift rho) - (-rho'.im + shift rho')) +
            (shift rho - shift rho')| := by congr 1 <;> ring
      _ ≤ |-((-rho.im + shift rho) - (-rho'.im + shift rho'))| +
          |shift rho - shift rho'| := abs_add_le _ _
      _ = |(-rho.im + shift rho) - (-rho'.im + shift rho')| +
          |shift rho - shift rho'| := by rw [abs_neg]
  linarith

/-- Exact Type-I Fourier extraction from a long-spaced source set.  Unlike
the generic crowding wrapper, this loses no further cardinality: the selected
polynomial threshold is exactly `V/(4*A*J)`, where `J` is the detector dyadic
count. -/
theorem exists_typeI_fourier_family_of_longSeparated
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N)) (S : Finset ℂ)
    {H A V C : ℝ} (hHC : 2 * Real.pi * H ≤ C)
    (hsep : ∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
      2 * C + 1 ≤ |rho.im - rho'.im|)
    (hA : 0 < A) (hV : 0 < V)
    (hmass : ∀ rho ∈ S,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ∀ rho ∈ S,
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V / (detectorDyadicCount N : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount N *
        ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) :
    ∃ (xi : ℂ → ℝ) (W : Finset ℝ),
      W = S.image (fun rho => -rho.im + 2 * Real.pi * xi rho) ∧
      OneSeparated W ∧ W.card = S.card ∧
      (∀ t ∈ W,
        V / (4 * A * detectorDyadicCount N) ≤
          ‖dirichletPolynomial
            (detectorCommonCoefficient chi U N Y sigma)
            (2 ^ (j : ℕ)) t‖) := by
  obtain ⟨xi, hxi⟩ := exists_typeI_fourier_assignment
    chi hU Y sigma j S hA hV hmass htail hblock
  let W := S.image (fun rho => -rho.im + 2 * Real.pi * xi rho)
  have hshift : ∀ rho ∈ S, |2 * Real.pi * xi rho| ≤ C := by
    intro rho hrho
    have hxabs : |xi rho| ≤ H := abs_le.mpr (hxi rho hrho).1
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left hxabs (by positivity)).trans hHC
  obtain ⟨hWsep, hWcard⟩ :=
    oneSeparated_image_neg_im_add_of_longSeparated S
      (fun rho => 2 * Real.pi * xi rho) hshift hsep
  refine ⟨xi, W, rfl, hWsep, hWcard, ?_⟩
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨rho, hrho, rfl⟩
  exact (hxi rho hrho).2

/-- A shell chosen separately for each character is reduced to one literal
common detector shell before applying the all-character Halasz theorem.  The
only loss is the exact dyadic count `r`; separation, height, and the
shell-normalized large-value threshold are preserved. -/
theorem exists_common_typeI_detector_shell_family
    {q U N r : ℕ} [NeZero q] (hr : 0 < r)
    (chosen : DirichletCharacter ℂ q → Fin r)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (Y sigma V T : ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma)
        (2 ^ ((chosen chi : Fin r) : ℕ)) t‖) :
    ∃ i : Fin r,
      (∑ chi : DirichletCharacter ℂ q, (W chi).card ≤
        r * ∑ chi : DirichletCharacter ℂ q,
          (restrictFamilyByIndex chosen W i chi).card) ∧
      (∀ chi, OneSeparated (restrictFamilyByIndex chosen W i chi)) ∧
      (∀ chi, ∀ t ∈ restrictFamilyByIndex chosen W i chi, |t| ≤ T) ∧
      (∀ chi, ∀ t ∈ restrictFamilyByIndex chosen W i chi,
        V ≤ ‖dirichletPolynomial
          (detectorCommonCoefficient chi U N Y sigma)
          (2 ^ (i : ℕ)) t‖) := by
  obtain ⟨i, hcard, hsep', hheight'⟩ :=
    exists_common_detector_shell_family hr chosen W hsep hheight
  refine ⟨i, hcard, hsep', hheight', ?_⟩
  intro chi t ht
  have hchosen : chosen chi = i := by
    by_contra hne
    simp [restrictFamilyByIndex, hne] at ht
  have htW : t ∈ W chi := by
    simpa [restrictFamilyByIndex, hchosen] using ht
  simpa [hchosen] using hlarge chi t htW

end
end MAPMontgomeryLowStripNonprincipalSelection

#print axioms MAPMontgomeryLowStripNonprincipalSelection.exists_simultaneous_nonprincipal_threeBSeparated
#print axioms MAPMontgomeryLowStripNonprincipalSelection.oneSeparated_image_neg_im_add_of_longSeparated
#print axioms MAPMontgomeryLowStripNonprincipalSelection.exists_typeI_fourier_family_of_longSeparated
#print axioms MAPMontgomeryLowStripNonprincipalSelection.exists_common_typeI_detector_shell_family
