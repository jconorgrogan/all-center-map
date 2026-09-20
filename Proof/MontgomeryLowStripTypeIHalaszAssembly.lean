import MontgomeryLowStripSourceSplit
import MontgomeryTheorem83Halasz
import MontgomeryTheorem83SmoothHalasz
import MontgomerySmoothMajorant
import MontgomeryDetectorCharacterFactorization
import MontgomeryCharacterShellGrouping

/-!
# Montgomery low-strip Type-I Halasz assembly

This module puts the repaired Appendix A.4 low-strip split and the exact
finite Halasz reduction for Montgomery Theorem 8.3 on the same detector
coefficient.  The source correlation-kernel estimate remains displayed as a
premise; all coefficient factorization, row geometry, cardinality
absorption, and normalization around it are certified.
-/

namespace MAPMontgomeryLowStripTypeIHalaszAssembly

open scoped BigOperators ComplexConjugate
open CGLProofDAG MontgomeryVaughanFiniteReduction
open MAPMRTLemma210DyadicMeanSquare
open MAPMontgomeryDetectorCharacterFactorization
open MAPMontgomeryTheorem83Halasz
open MAPMontgomeryTheorem83SmoothHalasz
open MAPMontgomerySmoothMajorant
open MAPMontgomeryCharacterShellGrouping
open MAPAppendixA4PostA5SetAdapter

noncomputable section

/-- Family-level shell pigeonhole required between the fixed-character
source split and the all-character Theorem 8.3 consumer.  A single shell
retains at least a `1/r` share and its restricted ordinate fibers preserve
both one-separation and the symmetric height box. -/
theorem exists_common_detector_shell_family
    {q r : ℕ} [NeZero q] (hr : 0 < r) {T : ℝ}
    (chosen : DirichletCharacter ℂ q → Fin r)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T) :
    ∃ i : Fin r,
      (∑ chi : DirichletCharacter ℂ q, (W chi).card ≤
        r * ∑ chi : DirichletCharacter ℂ q,
          (restrictFamilyByIndex chosen W i chi).card) ∧
      (∀ chi, OneSeparated (restrictFamilyByIndex chosen W i chi)) ∧
      (∀ chi, ∀ t ∈ restrictFamilyByIndex chosen W i chi, |t| ≤ T) := by
  obtain ⟨i, hcard⟩ := exists_common_character_index hr chosen W
  refine ⟨i, hcard, ?_, ?_⟩
  · intro chi t ht u hu htu
    exact hsep chi t
      (restrictFamilyByIndex_subset chosen W i chi ht) u
      (restrictFamilyByIndex_subset chosen W i chi hu) htu
  · intro chi t ht
    exact hheight chi t (restrictFamilyByIndex_subset chosen W i chi ht)

/-- Theorem 8.3's absorbed large-value conclusion for the literal detector
shell emitted by the repaired low-strip split.  The character twist has been
removed from the coefficient before the common correlation energy is formed.
-/
theorem detectorShell_character_halasz_large_values_absorbed
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (Y sigma : ℝ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hkernel :
      ∀ eta : ((chi : DirichletCharacter ℂ q) × ℝ) → ℂ,
      (∀ row ∈ characterRows W, ‖eta row‖ = 1) →
        MAPJutilaDeterministicCore.correlationEnergy
            (characterRows W) (dyadicSupport D) (fun _ => 1) eta
            characterRowVector ≤
          ((characterRows W).card : ℝ) * C *
            ((D : ℝ) + ((characterRows W).card : ℝ) * K))
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  let a : ℕ → ℂ := untwistedDetectorCommonCoefficient U N Y sigma
  have hlargePacket : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D) a chi t‖ := by
    intro chi t ht
    simpa [a,
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
      hlarge chi t ht
  simpa [a] using
    character_halasz_large_values_absorbed hD a hT hV hC hK W
      hsep hheight hlargePacket hkernel hthreshold

/-- Alternate detector-shell weld through a signed Hermitian operator form.
The published source route uses long spacing and the equation-(30) pairwise
kernel; see `MontgomeryEquation30SourceHalasz`. -/
theorem detectorShell_character_smooth_large_values_absorbed_of_operatorBound
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (tail : Finset ℕ)
    (Y sigma : ℝ) (b : ℕ → ℝ) {T V C : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (hbpos : ∀ n ∈ smoothCarrier D tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport D, 1 ≤ b n)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hoperator : WeightedGramOperatorBound
      (characterRows W) (smoothCarrier D tail) b characterRowVector
      (C * ((D : ℝ) + ((characterRows W).card : ℝ) *
        theorem83KernelScale q T)))
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D *
            theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  let a : ℕ → ℂ := untwistedDetectorCommonCoefficient U N Y sigma
  have hlargePacket : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D) a chi t‖ := by
    intro chi t ht
    simpa [a,
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
      hlarge chi t ht
  simpa [a] using
    character_smooth_large_values_absorbed_of_operatorBound
      hD tail a b hT hV hC hscale hbpos hbmajor W hsep hheight
        hlargePacket hoperator hthreshold

/-- Operator-form alternative specialized to the equation-(33) positive
majorant. -/
theorem detectorShell_character_montgomeryWeight_largeValues_of_operatorBound
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (tail : Finset ℕ)
    (htailPos : ∀ n ∈ smoothCarrier D tail, 0 < n)
    (Y sigma : ℝ) {k T V C : ℝ} (hk : 1 ≤ k)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hoperator : WeightedGramOperatorBound
      (characterRows W) (smoothCarrier D tail)
      (montgomerySmoothWeight (D : ℝ) k) characterRowVector
      (C * ((D : ℝ) + ((characterRows W).card : ℝ) *
        theorem83KernelScale q T)))
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D *
            theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  apply detectorShell_character_smooth_large_values_absorbed_of_operatorBound
    hD tail Y sigma (montgomerySmoothWeight (D : ℝ) k)
      hT hV hC hscale
  · intro n hn
    exact montgomerySmoothWeight_pos
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD))
      (zero_lt_one.trans_le hk) (htailPos n hn)
  · intro n hn
    exact montgomerySmoothWeight_ge_one_on_dyadic hD hk hn
  · exact hsep
  · exact hheight
  · exact hlarge
  · exact hoperator
  · exact hthreshold

/-- Legacy smooth absolute-row/Schur weld.  The premise is an overstrong
surrogate and fails at the advertised source scale; use the operator theorem
above. -/
theorem detectorShell_character_smooth_halasz_large_values_absorbed_sourceScale
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (tail : Finset ℕ)
    (Y sigma : ℝ) (b : ℕ → ℝ) {T V C : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (hbpos : ∀ n ∈ smoothCarrier D tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport D, 1 ≤ b n)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ smoothCarrier D tail,
              (b n : ℂ) * conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((D : ℝ) + ((characterRows W).card : ℝ) *
          theorem83KernelScale q T))
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D *
            theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  let a : ℕ → ℂ := untwistedDetectorCommonCoefficient U N Y sigma
  have hlargePacket : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D) a chi t‖ := by
    intro chi t ht
    simpa [a,
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
      hlarge chi t ht
  simpa [a] using
    character_smooth_halasz_large_values_absorbed_sourceScale
      hD tail a b hT hV hC hscale hbpos hbmajor W hsep hheight
        hlargePacket hrowKernel hthreshold

/-- Legacy absolute-row specialization of Montgomery's literal weight.  The
conditional theorem is valid but its row-sum premise is not the source
mechanism. -/
theorem detectorShell_character_montgomeryWeight_halasz_absorbed_sourceScale
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (tail : Finset ℕ)
    (htailPos : ∀ n ∈ smoothCarrier D tail, 0 < n)
    (Y sigma : ℝ) {k T V C : ℝ} (hk : 1 ≤ k)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ smoothCarrier D tail,
              (montgomerySmoothWeight (D : ℝ) k n : ℂ) *
                conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((D : ℝ) + ((characterRows W).card : ℝ) *
          theorem83KernelScale q T))
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D *
            theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  apply detectorShell_character_smooth_halasz_large_values_absorbed_sourceScale
    hD tail Y sigma (montgomerySmoothWeight (D : ℝ) k)
      hT hV hC hscale
  · intro n hn
    exact montgomerySmoothWeight_pos
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD))
      (zero_lt_one.trans_le hk) (htailPos n hn)
  · intro n hn
    exact montgomerySmoothWeight_ge_one_on_dyadic hD hk hn
  · exact hsep
  · exact hheight
  · exact hlarge
  · exact hrowKernel
  · exact hthreshold

/-- Detector-shell specialization with Montgomery's exact source kernel as
the sole analytic premise.  In particular, the coefficient depending on the
character is factored into one common untwisted coefficient before the
rowwise `B`-kernel estimate is used. -/
theorem detectorShell_character_halasz_large_values_absorbed_of_rowKernel
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (Y sigma : ℝ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ dyadicSupport D,
              conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((D : ℝ) + ((characterRows W).card : ℝ) * K))
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  let a : ℕ → ℂ := untwistedDetectorCommonCoefficient U N Y sigma
  have hlargePacket : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D) a chi t‖ := by
    intro chi t ht
    simpa [a,
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
      hlarge chi t ht
  simpa [a] using
    character_halasz_large_values_absorbed_of_rowKernel
      hD a hT hV hC hK W hsep hheight hlargePacket hrowKernel hthreshold

/-- The preceding detector-shell weld at Montgomery's literal hybrid scale
`sqrt(q*T) * log(q*T)`.  This is the exact Type-I large-value interface used
after the source split; no `q*T + D` mean-square loss has replaced the
Halasz refinement. -/
theorem detectorShell_character_halasz_large_values_absorbed_sourceScale
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (Y sigma : ℝ) {T V C : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ dyadicSupport D,
              conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((D : ℝ) + ((characterRows W).card : ℝ) *
          theorem83KernelScale q T))
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D *
            theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  let a : ℕ → ℂ := untwistedDetectorCommonCoefficient U N Y sigma
  have hlargePacket : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D) a chi t‖ := by
    intro chi t ht
    simpa [a,
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
      hlarge chi t ht
  simpa [a] using
    character_halasz_large_values_absorbed_sourceScale
      hD a hT hV hC hscale W hsep hheight hlargePacket hrowKernel hthreshold

/-- A stronger detector-shell route with separate diagonal and uniform
distinct-row premises.  It is useful for alternative kernels but is not the
literal Montgomery source formulation. -/
theorem detectorShell_character_halasz_large_values_absorbed_of_pairwise
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (Y sigma : ℝ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hdiag : ∀ row ∈ characterRows W,
      ‖∑ n ∈ dyadicSupport D,
          conj (characterRowVector row n) *
            characterRowVector row n‖ ≤ C * D)
    (hoff : ∀ row ∈ characterRows W,
      ∀ row' ∈ characterRows W, row ≠ row' →
        ‖∑ n ∈ dyadicSupport D,
            conj (characterRowVector row n) *
              characterRowVector row' n‖ ≤ C * K)
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  let a : ℕ → ℂ := untwistedDetectorCommonCoefficient U N Y sigma
  have hlargePacket : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D) a chi t‖ := by
    intro chi t ht
    simpa [a,
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
      hlarge chi t ht
  simpa [a] using
    character_halasz_large_values_absorbed_of_pairwise
      hD a hT hV hC hK W hsep hheight hlargePacket hdiag hoff hthreshold

/-- An optional stronger detector-shell route in which the diagonal kernel is
discharged and only a uniform distinct-row estimate is assumed. -/
theorem detectorShell_character_halasz_large_values_absorbed_of_offDiagonal
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    (Y sigma : ℝ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hCone : 1 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖)
    (hoff : ∀ row ∈ characterRows W,
      ∀ row' ∈ characterRows W, row ≠ row' →
        ‖∑ n ∈ dyadicSupport D,
            conj (characterRowVector row n) *
              characterRowVector row' n‖ ≤ C * K)
    (hthreshold :
      2 * C * coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D * D := by
  let a : ℕ → ℂ := untwistedDetectorCommonCoefficient U N Y sigma
  have hlargePacket : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D) a chi t‖ := by
    intro chi t ht
    simpa [a,
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
      hlarge chi t ht
  simpa [a] using
    character_halasz_large_values_absorbed_of_offDiagonal
      hD a hT hV hCone hK W hsep hheight hlargePacket hoff hthreshold

/-- The repaired low-strip pointwise split used immediately before the
preceding family theorem.  Re-exporting the literal statement here prevents
the Halasz assembly from drifting to a different truncation envelope or
Type-II normalization. -/
theorem repaired_lowStrip_detector_pointwise
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y R V : ℝ} (hY : 1 ≤ Y) (hV : 0 < V)
    (hUN : U ≤ MAPAppendixA4DetectorDichotomy.detectorArithmeticCutoff Y R)
    (hB : 1 ≤ MAPAppendixA4DetectorDichotomy.detectorVerticalCutoff R)
    (hbudget :
      MAPAppendixA4RecenteredGammaRepair.detectorTruncationErrorEnvelopePolynomialHeight
          q U rho Y R + V + V ≤ Real.exp (-(1 / Y))) :
    V ≤ ‖MAPAppendixA4DetectorDichotomy.arithmeticDetectorBlock chi U
        (MAPAppendixA4DetectorDichotomy.detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc
          (-(MAPAppendixA4DetectorDichotomy.detectorVerticalCutoff R))
          (MAPAppendixA4DetectorDichotomy.detectorVerticalCutoff R),
        V /
            ((MAPMontgomeryLowStripGamma.lowStripGammaConstant delta / 2) *
              Real.rpow Y (1 / 2 - rho.re) *
              (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ :=
  MAPMontgomeryLowStripSourceSplit.detector_to_typeI_or_sourceTypeII_lowStrip
    chi hchi hdelta hU hrho hbetaLow hbetaHigh hY hV hUN hB hbudget

end
end MAPMontgomeryLowStripTypeIHalaszAssembly

#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.exists_common_detector_shell_family
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_halasz_large_values_absorbed
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_smooth_large_values_absorbed_of_operatorBound
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_montgomeryWeight_largeValues_of_operatorBound
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_smooth_halasz_large_values_absorbed_sourceScale
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_montgomeryWeight_halasz_absorbed_sourceScale
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_halasz_large_values_absorbed_of_rowKernel
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_halasz_large_values_absorbed_sourceScale
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_halasz_large_values_absorbed_of_pairwise
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.detectorShell_character_halasz_large_values_absorbed_of_offDiagonal
#print axioms MAPMontgomeryLowStripTypeIHalaszAssembly.repaired_lowStrip_detector_pointwise
