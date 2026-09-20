import CGLDetectorStructuredLargeValue
import PostA5HighStripSplitReductionFromFourthMoment

/-!
# A source-faithful Type-I large-value seam

The earlier structured seam remembers the normalized detector coefficient but
forgets the exact detector scales and the origin of the sampling ordinates.
This module keeps the literal data needed by a MAP-specific large-value
argument:

* the arithmetic cutoff is `detectorArithmeticCutoff Y R`;
* the normalization is the exact inverse shell majorant;
* positivity of the selected dyadic block forces `U < 2 * D`;
* every sample ordinate is obtained from a selected zero ordinate by the
  Fourier shift and the single optional recentering by `T`.

No large-value estimate is asserted here.
-/

namespace CGLDetectorSourceFaithfulLargeValue

open scoped BigOperators FourierTransform
open CGLProofDAG DirichletZeros MAPAppendixA4PostA5SetAdapter
open ZeroDensityInterface MAPGuthMaynard
open CGLCompactStripDensityConstructor
open MAPAppendixA4DetectorDichotomy MAPAppendixA4RecenteredGammaRepair
open PostA5TypeIFourierAssembly PostA5TypeIOrdinateRecentering
open PostA5RecenteredTypeIExtractor PostA5LongSpacingAssembly
open PostA5CrowdingDeterministic PostA5HighStripSplitAssembly
open PostA5TypeICoefficientProvenance
open PostA5HighStripSplitReductionFromFourthMoment
open SchwartzMap

noncomputable section

/-- The exact shell normalization used by the literal Type-I producer. -/
def literalTypeIScale (D : ℕ) (sigma Kd e : ℝ) : ℝ :=
  (Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e))⁻¹

/-- Compact provenance for the only two recentering branches.  The branch of
the coefficient and the branch of the ordinates are coupled, so a consumer
cannot combine an untranslated coefficient with translated sample points. -/
def IsLiteralRecenteredDetectorPair
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U Ncut : ℕ) (Y sigma : ℝ) (D : ℕ) (scale T H : ℝ)
    (Z : Finset ℂ) (b : ℕ → ℂ) (W : Finset ℝ) : Prop :=
  (b = normalizedDetectorCoefficient chi U Ncut Y sigma D scale ∧
      ∀ t ∈ W, ∃ rho ∈ Z, ∃ xi ∈ Set.Icc (-H) H,
        t = -rho.im + 2 * Real.pi * xi) ∨
    (b = translatedCoefficient
        (normalizedDetectorCoefficient chi U Ncut Y sigma D scale) T ∧
      ∀ t ∈ W, ∃ rho ∈ Z, ∃ xi ∈ Set.Icc (-H) H,
        t = -rho.im + 2 * Real.pi * xi + T)

/-- The exact normalized Type-I witness at the literal detector cutoff.  The
normalization and cutoff are terms, rather than existential parameters. -/
def IsLiteralNormalizedTypeIWitness
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U : ℕ) (Y R sigma Kd e T H : ℝ) (D : ℕ)
    (Z : Finset ℂ) (b : ℕ → ℂ) (W : Finset ℝ) : Prop :=
  U < 2 * D ∧
    IsLiteralRecenteredDetectorPair chi U (detectorArithmeticCutoff Y R)
      Y sigma D (literalTypeIScale D sigma Kd e) T H Z b W

/-- The project-scale specialization used by the current A.4 producer.  This
hard-codes all five identities that were erased by the older existential
seam: `U`, `Y`, `R`, `Ncut`, and the dyadic length `D`. -/
def IsProjectScaleLiteralTypeIWitness
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (kappa h Kd e T sigma : ℝ) (Z : Finset ℂ)
    (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) : Prop :=
  let U : ℕ := ⌊Real.rpow T (2 * kappa)⌋₊
  let Y : ℝ := Real.rpow T (1 / 2)
  let Ncut : ℕ := detectorArithmeticCutoff Y T
  chi.IsPrimitive ∧ chi ≠ 1 ∧
    (∀ rho ∈ Z, DirichletCharacter.LFunction chi rho = 0) ∧
    (∀ rho ∈ Z, sigma ≤ rho.re) ∧
    (∀ rho ∈ Z, rho.re ≤ 1) ∧
    (∀ rho ∈ Z, |rho.im| ≤ T) ∧
    (∀ rho ∈ Z, ∀ rho' ∈ Z, rho ≠ rho' →
      3 * detectorVerticalCutoff T ≤ |rho.im - rho'.im|) ∧
    4 ≤ T ∧ 1 ≤ U ∧ U ≤ Ncut ∧
    ∃ j : Fin (detectorDyadicCount Ncut),
      D = 2 ^ (j : ℕ) ∧
      (D : ℝ) ≤ T ∧
      (D : ℝ) ≤ Y * (Real.log T) ^ 2 ∧
      IsLiteralNormalizedTypeIWitness chi U Y T sigma Kd e T
        (Real.rpow T h) D Z b W

/-- The producer has a separate empty-Type-I branch.  No analytic estimate is
needed there, so it is recorded explicitly instead of fabricating dyadic
provenance for a dummy polynomial. -/
def IsProjectScaleLiteralTypeIOutcome
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (kappa h Kd e T sigma : ℝ) (Z : Finset ℂ)
    (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) : Prop :=
  W = ∅ ∨
    IsProjectScaleLiteralTypeIWitness
      chi kappa h Kd e T sigma Z D b W

/-- The WIP producer writes `kDet = 2 * kOut`; hence its mollifier cutoff is
definitionally the one hard-coded by the project-scale witness. -/
theorem projectScale_mollifier_eq_of_detector_relation
    (T kOut kDet : ℝ) (hkDet : kDet = 2 * kOut) :
    ⌊Real.rpow T kDet⌋₊ = ⌊Real.rpow T (2 * kOut)⌋₊ := by
  rw [hkDet]

/-- Assemble the project-scale record once the literal producer has supplied
its dyadic witness.  Every parameter in the conclusion is the exact term used
by the producer; there are no existential cutoff or normalization variables. -/
theorem projectScaleLiteralTypeIWitness_of_literalData
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (kappa h Kd e T sigma : ℝ) (Z : Finset ℂ)
    (j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff (Real.rpow T (1 / 2)) T)))
    (b : ℕ → ℂ) (W : Finset ℝ)
    (hprimitive : chi.IsPrimitive) (hchi : chi ≠ 1)
    (hzero : ∀ rho ∈ Z, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z, sigma ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ Z, rho.re ≤ 1)
    (hheight : ∀ rho ∈ Z, |rho.im| ≤ T)
    (hsep : ∀ rho ∈ Z, ∀ rho' ∈ Z, rho ≠ rho' →
      3 * detectorVerticalCutoff T ≤ |rho.im - rho'.im|)
    (hT : 4 ≤ T)
    (hU : 1 ≤ ⌊Real.rpow T (2 * kappa)⌋₊)
    (hUN : ⌊Real.rpow T (2 * kappa)⌋₊ ≤
      detectorArithmeticCutoff (Real.rpow T (1 / 2)) T)
    (hDtime : ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T)
    (hDhigh : ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤
      Real.rpow T (1 / 2) * (Real.log T) ^ 2)
    (hpair : IsLiteralNormalizedTypeIWitness chi
      ⌊Real.rpow T (2 * kappa)⌋₊ (Real.rpow T (1 / 2)) T sigma
      Kd e T (Real.rpow T h) (2 ^ (j : ℕ)) Z b W) :
    IsProjectScaleLiteralTypeIWitness
      chi kappa h Kd e T sigma Z (2 ^ (j : ℕ)) b W := by
  exact ⟨hprimitive, hchi, hzero, hbetaLow, hbetaHigh, hheight, hsep,
    hT, hU, hUN, j, rfl, hDtime, hDhigh, hpair⟩

/-- Candidate analytic input at the exact project-scale producer surface.
Unlike an arbitrary-coefficient GM statement, its sample set must be a
literal image of selected zero ordinates. -/
def ProjectScaleSourceFaithfulThirtyThirteenLargeValue : Prop :=
  ∀ kappa eta : ℝ, 0 < kappa → 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T sigma h Kd e : ℝ) (D : ℕ) (b : ℕ → ℂ)
        (W : Finset ℝ),
        T₀ ≤ T → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        Real.rpow T kappa ≤ D →
        (∀ n, ‖b n‖ ≤ 1) → OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W,
          Real.rpow D sigma *
              Real.rpow T (-inputLoss kappa (eta / 2)) ≤
            ‖dirichletPolynomial b D t‖) →
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
          (Z : Finset ℂ),
          IsProjectScaleLiteralTypeIOutcome
            chi kappa h Kd e T sigma Z D b W →
          (W.card : ℝ) ≤
            C * Real.rpow T (densityCoeff * (1 - sigma) + eta)

/-- The published arbitrary-coefficient large-value estimate implies the
source-faithful project-scale seam. -/
theorem projectScaleSourceFaithful_of_uniform
    (huniform : UniformThirtyThirteenLargeValue) :
    ProjectScaleSourceFaithfulThirtyThirteenLargeValue := by
  intro kappa eta hkappa heta
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := huniform kappa eta hkappa heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T sigma h Kd e D b W hT hsigmaLow hsigmaHigh hDlow hb hsep
    hheight hlarge q _inst chi Z hsource
  rcases hsource with hWempty | hsource
  · subst W
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hC.le
      (Real.rpow_nonneg (by linarith [hT₀.trans hT] : 0 ≤ T) _)
  · have hDhigh :
        (D : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 := by
      dsimp [IsProjectScaleLiteralTypeIWitness] at hsource
      obtain ⟨_hprimitive, _hchi, _hzero, _hbetaLow, _hbetaHigh,
        _hzeroHeight, _hzeroSep, _hT, _hU, _hUN, j, _hDj, _hDtime,
        hDhigh, _hpair⟩ := hsource
      simpa using hDhigh
    exact hbound T sigma D b W hT hsigmaLow hsigmaHigh hDlow hDhigh hb
      hsep hheight hlarge

/-- Recenter a literal producer set while retaining the common zero source
of every sample point and coupling it to the coefficient branch. -/
theorem exists_nonnegative_recentered_largeValueSet_with_zero_provenance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U Ncut : ℕ) (Y sigma : ℝ) (D : ℕ) (scale : ℝ)
    (Z : Finset ℂ) (H : ℝ) (braw : ℕ → ℂ)
    (Wraw : Finset ℝ) {T V : ℝ}
    (hbraw : braw = detectorCommonCoefficient chi U Ncut Y sigma)
    (hsource : ∀ t ∈ Wraw, ∃ rho ∈ Z, ∃ xi ∈ Set.Icc (-H) H,
      t = -rho.im + 2 * Real.pi * xi)
    (hsep : OneSeparated Wraw)
    (hscale : 0 ≤ scale)
    (hheight : ∀ t ∈ Wraw, |t| ≤ T)
    (hlarge : ∀ t ∈ Wraw, V ≤ ‖dirichletPolynomial braw D t‖) :
    ∃ (b : ℕ → ℂ) (W : Finset ℝ),
      IsLiteralRecenteredDetectorPair chi U Ncut Y sigma D scale T H Z
        b W ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        scale * V ≤ ‖dirichletPolynomial b D t‖) ∧
      Wraw.card ≤ 2 * W.card := by
  classical
  let Wneg := nonpositivePart Wraw
  let Wpos := nonnegativePart Wraw
  have hcard : Wraw.card ≤ Wneg.card + Wpos.card := by
    simpa [Wneg, Wpos] using card_le_sign_parts Wraw
  by_cases hchoice : Wneg.card ≤ Wpos.card
  · refine ⟨shellNormalizedCoefficient braw D scale, Wpos, ?_, ?_, ?_, ?_, ?_⟩
    · left
      constructor
      · rw [hbraw]
        rfl
      · intro t ht
        have htW : t ∈ Wraw := (Finset.mem_filter.mp ht).1
        exact hsource t htW
    · exact oneSeparated_subset hsep (Finset.filter_subset _ _)
    · intro t ht
      have htW : t ∈ Wraw := (Finset.mem_filter.mp ht).1
      have h0t : 0 ≤ t := (Finset.mem_filter.mp ht).2
      exact ⟨h0t, (abs_le.mp (hheight t htW)).2⟩
    · intro t ht
      rw [dirichletPolynomial_shellNormalizedCoefficient braw D hscale]
      exact mul_le_mul_of_nonneg_left
        (hlarge t (Finset.mem_filter.mp ht).1) hscale
    · omega
  · let W : Finset ℝ := Wneg.image fun t => t + T
    refine ⟨shellNormalizedCoefficient (translatedCoefficient braw T) D scale,
      W, ?_, ?_, ?_, ?_, ?_⟩
    · right
      constructor
      · rw [shellNormalizedCoefficient_translatedCoefficient, hbraw]
        rfl
      · intro u hu
        change u ∈ Wneg.image (fun t => t + T) at hu
        rw [Finset.mem_image] at hu
        obtain ⟨t, ht, rfl⟩ := hu
        have htW : t ∈ Wraw := (Finset.mem_filter.mp ht).1
        obtain ⟨rho, hrho, xi, hxi, rfl⟩ := hsource t htW
        exact ⟨rho, hrho, xi, hxi, by ring⟩
    · exact oneSeparated_image_add
        (oneSeparated_subset hsep (Finset.filter_subset _ _)) T
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      have htW : t ∈ Wraw := (Finset.mem_filter.mp ht).1
      have ht0 : t ≤ 0 := (Finset.mem_filter.mp ht).2
      have htneg : -T ≤ t := (abs_le.mp (hheight t htW)).1
      constructor <;> linarith
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      rw [dirichletPolynomial_shellNormalizedCoefficient
        (translatedCoefficient braw T) D hscale]
      rw [dirichletPolynomial_translatedCoefficient]
      exact mul_le_mul_of_nonneg_left
        (hlarge t (Finset.mem_filter.mp ht).1) hscale
    · rw [show W.card = Wneg.card by exact card_image_add Wneg T]
      omega

/-- Adapter from the exact Fourier-selection producer, with endpoint collar,
to the compact recentered zero-image provenance. -/
theorem exists_typeI_commonPolynomial_with_zero_provenance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U Ncut : ℕ} (hU : 1 ≤ U) (Y sigma scale : ℝ)
    (hscale : 0 ≤ scale)
    (j : Fin (detectorDyadicCount Ncut))
    (S : Finset ℂ) (weight : ℂ → ℕ) {H A V T : ℝ} {C M : ℕ}
    (hC : 2 * Real.pi * H ≤ C)
    (hheight : ∀ rho ∈ S, |rho.im| ≤ T)
    (hA : 0 < A) (hV : 0 < V)
    (hmass : ∀ rho ∈ endpointInterior S T C,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff
          (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ∀ rho ∈ endpointInterior S T C,
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U Ncut Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V / (detectorDyadicCount Ncut : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount Ncut *
        ‖arithmeticDetectorDyadicBlock chi U Ncut rho Y j‖)
    (hsource : ∀ m : ℤ,
      ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) :
    ∃ (braw : ℕ → ℂ) (W : Finset ℝ),
      IsLiteralRecenteredDetectorPair chi U Ncut Y sigma (2 ^ (j : ℕ))
        scale T H S braw W ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        scale * (V / (4 * A * detectorDyadicCount Ncut)) ≤
          ‖dirichletPolynomial braw (2 ^ (j : ℕ)) t‖) ∧
      ∑ rho ∈ S, weight rho ≤
        4 * (shiftedFloorWindowCount C * M) * W.card +
          2 * (C + 1) * M := by
  classical
  let Sint := endpointInterior S T C
  have hSintHeight : ∀ rho ∈ Sint, |rho.im| + C ≤ T := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  have hSintSource : ∀ m : ℤ,
      ∑ rho ∈ Sint with Int.floor rho.im = m, weight rho ≤ M := by
    intro m
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hsource m)
    · intro rho hrho
      have hrho' := Finset.mem_filter.mp hrho
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hrho'.1).1, hrho'.2⟩
    · intro rho hrho hrhoNot
      exact Nat.zero_le _
  obtain ⟨xi, Wraw, hxi, hWsub, hWsep, hWlarge, hWweight⟩ :=
    exists_typeI_commonPolynomial_oneSeparated
      chi hU Y sigma j Sint weight hC hA hV hmass htail
        (fun rho hrho => hblock rho (Finset.filter_subset _ _ hrho))
        hSintSource
  have hWheight : ∀ t ∈ Wraw, |t| ≤ T := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp (hWsub ht)
    have hxiAbs : |xi rho| ≤ H := abs_le.mpr (hxi rho hrho).1
    have hshift : |2 * Real.pi * xi rho| ≤ C := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
      exact (mul_le_mul_of_nonneg_left hxiAbs (by positivity)).trans hC
    calc
      |-rho.im + 2 * Real.pi * xi rho| ≤
          |rho.im| + |2 * Real.pi * xi rho| := by
        simpa [abs_neg] using abs_add_le (-rho.im) (2 * Real.pi * xi rho)
      _ ≤ |rho.im| + C := by gcongr
      _ ≤ T := hSintHeight rho hrho
  have hWsource : ∀ t ∈ Wraw,
      ∃ rho ∈ S, ∃ x ∈ Set.Icc (-H) H,
        t = -rho.im + 2 * Real.pi * x := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp (hWsub ht)
    exact ⟨rho, Finset.filter_subset _ _ hrho, xi rho, (hxi rho hrho).1, rfl⟩
  obtain ⟨b, W, hpair, hWsep', hWheight', hWlarge', hWcard⟩ :=
    exists_nonnegative_recentered_largeValueSet_with_zero_provenance
      chi U Ncut Y sigma (2 ^ (j : ℕ)) scale S H
      (detectorCommonCoefficient chi U Ncut Y sigma) Wraw rfl hWsource
      hWsep hscale hWheight hWlarge
  refine ⟨b, W, hpair, hWsep', hWheight', hWlarge', ?_⟩
  · have hcollar := sum_endpointCollar_weight_le S weight C M hheight hsource
    have hpartition :
        (∑ rho ∈ S, weight rho) =
          (∑ rho ∈ endpointInterior S T C, weight rho) +
            ∑ rho ∈ endpointCollar S T C, weight rho := by
      rw [← Finset.sum_union (disjoint_endpointInterior_endpointCollar S T C)]
      rw [endpointInterior_union_endpointCollar]
    rw [hpartition]
    exact Nat.add_le_add (hWweight.trans (by
      calc
        2 * (shiftedFloorWindowCount C * M) * Wraw.card ≤
            2 * (shiftedFloorWindowCount C * M) * (2 * W.card) := by gcongr
        _ = 4 * (shiftedFloorWindowCount C * M) * W.card := by ring))
      hcollar

/-- Exact normalization adapter for a nonempty positive selected Type-I
block.  This is the point where `U < 2 * D` is proved, rather than included
as a free hypothesis. -/
theorem exists_literalNormalizedTypeIWitness_of_positiveSelectedBlock
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U : ℕ} (hU : 1 ≤ U) (Y R sigma Kd e : ℝ)
    (j : Fin (detectorDyadicCount (detectorArithmeticCutoff Y R)))
    (S : Finset ℂ) (hS : S.Nonempty) (weight : ℂ → ℕ)
    {H A V T : ℝ} {C M : ℕ}
    (hC : 2 * Real.pi * H ≤ C)
    (hheight : ∀ rho ∈ S, |rho.im| ≤ T)
    (hA : 0 < A) (hV : 0 < V) (hY : 0 < Y)
    (hsigma : 0 ≤ sigma) (hKd : 0 < Kd) (he : 0 ≤ e)
    (hmass : ∀ rho ∈ endpointInterior S T C,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff
          (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ∀ rho ∈ endpointInterior S T C,
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U
            (detectorArithmeticCutoff Y R) Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V / (detectorDyadicCount
            (detectorArithmeticCutoff Y R) : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount (detectorArithmeticCutoff Y R) *
        ‖arithmeticDetectorDyadicBlock chi U
          (detectorArithmeticCutoff Y R) rho Y j‖)
    (hdiv : ∀ n : ℕ, 0 < n →
      (orderedDivisorCount 2 n : ℝ) ≤ Kd * Real.rpow n e)
    (hsource : ∀ m : ℤ,
      ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) :
    ∃ (b : ℕ → ℂ) (W : Finset ℝ),
      IsLiteralNormalizedTypeIWitness chi U Y R sigma Kd e T H
        (2 ^ (j : ℕ)) S b W ∧
      (∀ n, ‖b n‖ ≤ 1) ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        literalTypeIScale (2 ^ (j : ℕ)) sigma Kd e *
            (V / (4 * A * detectorDyadicCount
              (detectorArithmeticCutoff Y R))) ≤
          ‖dirichletPolynomial b (2 ^ (j : ℕ)) t‖) ∧
      ∑ rho ∈ S, weight rho ≤
        4 * (shiftedFloorWindowCount C * M) * W.card +
          2 * (C + 1) * M := by
  let D : ℕ := 2 ^ (j : ℕ)
  let scale : ℝ := literalTypeIScale D sigma Kd e
  have hD : 1 ≤ D := by
    dsimp [D]
    exact Nat.one_le_two_pow
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hLpos : 0 < Real.rpow D (-sigma) *
      (Kd * Real.rpow (2 * D) e) := by
    exact mul_pos (Real.rpow_pos_of_pos hDpos _)
      (mul_pos hKd (Real.rpow_pos_of_pos (by positivity) _))
  have hscale : 0 ≤ scale := by
    dsimp [scale, literalTypeIScale]
    exact inv_nonneg.mpr hLpos.le
  obtain ⟨b, W, hpair, hWsep, hWheight, hWlarge, hcard⟩ :=
    exists_typeI_commonPolynomial_with_zero_provenance
      chi hU Y sigma scale hscale j S weight hC hheight hA hV hmass
        htail hblock hsource
  have hUD : U < 2 * D := by
    obtain ⟨rho, hrho⟩ := hS
    exact mollifier_lt_two_pow_of_positive_selected_block
      chi hU hV rho Y j (hblock rho hrho)
  have hb : ∀ n, ‖b n‖ ≤ 1 := by
    have hbase : ∀ n ∈ Finset.Ioc D (2 * D),
        ‖detectorCommonCoefficient chi U
          (detectorArithmeticCutoff Y R) Y sigma n‖ ≤
          Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e) := by
      exact detectorCommonCoefficient_shell_bound chi hY hD hsigma he hKd.le
        hdiv
    rcases hpair with hpair | hpair
    · rw [hpair.1]
      apply norm_shellNormalizedCoefficient_le_one
        (detectorCommonCoefficient chi U
          (detectorArithmeticCutoff Y R) Y sigma)
        hscale hLpos.le
      · exact (inv_mul_cancel₀ hLpos.ne').le
      · exact hbase
    · rw [hpair.1]
      intro n
      rw [norm_translatedCoefficient]
      apply norm_shellNormalizedCoefficient_le_one
        (detectorCommonCoefficient chi U
          (detectorArithmeticCutoff Y R) Y sigma)
        hscale hLpos.le
      · exact (inv_mul_cancel₀ hLpos.ne').le
      · exact hbase
  refine ⟨b, W, ⟨hUD, ?_⟩, hb, hWsep, hWheight, ?_, hcard⟩
  · simpa [D, scale] using hpair
  · simpa [D, scale] using hWlarge

end
end CGLDetectorSourceFaithfulLargeValue

#print axioms CGLDetectorSourceFaithfulLargeValue.projectScaleSourceFaithful_of_uniform
#print axioms CGLDetectorSourceFaithfulLargeValue.projectScaleLiteralTypeIWitness_of_literalData
#print axioms CGLDetectorSourceFaithfulLargeValue.exists_nonnegative_recentered_largeValueSet_with_zero_provenance
#print axioms CGLDetectorSourceFaithfulLargeValue.exists_typeI_commonPolynomial_with_zero_provenance
#print axioms CGLDetectorSourceFaithfulLargeValue.exists_literalNormalizedTypeIWitness_of_positiveSelectedBlock
