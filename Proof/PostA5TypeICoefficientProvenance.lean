import PostA5HighStripSplitAssembly

/-!
# Preserve the literal Type-I detector coefficient

The canonical recentering theorem intentionally exports only equality of
coefficient norms.  That is enough for an arbitrary-coefficient large-values
theorem, but it erases information that may permit a weaker MAP-specific
analytic input.  This module proves a source-faithful variant which records
that recentering makes exactly one binary choice: the coefficient is either
unchanged or multiplied by the single translation phase `n^(-iT)`.
-/

namespace PostA5TypeICoefficientProvenance

open scoped BigOperators FourierTransform
open CGLProofDAG MAPAppendixA4PostA5SetAdapter SchwartzMap
open DirichletZeros MAPAppendixA4DetectorDichotomy
open MAPAppendixA4RecenteredGammaRepair PostA5RecenteredSourceSplit
open PostA5RecenteredTypeIExtractor PostA5TypeIIFourthMoment
open PostA5LongSpacingAssembly PostA5CrowdingDeterministic
open PostA5TypeIFourierAssembly PostA5TypeIOrdinateRecentering
open PostA5HighStripSplitAssembly

noncomputable section

/-- The literal normalized detector coefficient that enters the large-value
step, before the optional sign-recentering modulation. -/
def normalizedDetectorCoefficient
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U Ncut : ℕ) (Y sigma : ℝ) (D : ℕ) (scale : ℝ) : ℕ → ℂ :=
  shellNormalizedCoefficient
    (detectorCommonCoefficient chi U Ncut Y sigma) D scale

/-- Exact two-point provenance class retained by the Type-I detector. -/
def IsNormalizedDetectorCoefficient
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U Ncut : ℕ) (Y sigma : ℝ) (D : ℕ) (scale T : ℝ)
    (b : ℕ → ℂ) : Prop :=
  b = normalizedDetectorCoefficient chi U Ncut Y sigma D scale ∨
  b = translatedCoefficient
    (normalizedDetectorCoefficient chi U Ncut Y sigma D scale) T

/-- Shell normalization commutes exactly with the one global translation
phase introduced by recentering. -/
theorem shellNormalizedCoefficient_translatedCoefficient
    (b : ℕ → ℂ) (D : ℕ) (scale c : ℝ) :
    shellNormalizedCoefficient (translatedCoefficient b c) D scale =
      translatedCoefficient (shellNormalizedCoefficient b D scale) c := by
  funext n
  unfold shellNormalizedCoefficient translatedCoefficient
  by_cases hn : n ∈ Finset.Ioc D (2 * D)
  · simp only [if_pos hn]
    ring
  · simp only [if_neg hn, zero_mul]

/-- Normalizing a coefficient with the exact recentering provenance yields
the two-point normalized detector provenance class. -/
theorem isNormalizedDetectorCoefficient_of_recentered
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U Ncut : ℕ) (Y sigma : ℝ) (D : ℕ) (scale T : ℝ)
    {braw : ℕ → ℂ}
    (hbraw :
      braw = detectorCommonCoefficient chi U Ncut Y sigma ∨
      braw = translatedCoefficient
        (detectorCommonCoefficient chi U Ncut Y sigma) T) :
    IsNormalizedDetectorCoefficient chi U Ncut Y sigma D scale T
      (shellNormalizedCoefficient braw D scale) := by
  rcases hbraw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (shellNormalizedCoefficient_translatedCoefficient
      (detectorCommonCoefficient chi U Ncut Y sigma) D scale T)

/-- Exact coefficient provenance for sign recentering.  In particular, the
output is not an arbitrary coefficient sequence with the same norms. -/
theorem exists_nonnegative_recentered_largeValueSet_with_provenance
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T V : ℝ}
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) :
    ∃ (b' : ℕ → ℂ) (W' : Finset ℝ),
      (b' = b ∨ b' = translatedCoefficient b T) ∧
      OneSeparated W' ∧
      (∀ t ∈ W', 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W', V ≤ ‖dirichletPolynomial b' N t‖) ∧
      W.card ≤ 2 * W'.card := by
  classical
  let Wneg := nonpositivePart W
  let Wpos := nonnegativePart W
  have hcard : W.card ≤ Wneg.card + Wpos.card := by
    simpa [Wneg, Wpos] using card_le_sign_parts W
  by_cases hchoice : Wneg.card ≤ Wpos.card
  · refine ⟨b, Wpos, Or.inl rfl, ?_, ?_, ?_, ?_⟩
    · exact oneSeparated_subset hsep (Finset.filter_subset _ _)
    · intro t ht
      have htW : t ∈ W := (Finset.mem_filter.mp ht).1
      have h0t : 0 ≤ t := (Finset.mem_filter.mp ht).2
      exact ⟨h0t, (abs_le.mp (hheight t htW)).2⟩
    · intro t ht
      exact hlarge t (Finset.mem_filter.mp ht).1
    · omega
  · let b' := translatedCoefficient b T
    let W' := Wneg.image fun t => t + T
    refine ⟨b', W', Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · exact oneSeparated_image_add
        (oneSeparated_subset hsep (Finset.filter_subset _ _)) T
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      have htW : t ∈ W := (Finset.mem_filter.mp ht).1
      have ht0 : t ≤ 0 := (Finset.mem_filter.mp ht).2
      have htneg : -T ≤ t := (abs_le.mp (hheight t htW)).1
      constructor <;> linarith
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      rw [dirichletPolynomial_translatedCoefficient]
      exact hlarge t (Finset.mem_filter.mp ht).1
    · rw [show W'.card = Wneg.card by exact card_image_add Wneg T]
      omega

/-- The complete Fourier-selection, collar, and sign-recentering theorem with
the detector coefficient retained exactly.  The only possible output
coefficients are the common detector coefficient itself and its one global
translation modulation. -/
theorem exists_typeI_commonPolynomial_recentered_with_collar_provenance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N))
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
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V / (detectorDyadicCount N : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount N *
        ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖)
    (hsource : ∀ m : ℤ,
      ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) :
    ∃ (b : ℕ → ℂ) (W : Finset ℝ),
      (b = detectorCommonCoefficient chi U N Y sigma ∨
        b = translatedCoefficient
          (detectorCommonCoefficient chi U N Y sigma) T) ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        V / (4 * A * detectorDyadicCount N) ≤
          ‖dirichletPolynomial b (2 ^ (j : ℕ)) t‖) ∧
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
    have hxlo : -H ≤ xi rho := (hxi rho hrho).1.1
    have hxhi : xi rho ≤ H := (hxi rho hrho).1.2
    have hxiAbs : |xi rho| ≤ H := (abs_le).2 ⟨hxlo, hxhi⟩
    have hshift : |2 * Real.pi * xi rho| ≤ C := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
      exact (mul_le_mul_of_nonneg_left hxiAbs (by positivity)).trans hC
    calc
      |-rho.im + 2 * Real.pi * xi rho| ≤
          |rho.im| + |2 * Real.pi * xi rho| := by
        simpa [abs_neg] using abs_add_le (-rho.im) (2 * Real.pi * xi rho)
      _ ≤ |rho.im| + C := by gcongr
      _ ≤ T := hSintHeight rho hrho
  obtain ⟨b, W, hb, hWsep', hWheight', hWlarge', hWcard⟩ :=
    exists_nonnegative_recentered_largeValueSet_with_provenance
      (detectorCommonCoefficient chi U N Y sigma)
      (2 ^ (j : ℕ)) Wraw hWsep hWheight hWlarge
  refine ⟨b, W, hb, hWsep', hWheight', hWlarge', ?_⟩
  have hcollar := sum_endpointCollar_weight_le S weight C M hheight hsource
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

/-! ## Provenance-preserving finite high-strip split -/

/-- Exact finite A.4/A.5 two-branch weld with the literal Type-I coefficient
retained in the output.  This is the source-faithful strengthening of
`PostA5HighStripSplitAssembly.finite_highStrip_split_witness`: the numerical
conclusion is identical, and the final existential records that `b` is the
normalized detector coefficient or its single global recentering modulation.

The Type-II input is still only the fourth moment of the actual shifted
ordinate image.  No arbitrary-coefficient large-values theorem is used here. -/
theorem finite_highStrip_structured_split_witness
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {kappaDet etaDet kappaOut etaOut e h T sigma Y R V Kd Mfourth AZI AZII : ℝ}
    {U P C : ℕ} (Z0 : Finset ℂ)
    (hT : 4 ≤ T) (hY : 1 ≤ Y) (hR : 0 < R)
    (hU : 1 ≤ U) (hV : 0 < V) (he : 0 < e) (hKd : 0 < Kd)
    (hkappaDet : 0 < kappaDet) (hetaDet : 0 < etaDet)
    (hkappaOut : 0 < kappaOut) (hetaOut : 0 < etaOut) (hh : 0 < h)
    (hzero : ∀ rho ∈ Z0, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z0, sigma ≤ rho.re)
    (hbetaSeven : 7 / 10 ≤ sigma) (hbetaFour : sigma ≤ 4 / 5)
    (hbetaHigh : ∀ rho ∈ Z0, rho.re ≤ 1)
    (hheight : ∀ rho ∈ Z0, |rho.im| ≤ T)
    (hsep : ∀ rho ∈ Z0, ∀ rho' ∈ Z0, rho ≠ rho' →
      3 * detectorVerticalCutoff R ≤ |rho.im - rho'.im|)
    (hcountThin : dirichletZeroCount chi sigma T ≤ P * Z0.card)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z0,
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + V + V ≤
        Real.exp (-(1 / Y)))
    (hVR : V = Real.rpow R (-inputLoss kappaDet etaDet))
    (hVlower : Real.rpow T (-inputLoss kappaDet etaDet) ≤ V)
    (hDtime : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)), ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T)
    (hJtime : (detectorDyadicCount
      (detectorArithmeticCutoff Y R) : ℝ) ≤ 2 * T)
    (hC : 2 * Real.pi * Real.rpow T h ≤ C)
    (htail : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (rho : ℂ),
      sigma ≤ rho.re → rho.re ≤ 1 →
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U
            (detectorArithmeticCutoff Y R) Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        (V / (detectorDyadicCount
          (detectorArithmeticCutoff Y R) : ℝ)) / 2)
    (hdiv : ∀ n : ℕ, 0 < n →
      (orderedDivisorCount 2 n : ℝ) ≤ Kd * Real.rpow n e)
    (hUoutLow : Real.rpow T kappaOut ≤ U)
    (hUoutHigh : (U : ℝ) ≤
      Real.rpow T (1 / 2) * (Real.log T) ^ 2)
    (hNlow : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (rho : ℂ),
      rho ∈ Z0 →
      V ≤ (detectorDyadicCount (detectorArithmeticCutoff Y R) : ℝ) *
        ‖arithmeticDetectorDyadicBlock chi U
          (detectorArithmeticCutoff Y R) rho Y j‖ →
      Real.rpow T kappaOut ≤ (2 ^ (j : ℕ) : ℕ))
    (hNhigh : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)),
      ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤
        Real.rpow T (1 / 2) * (Real.log T) ^ 2)
    (hthreshold : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)),
      let D : ℕ := 2 ^ (j : ℕ)
      let L : ℝ := Real.rpow D (-sigma) *
        (Kd * Real.rpow (2 * D) e)
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
        L⁻¹ * (V /
          (4 * (24 * Real.rpow T h) *
            detectorDyadicCount (detectorArithmeticCutoff Y R))))
    (hmoment : ∀ (shift : ℂ → ℝ) (SII : Finset ℂ),
      SII ⊆ postA5SourceTypeIISet chi U Y R V Z0 →
      (∀ rho ∈ SII,
        shift rho ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R)) →
      (∑ t ∈ SII.image (fun rho => rho.im + shift rho),
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤ Mfourth)
    (hZIledger : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (W : Finset ℝ),
      ((P * detectorDyadicCount (detectorArithmeticCutoff Y R) *
        (4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1) : ℕ) : ℝ) ≤
        AZI * Real.rpow T etaOut * (1 + (W.card : ℝ)))
    (hZIIledger : (P : ℝ) *
      (Mfourth /
        (V / (29 * Real.rpow Y (1 / 2 - sigma) *
          (2 * Real.sqrt U))) ^ 4) ≤
      AZII * Real.rpow T
        (2 * (1 - sigma) + 2 * kappaOut + etaOut)) :
    ∃ (Nout : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ),
      Real.rpow T kappaOut ≤ Nout ∧
      (Nout : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
      (∀ n, ‖b n‖ ≤ 1) ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        Real.rpow Nout sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
          ‖dirichletPolynomial b Nout t‖) ∧
      dirichletZeroCount chi sigma T ≤ ZI + ZII ∧
      (ZI : ℝ) ≤ AZI * Real.rpow T etaOut * (1 + (W.card : ℝ)) ∧
      (ZII : ℝ) ≤ AZII * Real.rpow T
        (2 * (1 - sigma) + 2 * kappaOut + etaOut) ∧
      ∃ (Uout NcutOut : ℕ) (Yout scaleOut : ℝ),
        IsNormalizedDetectorCoefficient chi Uout NcutOut Yout sigma
          Nout scaleOut T b := by
  classical
  let Ncut := detectorArithmeticCutoff Y R
  let ZIset := postA5TypeISet chi U Y R V Z0
  let ZIIset := postA5SourceTypeIISet chi U Y R V Z0
  have hbudget' : ∀ rho ∈ Z0,
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R +
          Real.rpow R (-inputLoss kappaDet etaDet) +
          Real.rpow R (-inputLoss kappaDet etaDet) ≤
        Real.exp (-(1 / Y)) := by
    intro rho hrho
    rw [← hVR]
    exact hbudget rho hrho
  have hbetaLow' : ∀ rho ∈ Z0, 7 / 10 ≤ rho.re := by
    intro rho hrho
    exact hbetaSeven.trans (hbetaLow rho hrho)
  obtain ⟨j, S1, hS1, hcardI, hblock, hcardSplit⟩ :=
    post_A5_budgeted_zeroSet_common_dyadic_or_sourceTypeII_polynomial_height
      chi hchi hkappaDet hetaDet hU hY hR hzero hbetaLow' hbetaHigh hUN hB hbudget'
  have hS1Z0 : S1 ⊆ Z0 := by
    intro rho hrho
    have hziset : rho ∈ postA5TypeISet chi U Y R
        (Real.rpow R (-inputLoss kappaDet etaDet)) Z0 := hS1 hrho
    exact (Finset.mem_filter.mp hziset).1
  have hS1source : ∀ m : ℤ,
      ∑ rho ∈ S1 with Int.floor rho.im = m, (1 : ℕ) ≤ 1 := by
    intro m
    simp only [Finset.sum_const, Nat.smul_one_eq_cast]
    exact floorBin_card_le_one_of_threeSeparated S1 hB
      (fun rho hrho rho' hrho' hne =>
        hsep rho (hS1Z0 hrho) rho' (hS1Z0 hrho') hne) m
  have hD : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
  have hmass : ∀ rho ∈ endpointInterior S1 T C,
      (∫ xi in Set.Icc (-(Real.rpow T h)) (Real.rpow T h),
        ‖((𝓕 (detectorRealPartCutoff
          (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        24 * Real.rpow T h := by
    intro rho hrho
    have hrhoS : rho ∈ S1 := Finset.filter_subset _ _ hrho
    have hrhoZ : rho ∈ Z0 := hS1Z0 hrhoS
    apply integral_norm_fourier_detectorRealPartCutoff_Icc_le hD
    · exact sub_nonneg.mpr (hbetaLow rho hrhoZ)
    · linarith [hbetaHigh rho hrhoZ]
    · exact Real.rpow_nonneg (by linarith : 0 ≤ T) _
  obtain ⟨braw, W, hbraw, hWsep, hWheight, hWlarge, hS1card⟩ :=
    exists_typeI_commonPolynomial_recentered_with_collar_provenance
      chi hU Y sigma j S1 (fun _ => 1) hC
      (fun rho hrho => hheight rho (hS1Z0 hrho))
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)) hV
      hmass
      (fun rho hrho => htail j rho
        (hbetaLow rho (hS1Z0 (Finset.filter_subset _ _ hrho)))
        (hbetaHigh rho (hS1Z0 (Finset.filter_subset _ _ hrho))))
      (fun rho hrho => by
        rw [hVR]
        exact hblock rho hrho)
      hS1source
  let D : ℕ := 2 ^ (j : ℕ)
  let L : ℝ := Real.rpow D (-sigma) *
    (Kd * Real.rpow (2 * D) e)
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos (Real.rpow_pos_of_pos hDpos _)
      (mul_pos hKd (Real.rpow_pos_of_pos (by positivity) _))
  let scale : ℝ := L⁻¹
  have hscale : 0 ≤ scale := inv_nonneg.mpr hLpos.le
  have hscaleL : scale * L ≤ 1 := by
    dsimp [scale]
    rw [inv_mul_cancel₀ hLpos.ne']
  let b : ℕ → ℂ := shellNormalizedCoefficient braw D scale
  have hbrawNorm : ∀ n,
      ‖braw n‖ = ‖detectorCommonCoefficient chi U Ncut Y sigma n‖ := by
    intro n
    rcases hbraw with hbraw | hbraw
    · rw [hbraw]
    · rw [hbraw, norm_translatedCoefficient]
  have hb : ∀ n, ‖b n‖ ≤ 1 := by
    apply norm_shellNormalizedCoefficient_le_one braw hscale hLpos.le hscaleL
    intro n hn
    rw [hbrawNorm n]
    dsimp [L, D, Ncut]
    exact detectorCommonCoefficient_shell_bound chi (by linarith) hD
      (by linarith) he.le hKd.le hdiv n hn
  have hprovenance :
      IsNormalizedDetectorCoefficient chi U Ncut Y sigma D scale T b := by
    exact isNormalizedDetectorCoefficient_of_recentered
      chi U Ncut Y sigma D scale T hbraw
  have hWlarge' : ∀ t ∈ W,
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
        ‖dirichletPolynomial b D t‖ := by
    intro t ht
    calc
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
          scale * (V / (4 * (24 * Real.rpow T h) *
            detectorDyadicCount (detectorArithmeticCutoff Y R))) := by
        simpa [D, L, scale] using hthreshold j
      _ ≤ scale * ‖dirichletPolynomial braw D t‖ := by
        exact mul_le_mul_of_nonneg_left (by simpa [D] using hWlarge t ht) hscale
      _ = ‖dirichletPolynomial b D t‖ := by
        symm
        exact dirichletPolynomial_shellNormalizedCoefficient braw D hscale t
  have hZIIsetSub : ZIIset ⊆
      postA5SourceTypeIISet chi U Y R V Z0 := by
    intro rho hrho
    simpa [ZIIset] using hrho
  obtain ⟨shift, hshiftChoice⟩ :=
    exists_sourceTypeII_shift_assignment chi hZIIsetSub
  have hshiftAbs : ∀ rho ∈ ZIIset,
      |shift rho| ≤ detectorVerticalCutoff R := by
    intro rho hrho
    exact abs_le.mpr (hshiftChoice rho hrho).1
  have hZIIbeta : ∀ rho ∈ ZIIset, sigma ≤ rho.re := by
    intro rho hrho
    have hrhoZ : rho ∈ Z0 := by
      have hz := (mem_postA5SourceTypeIISet_iff chi U Y R V Z0 rho).mp
        (hZIIsetSub hrho)
      exact hz.1
    exact hbetaLow rho hrhoZ
  have hZIIsep : ∀ rho ∈ ZIIset, ∀ rho' ∈ ZIIset, rho ≠ rho' →
      3 * detectorVerticalCutoff R ≤ |rho.im - rho'.im| := by
    intro rho hrho rho' hrho' hne
    apply hsep rho
    · exact (mem_postA5SourceTypeIISet_iff chi U Y R V Z0 rho).mp
        (hZIIsetSub hrho) |>.1
    · exact (mem_postA5SourceTypeIISet_iff chi U Y R V Z0 rho').mp
        (hZIIsetSub hrho') |>.1
    · exact hne
  have hmoment' := hmoment shift ZIIset hZIIsetSub
    (fun rho hrho => (hshiftChoice rho hrho).1)
  have hZIIcard : (ZIIset.card : ℝ) ≤
      Mfourth / (V / (29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U))) ^ 4 :=
    typeII_card_le_of_shifted_fourthMoment chi ZIIset shift hB hU hY hV
      hshiftAbs hZIIsep hZIIbeta
      (fun rho hrho => (hshiftChoice rho hrho).2) hmoment'
  let typeICost : ℕ :=
    4 * (shiftedFloorWindowCount C * 1) * W.card + 2 * (C + 1) * 1
  let ZIout : ℕ :=
    P * detectorDyadicCount (detectorArithmeticCutoff Y R) * typeICost
  let ZIIout : ℕ := P * ZIIset.card
  have hS1card' : S1.card ≤ typeICost := by
    simpa [typeICost] using hS1card
  have hcardI' : ZIset.card ≤
      detectorDyadicCount (detectorArithmeticCutoff Y R) * S1.card := by
    dsimp [ZIset]
    rw [hVR]
    exact hcardI
  have hcardSplit' : Z0.card ≤ ZIset.card + ZIIset.card := by
    dsimp [ZIset, ZIIset]
    rw [hVR]
    exact hcardSplit
  have hcount : dirichletZeroCount chi sigma T ≤ ZIout + ZIIout := by
    calc
      dirichletZeroCount chi sigma T ≤ P * Z0.card := hcountThin
      _ ≤ P * (ZIset.card + ZIIset.card) :=
        Nat.mul_le_mul_left P hcardSplit'
      _ ≤ P *
          (detectorDyadicCount (detectorArithmeticCutoff Y R) * S1.card +
            ZIIset.card) := by
        exact Nat.mul_le_mul_left P (Nat.add_le_add_right hcardI' _)
      _ ≤ P *
          (detectorDyadicCount (detectorArithmeticCutoff Y R) * typeICost +
            ZIIset.card) := by
        gcongr
      _ = ZIout + ZIIout := by
        dsimp [ZIout, ZIIout]
        ring
  have hZIIoutBound : (ZIIout : ℝ) ≤ AZII * Real.rpow T
      (2 * (1 - sigma) + 2 * kappaOut + etaOut) := by
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    dsimp [ZIIout]
    push_cast
    exact (mul_le_mul_of_nonneg_left hZIIcard hP0).trans hZIIledger
  by_cases hS1ne : S1.Nonempty
  · obtain ⟨rho, hrho⟩ := hS1ne
    refine ⟨D, b, W, ZIout, ZIIout, ?_, ?_, hb, hWsep, hWheight,
      hWlarge', hcount, ?_, hZIIoutBound, U, Ncut, Y, scale, hprovenance⟩
    · simpa [D] using hNlow j rho (hS1Z0 hrho) (by
        rw [hVR]
        exact hblock rho hrho)
    · simpa [D] using hNhigh j
    · simpa [ZIout, typeICost] using hZIledger j W
  · have hS1empty : S1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS1ne
    have hZIempty : ZIset.card = 0 := by
      have hcardI'' := hcardI'
      rw [hS1empty] at hcardI''
      simp only [Finset.card_empty, mul_zero] at hcardI''
      omega
    have hZ0toII : Z0.card ≤ ZIIset.card := by
      rw [hZIempty, zero_add] at hcardSplit'
      exact hcardSplit'
    have hcountEmpty : dirichletZeroCount chi sigma T ≤ ZIIout := by
      calc
        dirichletZeroCount chi sigma T ≤ P * Z0.card := hcountThin
        _ ≤ P * ZIIset.card := Nat.mul_le_mul_left P hZ0toII
        _ = ZIIout := rfl
    let Lempty : ℝ := Real.rpow U (-sigma) *
      (Kd * Real.rpow (2 * U) e)
    have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
    have hLemptyPos : 0 < Lempty := by
      dsimp [Lempty]
      exact mul_pos (Real.rpow_pos_of_pos hUpos _)
        (mul_pos hKd (Real.rpow_pos_of_pos (by positivity) _))
    let scaleEmpty : ℝ := Lempty⁻¹
    have hscaleEmpty : 0 ≤ scaleEmpty := inv_nonneg.mpr hLemptyPos.le
    have hscaleEmptyL : scaleEmpty * Lempty ≤ 1 := by
      dsimp [scaleEmpty]
      rw [inv_mul_cancel₀ hLemptyPos.ne']
    let bEmpty : ℕ → ℂ := normalizedDetectorCoefficient
      chi U Ncut Y sigma U scaleEmpty
    have hbEmpty : ∀ n, ‖bEmpty n‖ ≤ 1 := by
      apply norm_shellNormalizedCoefficient_le_one
        (detectorCommonCoefficient chi U Ncut Y sigma)
        hscaleEmpty hLemptyPos.le hscaleEmptyL
      intro n hn
      dsimp [Lempty, Ncut]
      exact detectorCommonCoefficient_shell_bound chi (by linarith) hU
        (by linarith) he.le hKd.le hdiv n hn
    have hprovenanceEmpty :
        IsNormalizedDetectorCoefficient chi U Ncut Y sigma U scaleEmpty T
          bEmpty := Or.inl rfl
    refine ⟨U, bEmpty, ∅, 0, ZIIout, hUoutLow, hUoutHigh,
      hbEmpty, ?_, ?_, ?_, ?_, ?_, hZIIoutBound,
      U, Ncut, Y, scaleEmpty, hprovenanceEmpty⟩
    · intro t ht
      simp at ht
    · intro t ht
      simp at ht
    · intro t ht
      simp at ht
    · simpa using hcountEmpty
    · have hzeroLedger := hZIledger j (∅ : Finset ℝ)
      norm_num at hzeroLedger ⊢
      have hlhs : (0 : ℝ) ≤
          (P : ℝ) * detectorDyadicCount (detectorArithmeticCutoff Y R) *
            (2 * ((C : ℝ) + 1)) := by positivity
      exact hlhs.trans hzeroLedger

end
end PostA5TypeICoefficientProvenance

#print axioms PostA5TypeICoefficientProvenance.shellNormalizedCoefficient_translatedCoefficient
#print axioms PostA5TypeICoefficientProvenance.isNormalizedDetectorCoefficient_of_recentered
#print axioms PostA5TypeICoefficientProvenance.exists_nonnegative_recentered_largeValueSet_with_provenance
#print axioms PostA5TypeICoefficientProvenance.exists_typeI_commonPolynomial_recentered_with_collar_provenance
#print axioms PostA5TypeICoefficientProvenance.finite_highStrip_structured_split_witness
