import MAPDynamicHBPerronCellWeldV3

/-!
# The global Corollary 2.5 constant in the dynamic V3 packet source

MRT Corollary 2.5 quantifies its constant before every packet parameter.  The
older dynamic wrapper hid this by choosing an existential separately for each
packet.  This module checks that the actual certified constructor uses the
same global constant at every packet.
-/

namespace MAPDynamicHBCanonicalPerronConstantV3

open MAPMRTCorollary25 MAPMRTCorollary25Certified
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary25Instantiation MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1CoefficientBound MAPMRTCorollary25Minkowski
open MixedMeanFrontend
open MAPHBPerronSourceData MAPDynamicHBPacketPerronV3
open MAPFarAnnulusSourceToModel
open MAPDynamicHBPerronCellWeldV3 MAPDynamicHBScaledPacketSourceV3
open MAPMRTCorollary53Source
open MRTLemma215DynamicHighPacketIndexV3 MRTLemma215OpenIntervalCutoffV3

noncomputable section

def canonicalPerronKFour : ℝ :=
  Classical.choose (mrtCorollary25_certified (4 : ℝ) (by norm_num))

theorem canonicalPerronKFour_pos : 0 < canonicalPerronKFour :=
  (Classical.choose_spec
    (mrtCorollary25_certified (4 : ℝ) (by norm_num))).1

/-- Fixed-constant integrated cutoff transfer.  This is the literal proof
of the existing integrated weld with the globally quantified Corollary 2.5
constant supplied explicitly. -/
theorem literalTypeD1_component95_cutoff_transfer_fixed
    {Chi : Type*} [Fintype Chi]
    {N M T X1 X2 B U a b : ℝ}
    {alpha beta : ℕ → ℂ} {phase : Chi → ℕ → ℂ}
    (K : ℝ) (hK : 0 < K)
    (hcut : ∀ (X T X1 X2 t B : ℝ) (f : ℕ → ℂ),
      1 ≤ X → 1 ≤ T → 0 ≤ B →
      SupportedNear X 4 f →
      (∀ n : ℕ, ‖f n‖ ≤ B) →
      ‖halfLineDirichletPolynomial X 4 (intervalCutoff X1 X2 f) t‖ ≤
        K * ((∫ u in (-T)..T,
            ‖halfLineDirichletPolynomial X 4 f (t + u)‖ / (1 + |u|)) +
          B * Real.sqrt X * Real.log (2 + T) / T))
    (hN : 0 < N) (hM : 0 < M) (hNM : 1 ≤ N * M)
    (hT : 1 ≤ T) (hB : 0 ≤ B) (hU : 0 ≤ U) (hab : a ≤ b)
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    (hphase : ∀ chi n, ‖phase chi n‖ ≤ 1)
    (hcoeff : ∀ n, ‖literalDirichletConvolution alpha beta n‖ ≤ B) :
    (∫ t in a..b,
      (characterMovingMass
        (typeD1ClippedNorm N M X1 X2 phase alpha beta) U t) ^ 2) ≤
      2 * K ^ 2 *
        ((∫ u in (-T)..T, perronWeight u) ^ 2 *
            (∫ s in (a - T)..(b + T),
              (characterMovingMass
                (typeD1FullNorm N M phase alpha beta) U s) ^ 2) +
          (b - a) *
            (2 * U * (Fintype.card Chi : ℝ) *
              (B * Real.sqrt (N * M) * Real.log (2 + T) / T)) ^ 2) := by
  let clip : Chi → ℝ → ℝ :=
    typeD1ClippedNorm N M X1 X2 phase alpha beta
  let full : Chi → ℝ → ℝ :=
    typeD1FullNorm N M phase alpha beta
  let E₀ := B * Real.sqrt (N * M) * Real.log (2 + T) / T
  have hfullCont : ∀ chi, Continuous (full chi) := fun chi ↦
    continuous_typeD1FullNorm N M phase alpha beta chi
  have hclipCont : ∀ chi, Continuous (clip chi) := fun chi ↦
    continuous_typeD1ClippedNorm N M X1 X2 phase alpha beta chi
  have hfull0 : ∀ chi t, 0 ≤ full chi t := fun chi t ↦ norm_nonneg _
  have hclip0 : ∀ chi t, 0 ≤ clip chi t := fun chi t ↦ norm_nonneg _
  have hE₀ : 0 ≤ E₀ := by
    dsimp only [E₀]
    have hlog : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
    positivity
  have hsupp : SupportedNear (N * M) 4
      (literalDirichletConvolution alpha beta) :=
    supportedNear_four_literalDirichletConvolution hN hM halpha hbeta
  have hpoint : ∀ chi s,
      clip chi s ≤ K * (perronConvolution (full chi) T s + E₀) := by
    intro chi s
    have hc := hcut (N * M) T X1 X2 s B
      (characterTwist (phase chi) (literalDirichletConvolution alpha beta))
      hNM hT hB (supportedNear_characterTwist hsupp)
      (norm_characterTwist_le (hphase chi) hcoeff)
    have hconv : perronConvolution (full chi) T s =
        ∫ u in (-T)..T,
          ‖halfLineDirichletPolynomial (N * M) 4
            (characterTwist (phase chi)
              (literalDirichletConvolution alpha beta)) (s + u)‖ /
              (1 + |u|) := by
      unfold perronConvolution
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only [full, typeD1FullNorm]
      rw [perronWeight]
      ring
    rw [hconv]
    simpa only [clip, E₀, typeD1ClippedNorm] using hc
  simpa only [clip, full, E₀] using
    character_component_square_cutoff_transfer hclipCont hfullCont
      hclip0 hfull0 hab hU (lt_of_lt_of_le zero_lt_one hT)
      hK.le hE₀ hpoint

/-- The global certified `C=4` constant supplies the fixed transfer. -/
theorem literalTypeD1_component95_cutoff_transfer_canonical
    {Chi : Type*} [Fintype Chi]
    {N M T X1 X2 B U a b : ℝ}
    {alpha beta : ℕ → ℂ} {phase : Chi → ℕ → ℂ}
    (hN : 0 < N) (hM : 0 < M) (hNM : 1 ≤ N * M)
    (hT : 1 ≤ T) (hB : 0 ≤ B) (hU : 0 ≤ U) (hab : a ≤ b)
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    (hphase : ∀ chi n, ‖phase chi n‖ ≤ 1)
    (hcoeff : ∀ n, ‖literalDirichletConvolution alpha beta n‖ ≤ B) :
    (∫ t in a..b,
      (characterMovingMass
        (typeD1ClippedNorm N M X1 X2 phase alpha beta) U t) ^ 2) ≤
      2 * canonicalPerronKFour ^ 2 *
        ((∫ u in (-T)..T, perronWeight u) ^ 2 *
            (∫ s in (a - T)..(b + T),
              (characterMovingMass
                (typeD1FullNorm N M phase alpha beta) U s) ^ 2) +
          (b - a) *
            (2 * U * (Fintype.card Chi : ℝ) *
              (B * Real.sqrt (N * M) * Real.log (2 + T) / T)) ^ 2) := by
  exact literalTypeD1_component95_cutoff_transfer_fixed
    canonicalPerronKFour canonicalPerronKFour_pos
    (Classical.choose_spec
      (mrtCorollary25_certified (4 : ℝ) (by norm_num))).2
    hN hM hNM hT hB hU hab halpha hbeta hphase hcoeff


/-- Source-level padded-cell transfer with the same global Perron constant for
every packet. -/
theorem literalTypeD1_component95_to_paddedCell_canonical
    {q N M : ℕ} [NeZero q]
    {T X1 X2 B U a b : ℝ}
    {alpha beta : ℕ → ℂ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hT : 1 ≤ T) (hB : 0 ≤ B) (hU : 0 ≤ U) (hab : a ≤ b)
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (hcoeff : ∀ n, ‖literalDirichletConvolution alpha beta n‖ ≤ B) :
    (∫ t in a..b,
      (characterMovingMass
        (typeD1ClippedNorm (N : ℝ) (M : ℝ) X1 X2
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha beta) U t) ^ 2) ≤
      perronCellError q N M T B U a b canonicalPerronKFour +
        literalFactoredTypeDCell q M N
          (paddedCharacterTwist q q le_rfl beta)
          (scaleCoeffFamily (perronCellScale canonicalPerronKFour T)
            (paddedCharacterTwist q q le_rfl alpha))
          (a - T) (b + T) U := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNM : (1 : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast Nat.mul_le_mul hN hM
  have htransfer :=
    literalTypeD1_component95_cutoff_transfer_canonical
      (N := (N : ℝ)) (M := (M : ℝ)) (T := T)
      (X1 := X1) (X2 := X2) (B := B) (U := U) (a := a) (b := b)
      hNr hMr hNM hT hB hU hab
      (supportedDyadic_coe_of_supportedNatDyadic halpha)
      (supportedDyadic_coe_of_supportedNatDyadic hbeta)
      (fun (chi : DirichletCharacter ℂ q) n ↦
        DirichletCharacter.norm_le_one chi n) hcoeff
  let W : ℝ := ∫ u in (-T)..T, perronWeight u
  let E : ℝ :=
    2 * U * (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
      (B * Real.sqrt ((N : ℝ) * (M : ℝ)) * Real.log (2 + T) / T)
  let Ep : ℝ :=
    2 * U * q *
      (B * Real.sqrt ((N : ℝ) * (M : ℝ)) * Real.log (2 + T) / T)
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ q := by
    exact_mod_cast card_dirichletCharacters_le_modulus q
  have hbase :
      0 ≤ B * Real.sqrt ((N : ℝ) * (M : ℝ)) *
        Real.log (2 + T) / T := by
    have hlog : 0 ≤ Real.log (2 + T) :=
      Real.log_nonneg (by linarith)
    positivity
  have hE : 0 ≤ E := by unfold E; positivity
  have hEp : 0 ≤ Ep := by unfold Ep; positivity
  have hEEp : E ≤ Ep := by
    unfold E Ep
    gcongr
  have hW : 0 ≤ W := by
    unfold W
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu ↦ (perronWeight_pos u).le)
  have hc : 0 ≤ perronCellScale canonicalPerronKFour T := by
    unfold perronCellScale
    have hW' : 0 ≤ ∫ u in (-T)..T, perronWeight u := by
      simpa [W] using hW
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg 2) canonicalPerronKFour_pos.le) hW'
  have hfull :=
    integral_characterMovingMass_typeD1FullNorm_eq_literalFactoredCell
      (q := q) (N := N) (M := M)
      hN hM halpha hbeta (a - T) (b + T) U
  have hscale :=
    literalFactoredTypeDCell_scale_long hc
      (paddedCharacterTwist q q le_rfl beta)
      (paddedCharacterTwist q q le_rfl alpha)
      (q := q) (M := M) (N := N) (a := a - T) (b := b + T) (U := U)
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hscaleSq : perronCellScale canonicalPerronKFour T ^ 2 =
      2 * canonicalPerronKFour ^ 2 * W ^ 2 := by
    unfold perronCellScale
    change
      (Real.sqrt 2 * canonicalPerronKFour *
        (∫ u in (-T)..T, perronWeight u)) ^ 2 =
        2 * canonicalPerronKFour ^ 2 *
          (∫ u in (-T)..T, perronWeight u) ^ 2
    nlinarith
  rw [hfull] at htransfer
  rw [hscale]
  unfold perronCellError
  change _ ≤ 2 * canonicalPerronKFour ^ 2 * (b - a) * Ep ^ 2 +
    perronCellScale canonicalPerronKFour T ^ 2 *
      literalFactoredTypeDCell q M N
        (paddedCharacterTwist q q le_rfl beta)
        (paddedCharacterTwist q q le_rfl alpha) (a - T) (b + T) U
  rw [hscaleSq]
  have herr : E ^ 2 ≤ Ep ^ 2 := by nlinarith
  calc
    _ ≤ 2 * canonicalPerronKFour ^ 2 *
        (W ^ 2 *
          literalFactoredTypeDCell q M N
            (paddedCharacterTwist q q le_rfl beta)
            (paddedCharacterTwist q q le_rfl alpha)
            (a - T) (b + T) U +
          (b - a) * E ^ 2) := by
      simpa [W, E] using htransfer
    _ ≤ 2 * canonicalPerronKFour ^ 2 *
        (W ^ 2 *
          literalFactoredTypeDCell q M N
            (paddedCharacterTwist q q le_rfl beta)
            (paddedCharacterTwist q q le_rfl alpha)
            (a - T) (b + T) U +
          (b - a) * Ep ^ 2) := by
      gcongr
    _ = _ := by ring


/-- Corollary 2.5 applied to one dynamic packet with the same global constant
for all X, branches, and packets. -/
theorem dynamicPacketPerronTransferCanonicalV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
        (componentEndpoints p.X p.beta p.eta component).2,
      (characterMovingMass
        (typeD1ClippedNorm
          (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (openSourceLeft p.X) (2 * p.X)
          (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
          (scaledAllPacketLongCoeffV3 packet)
          (allPacketShortCoeffV3 packet))
        (stationaryWidth p.beta p.H) t) ^ 2) ≤
      perronCellError p.q
        (highPacketLongLengthV3 (allPacketGlobalV3 packet))
        (highPacketShortLengthV3 (allPacketGlobalV3 packet)) p.X
        (dynamicPacketConvolutionBoundV3 packet)
        (stationaryWidth p.beta p.H)
        (componentEndpoints p.X p.beta p.eta component).1
        (componentEndpoints p.X p.beta p.eta component).2
        canonicalPerronKFour +
      literalFactoredTypeDCell p.q
        (highPacketShortLengthV3 (allPacketGlobalV3 packet))
        (highPacketLongLengthV3 (allPacketGlobalV3 packet))
        (paddedCharacterTwist p.q p.q le_rfl
          (allPacketShortCoeffV3 packet))
        (scaleCoeffFamily (perronCellScale canonicalPerronKFour p.X)
          (paddedCharacterTwist p.q p.q le_rfl
            (scaledAllPacketLongCoeffV3 packet)))
        ((componentEndpoints p.X p.beta p.eta component).1 - p.X)
        ((componentEndpoints p.X p.beta p.eta component).2 + p.X)
        (stationaryWidth p.beta p.H) := by
  have hgeom := highPacket_geometryV3 (allPacketGlobalV3 packet)
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX0 : 0 ≤ p.X := by linarith
  exact literalTypeD1_component95_to_paddedCell_canonical
    (by omega : 1 ≤ highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (by omega : 1 ≤ highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (by linarith : 1 ≤ p.X)
    (dynamicPacketConvolutionBoundV3_nonneg packet)
    (by unfold stationaryWidth; positivity)
    (MAPMRTProposition51Source.componentEndpoints_mono
      (beta := p.beta) hX0 hp.2.2.2.2.1 hp.2.2.2.2.2.1 component)
    (scaledAllPacketLongSupportV3 packet)
    (allPacketShortSupportV3 packet)
    (dynamicPacketConvolutionBoundV3_bound packet)

end
end MAPDynamicHBCanonicalPerronConstantV3

#print axioms MAPDynamicHBCanonicalPerronConstantV3.literalTypeD1_component95_cutoff_transfer_canonical
#print axioms MAPDynamicHBCanonicalPerronConstantV3.literalTypeD1_component95_to_paddedCell_canonical
#print axioms MAPDynamicHBCanonicalPerronConstantV3.dynamicPacketPerronTransferCanonicalV3
