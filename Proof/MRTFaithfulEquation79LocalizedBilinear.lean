import MRTFaithfulEquation79Bilinear

/-!
# Restricting the faithful equation-(79) energy to the literal MRT region

The medium multiplier is supported on the two-component source region `I`.
This file uses that support, rather than enlarging to a global critical-line
weight, before the equation-(81) Schur step.
-/

namespace MAPMRTFaithfulEquation79LocalizedBilinear

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51Source
open MAPMRTProposition51HardBranch MAPMRTMediumEq79Parallel
open MAPMRTFaithfulSmoothCutoff MAPMRTEquation79PacketBilinearCore
open MAPMRTWholeLineEquation81FromEquation82
open MAPMRTFaithfulEquation79Bilinear
open MAPMRTEquation81Averaging MAPMRTEquation81AveragingBilinear
open MAPMRTFaithfulEquation81Weld

noncomputable section

/-- The critical polynomial norm restricted to the exact two-component
frequency region following source equation (79). -/
def sourceMaskedCriticalNormWeight
    (N : ℕ) (X beta eta : ℝ) (f : ℕ → ℂ) : ℝ → ENNReal :=
  (sourceFrequencyRegion X beta eta).indicator (criticalNormWeight N f)

/-- One component of the exact source-region mask. -/
def componentMaskedCriticalNormWeight
    (N : ℕ) (X beta eta : ℝ) (f : ℕ → ℂ)
    (component : OuterComponent) : ℝ → ENNReal :=
  let endpoints := componentEndpoints X beta eta component
  (Set.Icc endpoints.1 endpoints.2).indicator (criticalNormWeight N f)

theorem measurableSet_sourceFrequencyRegion (X beta eta : ℝ) :
    MeasurableSet (sourceFrequencyRegion X beta eta) := by
  unfold sourceFrequencyRegion
  exact (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

theorem measurable_sourceMaskedCriticalNormWeight
    (N : ℕ) (X beta eta : ℝ) (f : ℕ → ℂ) :
    Measurable (sourceMaskedCriticalNormWeight N X beta eta f) := by
  exact (measurable_criticalNormWeight N f).indicator
    (measurableSet_sourceFrequencyRegion X beta eta)

theorem measurable_componentMaskedCriticalNormWeight
    (N : ℕ) (X beta eta : ℝ) (f : ℕ → ℂ)
    (component : OuterComponent) :
    Measurable (componentMaskedCriticalNormWeight N X beta eta f component) := by
  exact (measurable_criticalNormWeight N f).indicator measurableSet_Icc

/-- Splitting the source region into its two signed components.  The inequality
form is robust at endpoints and is exactly what positive Tonelli needs. -/
theorem sourceMasked_le_signed_components
    {N : ℕ} {X beta eta t : ℝ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (heta : 0 < eta) :
    sourceMaskedCriticalNormWeight N X beta eta f t ≤
      componentMaskedCriticalNormWeight N X beta eta f .negative t +
      componentMaskedCriticalNormWeight N X beta eta f .positive t := by
  by_cases ht : t ∈ sourceFrequencyRegion X beta eta
  · have hbX : 0 ≤ |beta| * X := mul_nonneg (abs_nonneg _) hX
    have ha : 0 ≤ eta * |beta| * X := by positivity
    rcases le_total 0 t with ht0 | ht0
    · have habs : |t| = t := abs_of_nonneg ht0
      have hp : t ∈ Set.Icc (outerLower X beta eta) (outerUpper X beta eta) := by
        rw [mem_sourceFrequencyRegion_iff, habs] at ht
        simpa [outerLower, outerUpper] using ht
      simp [sourceMaskedCriticalNormWeight, componentMaskedCriticalNormWeight,
        componentEndpoints, ht, hp]
    · have habs : |t| = -t := abs_of_nonpos ht0
      have hn : t ∈ Set.Icc (-outerUpper X beta eta) (-outerLower X beta eta) := by
        rw [Set.mem_Icc]
        rw [mem_sourceFrequencyRegion_iff, habs] at ht
        dsimp [outerLower, outerUpper]
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simp [sourceMaskedCriticalNormWeight, componentMaskedCriticalNormWeight,
        componentEndpoints, ht, hn]
  · simp [sourceMaskedCriticalNormWeight, ht]

/-- Monotonicity of the positive packet-correlation bilinear in its weight. -/
theorem packetCorrelationBilinear_mono
    {J : ℝ → ℝ → ℂ} {F G : ℝ → ENNReal}
    (hFG : ∀ t, F t ≤ G t) :
    packetCorrelationBilinear J F ≤ packetCorrelationBilinear J G := by
  unfold packetCorrelationBilinear
  apply lintegral_mono
  intro z
  exact mul_le_mul_right' (mul_le_mul (hFG z.1) (hFG z.2) bot_le bot_le) _

/-- The faithful equation-(79) amplitude is pointwise bounded by the critical
norm with the exact source-region mask retained. -/
theorem ofReal_norm_sourceTildePolynomial_le_masked
    {N : ℕ} {X beta eta t : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    ENNReal.ofReal
        ‖sourceTildePolynomial N X beta eta faithfulCutoff f t‖ ≤
      sourceMaskedCriticalNormWeight N X beta eta f t := by
  by_cases ht : t ∈ sourceFrequencyRegion X beta eta
  · rw [sourceMaskedCriticalNormWeight, Set.indicator_of_mem ht]
    apply ENNReal.ofReal_le_ofReal
    have hraw := norm_sourceTildePolynomial_le
      (N := N) (X := X) (beta := beta) (eta := eta)
      (t := t) (f := f) (cutoff := faithfulCutoff)
      (fun y ↦ abs_faithfulCutoff_le_one y)
    have hc : (1 / Real.pi : ℝ) ≤ 1 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    exact hraw.trans (by
      simpa only [one_mul] using
        mul_le_of_le_one_left (norm_nonneg (finiteCriticalPolynomial N f t)) hc)
  · have hz := sourceTildePolynomial_eq_zero_off_sourceFrequencyRegion
      (N := N) (X := X) (beta := beta) (eta := eta) (t := t) (f := f)
      hX hbeta heta hetaSmall
      (fun y hy ↦ faithfulCutoff_one hy)
      (fun y hy ↦ faithfulCutoff_zero_of_one_le hy) ht
    simp [sourceMaskedCriticalNormWeight, ht, hz]

/-- Source-faithful equation-(79) packet energy, now dominated by the packet
bilinear with the exact region-`I` critical weight. -/
theorem faithful_equation79PacketEnergy_le_maskedBilinear
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    ENNReal.ofReal (∫ x : ℝ,
      ‖packetSuperposition
        (sourceTildePolynomial N X beta eta faithfulCutoff f)
        (fun r x ↦ sourceStationaryPacket X H x beta r
          faithfulCutoff faithfulCutoff) x‖ ^ 2) ≤
      packetCorrelationBilinear
        (fun r x ↦ sourceStationaryPacket X H x beta r
          faithfulCutoff faithfulCutoff)
        (sourceMaskedCriticalNormWeight N X beta eta f) := by
  calc
    _ ≤ packetCorrelationBilinear
        (fun r x ↦ sourceStationaryPacket X H x beta r
          faithfulCutoff faithfulCutoff)
        (fun t ↦ ENNReal.ofReal
          ‖sourceTildePolynomial N X beta eta faithfulCutoff f t‖) :=
      faithful_equation79PacketEnergy_le_packetCorrelationBilinear
        hX hH hbeta heta hetaSmall
    _ ≤ _ := packetCorrelationBilinear_mono
      (fun t ↦ ofReal_norm_sourceTildePolynomial_le_masked
        hX hbeta heta hetaSmall)

theorem equation81Average_mono
    {R : ℝ} {F G : ℝ → ENNReal} (hFG : ∀ t, F t ≤ G t) (x : ℝ) :
    equation81Average R F x ≤ equation81Average R G x := by
  unfold equation81Average
  apply lintegral_mono
  intro t
  exact mul_le_mul_right' (hFG t) _

/-- The exact signed-component split commutes with the positive moving-window
integral up to the endpoint-safe inequality needed downstream. -/
theorem equation81Average_sourceMasked_le_components
    {N : ℕ} {X R beta eta x : ℝ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (heta : 0 < eta) :
    equation81Average R (sourceMaskedCriticalNormWeight N X beta eta f) x ≤
      equation81Average R
          (componentMaskedCriticalNormWeight N X beta eta f .negative) x +
        equation81Average R
          (componentMaskedCriticalNormWeight N X beta eta f .positive) x := by
  unfold equation81Average
  calc
    _ ≤ ∫⁻ t : ℝ,
        (componentMaskedCriticalNormWeight N X beta eta f .negative t +
          componentMaskedCriticalNormWeight N X beta eta f .positive t) *
            symmetricBoxWeight R x t := by
      apply lintegral_mono
      intro t
      exact mul_le_mul_right' (sourceMasked_le_signed_components hX heta) _
    _ = ∫⁻ t : ℝ,
          componentMaskedCriticalNormWeight N X beta eta f .negative t *
            symmetricBoxWeight R x t +
          componentMaskedCriticalNormWeight N X beta eta f .positive t *
            symmetricBoxWeight R x t := by
      apply lintegral_congr
      intro t
      ring
    _ = _ := by
      rw [lintegral_add_left]
      exact (measurable_componentMaskedCriticalNormWeight
        N X beta eta f .negative).mul
          ((measurable_symmetricBoxWeight R).comp
            (measurable_const.prodMk measurable_id))

/-- A left exterior collar is reflected into the interval without decreasing
the full moving-window average.  This is the geometric heart of the endpoint
localization and uses no regularity of the weight. -/
theorem equation81Average_intervalMask_le_leftReflection
    {R a b x : ℝ} {F : ℝ → ENNReal}
    (hR : 0 ≤ R) (hx : x ∈ Set.Icc (a - R) a) :
    equation81Average R ((Set.Icc a b).indicator F) x ≤
      equation81Average R F (2 * a - x) := by
  unfold equation81Average
  apply lintegral_mono
  intro t
  by_cases ht : t ∈ Set.Icc a b
  · by_cases hbox : t - x ∈ Set.Icc (-R) R
    · have hreflect : t - (2 * a - x) ∈ Set.Icc (-R) R := by
        constructor
        · linarith [ht.1, hx.1]
        · linarith [hbox.2, hx.2]
      simp [symmetricBoxWeight, ht, hbox, hreflect]
    · simp [symmetricBoxWeight, ht, hbox]
  · simp [ht]

/-- The symmetric right-collar reflection counterpart. -/
theorem equation81Average_intervalMask_le_rightReflection
    {R a b x : ℝ} {F : ℝ → ENNReal}
    (hR : 0 ≤ R) (hx : x ∈ Set.Icc b (b + R)) :
    equation81Average R ((Set.Icc a b).indicator F) x ≤
      equation81Average R F (2 * b - x) := by
  unfold equation81Average
  apply lintegral_mono
  intro t
  by_cases ht : t ∈ Set.Icc a b
  · by_cases hbox : t - x ∈ Set.Icc (-R) R
    · have hreflect : t - (2 * b - x) ∈ Set.Icc (-R) R := by
        constructor
        · linarith [hbox.1, hx.1]
        · linarith [ht.2, hx.2]
      simp [symmetricBoxWeight, ht, hbox, hreflect]
    · simp [symmetricBoxWeight, ht, hbox]
  · simp [ht]

/-- Integrated left-collar reflection.  The reflected collar lands exactly
in the first radius-`R` segment of the source interval. -/
theorem lintegral_leftCollar_intervalMask_le
    {R a b : ℝ} {F : ℝ → ENNReal}
    (hR : 0 ≤ R) (hF : Measurable F) :
    (∫⁻ x in Set.Icc (a - R) a,
      (equation81Average R ((Set.Icc a b).indicator F) x) ^ 2) ≤
      ∫⁻ y in Set.Icc a (a + R), (equation81Average R F y) ^ 2 := by
  let A : ℝ → ENNReal := fun y ↦ (equation81Average R F y) ^ 2
  have hA : Measurable A :=
    (measurable_equation81Average hF).pow_const 2
  have hmono : (∫⁻ x in Set.Icc (a - R) a,
      (equation81Average R ((Set.Icc a b).indicator F) x) ^ 2) ≤
      ∫⁻ x in Set.Icc (a - R) a, A (2 * a - x) := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    exact pow_le_pow_left'
      (equation81Average_intervalMask_le_leftReflection hR hx) 2
  have hreflect :=
    (volume.measurePreserving_sub_left (2 * a)).setLIntegral_comp_emb
      (Homeomorph.subLeft (2 * a)).measurableEmbedding A
      (Set.Icc (a - R) a)
  have himage : (fun x : ℝ ↦ 2 * a - x) '' Set.Icc (a - R) a =
      Set.Icc a (a + R) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor <;> linarith [hx.1, hx.2]
    · intro hy
      refine ⟨2 * a - y, ?_, by ring⟩
      constructor <;> linarith [hy.1, hy.2]
  rw [himage] at hreflect
  exact hmono.trans_eq hreflect

/-- Integrated right-collar reflection into the last radius-`R` segment. -/
theorem lintegral_rightCollar_intervalMask_le
    {R a b : ℝ} {F : ℝ → ENNReal}
    (hR : 0 ≤ R) (hF : Measurable F) :
    (∫⁻ x in Set.Icc b (b + R),
      (equation81Average R ((Set.Icc a b).indicator F) x) ^ 2) ≤
      ∫⁻ y in Set.Icc (b - R) b, (equation81Average R F y) ^ 2 := by
  let A : ℝ → ENNReal := fun y ↦ (equation81Average R F y) ^ 2
  have hA : Measurable A :=
    (measurable_equation81Average hF).pow_const 2
  have hmono : (∫⁻ x in Set.Icc b (b + R),
      (equation81Average R ((Set.Icc a b).indicator F) x) ^ 2) ≤
      ∫⁻ x in Set.Icc b (b + R), A (2 * b - x) := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    exact pow_le_pow_left'
      (equation81Average_intervalMask_le_rightReflection hR hx) 2
  have hreflect :=
    (volume.measurePreserving_sub_left (2 * b)).setLIntegral_comp_emb
      (Homeomorph.subLeft (2 * b)).measurableEmbedding A
      (Set.Icc b (b + R))
  have himage : (fun x : ℝ ↦ 2 * b - x) '' Set.Icc b (b + R) =
      Set.Icc (b - R) b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor <;> linarith [hx.1, hx.2]
    · intro hy
      refine ⟨2 * b - y, ?_, by ring⟩
      constructor <;> linarith [hy.1, hy.2]
  rw [himage] at hreflect
  exact hmono.trans_eq hreflect

/-- The moving average of an interval-masked weight is supported in the
radius-`R` collar of that interval. -/
theorem equation81Average_intervalMask_eq_zero_off
    {R a b x : ℝ} {F : ℝ → ENNReal}
    (hR : 0 ≤ R) (hx : x ∉ Set.Icc (a - R) (b + R)) :
    equation81Average R ((Set.Icc a b).indicator F) x = 0 := by
  unfold equation81Average
  rw [show (fun t : ℝ ↦
      (Set.Icc a b).indicator F t * symmetricBoxWeight R x t) = 0 by
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · have hbox : t - x ∉ Set.Icc (-R) R := by
        intro htx
        apply hx
        constructor <;> linarith [ht.1, ht.2, htx.1, htx.2]
      simp [symmetricBoxWeight, ht, hbox]
    · simp [ht]]
  exact lintegral_zero

/-- A single interval mask costs at most its interior plus its two reflected
collars.  This gives the clean factor `3` used after splitting the signed
source region. -/
theorem lintegral_intervalMaskedAverage_sq_le_three
    {R a b : ℝ} {F : ℝ → ENNReal}
    (hR : 0 ≤ R) (hab : a ≤ b) (hRlen : R ≤ b - a)
    (hF : Measurable F) :
    (∫⁻ x : ℝ,
      (equation81Average R ((Set.Icc a b).indicator F) x) ^ 2) ≤
      3 * ∫⁻ x in Set.Icc a b, (equation81Average R F x) ^ 2 := by
  let M : ℝ → ENNReal := fun x ↦
    (equation81Average R ((Set.Icc a b).indicator F) x) ^ 2
  let A : ℝ → ENNReal := fun x ↦ (equation81Average R F x) ^ 2
  have hM : Measurable M :=
    (measurable_equation81Average (hF.indicator measurableSet_Icc)).pow_const 2
  have hA : Measurable A := (measurable_equation81Average hF).pow_const 2
  let L := Set.Icc (a - R) a
  let C := Set.Icc a b
  let U := Set.Icc b (b + R)
  have hcover (x : ℝ) :
      M x ≤ L.indicator M x + C.indicator M x + U.indicator M x := by
    by_cases hx : x ∈ Set.Icc (a - R) (b + R)
    · rcases le_total x a with hxa | hax
      · have hL : x ∈ L := ⟨hx.1, hxa⟩
        simp [L, C, U, hL]
        exact le_add_right (le_add_right le_rfl)
      · rcases le_total x b with hxb | hbx
        · have hC : x ∈ C := ⟨hax, hxb⟩
          simp [L, C, U, hC]
          exact le_add_right (le_add_left le_rfl)
        · have hU : x ∈ U := ⟨hbx, hx.2⟩
          simp [L, C, U, hU]
    · have hz : M x = 0 := by
        dsimp [M]
        rw [equation81Average_intervalMask_eq_zero_off hR hx]
        simp
      simp [hz]
  have hsplit : (∫⁻ x : ℝ, M x) ≤
      (∫⁻ x in L, M x) + (∫⁻ x in C, M x) + (∫⁻ x in U, M x) := by
    calc
      _ ≤ ∫⁻ x : ℝ, L.indicator M x + C.indicator M x + U.indicator M x :=
        lintegral_mono hcover
      _ = (∫⁻ x : ℝ, L.indicator M x) +
          (∫⁻ x : ℝ, C.indicator M x) +
          (∫⁻ x : ℝ, U.indicator M x) := by
        rw [lintegral_add_left, lintegral_add_left]
        · exact hM.indicator measurableSet_Icc
        · exact (hM.indicator measurableSet_Icc).add
            (hM.indicator measurableSet_Icc)
      _ = _ := by
        rw [lintegral_indicator measurableSet_Icc,
          lintegral_indicator measurableSet_Icc,
          lintegral_indicator measurableSet_Icc]
  let I : ENNReal := ∫⁻ x in Set.Icc a b, A x
  have hleft : (∫⁻ x in L, M x) ≤ I := by
    have hreflect := lintegral_leftCollar_intervalMask_le
      (R := R) (a := a) (b := b) hR hF
    have hsub : Set.Icc a (a + R) ⊆ Set.Icc a b := by
      intro x hx
      exact ⟨hx.1, by linarith [hx.2, hRlen]⟩
    exact hreflect.trans
      (lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hcenter : (∫⁻ x in C, M x) ≤ I := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    exact pow_le_pow_left' (equation81Average_mono
      (R := R) (fun t ↦ by
        by_cases ht : t ∈ Set.Icc a b <;> simp [ht]) x) 2
  have hright : (∫⁻ x in U, M x) ≤ I := by
    have hreflect := lintegral_rightCollar_intervalMask_le
      (R := R) (a := a) (b := b) hR hF
    have hsub : Set.Icc (b - R) b ⊆ Set.Icc a b := by
      intro x hx
      exact ⟨by linarith [hx.1, hRlen], hx.2⟩
    exact hreflect.trans
      (lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl)
  calc
    (∫⁻ x : ℝ, M x) ≤
        (∫⁻ x in L, M x) + (∫⁻ x in C, M x) + (∫⁻ x in U, M x) := hsplit
    _ ≤ I + I + I := add_le_add (add_le_add hleft hcenter) hright
    _ = 3 * I := by ring

theorem ennreal_add_sq_le_four_sum_sq (a b : ENNReal) :
    (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  rcases le_total a b with hab | hba
  · calc
      (a + b) ^ 2 ≤ (b + b) ^ 2 :=
        pow_le_pow_left' (add_le_add hab le_rfl) 2
      _ = 4 * b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) :=
        mul_le_mul_left' (le_add_left le_rfl) 4
  · calc
      (a + b) ^ 2 ≤ (a + a) ^ 2 :=
        pow_le_pow_left' (add_le_add le_rfl hba) 2
      _ = 4 * a ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) :=
        mul_le_mul_left' (le_add_right le_rfl) 4

/-- The complete two-component collar localization.  The constant `12` is a
safe overlap-independent constant: `4` for splitting the signed components
and `3` for the interior plus two reflected collars of each component. -/
theorem lintegral_sourceMaskedAverage_sq_le_twelve
    {N : ℕ} {X R beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (hR : 0 ≤ R) (heta : 0 < eta)
    (hRlen : R ≤ outerUpper X beta eta - outerLower X beta eta) :
    (∫⁻ x : ℝ,
      (equation81Average R
        (sourceMaskedCriticalNormWeight N X beta eta f) x) ^ 2) ≤
      12 * ((∫⁻ x in Set.Icc (-outerUpper X beta eta)
          (-outerLower X beta eta),
          (equation81Average R (criticalNormWeight N f) x) ^ 2) +
        ∫⁻ x in Set.Icc (outerLower X beta eta)
          (outerUpper X beta eta),
          (equation81Average R (criticalNormWeight N f) x) ^ 2) := by
  let F := criticalNormWeight N f
  let Mn := componentMaskedCriticalNormWeight N X beta eta f .negative
  let Mp := componentMaskedCriticalNormWeight N X beta eta f .positive
  let An : ℝ → ENNReal := fun x ↦ equation81Average R Mn x
  let Ap : ℝ → ENNReal := fun x ↦ equation81Average R Mp x
  have hpoint (x : ℝ) :
      (equation81Average R
        (sourceMaskedCriticalNormWeight N X beta eta f) x) ^ 2 ≤
        4 * (An x ^ 2 + Ap x ^ 2) := by
    exact (pow_le_pow_left'
      (equation81Average_sourceMasked_le_components hX heta) 2).trans
        (ennreal_add_sq_le_four_sum_sq (An x) (Ap x))
  have hmeasAn : Measurable (fun x ↦ An x ^ 2) :=
    (measurable_equation81Average
      (measurable_componentMaskedCriticalNormWeight
        N X beta eta f .negative)).pow_const 2
  have hglobal : (∫⁻ x : ℝ,
      (equation81Average R
        (sourceMaskedCriticalNormWeight N X beta eta f) x) ^ 2) ≤
      4 * ((∫⁻ x : ℝ, An x ^ 2) + ∫⁻ x : ℝ, Ap x ^ 2) := by
    calc
      _ ≤ ∫⁻ x : ℝ, 4 * (An x ^ 2 + Ap x ^ 2) := lintegral_mono hpoint
      _ = 4 * ∫⁻ x : ℝ, (An x ^ 2 + Ap x ^ 2) := by
        rw [lintegral_const_mul' 4]
        norm_num
      _ = _ := by rw [lintegral_add_left hmeasAn]
  have hlenNeg : R ≤
      (-outerLower X beta eta) - (-outerUpper X beta eta) := by
    linarith
  have hneg := lintegral_intervalMaskedAverage_sq_le_three
    (R := R) (a := -outerUpper X beta eta)
    (b := -outerLower X beta eta) (F := F)
    hR (by linarith [hRlen, hR]) hlenNeg (measurable_criticalNormWeight N f)
  have hpos := lintegral_intervalMaskedAverage_sq_le_three
    (R := R) (a := outerLower X beta eta)
    (b := outerUpper X beta eta) (F := F)
    hR (by linarith [hRlen, hR]) hRlen (measurable_criticalNormWeight N f)
  have hcomponents :
      (∫⁻ x : ℝ, An x ^ 2) + (∫⁻ x : ℝ, Ap x ^ 2) ≤
        3 * ((∫⁻ x in Set.Icc (-outerUpper X beta eta)
            (-outerLower X beta eta), (equation81Average R F x) ^ 2) +
          ∫⁻ x in Set.Icc (outerLower X beta eta)
            (outerUpper X beta eta), (equation81Average R F x) ^ 2) := by
    dsimp [An, Ap, Mn, Mp, componentMaskedCriticalNormWeight,
      componentEndpoints] at hneg hpos ⊢
    calc
      _ ≤ 3 * (∫⁻ x in Set.Icc (-outerUpper X beta eta)
              (-outerLower X beta eta), (equation81Average R F x) ^ 2) +
            3 * (∫⁻ x in Set.Icc (outerLower X beta eta)
              (outerUpper X beta eta), (equation81Average R F x) ^ 2) :=
        add_le_add hneg hpos
      _ = _ := by ring
  calc
    _ ≤ 4 * ((∫⁻ x : ℝ, An x ^ 2) + ∫⁻ x : ℝ, Ap x ^ 2) := hglobal
    _ ≤ 4 * (3 * ((∫⁻ x in Set.Icc (-outerUpper X beta eta)
            (-outerLower X beta eta), (equation81Average R F x) ^ 2) +
          ∫⁻ x in Set.Icc (outerLower X beta eta)
            (outerUpper X beta eta), (equation81Average R F x) ^ 2)) :=
      mul_le_mul_left' hcomponents 4
    _ = 12 * ((∫⁻ x in Set.Icc (-outerUpper X beta eta)
          (-outerLower X beta eta),
          (equation81Average R (criticalNormWeight N f) x) ^ 2) +
        ∫⁻ x in Set.Icc (outerLower X beta eta)
          (outerUpper X beta eta),
          (equation81Average R (criticalNormWeight N f) x) ^ 2) := by
      dsimp [F]
      ring

theorem proposition51ILintegral_eq_signed_components
    (N : ℕ) (X H beta eta : ℝ) (f : ℕ → ℂ) :
    proposition51ILintegral N X H f beta eta =
      (∫⁻ x in Set.Icc (-outerUpper X beta eta) (-outerLower X beta eta),
        (equation81Average (|beta| * H) (criticalNormWeight N f) x) ^ 2) +
      ∫⁻ x in Set.Icc (outerLower X beta eta) (outerUpper X beta eta),
        (equation81Average (|beta| * H) (criticalNormWeight N f) x) ^ 2 := by
  unfold proposition51ILintegral
  rw [Fintype.sum_eq_add OuterComponent.negative OuterComponent.positive
    (by decide) (by
      intro x hx
      cases x <;> simp at hx)]
  rfl

theorem sourceMasked_equation81Average_ne_top
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (x : ℝ) :
    equation81Average (|beta| * H)
      (sourceMaskedCriticalNormWeight N X beta eta f) x ≠ ⊤ := by
  have hpoint : ∀ t,
      sourceMaskedCriticalNormWeight N X beta eta f t ≤
        criticalNormWeight N f t := by
    intro t
    by_cases ht : t ∈ sourceFrequencyRegion X beta eta <;>
      simp [sourceMaskedCriticalNormWeight, ht]
  have hle := equation81Average_mono (R := |beta| * H) hpoint x
  rw [equation81Average_criticalNormWeight_eq_untwistedWindow
    (X := X) hH] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Equation (79) through equation (82), with the exact source-region mask
still present.  The remaining localization step is now a literal comparison
of the final displayed lintegral with `proposition51ILintegral`. -/
theorem faithful_equation79PacketEnergy_source_scale_masked
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    ENNReal.ofReal (|beta| * H) *
      ENNReal.ofReal (∫ x : ℝ,
        ‖packetSuperposition
          (sourceTildePolynomial N X beta eta faithfulCutoff f)
          (fun r x ↦ sourceStationaryPacket X H x beta r
            faithfulCutoff faithfulCutoff) x‖ ^ 2) ≤
      18 * ENNReal.ofReal (faithfulEquation82Scale X H beta) *
        (∫⁻ x : ℝ,
          (equation81Average (|beta| * H)
            (sourceMaskedCriticalNormWeight N X beta eta f) x) ^ 2) := by
  have henergy := faithful_equation79PacketEnergy_le_maskedBilinear
    (N := N) (f := f)
    hX (lt_of_lt_of_le zero_lt_one hH) hbeta heta hetaSmall
  have hschur := faithful_packetCorrelationBilinear_source_scale
    (X := X) (H := H) (beta := beta)
    (F := sourceMaskedCriticalNormWeight N X beta eta f)
    hH hHalf hhard
    (measurable_sourceMaskedCriticalNormWeight N X beta eta f)
    (sourceMasked_equation81Average_ne_top (le_trans zero_le_one hH))
  exact (mul_le_mul_left' henergy _).trans hschur

/-- The literal source components are wider than the moving-window radius
throughout the hard range; no enlarged frequency mask is required. -/
theorem source_component_width_ge_radius
    {X H beta eta : ℝ}
    (hX : 0 < X) (hHalf : H ≤ X / 2)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    |beta| * H ≤ outerUpper X beta eta - outerLower X beta eta := by
  have hb : 0 ≤ |beta| := abs_nonneg beta
  have he1 : eta ≤ 1 := by linarith
  have hehalf : eta ≤ 1 / 2 := by linarith
  have hdiv : |beta| * X ≤ |beta| * X / eta := by
    apply (le_div_iff₀ heta).2
    exact mul_le_of_le_one_right (mul_nonneg hb hX.le) he1
  have hsmall : eta * |beta| * X ≤ |beta| * (X / 2) := by
    calc
      eta * |beta| * X = eta * (|beta| * X) := by ring
      _ ≤ (1 / 2) * (|beta| * X) :=
        mul_le_mul_of_nonneg_right hehalf (mul_nonneg hb hX.le)
      _ = |beta| * (X / 2) := by ring
  have hH := mul_le_mul_of_nonneg_left hHalf hb
  dsimp [outerUpper, outerLower]
  nlinarith

/-- Complete source-scale packet energy estimate with the exact two-component
`proposition51ILintegral`.  The constant is `18 * 12`, combining the proved
Schur estimate with the reflected collars. -/
theorem faithful_equation79PacketEnergy_source_scale
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    ENNReal.ofReal (|beta| * H) *
      ENNReal.ofReal (∫ x : ℝ,
        ‖packetSuperposition
          (sourceTildePolynomial N X beta eta faithfulCutoff f)
          (fun r x ↦ sourceStationaryPacket X H x beta r
            faithfulCutoff faithfulCutoff) x‖ ^ 2) ≤
      216 * ENNReal.ofReal (faithfulEquation82Scale X H beta) *
        proposition51ILintegral N X H f beta eta := by
  have hlocal := lintegral_sourceMaskedAverage_sq_le_twelve
    (N := N) (X := X) (R := |beta| * H) (beta := beta) (eta := eta) (f := f)
    hX.le (mul_nonneg (abs_nonneg _) (le_trans zero_le_one hH)) heta
    (source_component_width_ge_radius hX hHalf heta hetaSmall)
  rw [← proposition51ILintegral_eq_signed_components] at hlocal
  calc
    _ ≤ 18 * ENNReal.ofReal (faithfulEquation82Scale X H beta) *
        (∫⁻ x : ℝ, (equation81Average (|beta| * H)
          (sourceMaskedCriticalNormWeight N X beta eta f) x) ^ 2) :=
      faithful_equation79PacketEnergy_source_scale_masked
        hX hH hHalf hbeta hhard heta hetaSmall
    _ ≤ 18 * ENNReal.ofReal (faithfulEquation82Scale X H beta) *
        (12 * proposition51ILintegral N X H f beta eta) :=
      mul_le_mul_left' hlocal _
    _ = _ := by ring

/-- Real-valued manuscript normalization of the fully localized estimate. -/
theorem faithful_equation79PacketEnergy_real_source_scale
    {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    (|beta| * H) * (∫ x : ℝ,
        ‖packetSuperposition
          (sourceTildePolynomial ⌊2 * X⌋₊ X beta eta faithfulCutoff f)
          (fun r x ↦ sourceStationaryPacket X H x beta r
            faithfulCutoff faithfulCutoff) x‖ ^ 2) ≤
      216 * faithfulEquation82Scale X H beta *
        proposition51I X H f beta eta := by
  have h := faithful_equation79PacketEnergy_source_scale
    (N := ⌊2 * X⌋₊) (f := f) hX hH hHalf hbeta hhard heta hetaSmall
  rw [proposition51ILintegral_eq_ofReal_proposition51I hX.le
    (le_trans zero_le_one hH) heta (by linarith : eta ≤ 1)] at h
  have hs := faithfulEquation82Scale_nonneg (beta := beta) hX (le_trans zero_le_one hH)
  have hbH : 0 ≤ |beta| * H := by positivity
  have hr : 0 ≤ 216 * faithfulEquation82Scale X H beta *
      proposition51I X H f beta eta := by
    apply mul_nonneg (mul_nonneg (by norm_num) hs)
    unfold proposition51I untwistedComponentIntegral
    apply Finset.sum_nonneg
    intro component hcomponent
    apply intervalIntegral.integral_nonneg
      (componentEndpoints_mono hX.le heta (by linarith : eta ≤ 1) component)
    intro t ht
    exact sq_nonneg _
  apply (ENNReal.ofReal_le_ofReal_iff hr).mp
  simpa only [ENNReal.ofReal_mul hbH, ENNReal.ofReal_mul
    (mul_nonneg (show (0 : ℝ) ≤ 216 by norm_num) hs),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 216 by norm_num),
    ENNReal.ofReal_ofNat] using h

/-- The packet energy has exactly the stationary `1 / (beta² * X)`
scale, with an absolute constant determined by the single faithful cutoff. -/
theorem faithful_equation79PacketEnergy_le_stationary_scale
    {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    (∫ x : ℝ,
        ‖packetSuperposition
          (sourceTildePolynomial ⌊2 * X⌋₊ X beta eta faithfulCutoff f)
          (fun r x ↦ sourceStationaryPacket X H x beta r
            faithfulCutoff faithfulCutoff) x‖ ^ 2) ≤
      (216 * faithfulEquation82Constant / (beta ^ 2 * X)) *
        proposition51I X H f beta eta := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have h := faithful_equation79PacketEnergy_real_source_scale
    (f := f) hX hH hHalf hbeta hhard heta hetaSmall
  apply (mul_le_mul_iff_right₀ (mul_pos hb hHpos)).mp
  calc
    _ ≤ 216 * faithfulEquation82Scale X H beta *
        proposition51I X H f beta eta := by simpa [mul_comm] using h
    _ = _ := by
      unfold faithfulEquation82Scale
      rw [← sq_abs beta]
      field_simp [hb.ne', hX.ne', hHpos.ne']
      <;> ring

#print axioms faithful_equation79PacketEnergy_le_stationary_scale

#print axioms faithful_equation79PacketEnergy_real_source_scale

#print axioms lintegral_intervalMaskedAverage_sq_le_three
#print axioms lintegral_sourceMaskedAverage_sq_le_twelve
#print axioms source_component_width_ge_radius
#print axioms faithful_equation79PacketEnergy_source_scale

#print axioms measurable_sourceMaskedCriticalNormWeight
#print axioms packetCorrelationBilinear_mono
#print axioms ofReal_norm_sourceTildePolynomial_le_masked
#print axioms faithful_equation79PacketEnergy_le_maskedBilinear
#print axioms sourceMasked_le_signed_components
#print axioms equation81Average_sourceMasked_le_components
#print axioms equation81Average_intervalMask_le_leftReflection
#print axioms equation81Average_intervalMask_le_rightReflection
#print axioms lintegral_leftCollar_intervalMask_le
#print axioms lintegral_rightCollar_intervalMask_le
#print axioms equation81Average_intervalMask_eq_zero_off
#print axioms sourceMasked_equation81Average_ne_top
#print axioms faithful_equation79PacketEnergy_source_scale_masked

end
end MAPMRTFaithfulEquation79LocalizedBilinear
