import HarmonicInterfaces

/-!
# Fejer weights on literal translated real windows

This module isolates the finite frequency geometry that is easy to lose in
paper notation.  The center is a real number, the target set uses the exact
`ceil`/`floor` endpoints from `FullMAP`, and the Fejer order is chosen only
after that window is fixed.
-/

namespace MAPHarmonicEndpoint

open AddCircle MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Integer frequency about which a real translated window is modulated. -/
def integerFrequencyCenter (h₀ : ℝ) : ℤ := ⌊h₀⌋

/-- The paper-safe order.  The extra factor two gives a uniform half-weight
on every frequency of the closed translated window, including endpoints. -/
def translatedFejerOrder (H : ℝ) : ℕ := 2 * ⌈H⌉₊ + 2

/-- Every literal endpoint frequency is within `ceil H` of the chosen
integer modulation center. -/
theorem translatedWindow_natAbs_sub_center_le
    {H h₀ : ℝ} (_hH : 0 ≤ H) {h : ℤ}
    (hh : h ∈ PrimePairEndpoints.translatedWindow H h₀) :
    (h - integerFrequencyCenter h₀).natAbs ≤ ⌈H⌉₊ := by
  rw [PrimePairEndpoints.translatedWindow, Finset.mem_Icc] at hh
  rcases hh with ⟨hhlo, hhhi⟩
  have hloCast : (↑⌈h₀ - H⌉ : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast hhlo
  have hhiCast : (h : ℝ) ≤ (↑⌊h₀ + H⌋ : ℝ) := by
    exact_mod_cast hhhi
  have hloReal : h₀ - H ≤ (h : ℝ) :=
    (Int.le_ceil (h₀ - H)).trans hloCast
  have hhiReal : (h : ℝ) ≤ h₀ + H :=
    hhiCast.trans (Int.floor_le (h₀ + H))
  have hcLe : ((integerFrequencyCenter h₀ : ℤ) : ℝ) ≤ h₀ :=
    Int.floor_le h₀
  have hcGt : h₀ - 1 < ((integerFrequencyCenter h₀ : ℤ) : ℝ) :=
    Int.sub_one_lt_floor h₀
  have hceil : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil H
  have hdloReal : -(⌈H⌉₊ : ℝ) ≤
      ((h - integerFrequencyCenter h₀ : ℤ) : ℝ) := by
    push_cast
    linarith
  have hdhiReal : ((h - integerFrequencyCenter h₀ : ℤ) : ℝ) <
      (⌈H⌉₊ : ℝ) + 1 := by
    push_cast
    linarith
  have hdloInt : -(⌈H⌉₊ : ℤ) ≤ h - integerFrequencyCenter h₀ := by
    exact_mod_cast hdloReal
  have hdhiInt : h - integerFrequencyCenter h₀ < (⌈H⌉₊ : ℤ) + 1 := by
    exact_mod_cast hdhiReal
  have habsInt : |h - integerFrequencyCenter h₀| ≤ (⌈H⌉₊ : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have hnatInt : ((h - integerFrequencyCenter h₀).natAbs : ℤ) ≤
      (⌈H⌉₊ : ℤ) := by
    simpa [Int.natCast_natAbs] using habsInt
  exact_mod_cast hnatInt

/-- Exact triangular coefficient of the finite Fejer kernel. -/
theorem pairMultiplicity_eq_sub_natAbs
    (N : ℕ) (k : ℤ) (hk : k.natAbs < N) :
    FejerLocalMass.pairMultiplicity N k = N - k.natAbs := by
  classical
  rw [FejerLocalMass.pairMultiplicity]
  by_cases hk0 : 0 ≤ k
  · have hkcast : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hk0
    let s := ((Finset.range N ×ˢ Finset.range N).filter
      (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = k))
    have hcard : s.card = (Finset.range (N - k.natAbs)).card := by
      apply Finset.card_bij (fun p hp ↦ p.2)
      · intro p hp
        simp only [s, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range] at hp
        simp only [Finset.mem_range]
        omega
      · intro p hp q hq hpq
        simp only [s, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range] at hp hq
        rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        simp only at hpq
        have hab : a = c := by
          norm_num at hp hq
          omega
        simp [hab, hpq]
      · intro b hb
        simp only [Finset.mem_range] at hb
        let p : ℕ × ℕ := (b + k.natAbs, b)
        have hp : p ∈ s := by
          simp only [s, Finset.mem_filter, Finset.mem_product,
            Finset.mem_range, p]
          constructor
          · omega
          · norm_num [hkcast]
        exact ⟨p, hp, rfl⟩
    simpa [s] using hcard
  · have hkneg : k < 0 := lt_of_not_ge hk0
    have hkcast : (k.natAbs : ℤ) = -k := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    let s := ((Finset.range N ×ˢ Finset.range N).filter
      (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = k))
    have hcard : s.card = (Finset.range (N - k.natAbs)).card := by
      apply Finset.card_bij (fun p hp ↦ p.1)
      · intro p hp
        simp only [s, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range] at hp
        simp only [Finset.mem_range]
        omega
      · intro p hp q hq hpq
        simp only [s, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range] at hp hq
        rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        simp only at hpq
        have hbd : b = d := by
          norm_num at hp hq
          omega
        simp [hpq, hbd]
      · intro a ha
        simp only [Finset.mem_range] at ha
        let p : ℕ × ℕ := (a, a + k.natAbs)
        have hp : p ∈ s := by
          simp only [s, Finset.mem_filter, Finset.mem_product,
            Finset.mem_range, p]
          constructor
          · omega
          · norm_num [hkcast]
        exact ⟨p, hp, rfl⟩
    simpa [s] using hcard

/-- The Fejer pair count is at least half the order throughout the exact
translated frequency window. -/
theorem translatedWindow_pairMultiplicity_half
    {H h₀ : ℝ} (hH : 0 ≤ H) {h : ℤ}
    (hh : h ∈ PrimePairEndpoints.translatedWindow H h₀) :
    translatedFejerOrder H ≤
      2 * FejerLocalMass.pairMultiplicity (translatedFejerOrder H)
        (h - integerFrequencyCenter h₀) := by
  have hk := translatedWindow_natAbs_sub_center_le hH hh
  have hklt : (h - integerFrequencyCenter h₀).natAbs <
      translatedFejerOrder H := by
    simp only [translatedFejerOrder]
    omega
  rw [pairMultiplicity_eq_sub_natAbs _ _ hklt]
  simp only [translatedFejerOrder]
  omega

/-- Weighted Fejer energy about an integer modulation center. -/
def fejerFourierEnergy (w : UnitAddCircle → ℝ) (N : ℕ) (c : ℤ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
    ((FejerLocalMass.pairMultiplicity N k : ℝ) / N) *
      ‖circleCoefficient w (c + k)‖ ^ 2

theorem fejerFourierEnergy_nonneg
    (w : UnitAddCircle → ℝ) (N : ℕ) (c : ℤ) :
    0 ≤ fejerFourierEnergy w N c := by
  unfold fejerFourierEnergy
  positivity

/-- The modulated Fejer convolution whose integral against the same positive
density is the weighted Fourier energy.  It is written as a finite sum, so
there is no hidden convergence or measure convention. -/
def shiftedFejerConvolution
    (w : UnitAddCircle → ℝ) (N : ℕ) (c : ℤ)
    (x : UnitAddCircle) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
    ((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
      fourier (-(c + k)) x * conj (circleCoefficient w (c + k))

theorem integrable_density_mul_fourier
    {w : UnitAddCircle → ℝ}
    (hw : Integrable w AddCircle.haarAddCircle) (h : ℤ) :
    Integrable (fun x : UnitAddCircle ↦
      (w x : ℂ) * fourier (-h) x) AddCircle.haarAddCircle := by
  apply hw.ofReal.mul_bdd
  · exact (map_continuous (fourier (-h))).aestronglyMeasurable
  · apply ae_of_all
    intro x
    rw [fourier_apply, Circle.norm_coe]

/-- Exact normalized-Haar factorization of the modulated Fejer interaction.
This is the positive-measure large-sieve algebra before the separate spatial
kernel-decay estimate. -/
theorem integral_density_mul_shiftedFejerConvolution
    {w : UnitAddCircle → ℝ}
    (hw : Integrable w AddCircle.haarAddCircle) (N : ℕ) (c : ℤ) :
    (∫ x : UnitAddCircle,
        (w x : ℂ) * shiftedFejerConvolution w N c x
          ∂AddCircle.haarAddCircle) =
      (fejerFourierEnergy w N c : ℂ) := by
  classical
  have hfun :
      (fun x : UnitAddCircle ↦
        (w x : ℂ) * shiftedFejerConvolution w N c x) =
      (fun x : UnitAddCircle ↦
        ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          (((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
            ((w x : ℂ) * fourier (-(c + k)) x)) *
              conj (circleCoefficient w (c + k))) := by
    funext x
    simp only [shiftedFejerConvolution]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfun, integral_finsetSum]
  · calc
      (∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          ∫ x : UnitAddCircle,
            (((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
              ((w x : ℂ) * fourier (-(c + k)) x)) *
                conj (circleCoefficient w (c + k))
              ∂AddCircle.haarAddCircle) =
        ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          (((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
            circleCoefficient w (c + k)) *
              conj (circleCoefficient w (c + k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [integral_mul_const, integral_const_mul]
        rfl
      _ = (fejerFourierEnergy w N c : ℂ) := by
        simp only [fejerFourierEnergy]
        symm
        change Complex.ofRealHom
            (∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
              ((FejerLocalMass.pairMultiplicity N k : ℝ) / N) *
                ‖circleCoefficient w (c + k)‖ ^ 2) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        norm_cast
  · intro k hk
    have hi := (integrable_density_mul_fourier hw (c + k)).const_mul
      (((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ))
    exact hi.mul_const _

/-- Positive-density Fejer/local Fourier-mass inequality.  The local input is
the literal uniform bound for the finite modulated Fejer convolution.  The
remaining geometric bridge to radius-`1/(2H)` arc masses is isolated in the
audit rather than hidden as a measure convention. -/
theorem fejerFourierEnergy_le_total_mul_local
    {w : UnitAddCircle → ℝ}
    (hw : Integrable w AddCircle.haarAddCircle)
    (hw0 : ∀ x, 0 ≤ w x) (N : ℕ) (c : ℤ) {localBound : ℝ}
    (_hlocal0 : 0 ≤ localBound)
    (hlocal : ∀ x, ‖shiftedFejerConvolution w N c x‖ ≤ localBound) :
    fejerFourierEnergy w N c ≤
      (∫ x : UnitAddCircle, w x ∂AddCircle.haarAddCircle) * localBound := by
  have hid := integral_density_mul_shiftedFejerConvolution hw N c
  have henergyNorm : fejerFourierEnergy w N c ≤
      ‖∫ x : UnitAddCircle,
          (w x : ℂ) * shiftedFejerConvolution w N c x
            ∂AddCircle.haarAddCircle‖ := by
    rw [hid]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerFourierEnergy_nonneg w N c)]
    exact le_rfl
  have hnormIntegral :
      ‖∫ x : UnitAddCircle,
          (w x : ℂ) * shiftedFejerConvolution w N c x
            ∂AddCircle.haarAddCircle‖ ≤
        ∫ x : UnitAddCircle,
          ‖(w x : ℂ) * shiftedFejerConvolution w N c x‖
            ∂AddCircle.haarAddCircle :=
    norm_integral_le_integral_norm _
  have hpoint : ∀ x : UnitAddCircle,
      ‖(w x : ℂ) * shiftedFejerConvolution w N c x‖ ≤
        w x * localBound := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
    exact mul_le_mul_of_nonneg_left (hlocal x) (hw0 x)
  have hmajor :
      (∫ x : UnitAddCircle,
          ‖(w x : ℂ) * shiftedFejerConvolution w N c x‖
            ∂AddCircle.haarAddCircle) ≤
        ∫ x : UnitAddCircle, w x * localBound
          ∂AddCircle.haarAddCircle := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun x ↦ norm_nonneg _)
    · exact hw.mul_const localBound
    · exact Filter.Eventually.of_forall hpoint
  calc
    fejerFourierEnergy w N c ≤
        ‖∫ x : UnitAddCircle,
          (w x : ℂ) * shiftedFejerConvolution w N c x
            ∂AddCircle.haarAddCircle‖ := henergyNorm
    _ ≤ ∫ x : UnitAddCircle,
        ‖(w x : ℂ) * shiftedFejerConvolution w N c x‖
          ∂AddCircle.haarAddCircle := hnormIntegral
    _ ≤ ∫ x : UnitAddCircle, w x * localBound
          ∂AddCircle.haarAddCircle := hmajor
    _ = (∫ x : UnitAddCircle, w x ∂AddCircle.haarAddCircle) *
          localBound := integral_mul_const _ _

/-- The exact real-center window is dominated by twice the corresponding
Fejer-weighted energy.  No frequency endpoint is discarded. -/
theorem translatedWindow_fourierMass_le_two_fejerEnergy
    (w : UnitAddCircle → ℝ) {H h₀ : ℝ} (hH : 0 ≤ H) :
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        ‖circleCoefficient w h‖ ^ 2) ≤
      2 * fejerFourierEnergy w (translatedFejerOrder H)
        (integerFrequencyCenter h₀) := by
  classical
  let N := translatedFejerOrder H
  let c := integerFrequencyCenter h₀
  have hN : 0 < N := by simp [N, translatedFejerOrder]
  have hsubset :
      (PrimePairEndpoints.translatedWindow H h₀).image (fun h ↦ h - c) ⊆
        Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨h, hh, rfl⟩
    rw [Finset.mem_Icc]
    have habs := translatedWindow_natAbs_sub_center_le hH hh
    have hklt : (h - c).natAbs < N := by
      simp only [N, c, translatedFejerOrder]
      omega
    have habsInt : |h - c| < (N : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hklt
    rw [abs_lt] at habsInt
    omega
  have hinj : Function.Injective (fun h : ℤ ↦ h - c) := by
    exact sub_left_injective
  calc
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        ‖circleCoefficient w h‖ ^ 2) =
      ∑ k ∈ (PrimePairEndpoints.translatedWindow H h₀).image
          (fun h ↦ h - c),
        ‖circleCoefficient w (c + k)‖ ^ 2 := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro h hh
        congr 2
        abel
      · intro a ha b hb hab
        exact hinj hab
    _ ≤ ∑ k ∈ (PrimePairEndpoints.translatedWindow H h₀).image
          (fun h ↦ h - c),
        2 * (((FejerLocalMass.pairMultiplicity N k : ℝ) / N) *
          ‖circleCoefficient w (c + k)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨h, hh, rfl⟩
      have hhalf := translatedWindow_pairMultiplicity_half hH hh
      have hratio : (1 : ℝ) ≤
          2 * ((FejerLocalMass.pairMultiplicity N (h - c) : ℝ) / N) := by
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        rw [show 2 * ((FejerLocalMass.pairMultiplicity N (h - c) : ℝ) / N) =
          (2 * (FejerLocalMass.pairMultiplicity N (h - c) : ℝ)) / N by ring]
        apply (le_div_iff₀ hNr).2
        change N ≤ 2 * FejerLocalMass.pairMultiplicity N (h - c) at hhalf
        have hhalfr : (N : ℝ) ≤
            2 * (FejerLocalMass.pairMultiplicity N (h - c) : ℝ) := by
          exact_mod_cast hhalf
        simpa only [one_mul] using hhalfr
      have hsquare : 0 ≤ ‖circleCoefficient w (c + (h - c))‖ ^ 2 := sq_nonneg _
      calc
        ‖circleCoefficient w (c + (h - c))‖ ^ 2 =
            1 * ‖circleCoefficient w (c + (h - c))‖ ^ 2 := by ring
        _ ≤ (2 * ((FejerLocalMass.pairMultiplicity N (h - c) : ℝ) / N)) *
            ‖circleCoefficient w (c + (h - c))‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hratio hsquare
        _ = 2 * (((FejerLocalMass.pairMultiplicity N (h - c) : ℝ) / N) *
            ‖circleCoefficient w (c + (h - c))‖ ^ 2) := by ring
    _ ≤ ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
        2 * (((FejerLocalMass.pairMultiplicity N k : ℝ) / N) *
          ‖circleCoefficient w (c + k)‖ ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k hkbig hksmall
      positivity
    _ = 2 * fejerFourierEnergy w N c := by
      simp [fejerFourierEnergy, Finset.mul_sum]

/-- User-facing combination: exact real translated window, both endpoints,
positive density, and a uniform Fejer-local convolution bound. -/
theorem translatedWindow_fourierMass_le_total_mul_local
    {w : UnitAddCircle → ℝ}
    (hw : Integrable w AddCircle.haarAddCircle)
    (hw0 : ∀ x, 0 ≤ w x) {H h₀ localBound : ℝ}
    (hH : 0 ≤ H) (hlocal0 : 0 ≤ localBound)
    (hlocal : ∀ x,
      ‖shiftedFejerConvolution w (translatedFejerOrder H)
          (integerFrequencyCenter h₀) x‖ ≤ localBound) :
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        ‖circleCoefficient w h‖ ^ 2) ≤
      2 * (∫ x : UnitAddCircle, w x ∂AddCircle.haarAddCircle) *
        localBound := by
  calc
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        ‖circleCoefficient w h‖ ^ 2) ≤
      2 * fejerFourierEnergy w (translatedFejerOrder H)
        (integerFrequencyCenter h₀) :=
      translatedWindow_fourierMass_le_two_fejerEnergy w hH
    _ ≤ 2 * ((∫ x : UnitAddCircle, w x
          ∂AddCircle.haarAddCircle) * localBound) := by
      gcongr
      exact fejerFourierEnergy_le_total_mul_local hw hw0 _ _ hlocal0 hlocal
    _ = 2 * (∫ x : UnitAddCircle, w x
          ∂AddCircle.haarAddCircle) * localBound := by ring

/-!
The following proposition is intentionally a *definition of the exact open
geometric bridge*, not an axiom or theorem.  Proving it requires the spatial
decay/annular partition for the finite kernel.  Once it is proved, the next
theorem turns it into the paper's positive-measure large sieve without any
arithmetic hypothesis.
-/

def ArcMassControlsShiftedFejerConvolution : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (w : UnitAddCircle → ℝ) (H h₀ localBound : ℝ),
      Integrable w AddCircle.haarAddCircle →
      (∀ x, 0 ≤ w x) →
      1 ≤ H → 0 ≤ localBound →
      (∀ center : UnitAddCircle,
        (∫ x in PrimePairEndpoints.centeredArc H center, w x
          ∂AddCircle.haarAddCircle) ≤ localBound) →
      ∀ x : UnitAddCircle,
        ‖shiftedFejerConvolution w (translatedFejerOrder H)
            (integerFrequencyCenter h₀) x‖ ≤
          C₀ * H * localBound

/-- The exact report-level large-sieve interface follows formally from the
single spatial kernel bridge above. -/
theorem exists_positiveMeasureFejerLocalFourierConstant_of_arcMassControl
    (hgeo : ArcMassControlsShiftedFejerConvolution) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (w : UnitAddCircle → ℝ)
        (H h₀ totalBound localBound : ℝ),
        Integrable w AddCircle.haarAddCircle →
        (∀ x, 0 ≤ w x) →
        1 ≤ H → 0 ≤ totalBound → 0 ≤ localBound →
        (∫ x : UnitAddCircle, w x ∂AddCircle.haarAddCircle) ≤ totalBound →
        (∀ center : UnitAddCircle,
          (∫ x in PrimePairEndpoints.centeredArc H center, w x
            ∂AddCircle.haarAddCircle) ≤ localBound) →
        (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
          ‖circleCoefficient w h‖ ^ 2) ≤
            C₀ * H * totalBound * localBound := by
  rcases hgeo with ⟨C, hC, hgeo⟩
  refine ⟨2 * C, by positivity, ?_⟩
  intro w H h₀ totalBound localBound hw hw0 hH htotal0 hlocal0
    htotal hlocal
  have hconv := hgeo w H h₀ localBound hw hw0 hH hlocal0 hlocal
  have hbase := translatedWindow_fourierMass_le_total_mul_local
    hw hw0 (zero_le_one.trans hH) (by positivity) hconv
  calc
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        ‖circleCoefficient w h‖ ^ 2) ≤
      2 * (∫ x : UnitAddCircle, w x ∂AddCircle.haarAddCircle) *
        (C * H * localBound) := hbase
    _ ≤ 2 * totalBound * (C * H * localBound) := by
      gcongr
    _ = (2 * C) * H * totalBound * localBound := by ring

end

end MAPHarmonicEndpoint
