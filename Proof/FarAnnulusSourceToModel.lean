import FarAnnulusMRTConnector
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Source-to-model algebra for MAP Type-d cells

This file proves the finite algebra that precedes the mixed-mean estimate:

* a selected factor separates exactly from a finite convolution polynomial;
* an arbitrary finite complementary support is decomposed exactly into
  disjoint dyadic blocks;
* each block is rewritten as the literal `longFactor` expected by Lemma 2.1;
* single-character coefficient families are lifted to the two independent
  character indices produced by expansion of the squared character sum.

No bound for an actual MRT integral is assumed here.
-/

namespace MAPFarAnnulusSourceToModel

open scoped BigOperators
open MixedMeanFrontend MAPNormalizedWrapper MixedMeanMajorantWeld
open MAPFarAnnulusMRT
open DeterminantCountWeld

noncomputable section

/-! ## Exact separation of a finite convolution polynomial -/

/-- A finite two-factor convolution polynomial before equal products are
collected.  This is the literal multiple sum produced by a Type-d cell. -/
def pairProductPolynomial
    (shortSupport longSupport : Finset ℕ)
    (beta g : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ shortSupport.product longSupport,
    (beta p.1 * g p.2) * mellinPhase (p.1 * p.2) t

/-- The Mellin clock is multiplicative on positive integer arguments. -/
theorem mellinPhase_mul
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    mellinPhase (m * n) t = mellinPhase m t * mellinPhase n t := by
  unfold mellinPhase
  rw [Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (Nat.ne_of_gt hm))
      (by exact_mod_cast (Nat.ne_of_gt hn)),
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A finite Type-d convolution polynomial factors exactly as the product of
the selected short polynomial and its complementary polynomial. -/
theorem pairProductPolynomial_eq_mul_dirichletPoly
    {shortSupport longSupport : Finset ℕ}
    (hshort : ∀ m ∈ shortSupport, 0 < m)
    (hlong : ∀ n ∈ longSupport, 0 < n)
    (beta g : ℕ → ℂ) (t : ℝ) :
    pairProductPolynomial shortSupport longSupport beta g t =
      dirichletPoly shortSupport beta t *
        dirichletPoly longSupport g t := by
  unfold pairProductPolynomial dirichletPoly
  have hproduct := Finset.sum_product shortSupport longSupport
    (fun p ↦ (beta p.1 * g p.2) * mellinPhase (p.1 * p.2) t)
  rw [Finset.product_eq_sprod]
  rw [hproduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mellinPhase_mul (hshort m hm) (hlong n hn)]
  ring

/-! ## Exact disjoint dyadic decomposition of the complementary support -/

/-- The block assigned to index `i`.  The assignment function makes the
blocks disjoint by construction. -/
def assignedBlock {b : ℕ} (support : Finset ℕ)
    (blockOf : ℕ → Fin b) (i : Fin b) : Finset ℕ :=
  support.filter fun n ↦ blockOf n = i

/-- Every support element belongs to its assigned block. -/
theorem mem_assignedBlock_self {b : ℕ} {support : Finset ℕ}
    (blockOf : ℕ → Fin b) {n : ℕ} (hn : n ∈ support) :
    n ∈ assignedBlock support blockOf (blockOf n) := by
  simp [assignedBlock, hn]

/-- Distinct assigned blocks are disjoint. -/
theorem assignedBlock_disjoint {b : ℕ} (support : Finset ℕ)
    (blockOf : ℕ → Fin b) {i j : Fin b} (hij : i ≠ j) :
    Disjoint (assignedBlock support blockOf i)
      (assignedBlock support blockOf j) := by
  rw [Finset.disjoint_left]
  intro n hni hnj
  simp only [assignedBlock, Finset.mem_filter] at hni hnj
  exact hij (hni.2.symm.trans hnj.2)

/-- Exact finite polynomial decomposition into the assigned blocks. -/
theorem dirichletPoly_eq_sum_assignedBlocks
    {b : ℕ} (support : Finset ℕ) (blockOf : ℕ → Fin b)
    (g : ℕ → ℂ) (t : ℝ) :
    dirichletPoly support g t =
      ∑ i : Fin b, dirichletPoly (assignedBlock support blockOf i) g t := by
  unfold dirichletPoly assignedBlock
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp [hn]

/-- Mask the complementary coefficient to one assigned block. -/
def assignedBlockCoeff {b : ℕ} (support : Finset ℕ)
    (blockOf : ℕ → Fin b) (i : Fin b) (g : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ assignedBlock support blockOf i then g n else 0

/-- If an assigned block lies in `(N,2N]`, its finite polynomial is exactly
the paper's `longFactor` with the masked coefficient. -/
theorem dirichletPoly_assignedBlock_eq_longFactor
    {b : ℕ} {support : Finset ℕ} {blockOf : ℕ → Fin b}
    {i : Fin b} {N : ℕ}
    (hsub : assignedBlock support blockOf i ⊆ dyadic N)
    (g : ℕ → ℂ) (t : ℝ) :
    dirichletPoly (assignedBlock support blockOf i) g t =
      longFactor N (assignedBlockCoeff support blockOf i g) t := by
  classical
  unfold longFactor dirichletPoly assignedBlockCoeff
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [hn]
  · intro n hnDyadic hnNotBlock
    simp [hnNotBlock]

/-- The complementary polynomial is therefore exactly a finite sum of the
literal dyadic long factors required by Lemma 2.1. -/
theorem dirichletPoly_eq_sum_longFactors
    {b : ℕ} (support : Finset ℕ) (blockOf : ℕ → Fin b)
    (length : Fin b → ℕ)
    (hsub : ∀ i, assignedBlock support blockOf i ⊆ dyadic (length i))
    (g : ℕ → ℂ) (t : ℝ) :
    dirichletPoly support g t =
      ∑ i : Fin b,
        longFactor (length i) (assignedBlockCoeff support blockOf i g) t := by
  rw [dirichletPoly_eq_sum_assignedBlocks support blockOf g t]
  apply Finset.sum_congr rfl
  intro i hi
  exact dirichletPoly_assignedBlock_eq_longFactor (hsub i) g t

/-- Combining factor separation and block decomposition gives the exact
finite Type-d source identity used after cutoff removal. -/
theorem pairProductPolynomial_eq_short_mul_sum_longFactors
    {b : ℕ} {shortSupport longSupport : Finset ℕ}
    (hshort : ∀ m ∈ shortSupport, 0 < m)
    (hlong : ∀ n ∈ longSupport, 0 < n)
    (blockOf : ℕ → Fin b) (length : Fin b → ℕ)
    (hsub : ∀ i, assignedBlock longSupport blockOf i ⊆ dyadic (length i))
    (beta g : ℕ → ℂ) (t : ℝ) :
    pairProductPolynomial shortSupport longSupport beta g t =
      dirichletPoly shortSupport beta t *
        (∑ i : Fin b,
          longFactor (length i)
            (assignedBlockCoeff longSupport blockOf i g) t) := by
  rw [pairProductPolynomial_eq_mul_dirichletPoly hshort hlong,
    dirichletPoly_eq_sum_longFactors longSupport blockOf length hsub]

/-! ## Character-square expansion data -/

/-- Lift a one-character short family to the second character index in the
expanded square. -/
def pairShortFamily {q : ℕ} (beta : Fin q → ℕ → ℂ) :
    Fin q → Fin q → ℕ → ℂ := fun _chi chi' ↦ beta chi'

/-- Lift a one-character long family to the first character index in the
expanded square. -/
def pairLongFamily {q : ℕ} (g : Fin q → ℕ → ℂ) :
    Fin q → Fin q → ℕ → ℂ := fun chi _chi' ↦ g chi

/-- Pointwise coefficient hypotheses pass unchanged to the two independent
character indices; character phases never enlarge coefficient norms. -/
theorem pairFamilies_coefficientBounds
    {q M N a k : ℕ} {beta g : Fin q → ℕ → ℂ}
    (hbeta : ∀ chi, ∀ m ∈ dyadic M,
      ‖beta chi m‖ ≤ Real.log (2 * (m : ℝ)) ^ a)
    (hg : ∀ chi, ∀ n ∈ dyadic N,
      ‖g chi n‖ ≤ (MixedMellinCert.tauAF k n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ a) :
    ∀ chi chi', PaperCoefficientBounds M N a k
      (pairShortFamily beta chi chi') (pairLongFamily g chi chi') := by
  intro chi chi'
  exact ⟨hbeta chi', hg chi⟩

/-- The exact character-pair mass obtained from one-character short and long
families.  This theorem records which of the two independent indices acts on
which factor. -/
theorem characterPairMixedMass_pairFamilies
    {q M N : ℕ} (beta g : Fin q → ℕ → ℂ) (t₀ T U : ℝ) :
    characterPairMixedMass q M N (pairShortFamily beta)
        (pairLongFamily g) t₀ T U =
      U * ∑ chi : Fin q, ∑ chi' : Fin q,
        (MixedMeanMajorantWeld.paperLiteralMixedMean M N
          (beta chi') (g chi) t₀ T U).re := by
  rfl

/-! ## Literal post-Cauchy Type-d cell -/

/-- Squared norm of the paper-normalized long factor for one character. -/
def longCharacterEnergy {q : ℕ} (N : ℕ) (g : Fin q → ℕ → ℂ)
    (chi : Fin q) (t : ℝ) : ℝ :=
  ‖longFactor N (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) t‖ ^ 2

/-- Squared norm of the paper-normalized selected beta factor for one
character. -/
def shortCharacterEnergy {q : ℕ} (M : ℕ) (beta : Fin q → ℕ → ℂ)
    (chi : Fin q) (t : ℝ) : ℝ :=
  ‖shortFactor M (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) t‖ ^ 2

/-- The product of the two character-summed moving-window energies obtained
from the literal Type-d cell after the first Cauchy--Schwarz inequality in
MRT Section 7.  No far-annulus estimate is built into this definition. -/
def postCauchyTypeDCell
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    (a b U : ℝ) : ℝ :=
  ∫ t in a..b,
    (∑ chi : Fin q,
      ∫ s in (t - U)..(t + U), longCharacterEnergy N g chi s) *
    (∑ chi' : Fin q,
      ∫ r in (t - U)..(t + U), shortCharacterEnergy M beta chi' r)

/-- A continuous integrand has a continuous moving-window integral.  This is
the regularity input needed to commute the finite character sums with the
outer compact integral. -/
theorem continuous_movingWindowIntegral
    {f : ℝ → ℝ} (hf : Continuous f) (U : ℝ) :
    Continuous (fun t : ℝ ↦ ∫ s in (t - U)..(t + U), f s) := by
  let F : ℝ → ℝ := fun x ↦ ∫ s in 0..x, f s
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hf.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hwindow : (fun t : ℝ ↦ ∫ s in (t - U)..(t + U), f s) =
      fun t ↦ F (t + U) - F (t - U) := by
    funext t
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 (t - U))
      (hf.intervalIntegrable (μ := MeasureTheory.volume) (t - U) (t + U))
    dsimp [F]
    linarith
  rw [hwindow]
  exact (hF.comp (continuous_id.add continuous_const)).sub
    (hF.comp (continuous_id.sub continuous_const))

theorem continuous_longCharacterEnergy
    {q : ℕ} (N : ℕ) (g : Fin q → ℕ → ℂ) (chi : Fin q) :
    Continuous (longCharacterEnergy N g chi) := by
  exact continuous_sq_norm_longFactor N
    (MixedMeanMajorantWeld.invSqrtCoeff (g chi))

theorem continuous_shortCharacterEnergy
    {q : ℕ} (M : ℕ) (beta : Fin q → ℕ → ℂ) (chi : Fin q) :
    Continuous (shortCharacterEnergy M beta chi) := by
  simpa [shortCharacterEnergy, add_zero] using
    continuous_sq_norm_shortFactor M
      (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) 0

theorem continuous_norm_longFactor (N : ℕ) (g : ℕ → ℂ) :
    Continuous (fun t : ℝ ↦ ‖longFactor N g t‖) := by
  unfold longFactor dirichletPoly mellinPhase
  fun_prop

theorem continuous_norm_shortFactor (M : ℕ) (beta : ℕ → ℂ) :
    Continuous (fun t : ℝ ↦ ‖shortFactor M beta t‖) := by
  unfold shortFactor dirichletPoly mellinPhase
  fun_prop

/-- The post-Cauchy cell expands exactly into the two independent character
indices which occur in `characterPairMixedMass`.  This is a finite
character-expansion theorem, not an estimate. -/
theorem postCauchyTypeDCell_eq_characterPairIntegral
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    (a b U : ℝ) :
    postCauchyTypeDCell q M N beta g a b U =
      ∑ chi : Fin q, ∑ chi' : Fin q,
        ∫ t in a..b,
          (∫ s in (t - U)..(t + U), longCharacterEnergy N g chi s) *
          (∫ r in (t - U)..(t + U),
            shortCharacterEnergy M beta chi' r) := by
  unfold postCauchyTypeDCell
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro chi hchi
    rw [intervalIntegral.integral_finsetSum]
    intro chi' hchi'
    exact ((continuous_movingWindowIntegral
      (continuous_longCharacterEnergy N g chi) U).mul
        (continuous_movingWindowIntegral
          (continuous_shortCharacterEnergy M beta chi') U)).intervalIntegrable _ _
  · intro chi hchi
    exact (continuous_finset_sum _ fun chi' _ ↦
      (continuous_movingWindowIntegral
        (continuous_longCharacterEnergy N g chi) U).mul
          (continuous_movingWindowIntegral
            (continuous_shortCharacterEnergy M beta chi') U)).intervalIntegrable _ _

/-- If `s` belongs to the radius-`U` window centered at `t`, then that whole
window is contained in the radius-`2U` window centered at `s`.  Hence a
nonnegative continuous energy over the first window is bounded by its integral
over the second. -/
theorem movingWindowIntegral_le_doubleWindow
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {t s U : ℝ} (hU : 0 ≤ U)
    (hs : s ∈ Set.Icc (t - U) (t + U)) :
    (∫ r in (t - U)..(t + U), f r) ≤
      ∫ r in (s - 2 * U)..(s + 2 * U), f r := by
  apply intervalIntegral.integral_mono_interval
  · linarith [hs.2]
  · linarith
  · linarith [hs.1]
  · exact Filter.Eventually.of_forall fun x ↦ hf0 x
  · exact hf.intervalIntegrable _ _

/-- Termwise geometry before the final Fubini swap: the short energy window
centered at `t` may be enlarged to the radius-`2U` window centered at the long
variable `s`. -/
theorem characterWindowProduct_le_mixedWindow
    {q M N : ℕ} (beta g : Fin q → ℕ → ℂ)
    (chi chi' : Fin q) {t U : ℝ} (hU : 0 ≤ U) :
    (∫ s in (t - U)..(t + U), longCharacterEnergy N g chi s) *
        (∫ r in (t - U)..(t + U),
          shortCharacterEnergy M beta chi' r) ≤
      ∫ s in (t - U)..(t + U),
        longCharacterEnergy N g chi s *
          (∫ r in (s - 2 * U)..(s + 2 * U),
            shortCharacterEnergy M beta chi' r) := by
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (continuous_longCharacterEnergy N g chi).mul continuous_const |>.intervalIntegrable _ _
  · exact (continuous_longCharacterEnergy N g chi).mul
      (continuous_movingWindowIntegral
        (continuous_shortCharacterEnergy M beta chi') (2 * U))
      |>.intervalIntegrable _ _
  · intro s hs
    exact mul_le_mul_of_nonneg_left
      (movingWindowIntegral_le_doubleWindow
        (continuous_shortCharacterEnergy M beta chi')
        (fun x ↦ sq_nonneg _) hU hs)
      (sq_nonneg _)

/-- The iterated moving-window expression immediately before MRT performs
the outer `t` integral by Fubini. -/
def preFubiniCharacterPairMass
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    (a b U : ℝ) : ℝ :=
  ∑ chi : Fin q, ∑ chi' : Fin q,
    ∫ t in a..b,
      ∫ s in (t - U)..(t + U),
        longCharacterEnergy N g chi s *
          (∫ r in (s - 2 * U)..(s + 2 * U),
            shortCharacterEnergy M beta chi' r)

/-- Everything before the final moving-window overlap count is now a proved
inequality: exact character expansion followed by the radius-doubling window
geometry. -/
theorem postCauchyTypeDCell_le_preFubiniCharacterPairMass
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    postCauchyTypeDCell q M N beta g a b U ≤
      preFubiniCharacterPairMass q M N beta g a b U := by
  rw [postCauchyTypeDCell_eq_characterPairIntegral]
  unfold preFubiniCharacterPairMass
  apply Finset.sum_le_sum
  intro chi hchi
  apply Finset.sum_le_sum
  intro chi' hchi'
  apply intervalIntegral.integral_mono_on hab
  · exact ((continuous_movingWindowIntegral
      (continuous_longCharacterEnergy N g chi) U).mul
        (continuous_movingWindowIntegral
          (continuous_shortCharacterEnergy M beta chi') U)).intervalIntegrable _ _
  · have hinner : Continuous (fun s : ℝ ↦
        longCharacterEnergy N g chi s *
          (∫ r in (s - 2 * U)..(s + 2 * U),
            shortCharacterEnergy M beta chi' r)) :=
      (continuous_longCharacterEnergy N g chi).mul
        (continuous_movingWindowIntegral
          (continuous_shortCharacterEnergy M beta chi') (2 * U))
    exact (continuous_movingWindowIntegral hinner U).intervalIntegrable _ _
  · intro t ht
    exact characterWindowProduct_le_mixedWindow beta g chi chi' hU

/-- The stationary mixed integral written with an actual translated short
variable rather than the displacement variable used by Lemma 2.1. -/
def stationaryCharacterMixedIntegral
    {q : ℕ} (M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    (chi chi' : Fin q) (t₀ T U : ℝ) : ℝ :=
  ∫ s in (t₀ - T / 2)..(t₀ + T / 2),
    longCharacterEnergy N g chi s *
      (∫ r in (s - 2 * U)..(s + 2 * U),
        shortCharacterEnergy M beta chi' r)

/-- Translation from the physical short variable `r` to the displacement
variable `u=r-s` is exact. -/
theorem stationaryCharacterMixedIntegral_eq_literalMixedMeanReal
    {q : ℕ} (M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    (chi chi' : Fin q) (t₀ T U : ℝ) :
    stationaryCharacterMixedIntegral M N beta g chi chi' t₀ T U =
      literalMixedMeanReal M N
        (MixedMeanMajorantWeld.invSqrtCoeff (beta chi'))
        (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) t₀ T U := by
  unfold stationaryCharacterMixedIntegral literalMixedMeanReal
  apply intervalIntegral.integral_congr
  intro s hs
  congr 1
  have hshift := intervalIntegral.integral_comp_add_right
    (shortCharacterEnergy M beta chi') s
    (a := -2 * U) (b := 2 * U)
  have hinner :
      (∫ r in (s - 2 * U)..(s + 2 * U),
        shortCharacterEnergy M beta chi' r) =
      ∫ u in (-2 * U)..(2 * U),
        shortCharacterEnergy M beta chi' (s + u) := by
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hshift.symm
  change longCharacterEnergy N g chi s *
      (∫ r in (s - 2 * U)..(s + 2 * U),
        shortCharacterEnergy M beta chi' r) =
    longCharacterEnergy N g chi s *
      (∫ u in (-2 * U)..(2 * U),
        shortCharacterEnergy M beta chi' (s + u))
  rw [hinner]

/-- The connector's character-pair mass is literally `U` times the sum of
the stationary mixed integrals. -/
theorem characterPairMixedMass_pairFamilies_eq_stationaryIntegrals
    {q M N : ℕ} (beta g : Fin q → ℕ → ℂ) (t₀ T U : ℝ) :
    characterPairMixedMass q M N (pairShortFamily beta)
        (pairLongFamily g) t₀ T U =
      U * ∑ chi : Fin q, ∑ chi' : Fin q,
        stationaryCharacterMixedIntegral M N beta g chi chi' t₀ T U := by
  unfold characterPairMixedMass
  apply congrArg (fun z : ℝ ↦ U * z)
  apply Finset.sum_congr rfl
  intro chi hchi
  apply Finset.sum_congr rfl
  intro chi' hchi'
  rw [stationaryCharacterMixedIntegral_eq_literalMixedMeanReal]
  unfold MixedMeanMajorantWeld.paperLiteralMixedMean
  rw [literalMixedMean_re_eq]
  rfl

/-! ## The exact moving-window overlap count -/

/-- A fixed interval translated through a continuous integrand has a
continuous integral. -/
theorem continuous_translatedIntervalIntegral
    {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun u : ℝ ↦ ∫ t in a..b, f (t + u)) := by
  have hshift : (fun u : ℝ ↦ ∫ t in a..b, f (t + u)) =
      fun u ↦ ∫ s in (a + u)..(b + u), f s := by
    funext u
    exact intervalIntegral.integral_comp_add_right f u
  rw [hshift]
  let F : ℝ → ℝ := fun x ↦ ∫ s in 0..x, f s
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hf.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hdiff : (fun u : ℝ ↦ ∫ s in (a + u)..(b + u), f s) =
      fun u ↦ F (b + u) - F (a + u) := by
    funext u
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 (a + u))
      (hf.intervalIntegrable (μ := MeasureTheory.volume) (a + u) (b + u))
    dsimp [F]
    linarith
  rw [hdiff]
  exact (hF.comp (continuous_const.add continuous_id)).sub
    (hF.comp (continuous_const.add continuous_id))

/-- Fubini on a compact rectangle, followed by interval inclusion, shows
that a radius-`U` moving window has overlap multiplicity at most `2U`.
This proves the literal source of the factor `U` in MRT Section 7. -/
theorem movingWindowSweep_le_two_mul
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    (∫ t in a..b, ∫ s in (t - U)..(t + U), f s) ≤
      2 * U * ∫ s in (a - U)..(b + U), f s := by
  have hinner (t : ℝ) :
      (∫ s in (t - U)..(t + U), f s) =
        ∫ u in (-U)..U, f (t + u) := by
    have hshift := intervalIntegral.integral_comp_add_right f t
      (a := -U) (b := U)
    simpa [add_comm, sub_eq_add_neg] using hshift.symm
  simp_rw [hinner]
  have hrect : MeasureTheory.Integrable
      (Function.uncurry (fun t u : ℝ ↦ f (t + u)))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Ioc (-U) U))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    have hcompact : IsCompact
        (Set.Icc a b ×ˢ Set.Icc (-U) U) :=
      isCompact_Icc.prod isCompact_Icc
    have hcont : Continuous (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) :=
      hf.comp (continuous_fst.add continuous_snd)
    exact (ContinuousOn.integrableOn_compact hcompact hcont.continuousOn).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hswap :
      (∫ t in a..b, ∫ u in (-U)..U, f (t + u)) =
        ∫ u in (-U)..U, ∫ t in a..b, f (t + u) := by
    simp_rw [intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le (by linarith : -U ≤ U)]
    exact MeasureTheory.integral_integral_swap hrect
  rw [hswap]
  have houter :
      (∫ u in (-U)..U, ∫ t in a..b, f (t + u)) ≤
        ∫ _u in (-U)..U, (∫ s in (a - U)..(b + U), f s) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuous_translatedIntervalIntegral hf a b).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
    · intro u hu
      rw [intervalIntegral.integral_comp_add_right]
      apply intervalIntegral.integral_mono_interval
      · linarith [hu.1]
      · simpa [add_comm] using add_le_add_right hab u
      · linarith [hu.2]
      · exact Filter.Eventually.of_forall fun x ↦ hf0 x
      · exact hf.intervalIntegrable _ _
  calc
    (∫ u in (-U)..U, ∫ t in a..b, f (t + u))
        ≤ ∫ _u in (-U)..U, (∫ s in (a - U)..(b + U), f s) := houter
    _ = 2 * U * ∫ s in (a - U)..(b + U), f s := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- The full Cauchy--Fubini reduction from the literal post-Cauchy Type-d
cell to stationary character-pair mixed integrals on the enlarged outer
interval. -/
theorem postCauchyTypeDCell_le_twoU_stationaryIntegrals
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    postCauchyTypeDCell q M N beta g a b U ≤
      2 * U * ∑ chi : Fin q, ∑ chi' : Fin q,
        stationaryCharacterMixedIntegral M N beta g chi chi'
          ((a + b) / 2) ((b - a) + 2 * U) U := by
  calc
    postCauchyTypeDCell q M N beta g a b U ≤
        preFubiniCharacterPairMass q M N beta g a b U :=
      postCauchyTypeDCell_le_preFubiniCharacterPairMass
        q M N beta g hab hU
    _ ≤ ∑ chi : Fin q, ∑ chi' : Fin q,
          (2 * U * stationaryCharacterMixedIntegral M N beta g chi chi'
            ((a + b) / 2) ((b - a) + 2 * U) U) := by
      apply Finset.sum_le_sum
      intro chi hchi
      apply Finset.sum_le_sum
      intro chi' hchi'
      have hsweep := movingWindowSweep_le_two_mul
        ((continuous_longCharacterEnergy N g chi).mul
          (continuous_movingWindowIntegral
            (continuous_shortCharacterEnergy M beta chi') (2 * U)))
        (fun s ↦ mul_nonneg (sq_nonneg _) <|
          intervalIntegral.integral_nonneg (by linarith)
            (fun r hr ↦ sq_nonneg _)) hab hU
      have hleft :
          (a + b) / 2 - ((b - a) + 2 * U) / 2 = a - U := by ring
      have hright :
          (a + b) / 2 + ((b - a) + 2 * U) / 2 = b + U := by ring
      unfold stationaryCharacterMixedIntegral
      rw [hleft, hright]
      exact hsweep
    _ = 2 * U * ∑ chi : Fin q, ∑ chi' : Fin q,
        stationaryCharacterMixedIntegral M N beta g chi chi'
          ((a + b) / 2) ((b - a) + 2 * U) U := by
      simp_rw [Finset.mul_sum]

/-- Direct connector to the exact mixed-mass object consumed by the certified
MRT mixed-mean theorem. -/
theorem postCauchyTypeDCell_le_two_characterPairMixedMass
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    postCauchyTypeDCell q M N beta g a b U ≤
      2 * characterPairMixedMass q M N (pairShortFamily beta)
        (pairLongFamily g) ((a + b) / 2) ((b - a) + 2 * U) U := by
  rw [characterPairMixedMass_pairFamilies_eq_stationaryIntegrals]
  have h := postCauchyTypeDCell_le_twoU_stationaryIntegrals
    q M N beta g hab hU
  nlinarith

/-! ## The first Cauchy inequality from the literal factored cell -/

/-- Compact-interval Cauchy--Schwarz in the squared form used on each
character after the Type-d factorization. -/
theorem intervalIntegral_mul_sq_le
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  let mu : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc a b)
  have hfm : MeasureTheory.MemLp f 2 mu := by
    apply (MeasureTheory.memLp_two_iff_integrable_sq
      hf.aestronglyMeasurable).2
    exact (hf.pow 2).intervalIntegrable a b |>.1
  have hgm : MeasureTheory.MemLp g 2 mu := by
    apply (MeasureTheory.memLp_two_iff_integrable_sq
      hg.aestronglyMeasurable).2
    exact (hg.pow 2).intervalIntegrable a b |>.1
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := mu) hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfm) (by simpa using hgm)
  dsimp [mu] at hh
  simp_rw [intervalIntegral.integral_of_le hab]
  simp only [Real.rpow_two, one_div] at hh
  have hrpow (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hrpow, hrpow] at hh
  have hI : 0 ≤ ∫ x in Set.Ioc a b, f x * g x :=
    MeasureTheory.integral_nonneg fun x ↦ mul_nonneg (hf0 x) (hg0 x)
  have hA : 0 ≤ ∫ x in Set.Ioc a b, f x ^ 2 :=
    MeasureTheory.integral_nonneg fun x ↦ sq_nonneg _
  have hB : 0 ≤ ∫ x in Set.Ioc a b, g x ^ 2 :=
    MeasureTheory.integral_nonneg fun x ↦ sq_nonneg _
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
    sq_nonneg (Real.sqrt (∫ x in Set.Ioc a b, f x ^ 2) -
      Real.sqrt (∫ x in Set.Ioc a b, g x ^ 2))]

/-- The literal factored Type-d character cell before Cauchy--Schwarz. -/
def literalFactoredTypeDCell
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    (a b U : ℝ) : ℝ :=
  ∫ t in a..b,
    (∑ chi : Fin q,
      ∫ s in (t - U)..(t + U),
        ‖longFactor N (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) s‖ *
        ‖shortFactor M (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖) ^ 2

/-- Cauchy--Schwarz simultaneously in the character index and in the moving
interval, with no extraneous factor of `q`. -/
theorem literalFactoredTypeDCell_le_postCauchyTypeDCell
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    literalFactoredTypeDCell q M N beta g a b U ≤
      postCauchyTypeDCell q M N beta g a b U := by
  unfold literalFactoredTypeDCell postCauchyTypeDCell
  apply intervalIntegral.integral_mono_on hab
  · apply (continuous_finsetSum Finset.univ)
      (fun chi hchi ↦ continuous_movingWindowIntegral
        ((continuous_norm_longFactor N
            (MixedMeanMajorantWeld.invSqrtCoeff (g chi))).mul
          (continuous_norm_shortFactor M
            (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)))) U)
      |>.pow 2 |>.intervalIntegrable _ _
  · exact ((continuous_finsetSum Finset.univ fun chi hchi ↦
      continuous_movingWindowIntegral
        (continuous_longCharacterEnergy N g chi) U).mul
      (continuous_finsetSum Finset.univ fun chi hchi ↦
        continuous_movingWindowIntegral
          (continuous_shortCharacterEnergy M beta chi) U)).intervalIntegrable _ _
  · intro t ht
    let I : Fin q → ℝ := fun chi ↦
      ∫ s in (t - U)..(t + U),
        ‖longFactor N (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) s‖ *
        ‖shortFactor M (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖
    let A : Fin q → ℝ := fun chi ↦
      ∫ s in (t - U)..(t + U), longCharacterEnergy N g chi s
    let B : Fin q → ℝ := fun chi ↦
      ∫ s in (t - U)..(t + U), shortCharacterEnergy M beta chi s
    have hA0 (chi : Fin q) : 0 ≤ A chi := by
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun s hs ↦ sq_nonneg _)
    have hB0 (chi : Fin q) : 0 ≤ B chi := by
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun s hs ↦ sq_nonneg _)
    have hI0 (chi : Fin q) : 0 ≤ I chi := by
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun s hs ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hterm (chi : Fin q) :
        I chi ≤ Real.sqrt (A chi) * Real.sqrt (B chi) := by
      have hsq := intervalIntegral_mul_sq_le
        (continuous_norm_longFactor N
          (MixedMeanMajorantWeld.invSqrtCoeff (g chi)))
        (continuous_norm_shortFactor M
          (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)))
        (fun x ↦ norm_nonneg _) (fun x ↦ norm_nonneg _)
        (by linarith : t - U ≤ t + U)
      have hsqrt := Real.le_sqrt_of_sq_le hsq
      change I chi ≤ Real.sqrt (A chi * B chi) at hsqrt
      rw [Real.sqrt_mul (hA0 chi)] at hsqrt
      exact hsqrt
    have hsum1 : (∑ chi, I chi) ≤
        ∑ chi, Real.sqrt (A chi) * Real.sqrt (B chi) :=
      Finset.sum_le_sum fun chi hchi ↦ hterm chi
    have hsum2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun chi ↦ Real.sqrt (A chi)) (fun chi ↦ Real.sqrt (B chi))
    have hAsq : (∑ chi, Real.sqrt (A chi) ^ 2) = ∑ chi, A chi := by
      apply Finset.sum_congr rfl
      intro chi hchi
      exact Real.sq_sqrt (hA0 chi)
    have hBsq : (∑ chi, Real.sqrt (B chi) ^ 2) = ∑ chi, B chi := by
      apply Finset.sum_congr rfl
      intro chi hchi
      exact Real.sq_sqrt (hB0 chi)
    rw [hAsq, hBsq] at hsum2
    have hsum : (∑ chi, I chi) ≤
        Real.sqrt (∑ chi, A chi) * Real.sqrt (∑ chi, B chi) :=
      hsum1.trans hsum2
    have hsumI0 : 0 ≤ ∑ chi, I chi :=
      Finset.sum_nonneg fun chi hchi ↦ hI0 chi
    have hsumA0 : 0 ≤ ∑ chi, A chi :=
      Finset.sum_nonneg fun chi hchi ↦ hA0 chi
    have hsumB0 : 0 ≤ ∑ chi, B chi :=
      Finset.sum_nonneg fun chi hchi ↦ hB0 chi
    change (∑ chi, I chi) ^ 2 ≤ (∑ chi, A chi) * ∑ chi, B chi
    nlinarith [Real.sq_sqrt hsumA0, Real.sq_sqrt hsumB0]

/-- Complete premise-free internal bridge from the literal factorized Type-d
cell to the mixed-mass contract consumed by Lemma 2.1. -/
theorem literalFactoredTypeDCell_le_two_characterPairMixedMass
    (q M N : ℕ) (beta g : Fin q → ℕ → ℂ)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    literalFactoredTypeDCell q M N beta g a b U ≤
      2 * characterPairMixedMass q M N (pairShortFamily beta)
        (pairLongFamily g) ((a + b) / 2) ((b - a) + 2 * U) U :=
  (literalFactoredTypeDCell_le_postCauchyTypeDCell
    q M N beta g hab hU).trans
      (postCauchyTypeDCell_le_two_characterPairMixedMass
        q M N beta g hab hU)

/-! ## Blockwise source family -/

/-- Character-pair mixed mass for every dyadic complementary block. -/
def blockwiseCharacterPairMixedMass
    {b q M : ℕ} (length : Fin b → ℕ)
    (beta : Fin q → ℕ → ℂ)
    (g : Fin b → Fin q → ℕ → ℂ)
    (t₀ T U : ℝ) : ℝ :=
  ∑ i : Fin b,
    characterPairMixedMass q M (length i)
      (pairShortFamily beta) (pairLongFamily (g i)) t₀ T U

/-- A termwise bound on the dyadic blocks sums without any additional
analytic loss. -/
theorem blockwiseCharacterPairMixedMass_le
    {b q M : ℕ} {length : Fin b → ℕ}
    {beta : Fin q → ℕ → ℂ} {g : Fin b → Fin q → ℕ → ℂ}
    {t₀ T U : ℝ} {bound : Fin b → ℝ}
    (hbound : ∀ i,
      characterPairMixedMass q M (length i)
        (pairShortFamily beta) (pairLongFamily (g i)) t₀ T U ≤ bound i) :
    blockwiseCharacterPairMixedMass (M := M) length beta g t₀ T U ≤
      ∑ i, bound i := by
  exact Finset.sum_le_sum fun i _ ↦ hbound i

end
end MAPFarAnnulusSourceToModel

#print axioms MAPFarAnnulusSourceToModel.mellinPhase_mul
#print axioms MAPFarAnnulusSourceToModel.pairProductPolynomial_eq_mul_dirichletPoly
#print axioms MAPFarAnnulusSourceToModel.dirichletPoly_eq_sum_longFactors
#print axioms MAPFarAnnulusSourceToModel.pairProductPolynomial_eq_short_mul_sum_longFactors
#print axioms MAPFarAnnulusSourceToModel.pairFamilies_coefficientBounds
#print axioms MAPFarAnnulusSourceToModel.movingWindowSweep_le_two_mul
#print axioms MAPFarAnnulusSourceToModel.postCauchyTypeDCell_le_two_characterPairMixedMass
#print axioms MAPFarAnnulusSourceToModel.intervalIntegral_mul_sq_le
#print axioms MAPFarAnnulusSourceToModel.literalFactoredTypeDCell_le_postCauchyTypeDCell
#print axioms MAPFarAnnulusSourceToModel.literalFactoredTypeDCell_le_two_characterPairMixedMass
#print axioms MAPFarAnnulusSourceToModel.blockwiseCharacterPairMixedMass_le
