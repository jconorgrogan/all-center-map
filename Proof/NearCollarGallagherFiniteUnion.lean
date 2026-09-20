import NearCollarGallagher

/-!
# Finite rational-collar reduction for the Gallagher branch

This file removes the finite-union part from
`MAPNearCollarGallagher.NearCollarGallagherTransfer`.  The remaining premise is
per reduced rational `a/q`; it no longer assumes the desired estimate on the
whole union of collars.
-/

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Metric Set
open scoped BigOperators ENNReal ArithmeticFunction

noncomputable section

open APFoundation PrimePairEndpoints MAPHarmonicEndpoint
open MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer
open MAPMajorArcWeld

/-- The finite set of reduced pairs indexing the paper's collars.  The second
ambient range is deliberately `range N`; the filter retains the literal
condition `a < q`. -/
def reducedRationalPairs (X : ℝ) (B : ℕ) : Finset (ℕ × ℕ) :=
  let N := ⌊collarQ X B⌋₊
  ((Finset.Icc 1 N).product (Finset.range N)).filter fun qa ↦
    qa.2 < qa.1 ∧ qa.2.Coprime qa.1

/-- One closed collar, with exactly the radius in manuscript (3.2). -/
def rationalCollar (epsilon X : ℝ) (Cc : ℕ) (qa : ℕ × ℕ) :
    Set UnitAddCircle :=
  Metric.closedBall (rationalCenter qa.1 qa.2)
    (4 * collarR X Cc / baseAperture epsilon X)

theorem mem_reducedRationalPairs_iff
    {X : ℝ} {B : ℕ} {q a : ℕ} :
    (q, a) ∈ reducedRationalPairs X B ↔
      1 ≤ q ∧ q ≤ ⌊collarQ X B⌋₊ ∧ a < q ∧ a.Coprime q := by
  simp [reducedRationalPairs]
  omega

/-- The existential collar definition is literally a finite union. -/
theorem outerRationalCollars_eq_biUnion_reducedRationalPairs
    {epsilon X : ℝ} {B Cc : ℕ} (hQ : 0 ≤ collarQ X B) :
    outerRationalCollars epsilon X B Cc =
      ⋃ qa ∈ (reducedRationalPairs X B : Set (ℕ × ℕ)),
        rationalCollar epsilon X Cc qa := by
  ext alpha
  constructor
  · rintro ⟨q, a, hq1, hqQ, haq, hcop, hdist⟩
    have hqN : q ≤ ⌊collarQ X B⌋₊ := Nat.le_floor hqQ
    have hp : (q, a) ∈ reducedRationalPairs X B :=
      (mem_reducedRationalPairs_iff).2 ⟨hq1, hqN, haq, hcop⟩
    refine Set.mem_iUnion.2 ⟨(q, a), Set.mem_iUnion.2 ⟨hp, ?_⟩⟩
    simpa [rationalCollar, Metric.mem_closedBall] using hdist
  · rintro halpha
    rcases Set.mem_iUnion.1 halpha with ⟨qa, halpha⟩
    rcases Set.mem_iUnion.1 halpha with ⟨hqa, halpha⟩
    rcases (mem_reducedRationalPairs_iff).1 hqa with
      ⟨hq1, hqN, haq, hcop⟩
    refine ⟨qa.1, qa.2, hq1, ?_, haq, hcop, ?_⟩
    · exact (Nat.cast_le.mpr hqN).trans (Nat.floor_le hQ)
    · simpa [rationalCollar, Metric.mem_closedBall] using halpha

/-- The paper's `4R/H_*` collar is exactly the closed ball at Gallagher's
real-line radius `1/(8y)`. -/
theorem rationalCollar_eq_gallagherBall
    {epsilon X : ℝ} (Cc : ℕ) (qa : ℕ × ℕ)
    (hX : 0 < X) (hlog : 0 < Real.log X) :
    rationalCollar epsilon X Cc qa =
      Metric.closedBall (rationalCenter qa.1 qa.2)
        (1 / (8 * gallagherWindow epsilon X Cc)) := by
  unfold rationalCollar
  rw [outerRadius_eq_inv_eight_window Cc hX hlog]

/-- Mathlib's fundamental-domain theorem, specialized to the probability
Haar normalization used by the paper.  This removes the global real-line to
`UnitAddCircle` transfer as an analytic premise. -/
theorem integral_Ioc_unitAddCircle_eq_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : UnitAddCircle → E) :
    (∫ beta in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        F (beta : UnitAddCircle)) =
      ∫ alpha : UnitAddCircle, F alpha ∂AddCircle.haarAddCircle := by
  have hpre := UnitAddCircle.integral_preimage (-(1 / 2 : ℝ)) F
  have hhaar := AddCircle.integral_haarAddCircle
    (T := (1 : ℝ)) (f := F)
  norm_num at hpre hhaar
  exact hpre.trans hhaar.symm

/-! ## Literal signed measure at one reduced rational -/

/-- Fourier transform of the paper's signed measure
`ν_{q,a} = Σ Λ(n)e(an/q)δ_n - (μ(q)/φ(q))1_(X,2X] dt`.
The continuous amplitude already carries the `e(βt)` sign. -/
def signedFourierDiscrepancy
    (X : ℝ) (q a : ℕ) (beta : ℝ) : ℂ :=
  primeExponentialSum X
      (rationalCenter q a + (beta : UnitAddCircle)) -
    primeMajorCoefficient q * dyadicContinuousAmplitude X beta

/-- Lebesgue length of `(x,x+y] ∩ (X,2X]`.  Half-open endpoint choices do
not alter the continuous measure, while the atomic term below retains them. -/
def dyadicContinuousWindowLength (X x y : ℝ) : ℝ :=
  max 0 (min (2 * X) (x + y) - max X x)

theorem dyadicContinuousWindowLength_nonneg (X x y : ℝ) :
    0 ≤ dyadicContinuousWindowLength X x y := by
  exact le_max_left _ _

/-- Atomic evaluation of the first term of `ν_{q,a}` on `(x,x+y]`, with
the dyadic support and both endpoint conventions literal. -/
def twistedPrimeSlidingWindow
    (X : ℝ) (q a : ℕ) (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    if x < (n : ℝ) ∧ (n : ℝ) ≤ x + y then
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        fourier (n : ℤ) (rationalCenter q a)
    else 0

/-- Literal evaluation `ν_{q,a}((x,x+y])`. -/
def signedSlidingDiscrepancy
    (X : ℝ) (q a : ℕ) (x y : ℝ) : ℂ :=
  twistedPrimeSlidingWindow X q a x y -
    primeMajorCoefficient q * dyadicContinuousWindowLength X x y

/-- Exact first harmonic theorem still absent from mathlib.  It is strictly
below the per-rational four-term estimate: no AP theorem, residue-class
decomposition, endpoint estimate, bad-prime-power estimate, collar union, or
continuous tail has been inserted.

The nonnegative arithmetic-scale premise is essential.  Without it, the
oriented continuous Fourier interval and the unoriented overlap-length model
disagree (the concrete case `X = -1`, `y = 1`, `q = 1`, `a = 0` is a formal
counterexample to the former unrestricted statement). -/
def SignedMeasureGallagherInequality : Prop :=
  ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (X y : ℝ) (q a : ℕ), 0 ≤ X → 0 < y →
      (∫ beta in Set.Icc (-(1 / (8 * y))) (1 / (8 * y)),
          ‖signedFourierDiscrepancy X q a beta‖ ^ 2) ≤
        Cg / y ^ 2 *
          ∫ x : ℝ, ‖signedSlidingDiscrepancy X q a x y‖ ^ 2

theorem card_reducedRationalPairs_le_floor_sq (X : ℝ) (B : ℕ) :
    (reducedRationalPairs X B).card ≤ ⌊collarQ X B⌋₊ ^ 2 := by
  unfold reducedRationalPairs
  exact (Finset.card_filter_le _ _).trans_eq (by simp [pow_two])

theorem sum_first_sq_reducedRationalPairs_le_floor_four
    (X : ℝ) (B : ℕ) :
    ∑ qa ∈ reducedRationalPairs X B, qa.1 ^ 2 ≤ ⌊collarQ X B⌋₊ ^ 4 := by
  let N := ⌊collarQ X B⌋₊
  have hpoint : ∀ qa ∈ reducedRationalPairs X B, qa.1 ^ 2 ≤ N ^ 2 := by
    intro qa hqa
    have hqN : qa.1 ≤ N := (mem_reducedRationalPairs_iff).1 hqa |>.2.1
    exact Nat.pow_le_pow_left hqN 2
  have hsum := Finset.sum_le_card_nsmul
    (reducedRationalPairs X B) (fun qa ↦ qa.1 ^ 2) (N ^ 2) hpoint
  have hcard : (reducedRationalPairs X B).card ≤ N ^ 2 := by
    simpa [N] using card_reducedRationalPairs_le_floor_sq X B
  calc
    ∑ qa ∈ reducedRationalPairs X B, qa.1 ^ 2 ≤
        (reducedRationalPairs X B).card * N ^ 2 := by
      simpa [nsmul_eq_mul] using hsum
    _ ≤ N ^ 2 * N ^ 2 := Nat.mul_le_mul_right _ hcard
    _ = N ^ 4 := by ring

theorem card_reducedRationalPairs_cast_le_collarQ_sq
    {X : ℝ} {B : ℕ} (hQ : 0 ≤ collarQ X B) :
    ((reducedRationalPairs X B).card : ℝ) ≤ collarQ X B ^ 2 := by
  have hcard := card_reducedRationalPairs_le_floor_sq X B
  have hfloor : (⌊collarQ X B⌋₊ : ℝ) ≤ collarQ X B := Nat.floor_le hQ
  calc
    ((reducedRationalPairs X B).card : ℝ) ≤
        ((⌊collarQ X B⌋₊ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (⌊collarQ X B⌋₊ : ℝ) ^ 2 := by norm_num
    _ ≤ collarQ X B ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 2

theorem sum_first_sq_reducedRationalPairs_cast_le_collarQ_four
    {X : ℝ} {B : ℕ} (hQ : 0 ≤ collarQ X B) :
    ∑ qa ∈ reducedRationalPairs X B, (qa.1 : ℝ) ^ 2 ≤
      collarQ X B ^ 4 := by
  have hsum := sum_first_sq_reducedRationalPairs_le_floor_four X B
  have hfloor : (⌊collarQ X B⌋₊ : ℝ) ≤ collarQ X B := Nat.floor_le hQ
  calc
    ∑ qa ∈ reducedRationalPairs X B, (qa.1 : ℝ) ^ 2 =
        ((∑ qa ∈ reducedRationalPairs X B, qa.1 ^ 2 : ℕ) : ℝ) := by
      norm_num
    _ ≤ ((⌊collarQ X B⌋₊ ^ 4 : ℕ) : ℝ) := by exact_mod_cast hsum
    _ = (⌊collarQ X B⌋₊ : ℝ) ^ 4 := by norm_num
    _ ≤ collarQ X B ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 4

/-- Restriction to a finite union is dominated by the sum of the restricted
measures.  No disjointness or measurability of the sets is required. -/
theorem restrict_biUnion_finset_le_sum
    {alpha iota : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (s : Finset iota) (t : iota → Set alpha) :
    mu.restrict (⋃ i ∈ (s : Set iota), t i) ≤
      ∑ i ∈ s, mu.restrict (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hset :
          (⋃ i ∈ ((insert a s : Finset iota) : Set iota), t i) =
            t a ∪ (⋃ i ∈ (s : Set iota), t i) := by
        ext x
        simp
      rw [hset, Finset.sum_insert ha]
      exact (Measure.restrict_union_le _ _).trans (add_le_add_right ih _)

/-- A nonnegative integrable density on a finite union costs at most the sum
of its masses on the individual sets. -/
theorem setIntegral_biUnion_finset_le_sum
    {alpha iota : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f : alpha → ℝ}
    (hf : Integrable f mu) (hfnn : ∀ x, 0 ≤ f x)
    (s : Finset iota) (t : iota → Set alpha) :
    (∫ x in ⋃ i ∈ (s : Set iota), t i, f x ∂mu) ≤
      ∑ i ∈ s, ∫ x in t i, f x ∂mu := by
  classical
  let nu : iota → Measure alpha := fun i ↦ mu.restrict (t i)
  have hfi : ∀ i ∈ s, Integrable f (nu i) := by
    intro i hi
    exact hf.mono_measure Measure.restrict_le_self
  have hsum : Integrable f (∑ i ∈ s, nu i) :=
    (integrable_finsetSum_measure).2 hfi
  have hmono := integral_mono_measure
    (restrict_biUnion_finset_le_sum mu s t)
    (Filter.Eventually.of_forall hfnn) hsum
  rw [integral_finsetSum_measure hfi] at hmono
  exact hmono

/-- The four contributions before summing reduced numerators and moduli.  The
factor `q^2` occurs only on the AP-maximal term, exactly as in the manuscript's
per-rational Gallagher estimate. -/
def perRationalFourTermRHS
    (q B D Cc : ℕ) (epsilon epsilonAP X : ℝ) : ℝ :=
  (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
    gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
    (Real.log X) ^ 4 / gallagherWindow epsilon X Cc +
    X / collarP X D

/-- The remaining analytic theorem after removing the finite collar union.
It is local to one literal reduced rational `a/q`; in particular, it does not
assume any estimate on `outerRationalCollars`. -/
def PerRationalNearCollarTransfer : Prop :=
  ∃ Cg Xg : ℝ, 0 < Cg ∧ 2 ≤ Xg ∧
    ∀ (epsilon epsilonAP X : ℝ) (B D Cc q a : ℕ),
      0 < epsilon → 0 < epsilonAP → Xg ≤ X →
      2 ≤ Real.log X →
      Real.rpow X (2 / 15 + epsilonAP) ≤
        gallagherWindow epsilon X Cc →
      1 ≤ gallagherWindow epsilon X Cc →
      gallagherWindow epsilon X Cc ≤ X / 2 →
      collarP X D / X ≤ 1 / (8 * gallagherWindow epsilon X Cc) →
      1 ≤ q → (q : ℝ) ≤ collarQ X B →
      a < q → a.Coprime q →
      (∫ alpha in rationalCollar epsilon X Cc (q, a) ∩ minorArcs X B D,
          ‖primeExponentialSum X alpha‖ ^ 2
            ∂AddCircle.haarAddCircle) ≤
        Cg * perRationalFourTermRHS q B D Cc epsilon epsilonAP X

/-- The exact finite-union and `Q^4/Q^2` bookkeeping.  Thus a proof of the
one-rational analytic estimate inhabits the original global transfer leaf. -/
theorem nearCollarGallagherTransfer_of_perRational
    (hper : PerRationalNearCollarTransfer) :
    NearCollarGallagherTransfer := by
  obtain ⟨Cg, Xg, hCg, hXg, hper⟩ := hper
  refine ⟨Cg, Xg, hCg, hXg, ?_⟩
  intro epsilon epsilonAP X B D Cc hepsilon hepsilonAP hXXg hlog
    hwindowLegal hwindowOne hwindowHalf htail
  have hlogpos : 0 < Real.log X := by linarith
  have hXpos : 0 < X := by linarith [hXg.trans hXXg]
  have hQ : 0 ≤ collarQ X B := by
    unfold collarQ
    positivity
  have hP : 0 < collarP X D := by
    unfold collarP
    positivity
  have hy : 0 < gallagherWindow epsilon X Cc :=
    gallagherWindow_pos Cc hXpos hlogpos
  let pairs := reducedRationalPairs X B
  let f : UnitAddCircle → ℝ := fun alpha ↦
    ‖primeExponentialSum X alpha‖ ^ 2
  let arcs : ℕ × ℕ → Set UnitAddCircle := fun qa ↦
    rationalCollar epsilon X Cc qa ∩ minorArcs X B D
  have hset :
      outerRationalCollars epsilon X B Cc ∩ minorArcs X B D =
        ⋃ qa ∈ (pairs : Set (ℕ × ℕ)), arcs qa := by
    rw [outerRationalCollars_eq_biUnion_reducedRationalPairs hQ]
    ext alpha
    simp only [Set.mem_inter_iff, Set.mem_iUnion, pairs, arcs]
    constructor
    · rintro ⟨⟨qa, hqa, halpha⟩, hminor⟩
      exact ⟨qa, hqa, halpha, hminor⟩
    · rintro ⟨qa, hqa, halpha, hminor⟩
      exact ⟨⟨qa, hqa, halpha⟩, hminor⟩
  rw [hset]
  have hfinite :
      (∫ alpha in ⋃ qa ∈ (pairs : Set (ℕ × ℕ)), arcs qa,
          f alpha ∂AddCircle.haarAddCircle) ≤
        ∑ qa ∈ pairs,
          ∫ alpha in arcs qa, f alpha ∂AddCircle.haarAddCircle := by
    exact setIntegral_biUnion_finset_le_sum
      (normSq_primeExponentialSum_integrable X)
      (fun _ ↦ sq_nonneg _) pairs arcs
  calc
    (∫ alpha in ⋃ qa ∈ (pairs : Set (ℕ × ℕ)), arcs qa,
        f alpha ∂AddCircle.haarAddCircle) ≤
        ∑ qa ∈ pairs,
          ∫ alpha in arcs qa, f alpha ∂AddCircle.haarAddCircle := hfinite
    _ ≤ ∑ qa ∈ pairs,
        Cg * perRationalFourTermRHS qa.1 B D Cc epsilon epsilonAP X := by
      apply Finset.sum_le_sum
      intro qa hqa
      rcases (mem_reducedRationalPairs_iff).1 hqa with
        ⟨hq1, hqfloor, haq, hcop⟩
      have hqQ : (qa.1 : ℝ) ≤ collarQ X B :=
        (Nat.cast_le.mpr hqfloor).trans (Nat.floor_le hQ)
      exact hper epsilon epsilonAP X B D Cc qa.1 qa.2
        hepsilon hepsilonAP hXXg hlog hwindowLegal hwindowOne hwindowHalf
        htail hq1 hqQ haq hcop
    _ ≤ Cg * nearFourTermRHS B D Cc epsilon epsilonAP X := by
      have hcard := card_reducedRationalPairs_cast_le_collarQ_sq hQ
      have hmoment :=
        sum_first_sq_reducedRationalPairs_cast_le_collarQ_four hQ
      have hap : 0 ≤ (apMaxIntegral B epsilonAP X).toReal := ENNReal.toReal_nonneg
      have hcommon :
          0 ≤ gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
              (Real.log X) ^ 4 / gallagherWindow epsilon X Cc +
              X / collarP X D := by positivity
      unfold nearFourTermRHS perRationalFourTermRHS
      dsimp only
      rw [← Finset.mul_sum]
      have hsumIdentity :
          ∑ qa ∈ pairs,
              ((qa.1 : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
                gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
                (Real.log X) ^ 4 / gallagherWindow epsilon X Cc +
                X / collarP X D) =
            (apMaxIntegral B epsilonAP X).toReal *
                (∑ qa ∈ pairs, (qa.1 : ℝ) ^ 2) +
              (pairs.card : ℝ) *
                (gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
                  (Real.log X) ^ 4 / gallagherWindow epsilon X Cc +
                  X / collarP X D) := by
        simp [Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
        ring
      rw [hsumIdentity]
      apply mul_le_mul_of_nonneg_left _ hCg.le
      calc
        (apMaxIntegral B epsilonAP X).toReal *
              (∑ qa ∈ pairs, (qa.1 : ℝ) ^ 2) +
            (pairs.card : ℝ) *
              (gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
                (Real.log X) ^ 4 / gallagherWindow epsilon X Cc +
                X / collarP X D) ≤
          (apMaxIntegral B epsilonAP X).toReal * collarQ X B ^ 4 +
            collarQ X B ^ 2 *
              (gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
                (Real.log X) ^ 4 / gallagherWindow epsilon X Cc +
                X / collarP X D) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (by simpa [pairs] using hmoment) hap)
            (mul_le_mul_of_nonneg_right (by simpa [pairs] using hcard) hcommon)
        _ = collarQ X B ^ 4 * (apMaxIntegral B epsilonAP X).toReal +
              collarQ X B ^ 2 * gallagherWindow epsilon X Cc *
                (Real.log X) ^ 2 +
              collarQ X B ^ 2 * (Real.log X) ^ 4 /
                gallagherWindow epsilon X Cc +
              X * collarQ X B ^ 2 / collarP X D := by ring

end
end MAPNearCollarGallagher

#print axioms MAPNearCollarGallagher.integral_Ioc_unitAddCircle_eq_haar
#print axioms MAPNearCollarGallagher.setIntegral_biUnion_finset_le_sum
#print axioms MAPNearCollarGallagher.nearCollarGallagherTransfer_of_perRational
