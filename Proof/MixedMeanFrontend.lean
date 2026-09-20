import DeterminantCountWeld

/-!
# Finite mixed-mean front end

This file keeps the continuous integrals literal.  It develops the exact
finite expansion and records the two independent Fourier moments before any
arithmetic estimate is invoked.
-/

noncomputable section

namespace MixedMeanFrontend

open MeasureTheory
open DeterminantCountWeld

/-- The Mellin phase `n^{-it}`.  At `n = 0` this is still a harmless total
function; all applications below restrict `n` to a positive dyadic box. -/
def mellinPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)

/-- A finite Dirichlet polynomial with an arbitrary pointwise coefficient
mask and a literal finite support. -/
def dirichletPoly (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * mellinPhase n t

/-- The short factor on `(M,2M]`. -/
def shortFactor (M : ℕ) (β : ℕ → ℂ) (t : ℝ) : ℂ :=
  dirichletPoly (dyadic M) β t

/-- The long factor on `(N,2N]`. -/
def longFactor (N : ℕ) (g : ℕ → ℂ) (t : ℝ) : ℂ :=
  dirichletPoly (dyadic N) g t

/-- Complex form of the nonnegative energy `|z|²`. -/
def energy (z : ℂ) : ℂ := z * star z

/-- The literal continuous mixed mean over the translated `t` window and the
independent `u` window.  No quadrature or finite proxy is used. -/
def literalMixedMean (M N : ℕ) (β g : ℕ → ℂ)
    (t₀ T U : ℝ) : ℂ :=
  ∫ t in (t₀ - T / 2)..(t₀ + T / 2),
    energy (longFactor N g t) *
      (∫ u in (-2 * U)..(2 * U), energy (shortFactor M β (t + u)))

/-- A coefficient pair from an exact square expansion. -/
def pairTerm (a : ℕ → ℂ) (i j : ℕ) (t : ℝ) : ℂ :=
  (a i * mellinPhase i t) * star (a j * mellinPhase j t)

/-- A pair term is a pointwise coefficient times one Mellin frequency. -/
theorem pairTerm_frequency_form (a : ℕ → ℂ) (i j : ℕ) (t : ℝ) :
    pairTerm a i j t =
      (a i * star (a j)) *
        Complex.exp
          ((((t * (Real.log j - Real.log i) : ℝ) : ℂ) * Complex.I)) := by
  simp only [pairTerm, mellinPhase, star_mul]
  have hj :
      star (Complex.exp (-((t * Real.log j : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (((t * Real.log j : ℝ) : ℂ) * Complex.I) := by
    change (starRingEnd ℂ)
      (Complex.exp (-((t * Real.log j : ℝ) : ℂ) * Complex.I)) = _
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hj]
  let x : ℂ := -((t * Real.log i : ℝ) : ℂ) * Complex.I
  let y : ℂ := ((t * Real.log j : ℝ) : ℂ) * Complex.I
  calc
    _ = (a i * star (a j)) * (Complex.exp x * Complex.exp y) := by
          simp only [x, y]
          ring
    _ = (a i * star (a j)) * Complex.exp (x + y) := by rw [Complex.exp_add]
    _ = _ := by
      simp only [x, y]
      congr 2
      push_cast
      ring

/-- A literal four-index term of the mixed square expansion. -/
def tupleTerm (β g : ℕ → ℂ) (q : LiteralTuple) (t u : ℝ) : ℂ :=
  pairTerm g q.2.1 q.2.2 t * pairTerm β q.1.1 q.1.2 (t + u)

/-- The full dyadic four-index box, before either Fourier constraint. -/
def dyadicTupleBox (M N : ℕ) : Finset LiteralTuple :=
  ((dyadic M).product (dyadic M)).product
    ((dyadic N).product (dyadic N))

theorem energy_dirichletPoly_expansion (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    energy (dirichletPoly s a t) =
      ∑ i ∈ s, ∑ j ∈ s, pairTerm a i j t := by
  exact MixedMellinCert.finite_square_expansion s (fun n ↦ a n * mellinPhase n t)

theorem mixed_integrand_expansion (M N : ℕ) (β g : ℕ → ℂ) (t u : ℝ) :
    energy (longFactor N g t) * energy (shortFactor M β (t + u)) =
      ∑ q ∈ dyadicTupleBox M N, tupleTerm β g q t u := by
  calc
    _ = (∑ n ∈ (dyadic N).product (dyadic N),
          pairTerm g n.1 n.2 t) *
        (∑ m ∈ (dyadic M).product (dyadic M),
          pairTerm β m.1 m.2 (t + u)) := by
            rw [longFactor, shortFactor,
              energy_dirichletPoly_expansion,
              energy_dirichletPoly_expansion]
            congr 1
            · exact (Finset.sum_product (dyadic N) (dyadic N)
                (fun n : ℕ × ℕ ↦ pairTerm g n.1 n.2 t)).symm
            · exact (Finset.sum_product (dyadic M) (dyadic M)
                (fun m : ℕ × ℕ ↦ pairTerm β m.1 m.2 (t + u))).symm
    _ = (∑ m ∈ (dyadic M).product (dyadic M),
          pairTerm β m.1 m.2 (t + u)) *
        (∑ n ∈ (dyadic N).product (dyadic N),
          pairTerm g n.1 n.2 t) := mul_comm _ _
    _ = ∑ m ∈ (dyadic M).product (dyadic M),
          ∑ n ∈ (dyadic N).product (dyadic N),
            pairTerm β m.1 m.2 (t + u) * pairTerm g n.1 n.2 t := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mul_sum]
    _ = ∑ q ∈ dyadicTupleBox M N, tupleTerm β g q t u := by
          symm
          calc
            _ = ∑ m ∈ (dyadic M).product (dyadic M),
                ∑ n ∈ (dyadic N).product (dyadic N),
                  tupleTerm β g (m, n) t u :=
              Finset.sum_product _ _ _
            _ = _ := by
              apply Finset.sum_congr rfl
              intro m hm
              apply Finset.sum_congr rfl
              intro n hn
              simp only [tupleTerm]
              rw [mul_comm]

/-- The literal iterated integral is exactly the iterated integral of the
four-index square expansion.  In particular, the continuous integral has not
been replaced by a quadrature rule or by a finite proxy. -/
theorem literalMixedMean_eq_integral_tupleSum
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ T U : ℝ) :
    literalMixedMean M N β g t₀ T U =
      ∫ t in (t₀ - T / 2)..(t₀ + T / 2),
        ∫ u in (-2 * U)..(2 * U),
          ∑ q ∈ dyadicTupleBox M N, tupleTerm β g q t u := by
  unfold literalMixedMean
  apply intervalIntegral.integral_congr
  intro t ht
  change
    energy (longFactor N g t) *
        (∫ u in (-2 * U)..(2 * U), energy (shortFactor M β (t + u))) =
      ∫ u in (-2 * U)..(2 * U),
        ∑ q ∈ dyadicTupleBox M N, tupleTerm β g q t u
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  exact mixed_integrand_expansion M N β g t u

/-- The frequency seen by the independent `u` clock. -/
def shortFrequency (q : LiteralTuple) : ℝ :=
  Real.log q.1.2 - Real.log q.1.1

/-- The frequency seen by the `t` clock.  It is deliberately written as the
sum of the short and long logarithmic differences, so the two clocks stay
syntactically distinct. -/
def jointFrequency (q : LiteralTuple) : ℝ :=
  shortFrequency q + (Real.log q.2.2 - Real.log q.2.1)

/-- The four pointwise coefficient masks, with their phases untouched. -/
def tupleCoefficient (β g : ℕ → ℂ) (q : LiteralTuple) : ℂ :=
  (g q.2.1 * star (g q.2.2)) *
    (β q.1.1 * star (β q.1.2))

/-- Exact separation of the two clocks on every expanded tuple.  The `u`
coefficient is `shortFrequency`; the `t` coefficient is independently
`jointFrequency`. -/
theorem tupleTerm_frequency_form (β g : ℕ → ℂ)
    (q : LiteralTuple) (t u : ℝ) :
    tupleTerm β g q t u =
      tupleCoefficient β g q *
        Complex.exp
          (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
            Complex.I) := by
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  rw [tupleTerm, pairTerm_frequency_form, pairTerm_frequency_form]
  let x : ℂ :=
    (((t * (Real.log n₂ - Real.log n₁) : ℝ) : ℂ) * Complex.I)
  let y : ℂ :=
    ((((t + u) * (Real.log m₂ - Real.log m₁) : ℝ) : ℂ) * Complex.I)
  calc
    _ = tupleCoefficient β g ((m₁, m₂), (n₁, n₂)) *
        (Complex.exp x * Complex.exp y) := by
          simp only [tupleCoefficient, x, y]
          ring
    _ = tupleCoefficient β g ((m₁, m₂), (n₁, n₂)) *
        Complex.exp (x + y) := by rw [Complex.exp_add]
    _ = _ := by
      simp only [x, y, jointFrequency, shortFrequency]
      congr 2
      push_cast
      ring

/-- The literal dyadic tuple set surviving both pointwise Fourier masks. -/
def frequencyTuples (M N : ℕ) (shortBand jointBand : ℝ) : Finset LiteralTuple :=
  (dyadicTupleBox M N).filter fun q ↦
    |shortFrequency q| ≤ shortBand ∧ |jointFrequency q| ≤ jointBand

/-- Equal-short-index tuples are retained as their own sector. -/
def equalShortFrequencySector (M N : ℕ) (shortBand jointBand : ℝ) :
    Finset LiteralTuple :=
  (frequencyTuples M N shortBand jointBand).filter fun q ↦ q.1.1 = q.1.2

/-- Unequal-short-index, positive-determinant survivor sector. -/
def positiveFrequencySector (M N : ℕ) (shortBand jointBand : ℝ) :
    Finset LiteralTuple :=
  (frequencyTuples M N shortBand jointBand).filter fun q ↦
    q.1.1 ≠ q.1.2 ∧ 0 < determinant q

/-- Unequal-short-index, negative-determinant survivor sector. -/
def negativeFrequencySector (M N : ℕ) (shortBand jointBand : ℝ) :
    Finset LiteralTuple :=
  (frequencyTuples M N shortBand jointBand).filter fun q ↦
    q.1.1 ≠ q.1.2 ∧ determinant q < 0

/-- Unequal-short-index, zero-determinant survivor sector. -/
def zeroFrequencySector (M N : ℕ) (shortBand jointBand : ℝ) :
    Finset LiteralTuple :=
  (frequencyTuples M N shortBand jointBand).filter fun q ↦
    q.1.1 ≠ q.1.2 ∧ determinant q = 0

/-- Weighted mass of a literal finite tuple set.  The weight is pointwise and
is not averaged, symmetrized, or replaced by a cardinality. -/
def weightedMass (w : LiteralTuple → ℝ) (s : Finset LiteralTuple) : ℝ :=
  ∑ q ∈ s, w q

/-- Exact sector decomposition of the two-frequency weighted tuple count. -/
theorem weighted_frequency_sector_decomposition
    (w : LiteralTuple → ℝ) (M N : ℕ) (shortBand jointBand : ℝ) :
    weightedMass w (frequencyTuples M N shortBand jointBand) =
      weightedMass w (equalShortFrequencySector M N shortBand jointBand) +
      weightedMass w (positiveFrequencySector M N shortBand jointBand) +
      weightedMass w (negativeFrequencySector M N shortBand jointBand) +
      weightedMass w (zeroFrequencySector M N shortBand jointBand) := by
  classical
  simp only [weightedMass, equalShortFrequencySector, positiveFrequencySector,
    negativeFrequencySector, zeroFrequencySector, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases heq : q.1.1 = q.1.2
  · simp [heq]
  · have hsign : determinant q < 0 ∨ determinant q = 0 ∨ 0 < determinant q :=
      lt_trichotomy (determinant q) 0
    rcases hsign with hneg | hzero | hpos
    · have hnpos : ¬0 < determinant q := not_lt_of_ge hneg.le
      simp [heq, hneg, hneg.ne, hnpos]
    · simp [heq, hzero]
    · have hnneg : ¬determinant q < 0 := not_lt_of_ge hpos.le
      simp [heq, hpos, hpos.ne', hnneg]

/-- The only arithmetic hypothesis intended at the end of this frontend: a
bound for the literal, pointwise-weighted, two-frequency tuple count. -/
def WeightedLiteralTupleCountBound
    (w : LiteralTuple → ℝ) (M N : ℕ) (shortBand jointBand Q : ℝ) : Prop :=
  weightedMass w (frequencyTuples M N shortBand jointBand) ≤ Q

/-- A count bound immediately controls the exact sum of all four determinant
sectors; this is a normalization/partition statement, not Shiu's estimate. -/
theorem sectorized_mass_le_of_weightedLiteralTupleCountBound
    {w : LiteralTuple → ℝ} {M N : ℕ} {shortBand jointBand Q : ℝ}
    (hcount : WeightedLiteralTupleCountBound w M N shortBand jointBand Q) :
    weightedMass w (equalShortFrequencySector M N shortBand jointBand) +
      weightedMass w (positiveFrequencySector M N shortBand jointBand) +
      weightedMass w (negativeFrequencySector M N shortBand jointBand) +
      weightedMass w (zeroFrequencySector M N shortBand jointBand) ≤ Q := by
  rw [← weighted_frequency_sector_decomposition]
  exact hcount

end MixedMeanFrontend

#print axioms MixedMeanFrontend.literalMixedMean_eq_integral_tupleSum
#print axioms MixedMeanFrontend.tupleTerm_frequency_form
#print axioms MixedMeanFrontend.weighted_frequency_sector_decomposition
#print axioms MixedMeanFrontend.sectorized_mass_le_of_weightedLiteralTupleCountBound
