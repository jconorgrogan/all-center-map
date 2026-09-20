import GuthMaynardProposition46Consumer
import GuthMaynardProposition46RawTrace
import GuthMaynardLemma44TraceOne
import GuthMaynardProposition46MainCancellation

/-!
# Proposition 4.6: Poisson trace and sector consumer

The matrix inequality is now connected to the literal Poisson main terms and
the exact infinite S1/S2/S3 quantities.  All remainder terms are explicit.
-/

namespace GuthMaynardProposition46SectorConsumer

open GuthMaynardSectionFourTrace GuthMaynardEquation55Infinite
open GuthMaynardProposition46RawTrace GuthMaynardLemma44TraceOne
open GuthMaynardProposition46MainCancellation GuthMaynardProposition46Consumer
open GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardJIteration
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

def sourceTraceCubePoissonError
    (N : ℕ) (W : Finset ℝ) (R : ℝ) (j : ℕ) : ℝ :=
  (N : ℝ) ^ 3 *
    ((W.card : ℝ) ^ 3 *
        ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0 ^ 2) +
      (W.card : ℝ) ^ 3 *
        (lemma43DerivativeConstant 0 *
          (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0))

def sourceTraceOnePoissonError
    (N : ℕ) (W : Finset ℝ) (q : ℕ) : ℝ :=
  (W.card : ℝ) * lemma43DerivativeConstant (q + 2) *
    (2 ^ (q + 2) * integerQuadraticMass) *
      ((N : ℝ) / (N : ℝ) ^ (q + 2))

def sourceTraceMainOne (N : ℕ) (W : Finset ℝ) : ℂ :=
  (N : ℂ) * (W.card : ℂ) * sourceHhat 0 0

def sourceTraceMainCube (N : ℕ) (W : Finset ℝ) : ℂ :=
  (N : ℂ) ^ 3 * (W.card : ℂ) * sourceHhat 0 0 ^ 3

def sourceTraceCubeDefectBudget
    (N : ℕ) (W : Finset ℝ) (R : ℝ) (j q : ℕ) : ℝ :=
  sourceTraceCubePoissonError N W R j +
    (‖sourceS1 N W‖ + ‖sourceS2 N W‖ + ‖sourceS3 N W‖) +
    sourceTraceOnePoissonError N W q *
      ((sourceTraceMainOne N W).re ^ 2 +
        |(sourceTraceMainOne N W).re * (sourceTraceOne W N).re| +
        (sourceTraceOne W N).re ^ 2) / (W.card : ℝ) ^ 2

def sourceTraceAverageBudget (N : ℕ) (W : Finset ℝ) (q : ℕ) : ℝ :=
  (N : ℝ) * lemma43DerivativeConstant 0 +
    sourceTraceOnePoissonError N W q / (W.card : ℝ)

private theorem re_sub_le_norm (z w : ℂ) : z.re - w.re ≤ ‖z - w‖ := by
  rw [← Complex.sub_re]
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

private theorem re_le_norm (z : ℂ) : z.re ≤ ‖z‖ := by
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

private theorem cube_difference_abs_le
    (x y E : ℝ) (hxy : |x - y| ≤ E) :
    |x ^ 3 - y ^ 3| ≤ E * (x ^ 2 + |x * y| + y ^ 2) := by
  rw [show x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) by ring,
    abs_mul]
  calc
    |x - y| * |x ^ 2 + x * y + y ^ 2| ≤
        E * |x ^ 2 + x * y + y ^ 2| := by
          gcongr
    _ ≤ E * (x ^ 2 + |x * y| + y ^ 2) := by
      have hE : 0 ≤ E := (abs_nonneg _).trans hxy
      gcongr
      calc
        |x ^ 2 + x * y + y ^ 2| ≤ |x ^ 2| + |x * y| + |y ^ 2| := by
          have h₁ := abs_add_le (x ^ 2 + x * y) (y ^ 2)
          have h₂ := abs_add_le (x ^ 2) (x * y)
          linarith
        _ = x ^ 2 + |x * y| + y ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg x), abs_of_nonneg (sq_nonneg y)]

/-- Pure real/complex cancellation ledger behind Proposition 4.6. -/
theorem trace_defect_le_of_main_approximations
    {C T M3 M1 S1 S2 S3 : ℂ} {E3 E1 r : ℝ}
    (hr : 0 < r)
    (hC : ‖C - (M3 + (S1 + S2 + S3))‖ ≤ E3)
    (hT : ‖T - M1‖ ≤ E1) :
    C.re - T.re ^ 3 / r ^ 2 ≤
      E3 + (‖S1‖ + ‖S2‖ + ‖S3‖) +
        |M3.re - M1.re ^ 3 / r ^ 2| +
        E1 * (M1.re ^ 2 + |M1.re * T.re| + T.re ^ 2) / r ^ 2 := by
  have hC' : C.re - (M3 + (S1 + S2 + S3)).re ≤ E3 :=
    (re_sub_le_norm C (M3 + (S1 + S2 + S3))).trans hC
  have hS1 : S1.re ≤ ‖S1‖ := re_le_norm S1
  have hS2 : S2.re ≤ ‖S2‖ := re_le_norm S2
  have hS3 : S3.re ≤ ‖S3‖ := re_le_norm S3
  have hTnorm : |T.re - M1.re| ≤ E1 := by
    have h := Complex.abs_re_le_norm (T - M1)
    rw [Complex.sub_re] at h
    exact h.trans hT
  have hcube := cube_difference_abs_le M1.re T.re E1 (by
    simpa [abs_sub_comm] using hTnorm)
  have hcubediv : (M1.re ^ 3 - T.re ^ 3) / r ^ 2 ≤
      E1 * (M1.re ^ 2 + |M1.re * T.re| + T.re ^ 2) / r ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg r)
    exact (le_abs_self _).trans hcube
  have hsector : S1.re + S2.re + S3.re ≤ ‖S1‖ + ‖S2‖ + ‖S3‖ := by
    linarith
  have hmismatch : M3.re - M1.re ^ 3 / r ^ 2 ≤
      |M3.re - M1.re ^ 3 / r ^ 2| := le_abs_self _
  have hid : C.re - T.re ^ 3 / r ^ 2 =
      (C.re - (M3.re + (S1.re + S2.re + S3.re))) +
        (S1.re + S2.re + S3.re) +
        (M3.re - M1.re ^ 3 / r ^ 2) +
        ((M1.re ^ 3 - T.re ^ 3) / r ^ 2) := by ring
  rw [hid]
  have hCre : C.re - (M3.re + (S1.re + S2.re + S3.re)) ≤ E3 := by
    simpa using hC'
  linarith

/-- The literal cubic trace defect is bounded by the explicit Poisson errors
and the three exact infinite frequency sectors.  There are no analytic sector
premises in this statement. -/
theorem source_trace_defect_le_sector_budget
    {N : ℕ} {W : Finset ℝ} {R : ℝ}
    (hN : 0 < N) (hW : W.Nonempty) (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (j q : ℕ) :
    (sourceTraceCube W N).re -
        (sourceTraceOne W N).re ^ 3 / (W.card : ℝ) ^ 2 ≤
      sourceTraceCubeDefectBudget N W R j q := by
  have hC := norm_sourceTraceCube_sub_main_and_sectors_le hN hR hsep j
  have hT := norm_sourceTraceOne_sub_main_le hN W q
  have hcancel := source_poisson_main_cancellation (N := N) (W := W) hW
  have h := trace_defect_le_of_main_approximations
    (C := sourceTraceCube W N) (T := sourceTraceOne W N)
    (M3 := sourceTraceMainCube N W) (M1 := sourceTraceMainOne N W)
    (S1 := sourceS1 N W) (S2 := sourceS2 N W) (S3 := sourceS3 N W)
    (E3 := sourceTraceCubePoissonError N W R j)
    (E1 := sourceTraceOnePoissonError N W q) (r := (W.card : ℝ))
    (by exact_mod_cast hW.card_pos) (by simpa [sourceTraceMainCube,
      sourceTraceCubePoissonError] using hC)
    (by simpa [sourceTraceMainOne, sourceTraceOnePoissonError] using hT)
  simpa [sourceTraceCubeDefectBudget, sourceTraceMainCube,
    sourceTraceMainOne, hcancel] using h

theorem source_trace_average_le_budget
    {N : ℕ} {W : Finset ℝ} (hN : 0 < N) (hW : W.Nonempty) (q : ℕ) :
    (sourceTraceOne W N).re / (W.card : ℝ) ≤
      sourceTraceAverageBudget N W q := by
  have hcard : 0 < (W.card : ℝ) := by exact_mod_cast hW.card_pos
  have hT := norm_sourceTraceOne_sub_main_le hN W q
  have hreal : (sourceTraceOne W N).re - (sourceTraceMainOne N W).re ≤
      sourceTraceOnePoissonError N W q := by
    exact (re_sub_le_norm (sourceTraceOne W N) (sourceTraceMainOne N W)).trans
      (by simpa [sourceTraceMainOne, sourceTraceOnePoissonError] using hT)
  have hmain : (sourceTraceMainOne N W).re ≤
      (N : ℝ) * (W.card : ℝ) * lemma43DerivativeConstant 0 := by
    calc
      (sourceTraceMainOne N W).re ≤ ‖sourceTraceMainOne N W‖ := re_le_norm _
      _ = (N : ℝ) * (W.card : ℝ) * ‖sourceHhat 0 0‖ := by
        simp [sourceTraceMainOne, norm_mul]
      _ ≤ (N : ℝ) * (W.card : ℝ) * lemma43DerivativeConstant 0 := by
        gcongr
        exact norm_sourceHhat_le_fixed 0 0
  have htotal : (sourceTraceOne W N).re ≤
      (N : ℝ) * (W.card : ℝ) * lemma43DerivativeConstant 0 +
        sourceTraceOnePoissonError N W q := by linarith
  apply (div_le_div_of_nonneg_right htotal hcard.le).trans_eq
  unfold sourceTraceAverageBudget
  field_simp [hcard.ne']

/-- Proposition 4.6 with the matrix, Poisson, zero-frequency, and trace-one
parts fully discharged.  The only large terms left on the right are the exact
infinite `S1`, `S2`, and `S3` sectors. -/
theorem source_proposition46_sector_form
    (W : Finset ℝ) (N : ℕ) (b : ℕ → ℂ) (L R : ℝ)
    (hN : 0 < N) (hW : W.Nonempty) (hL : 0 ≤ L) (hR : 0 < R)
    (hb : ∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1)
    (hlarge : ∀ t : SourceRow W, L ≤ ‖sourceDN b N t‖)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (j q : ℕ) :
    (W.card : ℝ) * L ^ 2 ≤
      8 * (N : ℝ) *
        ((sourceTraceCubeDefectBudget N W R j q) ^ (1 / 3 : ℝ) +
          sourceTraceAverageBudget N W q) := by
  have hbase := source_proposition46_trace_form W N b L hW hL hb hlarge
  have hdef := source_trace_defect_le_sector_budget hN hW hR hsep j q
  have hdef0 := source_trace_defect_nonneg W N hW
  have hrpow := Real.rpow_le_rpow hdef0 hdef
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have havg := source_trace_average_le_budget hN hW q
  exact hbase.trans (by gcongr)

end
end GuthMaynardProposition46SectorConsumer

#print axioms GuthMaynardProposition46SectorConsumer.trace_defect_le_of_main_approximations
#print axioms GuthMaynardProposition46SectorConsumer.source_trace_defect_le_sector_budget
#print axioms GuthMaynardProposition46SectorConsumer.source_trace_average_le_budget
#print axioms GuthMaynardProposition46SectorConsumer.source_proposition46_sector_form
