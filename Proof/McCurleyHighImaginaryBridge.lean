import KhaleWeakVKDeterministicBridge

/-!
# Source-faithful McCurley high-imaginary bridge

McCurley's published Theorem 1.1 uses

`R = 9.645908801`

and an **open** zero region.  Khale's source rounds this constant downward to
`9.64590880` and writes a closed boundary.  A downward rounding cannot justify
that boundary change.  We instead close the region with the rigorously larger
rational `9.64590881`; this supplies a strict inclusion in McCurley's published
open region.

The analytic McCurley input is not declared as a proposition in this file.  The
last theorem takes its literal real-exception conclusion as a local higher-order
hypothesis and proves the complete deterministic specialization to nonzero
imaginary ordinate.
-/

namespace MAPMcCurleyHighImaginaryBridge

open Complex

noncomputable section

/-- The constant printed in McCurley's published Theorem 1.1. -/
def publishedR : ℝ := 9.645908801

/-- A rigorously larger decimal used to pass from a closed boundary to the
published open region. -/
def safeClosedR : ℝ := 9.64590881

/-- The exact scale `max {q, q |t|, 10}` in McCurley's theorem. -/
def mccurleyScale (q : ℕ) (t : ℝ) : ℝ :=
  max (max (q : ℝ) ((q : ℝ) * |t|)) 10

/-- Boundary corresponding to a chosen de la Vallee Poussin constant. -/
def mccurleyBoundary (R : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  1 - 1 / (R * Real.log (mccurleyScale q t))

theorem one_lt_mccurleyScale (q : ℕ) (t : ℝ) :
    1 < mccurleyScale q t := by
  exact (by norm_num : (1 : ℝ) < 10).trans_le (le_max_right _ _)

theorem log_mccurleyScale_pos (q : ℕ) (t : ℝ) :
    0 < Real.log (mccurleyScale q t) :=
  Real.log_pos (one_lt_mccurleyScale q t)

/-- Khale's displayed McCurley constant is a downward rounding, so it is not a
safe replacement for the published value at a closed boundary. -/
theorem khale_downward_rounding_lt_published :
    (9.64590880 : ℝ) < publishedR := by
  norm_num [publishedR]

theorem publishedR_lt_safeClosedR : publishedR < safeClosedR := by
  norm_num [publishedR, safeClosedR]

/-- The closed boundary with the larger safe constant lies strictly inside
McCurley's published open region. -/
theorem published_boundary_lt_safe_closed_boundary (q : ℕ) (t : ℝ) :
    mccurleyBoundary publishedR q t <
      mccurleyBoundary safeClosedR q t := by
  have hlog := log_mccurleyScale_pos q t
  have hRpos : 0 < publishedR := by norm_num [publishedR]
  have hdenpos : 0 < publishedR * Real.log (mccurleyScale q t) :=
    mul_pos hRpos hlog
  have hdenlt :
      publishedR * Real.log (mccurleyScale q t) <
        safeClosedR * Real.log (mccurleyScale q t) :=
    mul_lt_mul_of_pos_right publishedR_lt_safeClosedR hlog
  have hinv := one_div_lt_one_div_of_lt hdenpos hdenlt
  dsimp [mccurleyBoundary]
  linarith

/-- Deterministic high-imaginary specialization of the exact conclusion used
from McCurley's Theorem 1.1.

The local hypothesis is the literal analytic source conclusion needed here:
any zero in the published **open** region is real.  McCurley's full theorem is
stronger: across all characters modulo `q` there is at most one such zero, and
it is simple and belongs to a real nonprincipal character.  Those unused parts
are intentionally absent from this consumer.

Using `safeClosedR`, the conclusion is valid on a closed boundary and never
relies on Khale's downward-rounded decimal. -/
theorem ne_zero_of_published_real_exception
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hPublishedRealException :
      ∀ (ψ : DirichletCharacter ℂ q) (s : ℂ),
        mccurleyBoundary publishedR q s.im < s.re →
        DirichletCharacter.LFunction ψ s = 0 →
        s.im = 0)
    {σ t : ℝ} (ht : t ≠ 0)
    (hσ : mccurleyBoundary safeClosedR q t ≤ σ) :
    DirichletCharacter.LFunction χ (σ + Complex.I * t) ≠ 0 := by
  intro hzero
  have hinside : mccurleyBoundary publishedR q t < σ :=
    (published_boundary_lt_safe_closed_boundary q t).trans_le hσ
  have him := hPublishedRealException χ (σ + Complex.I * t) (by simpa using hinside) hzero
  apply ht
  simpa using him

/-- The exact specialization used in the weak Khale patch range `t ≥ 3`. -/
theorem ne_zero_of_published_real_exception_of_three_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hPublishedRealException :
      ∀ (ψ : DirichletCharacter ℂ q) (s : ℂ),
        mccurleyBoundary publishedR q s.im < s.re →
        DirichletCharacter.LFunction ψ s = 0 →
        s.im = 0)
    {σ t : ℝ} (ht : 3 ≤ t)
    (hσ : mccurleyBoundary safeClosedR q t ≤ σ) :
    DirichletCharacter.LFunction χ (σ + Complex.I * t) ≠ 0 := by
  exact ne_zero_of_published_real_exception χ hPublishedRealException
    (by linarith) hσ

end

end MAPMcCurleyHighImaginaryBridge
