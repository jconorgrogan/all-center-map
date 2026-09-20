import HarmonicInterfaces

/-!
# Exact translated-window and rational-arc boundary welds

This module normalizes the public real-centered translated window all the way to
literal real inequalities.  It also records that the public major arcs are a
closed set of rational neighborhoods and that their complement is the exact
minor-arc region, so equality boundary points are assigned to the major arcs.
-/

open MeasureTheory Metric Set

namespace PrimePairEndpoints

/-- Membership in the public `ceil`/`floor` translated window is exactly the
pair of literal real inequalities.  Both inequalities are non-strict. -/
theorem mem_translatedWindow_iff_real_bounds
    {H h₀ : ℝ} {h : ℤ} :
    h ∈ translatedWindow H h₀ ↔
      h₀ - H ≤ (h : ℝ) ∧ (h : ℝ) ≤ h₀ + H := by
  simp only [translatedWindow, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

/-- The left endpoint is retained whenever it is itself an integer. -/
theorem left_endpoint_mem_translatedWindow
    {H h₀ : ℝ} {h : ℤ}
    (hH : 0 ≤ H)
    (hleft : (h : ℝ) = h₀ - H) :
    h ∈ translatedWindow H h₀ := by
  rw [mem_translatedWindow_iff_real_bounds]
  constructor <;> linarith

/-- The right endpoint is retained whenever it is itself an integer. -/
theorem right_endpoint_mem_translatedWindow
    {H h₀ : ℝ} {h : ℤ}
    (hH : 0 ≤ H)
    (hright : (h : ℝ) = h₀ + H) :
    h ∈ translatedWindow H h₀ := by
  rw [mem_translatedWindow_iff_real_bounds]
  constructor <;> linarith

/-- Exact criterion for the singular-series exceptional atom `h = 0` to occur
in the public translated window. -/
theorem zero_mem_translatedWindow_iff
    {H h₀ : ℝ} :
    (0 : ℤ) ∈ translatedWindow H h₀ ↔ h₀ - H ≤ 0 ∧ 0 ≤ h₀ + H := by
  simpa using
    (mem_translatedWindow_iff_real_bounds (H := H) (h₀ := h₀) (h := (0 : ℤ)))

/-- Equivalent symmetric form of the zero-membership criterion. -/
theorem zero_mem_translatedWindow_iff_abs
    {H h₀ : ℝ} :
    (0 : ℤ) ∈ translatedWindow H h₀ ↔ |h₀| ≤ H := by
  rw [zero_mem_translatedWindow_iff, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith

/-- Exact negated form, useful when deleting the forbidden zero shift. -/
theorem zero_not_mem_translatedWindow_iff_abs_lt
    {H h₀ : ℝ} :
    (0 : ℤ) ∉ translatedWindow H h₀ ↔ H < |h₀| := by
  rw [not_congr zero_mem_translatedWindow_iff_abs]
  exact not_le

/-- The public window really is closed at both integer endpoints. -/
example : (-1 : ℤ) ∈ translatedWindow (1 : ℝ) 0 := by
  rw [mem_translatedWindow_iff_real_bounds]
  norm_num

example : (1 : ℤ) ∈ translatedWindow (1 : ℝ) 0 := by
  rw [mem_translatedWindow_iff_real_bounds]
  norm_num

/-- A left-open replacement loses the left endpoint. -/
example : (-1 : ℤ) ∉ Finset.Ioc (-1 : ℤ) 1 := by decide

/-- An open replacement loses both endpoints. -/
example : (-1 : ℤ) ∉ Finset.Ioo (-1 : ℤ) 1 ∧
    (1 : ℤ) ∉ Finset.Ioo (-1 : ℤ) 1 := by decide

/-- With `h₀ = 1`, `H = 1/2`, the public window contains exactly the
single integer `1` among the nearby candidates. -/
example :
    (0 : ℤ) ∉ translatedWindow ((1 : ℝ) / 2) 1 ∧
    (1 : ℤ) ∈ translatedWindow ((1 : ℝ) / 2) 1 ∧
    (2 : ℤ) ∉ translatedWindow ((1 : ℝ) / 2) 1 := by
  simp only [mem_translatedWindow_iff_real_bounds]
  norm_num

/-- Reversing the rounding directions for the same real interval would use
`Icc 0 2` and spuriously insert both outside atoms. -/
example : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 2 ∧
    (2 : ℤ) ∈ Finset.Icc (0 : ℤ) 2 := by decide

/-- A narrow interval may contain no integer at all.  Here the correct public
window is empty at every candidate, while reversed rounding would insert two. -/
example :
    (0 : ℤ) ∉ translatedWindow ((1 : ℝ) / 4) ((1 : ℝ) / 2) ∧
    (1 : ℤ) ∉ translatedWindow ((1 : ℝ) / 4) ((1 : ℝ) / 2) ∧
    (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 1 ∧
    (1 : ℤ) ∈ Finset.Icc (0 : ℤ) 1 := by
  simp only [mem_translatedWindow_iff_real_bounds]
  norm_num

end PrimePairEndpoints

namespace RationalArcPartition

open PrimePairEndpoints

/-- Major and minor arcs cover the circle exactly. -/
theorem majorArcs_union_minorArcs
    (X : ℝ) (B D : ℕ) :
    majorArcs X B D ∪ minorArcs X B D = Set.univ := by
  simp [minorArcs]

/-- Major and minor arcs are exactly disjoint. -/
theorem majorArcs_inter_minorArcs
    (X : ℝ) (B D : ℕ) :
    majorArcs X B D ∩ minorArcs X B D = ∅ := by
  simp [minorArcs]

/-- Pointwise exclusive and exhaustive membership form of the partition. -/
theorem mem_majorArcs_xor_mem_minorArcs
    (X : ℝ) (B D : ℕ) (α : UnitAddCircle) :
    (α ∈ majorArcs X B D ∧ α ∉ minorArcs X B D) ∨
      (α ∉ majorArcs X B D ∧ α ∈ minorArcs X B D) := by
  by_cases hα : α ∈ majorArcs X B D
  · exact Or.inl ⟨hα, by simpa [minorArcs] using hα⟩
  · exact Or.inr ⟨hα, by simpa [minorArcs] using hα⟩

/-- The existing measurability facts combine with the exact set partition. -/
theorem measurable_exact_majorMinor_partition
    (X : ℝ) (B D : ℕ) :
    MeasurableSet (majorArcs X B D) ∧
      MeasurableSet (minorArcs X B D) ∧
      majorArcs X B D ∪ minorArcs X B D = Set.univ ∧
      majorArcs X B D ∩ minorArcs X B D = ∅ := by
  exact ⟨MAPHarmonicEndpoint.measurableSet_majorArcs X B D,
    MAPHarmonicEndpoint.measurableSet_minorArcs X B D,
    majorArcs_union_minorArcs X B D,
    majorArcs_inter_minorArcs X B D⟩

/-- A point at exact distance equal to a legal rational-arc radius belongs to
`majorArcs`, because the public definition uses `≤` rather than `<`. -/
theorem rational_boundary_mem_majorArcs
    {X : ℝ} {B D q a : ℕ} {α : UnitAddCircle}
    (hq : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
    (haq : a < q)
    (hac : a.Coprime q)
    (hboundary :
      dist α ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle)) =
        (Real.log X) ^ D / X) :
    α ∈ majorArcs X B D := by
  refine ⟨q, a, hq, hqX, haq, hac, ?_⟩
  exact hboundary.le

/-- The same equality-boundary point is not assigned to the minor arcs. -/
theorem rational_boundary_mem_major_not_minor
    {X : ℝ} {B D q a : ℕ} {α : UnitAddCircle}
    (hq : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
    (haq : a < q)
    (hac : a.Coprime q)
    (hboundary :
      dist α ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle)) =
        (Real.log X) ^ D / X) :
    α ∈ majorArcs X B D ∧ α ∉ minorArcs X B D := by
  have hmajor := rational_boundary_mem_majorArcs hq hqX haq hac hboundary
  exact ⟨hmajor, by simpa [minorArcs] using hmajor⟩

/-- A minor-arc point is strictly farther than the closed radius from every
legal reduced rational center.  This is the pointwise normal form of the
complement definition and records where strictness belongs. -/
theorem mem_minorArcs_iff_strictly_outside
    {X : ℝ} {B D : ℕ} {α : UnitAddCircle} :
    α ∈ minorArcs X B D ↔
      ∀ q a : ℕ,
        1 ≤ q →
        (q : ℝ) ≤ (Real.log X) ^ B →
        a < q →
        a.Coprime q →
        (Real.log X) ^ D / X <
          dist α ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle)) := by
  simp only [minorArcs, Set.mem_compl_iff, majorArcs, Set.mem_setOf_eq]
  push Not
  rfl

end RationalArcPartition

