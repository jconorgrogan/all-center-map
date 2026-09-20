import EndpointPerronZeroMismatch
import MellinDetectorLeaf

/-!
# Cancellation in the endpoint/Perron zero mismatch

The AP window uses a difference of two endpoint remainders.  At that stage
the regularizing constants in `(t^rho - 1) / rho` cancel exactly.  This file
performs that cancellation before any triangle inequality and splits off the
zeros below the positive Perron edge.
-/

namespace EndpointPerronZeroCancellation

open Set
open scoped BigOperators
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge
open MAPEndpointRegularizedZeroPrimitive

noncomputable section

/-- Endpoint primitive restricted to the positive-left-edge Perron support. -/
def positiveEdgeEndpointZeroTerm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma T t : ℝ) : ℂ :=
  endpointFiniteZeroPrimitive (zeroSupport chi sigma T)
    (zeroMultiplicity chi sigma T) t

/-- Endpoint primitive contributed by zeros in the omitted low strip
`0 ≤ Re rho < sigma`. -/
def lowStripEndpointZeroTerm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma T t : ℝ) : ℂ :=
  ∑ rho ∈ zeroSupport chi 0 T \ zeroSupport chi sigma T,
    (zeroMultiplicity chi 0 T rho : ℂ) *
      endpointRegularizedZeroTerm t rho

/-- The common-support aperture error after the endpoint regularizing
constants have canceled. -/
def endpointPerronApertureWindow
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma T a b : ℝ) : ℂ :=
  ∑ rho ∈ zeroSupport chi sigma T,
    (zeroMultiplicity chi sigma T rho : ℂ) *
      ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
        (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
          Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho

/-- The full endpoint primitive is the positive-edge primitive plus the
literal omitted low-strip primitive.  Multiplicity transport between the two
rectangles is proved, not assumed. -/
theorem endpointMultiplicityWeightedZeroTerm_eq_positiveEdge_add_lowStrip
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T t : ℝ} (hsigma : 0 ≤ sigma) :
    endpointMultiplicityWeightedZeroTerm chi 0 T t =
      positiveEdgeEndpointZeroTerm chi sigma T t +
        lowStripEndpointZeroTerm chi sigma T t := by
  classical
  let outer := zeroSupport chi 0 T
  let inner := zeroSupport chi sigma T
  let f : ℂ → ℂ := fun rho =>
    (zeroMultiplicity chi 0 T rho : ℂ) *
      endpointRegularizedZeroTerm t rho
  have hsub : inner ⊆ outer := by
    exact MAPMellinDetectorLeaf.zeroSupport_mono chi hsigma le_rfl
  have hmult : ∀ rho ∈ inner,
      zeroMultiplicity chi 0 T rho = zeroMultiplicity chi sigma T rho := by
    intro rho hrho
    have hinner : rho ∈ zeroRectangle sigma T :=
      mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho
    have houter : rho ∈ zeroRectangle 0 T :=
      MAPMellinDetectorLeaf.zeroRectangle_mono hsigma le_rfl hinner
    exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
      chi houter hinner
  have hinnerSum :
      ∑ rho ∈ inner, f rho =
        ∑ rho ∈ inner,
          (zeroMultiplicity chi sigma T rho : ℂ) *
            endpointRegularizedZeroTerm t rho := by
    apply Finset.sum_congr rfl
    intro rho hrho
    simp only [f, hmult rho hrho]
  have hsdiff := Finset.sum_sdiff_eq_sub (f := f) hsub
  simp only [endpointMultiplicityWeightedZeroTerm,
    endpointFiniteZeroPrimitive, positiveEdgeEndpointZeroTerm,
    lowStripEndpointZeroTerm]
  change (∑ rho ∈ outer, f rho) =
    (∑ rho ∈ inner,
      (zeroMultiplicity chi sigma T rho : ℂ) *
        endpointRegularizedZeroTerm t rho) +
      ∑ rho ∈ outer \ inner, f rho
  rw [← hinnerSum, hsdiff]
  ring

/-- On the positive-edge support, taking the endpoint window first cancels
the `-1/rho` constants exactly and leaves only the half-integer aperture
error displayed in `endpointPerronApertureWindow`. -/
theorem positiveEdge_endpoint_sub_perron_window_eq_aperture
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T a b : ℝ} (hsigma : 0 < sigma) :
    (positiveEdgeEndpointZeroTerm chi sigma T b -
        multiplicityWeightedPerronZeroSum chi sigma T
          (halfIntegerPoint ⌊b⌋₊)) -
      (positiveEdgeEndpointZeroTerm chi sigma T a -
        multiplicityWeightedPerronZeroSum chi sigma T
          (halfIntegerPoint ⌊a⌋₊)) =
        endpointPerronApertureWindow chi sigma T a b := by
  classical
  let S := zeroSupport chi sigma T
  let m : ℂ → ℂ := fun rho => (zeroMultiplicity chi sigma T rho : ℂ)
  let E : ℝ → ℂ → ℂ := fun t rho =>
    m rho * endpointRegularizedZeroTerm t rho
  let P : ℝ → ℂ → ℂ := fun u rho =>
    m rho * Complex.cpow (u : ℂ) rho / rho
  have hpoint : ∀ rho ∈ S,
      (E b rho - P (halfIntegerPoint ⌊b⌋₊) rho) -
        (E a rho - P (halfIntegerPoint ⌊a⌋₊) rho) =
      m rho *
        ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
          (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
            Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho := by
    intro rho hrho
    have hre : sigma ≤ rho.re :=
      (mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho).1.1
    have hrho0 : rho ≠ 0 := by
      intro hz
      subst rho
      norm_num at hre
      linarith
    simp only [E, P, m, endpointRegularizedZeroTerm, if_neg hrho0,
      APFoundation.regularizedZeroTerm]
    field_simp [hrho0]
    ring_nf
  simp only [positiveEdgeEndpointZeroTerm, endpointFiniteZeroPrimitive,
    multiplicityWeightedPerronZeroSum, endpointPerronApertureWindow]
  have hsumB :
      (∑ rho ∈ S, E b rho) -
          ∑ rho ∈ S, P (halfIntegerPoint ⌊b⌋₊) rho =
        ∑ rho ∈ S, (E b rho - P (halfIntegerPoint ⌊b⌋₊) rho) :=
    (Finset.sum_sub_distrib _ _).symm
  have hsumA :
      (∑ rho ∈ S, E a rho) -
          ∑ rho ∈ S, P (halfIntegerPoint ⌊a⌋₊) rho =
        ∑ rho ∈ S, (E a rho - P (halfIntegerPoint ⌊a⌋₊) rho) :=
    (Finset.sum_sub_distrib _ _).symm
  have hsumWindow :
      (∑ rho ∈ S, (E b rho - P (halfIntegerPoint ⌊b⌋₊) rho)) -
          ∑ rho ∈ S, (E a rho - P (halfIntegerPoint ⌊a⌋₊) rho) =
        ∑ rho ∈ S,
          ((E b rho - P (halfIntegerPoint ⌊b⌋₊) rho) -
            (E a rho - P (halfIntegerPoint ⌊a⌋₊) rho)) :=
    (Finset.sum_sub_distrib _ _).symm
  change ((∑ rho ∈ S, E b rho) -
      ∑ rho ∈ S, P (halfIntegerPoint ⌊b⌋₊) rho) -
    ((∑ rho ∈ S, E a rho) -
      ∑ rho ∈ S, P (halfIntegerPoint ⌊a⌋₊) rho) =
    ∑ rho ∈ S,
      m rho *
        ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
          (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
            Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho
  calc
    ((∑ rho ∈ S, E b rho) -
        ∑ rho ∈ S, P (halfIntegerPoint ⌊b⌋₊) rho) -
      ((∑ rho ∈ S, E a rho) -
        ∑ rho ∈ S, P (halfIntegerPoint ⌊a⌋₊) rho) =
      (∑ rho ∈ S, (E b rho - P (halfIntegerPoint ⌊b⌋₊) rho)) -
        ∑ rho ∈ S, (E a rho - P (halfIntegerPoint ⌊a⌋₊) rho) := by
          rw [hsumB, hsumA]
    _ = ∑ rho ∈ S,
        ((E b rho - P (halfIntegerPoint ⌊b⌋₊) rho) -
          (E a rho - P (halfIntegerPoint ⌊a⌋₊) rho)) := by
            exact hsumWindow
    _ = ∑ rho ∈ S,
        m rho *
          ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
            (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho := by
            apply Finset.sum_congr rfl
            intro rho hrho
            exact hpoint rho hrho

/-- Exact AP mismatch-window split.  The regularizing constants have already
canceled in the aperture term; the only additional zero contribution is the
literal low-strip endpoint window. -/
theorem endpointPerronZeroMismatch_window_eq_lowStrip_add_aperture
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {sigma T a b : ℝ} (hsigma : 0 < sigma) :
    MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
        chi sigma T b -
      MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
        chi sigma T a =
      (lowStripEndpointZeroTerm chi.primitiveCharacter sigma T b -
        lowStripEndpointZeroTerm chi.primitiveCharacter sigma T a) +
      endpointPerronApertureWindow chi.primitiveCharacter sigma T a b := by
  have hb :=
    endpointMultiplicityWeightedZeroTerm_eq_positiveEdge_add_lowStrip
      chi.primitiveCharacter (T := T) (t := b) hsigma.le
  have ha :=
    endpointMultiplicityWeightedZeroTerm_eq_positiveEdge_add_lowStrip
      chi.primitiveCharacter (T := T) (t := a) hsigma.le
  have hap := positiveEdge_endpoint_sub_perron_window_eq_aperture
    chi.primitiveCharacter (T := T) (a := a) (b := b) hsigma
  unfold MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
  rw [hb, ha]
  linear_combination hap

/-- Triangle bound only after cancellation: the common-support term retains
the difference between the real endpoints and their half-integer Perron
evaluation points. -/
theorem norm_endpointPerronApertureWindow_le_weighted_div_sigma
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T a b : ℝ} (hsigma : 0 < sigma) :
    ‖endpointPerronApertureWindow chi sigma T a b‖ ≤
      ∑ rho ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℝ) *
          ‖(Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
            (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)‖ / sigma := by
  unfold endpointPerronApertureWindow
  calc
    ‖∑ rho ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℂ) *
          ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
            (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho‖
        ≤ ∑ rho ∈ zeroSupport chi sigma T,
          ‖(zeroMultiplicity chi sigma T rho : ℂ) *
            ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
              (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
                Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho‖ :=
          norm_sum_le _ _
    _ ≤ ∑ rho ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℝ) *
          ‖(Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
            (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)‖ / sigma := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hre : sigma ≤ rho.re :=
        (mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho).1.1
      have hden : sigma ≤ ‖rho‖ := by
        calc
          sigma ≤ |rho.re| := by
            rw [abs_of_nonneg (hsigma.le.trans hre)]
            exact hre
          _ ≤ ‖rho‖ := Complex.abs_re_le_norm rho
      rw [norm_div, norm_mul, norm_natCast]
      exact div_le_div_of_nonneg_left
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hsigma hden

/-- Source-facing AP mismatch bound after the exact split.  The two terms are
now structurally different analytic leaves: the low-strip endpoint window and
the common-support half-integer aperture error. -/
theorem norm_endpointPerronZeroMismatch_window_le_lowStrip_add_weightedAperture
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {sigma T a b : ℝ} (hsigma : 0 < sigma) :
    ‖MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
        chi sigma T b -
      MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
        chi sigma T a‖ ≤
      ‖lowStripEndpointZeroTerm chi.primitiveCharacter sigma T b -
        lowStripEndpointZeroTerm chi.primitiveCharacter sigma T a‖ +
      ∑ rho ∈ zeroSupport chi.primitiveCharacter sigma T,
        (zeroMultiplicity chi.primitiveCharacter sigma T rho : ℝ) *
          ‖(Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
            (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)‖ / sigma := by
  rw [endpointPerronZeroMismatch_window_eq_lowStrip_add_aperture
    chi hsigma]
  exact (norm_add_le _ _).trans
    (add_le_add_right
      (norm_endpointPerronApertureWindow_le_weighted_div_sigma
        chi.primitiveCharacter hsigma) _)

/-- Moving a positive real endpoint to its canonical half integer costs at
most the length of that interval after division by `rho`.  This is the sharp
calculus step: the apparent `1 / |rho|` is canceled by the derivative of
`t^rho` before taking norms. -/
theorem norm_cpow_sub_halfInteger_cpow_div_le_abs
    {t : ℝ} {rho : ℂ} (ht : 1 ≤ t)
    (hre0 : 0 ≤ rho.re) (hre1 : rho.re ≤ 1) (hrho : rho ≠ 0) :
    ‖(Complex.cpow (t : ℂ) rho -
        Complex.cpow (halfIntegerPoint ⌊t⌋₊ : ℂ) rho) / rho‖ ≤
      |t - halfIntegerPoint ⌊t⌋₊| := by
  let u := halfIntegerPoint ⌊t⌋₊
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hfloor : 1 ≤ ⌊t⌋₊ := Nat.le_floor
    (show ((1 : ℕ) : ℝ) ≤ t by simpa using ht)
  have hu : 1 ≤ u := by
    have hfloorReal : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfloor
    unfold u halfIntegerPoint
    linarith
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have heq :
      (∫ r : ℝ in u..t, (r : ℂ) ^ (rho - 1)) =
        (Complex.cpow (t : ℂ) rho - Complex.cpow (u : ℂ) rho) / rho := by
    rw [intervalIntegral_cpow_sub_one_eq_endpointTerm_sub hu0 ht0 hre0]
    simp only [endpointRegularizedZeroTerm, if_neg hrho,
      APFoundation.regularizedZeroTerm]
    ring
  have hint :
      ‖∫ r : ℝ in u..t, (r : ℂ) ^ (rho - 1)‖ ≤
        1 * |t - u| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hrIcc : r ∈ Set.uIcc u t := Set.uIoc_subset_uIcc hr
      have hrOne : 1 ≤ r := by
        rw [Set.mem_uIcc] at hrIcc
        rcases hrIcc with hrIcc | hrIcc
        · exact hu.trans hrIcc.1
        · exact ht.trans hrIcc.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos
        (zero_lt_one.trans_le hrOne)]
      simp only [Complex.sub_re, Complex.one_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hrOne (by linarith))
  rw [heq] at hint
  simpa [u, abs_sub_comm] using hint

/-- Consequently the whole common-support half-integer aperture window is at
most one copy of the multiplicity-weighted zero count. -/
theorem norm_endpointPerronApertureWindow_le_zeroCount
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T a b : ℝ} (hsigma : 0 < sigma)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ‖endpointPerronApertureWindow chi sigma T a b‖ ≤
      (dirichletZeroCount chi sigma T : ℝ) := by
  unfold endpointPerronApertureWindow
  calc
    ‖∑ rho ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℂ) *
          ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
            (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho‖
        ≤ ∑ rho ∈ zeroSupport chi sigma T,
          ‖(zeroMultiplicity chi sigma T rho : ℂ) *
            ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
              (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
                Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho‖ :=
          norm_sum_le _ _
    _ ≤ ∑ rho ∈ zeroSupport chi sigma T,
          (zeroMultiplicity chi sigma T rho : ℝ) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hrect := mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho
      have hre0 : 0 ≤ rho.re := hsigma.le.trans hrect.1.1
      have hre1 : rho.re ≤ 1 := hrect.1.2
      have hrho0 : rho ≠ 0 := by
        intro hz
        subst rho
        have hsigmaZero : sigma ≤ 0 := by simpa using hrect.1.1
        linarith
      have hbnd := norm_cpow_sub_halfInteger_cpow_div_le_abs
        (rho := rho) hb hre0 hre1 hrho0
      have hand := norm_cpow_sub_halfInteger_cpow_div_le_abs
        (rho := rho) ha hre0 hre1 hrho0
      have heq :
          ((Complex.cpow (b : ℂ) rho - Complex.cpow (a : ℂ) rho) -
            (Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho)) / rho =
          (Complex.cpow (b : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho) / rho -
            (Complex.cpow (a : ℂ) rho -
              Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho) / rho := by
        field_simp [hrho0]
        ring
      rw [mul_div_assoc, heq, norm_mul, norm_natCast]
      calc
        (zeroMultiplicity chi sigma T rho : ℝ) *
            ‖(Complex.cpow (b : ℂ) rho -
                Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho) / rho -
              (Complex.cpow (a : ℂ) rho -
                Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho) / rho‖
            ≤ (zeroMultiplicity chi sigma T rho : ℝ) *
              (‖(Complex.cpow (b : ℂ) rho -
                  Complex.cpow (halfIntegerPoint ⌊b⌋₊ : ℂ) rho) / rho‖ +
                ‖(Complex.cpow (a : ℂ) rho -
                  Complex.cpow (halfIntegerPoint ⌊a⌋₊ : ℂ) rho) / rho‖) :=
              mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Nat.cast_nonneg _)
        _ ≤ (zeroMultiplicity chi sigma T rho : ℝ) *
              (|b - halfIntegerPoint ⌊b⌋₊| +
                |a - halfIntegerPoint ⌊a⌋₊|) := by
              gcongr
        _ ≤ (zeroMultiplicity chi sigma T rho : ℝ) := by
          have hbhalf := abs_halfIntegerPoint_floor_sub_le b
            (zero_le_one.trans hb)
          have hahalf := abs_halfIntegerPoint_floor_sub_le a
            (zero_le_one.trans ha)
          rw [abs_sub_comm] at hbhalf hahalf
          nlinarith [Nat.cast_nonneg (α := ℝ)
            (zeroMultiplicity chi sigma T rho)]
    _ = (dirichletZeroCount chi sigma T : ℝ) := by
      rw [← Nat.cast_sum, sum_zeroMultiplicity_eq_dirichletZeroCount]

/-- Final cancellation-preserving mismatch bound: only the low-strip endpoint
window remains analytic; the common-support aperture is reduced to the actual
finite zero count. -/
theorem norm_endpointPerronZeroMismatch_window_le_lowStrip_add_zeroCount
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {sigma T a b : ℝ} (hsigma : 0 < sigma)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ‖MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
        chi sigma T b -
      MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
        chi sigma T a‖ ≤
      ‖lowStripEndpointZeroTerm chi.primitiveCharacter sigma T b -
        lowStripEndpointZeroTerm chi.primitiveCharacter sigma T a‖ +
      (dirichletZeroCount chi.primitiveCharacter sigma T : ℝ) := by
  rw [endpointPerronZeroMismatch_window_eq_lowStrip_add_aperture
    chi hsigma]
  exact (norm_add_le _ _).trans
    (add_le_add_right
      (norm_endpointPerronApertureWindow_le_zeroCount
        chi.primitiveCharacter hsigma ha hb) _)

/-- In the complete AP character-window formula, the full endpoint zero-field
integral and the endpoint part of the mismatch cancel exactly.  The remaining
zero contribution is the negative Perron residue window.  This identity lets
the family argument choose a direct Perron-window route without paying twice
for the same zero field. -/
theorem neg_zeroFieldIntegral_add_endpointPerronMismatch_window_eq_neg_perronWindow
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {sigma T a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    -(∫ t : ℝ in a..b,
        APExplicitFormulaMajorantAdapter.actualZeroField
          chi.primitiveCharacter 0 T t) +
      (MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
          chi sigma T b -
        MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
          chi sigma T a) =
      -(multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
          (halfIntegerPoint ⌊b⌋₊) -
        multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
          (halfIntegerPoint ⌊a⌋₊)) := by
  have hwindow :=
    MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch_window_eq_integral_sub_perronWindow
      chi (sigma := sigma) (T := T) (x := a) (Y := b - a)
        ha (by simpa using hb)
  have hab : a + (b - a) = b := by ring
  rw [hab] at hwindow
  rw [hwindow]
  ring

/-- A Perron residue window on a positive-left-edge support is exactly the
integral of the corresponding literal zero field.  This is the family-energy
form of the common-support term, with all regularizing constants canceled. -/
theorem perronZeroSum_window_eq_interval_actualZeroField
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T u v : ℝ} (hsigma : 0 < sigma) :
    multiplicityWeightedPerronZeroSum chi sigma T v -
        multiplicityWeightedPerronZeroSum chi sigma T u =
      ∫ t : ℝ in u..v,
        APExplicitFormulaMajorantAdapter.actualZeroField chi sigma T t := by
  have hzeroPos : ∀ rho ∈ zeroSupport chi sigma T, 0 < rho.re := by
    intro rho hrho
    exact hsigma.trans_le
      (mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho).1.1
  have hint :=
    APExplicitFormulaMajorantAdapter.intervalIntegral_finiteZeroField
      (zeroSupport chi sigma T) (zeroMultiplicity chi sigma T)
      hzeroPos u (v - u)
  have huv : u + (v - u) = v := by ring
  rw [huv] at hint
  have hzeroWindow :=
    multiplicityWeightedZeroTerm_interval chi sigma T u (v - u)
  rw [huv] at hzeroWindow
  have hperron :
      multiplicityWeightedPerronZeroSum chi sigma T v -
          multiplicityWeightedPerronZeroSum chi sigma T u =
        ∑ rho ∈ zeroSupport chi sigma T,
          (zeroMultiplicity chi sigma T rho : ℂ) *
            ((Complex.cpow (v : ℂ) rho -
              Complex.cpow (u : ℂ) rho) / rho) := by
    unfold multiplicityWeightedPerronZeroSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro rho hrho
    change
      (zeroMultiplicity chi sigma T rho : ℂ) *
          Complex.cpow (v : ℂ) rho / rho -
        (zeroMultiplicity chi sigma T rho : ℂ) *
          Complex.cpow (u : ℂ) rho / rho =
      (zeroMultiplicity chi sigma T rho : ℂ) *
        ((Complex.cpow (v : ℂ) rho -
          Complex.cpow (u : ℂ) rho) / rho)
    simp only [div_eq_mul_inv]
    noncomm_ring
  rw [hperron, ← hzeroWindow]
  simpa only [APExplicitFormulaMajorantAdapter.finiteZeroPrimitive_actual_eq,
    APExplicitFormulaMajorantAdapter.actualZeroField] using hint.symm

/-- Therefore the exact full zero-field/mismatch cancellation is the
positive-support zero-field integral over the two half-integer endpoints. -/
theorem neg_zeroFieldIntegral_add_mismatch_eq_neg_positiveFieldHalfIntegerIntegral
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {sigma T a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hsigma : 0 < sigma) :
    -(∫ t : ℝ in a..b,
        APExplicitFormulaMajorantAdapter.actualZeroField
          chi.primitiveCharacter 0 T t) +
      (MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
          chi sigma T b -
        MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch
          chi sigma T a) =
      -(∫ t : ℝ in halfIntegerPoint ⌊a⌋₊..halfIntegerPoint ⌊b⌋₊,
        APExplicitFormulaMajorantAdapter.actualZeroField
          chi.primitiveCharacter sigma T t) := by
  rw [neg_zeroFieldIntegral_add_endpointPerronMismatch_window_eq_neg_perronWindow
    chi ha hb]
  rw [perronZeroSum_window_eq_interval_actualZeroField
    chi.primitiveCharacter hsigma]

end

end EndpointPerronZeroCancellation
