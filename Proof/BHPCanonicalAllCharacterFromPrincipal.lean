import BHPCanonicalNonprincipalFourthMoment
import BHPCanonicalPrincipalPointwise

/-!
# Exact all-character BHP reduction from the principal horizontal leaf

The nonprincipal source is now premise-free apart from Ramachandra's shifted
fourth moment.  This file isolates the sole missing pointwise input for the
principal character and proves that it is sufficient for the full
all-character selected fourth moment.
-/

namespace MAPBHPCanonicalAllCharacterFromPrincipal

set_option maxHeartbeats 4000000

open scoped BigOperators
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski
open MAPBHPCorrectedPerronKernel
open MAPBHPCorrectedContourShift
open MAPBHPShiftedHolderReduction
open MAPBHPShiftedRamachandraWeld
open MAPBHPCanonicalNonprincipalPointwise
open MAPBHPCanonicalPrincipalPointwise
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- Exact remaining principal pointwise leaf.  Its translated-pole term is
already expressed by the certified BHP principal weight; the work left to
inhabit this proposition is the sharp undamped horizontal zeta bound. -/
def CanonicalPrincipalPointwiseSource : Prop :=
  ∃ Cₚ : ℝ, 0 < Cₚ ∧
    ∀ (q X : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q) (t T x0 : ℝ),
      chi = 1 →
      2 ≤ X → 1 ≤ T → 8 ≤ x0 →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 →
      T ≤ x0 → 2 * T ≤ x0 → T ≤ (X : ℝ) → |t| ≤ T →
      ‖criticalPrefixPolynomial q X chi t‖ ≤
        Cₚ * (1 + Real.log x0) ^ 2 *
          (perronConvolution
              (shiftedCriticalLineLNorm chi
                (canonicalRamachandraOffset x0)) (2 * T) t +
            Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.sqrt (X : ℝ) / T +
            Real.sqrt (X : ℝ) * principalPerronWeight (chi, t))

/-- Source-faithful principal pointwise leaf for the actual MRT prefix range.
The literal Titchmarsh `1/sqrt X` term is retained, so no relation between the
height and the prefix cutoff is assumed. -/
def CanonicalPrincipalPointwiseSourceLiteral : Prop :=
  ∃ Cₚ : ℝ, 0 < Cₚ ∧
    ∀ (q X : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q) (t T x0 : ℝ),
      chi = 1 →
      2 ≤ X → 1 ≤ T → 8 ≤ x0 →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 →
      T ≤ x0 → 2 * T ≤ x0 → |t| ≤ T →
      ‖criticalPrefixPolynomial q X chi t‖ ≤
        Cₚ * (1 + Real.log x0) ^ 2 *
          (perronConvolution
              (shiftedCriticalLineLNorm chi
                (canonicalRamachandraOffset x0)) (2 * T) t +
            Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.sqrt (X : ℝ) / T +
            1 / Real.sqrt (X : ℝ) +
            Real.sqrt (X : ℝ) * principalPerronWeight (chi, t))

theorem isPrincipalCharacter_iff_eq_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    IsPrincipalCharacter chi ↔ chi = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    have hval : ((u.val.val : ℕ) : ZMod q) = u.val :=
      ZMod.natCast_zmod_val _
    have hu : IsUnit ((u.val.val : ℕ) : ZMod q) := by
      rw [hval]
      exact u.isUnit
    have hh := h u.val.val hu
    simpa [hval, MulChar.one_apply u.isUnit] using hh
  · intro h
    subst chi
    intro n hn
    exact MulChar.one_apply hn

theorem principalPerronWeight_eq_ite_eq_one
    {q : ℕ} [NeZero q]
    (z : DirichletCharacter ℂ q × ℝ) :
    principalPerronWeight z =
      if z.1 = 1 then 1 / (1 + |z.2|) else 0 := by
  classical
  unfold principalPerronWeight
  simp only [isPrincipalCharacter_iff_eq_one]

/-- The literal horizontal-edge estimate is sufficient for the no-`T <= X`
principal pointwise source.  Titchmarsh's `1/sqrt X` term is carried unchanged;
the translated pole is discharged by the certified residue bound. -/
theorem canonicalPrincipalPointwiseSourceLiteral_of_horizontal
    (hHorizontal : CanonicalPrincipalHorizontalSource) :
    CanonicalPrincipalPointwiseSourceLiteral := by
  classical
  obtain ⟨Ch, hCh, hhorizontal⟩ := hHorizontal
  let C319 : ℝ := canonicalTitchmarshConstant
  let Kleft : ℝ := 401 * Real.exp (1 / 400 : ℝ) / (2 * Real.pi)
  let C : ℝ := 2 * C319 + Kleft + Ch + 3
  have hC319 : 0 < C319 := canonicalTitchmarshConstant_pos
  have hKleft : 0 < Kleft := by dsimp [Kleft]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q X _inst chi t T x0 hchi hX hT hx0 hqx hXx hTx0 hTwoTx ht
  subst chi
  let L : ℝ := 1 + Real.log x0
  let V : ℝ := perronConvolution
    (shiftedCriticalLineLNorm (1 : DirichletCharacter ℂ q)
      (canonicalRamachandraOffset x0)) (2 * T) t
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  let d : ℝ := 1 / Real.sqrt (X : ℝ)
  let r : ℝ := Real.sqrt (X : ℝ) *
    principalPerronWeight ((1 : DirichletCharacter ℂ q), t)
  have hraw :=
    norm_criticalPrefixPolynomial_principal_le_canonicalContour
      (q := q) (X := X) (t := t) (T := T) (x0 := x0)
      hX hT hx0 hqx hXx hTwoTx ht
  have hraw' :
      ‖criticalPrefixPolynomial q X (1 : DirichletCharacter ℂ q) t‖ ≤
        C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) + d) +
          (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) * V +
          ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
            (X : ℝ) t (canonicalRamachandraOffset x0)
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ +
          3 * r := by
    have hrEq : r = Real.sqrt (X : ℝ) / (1 + |t|) := by
      dsimp [r]
      rw [principalPerronWeight_eq_ite_eq_one]
      simp
      ring
    convert hraw using 1 <;>
      dsimp only [C319, V, d] <;> rw [hrEq] <;> ring
  have hhoriz := hhorizontal q X t T x0 hX hT hx0 hqx hXx
    hTx0 hTwoTx ht
  have hhoriz' :
      ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
          (X : ℝ) t (canonicalRamachandraOffset x0)
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ ≤
        Ch * L ^ 2 * (a + b) := by
    simpa [L, a, b] using hhoriz
  have hlog0 : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hV : 0 ≤ V := by
    dsimp [V]
    exact perronConvolution_nonneg (fun _ => norm_nonneg _) (by linarith)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hr : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (principalPerronWeight_nonneg _)
  have hlogTerm : Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) ≤
      L ^ 2 * b := by
    dsimp [L, b]
    have hhalf : Real.sqrt (X : ℝ) / (2 * T) ≤
        Real.sqrt (X : ℝ) / T := by
      gcongr
      linarith
    calc
      Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) =
          Real.log x0 * (Real.sqrt (X : ℝ) / (2 * T)) := by ring
      _ ≤ Real.log x0 * (Real.sqrt (X : ℝ) / T) :=
        mul_le_mul_of_nonneg_left hhalf hlog0
      _ ≤ (1 + Real.log x0) ^ 2 *
          (Real.sqrt (X : ℝ) / T) := by
        have hc : Real.log x0 ≤ (1 + Real.log x0) ^ 2 := by
          nlinarith [sq_nonneg (Real.log x0)]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hdL : d ≤ L ^ 2 * d := by
    have hsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg L]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq hd
  have hperron :
      C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) + d) ≤
        (2 * C319) * L ^ 2 * (b + d) := by
    have hsum := add_le_add hlogTerm hdL
    calc
      C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) + d) ≤
          C319 * (L ^ 2 * b + L ^ 2 * d) :=
        mul_le_mul_of_nonneg_left hsum hC319.le
      _ ≤ (2 * C319) * L ^ 2 * (b + d) := by
        have hnon : 0 ≤ C319 * L ^ 2 * (b + d) := by positivity
        calc
          C319 * (L ^ 2 * b + L ^ 2 * d) =
              C319 * L ^ 2 * (b + d) := by ring
          _ ≤ 2 * (C319 * L ^ 2 * (b + d)) := by linarith
          _ = _ := by ring
  have hleftCoeff :
      Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) ≤ Kleft * L := by
    have hpoly : 1 + 400 * Real.log x0 ≤ 401 * L := by
      dsimp [L]
      nlinarith
    dsimp [Kleft]
    calc
      Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) ≤
        Real.exp (1 / 400 : ℝ) * (401 * L) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le)
            (by positivity)
      _ = 401 * Real.exp (1 / 400 : ℝ) / (2 * Real.pi) * L := by ring
  have hleft :
      (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi)) * V ≤ Kleft * L ^ 2 * V := by
    calc
      _ ≤ (Kleft * L) * V := mul_le_mul_of_nonneg_right hleftCoeff hV
      _ ≤ (Kleft * L ^ 2) * V := by
        have hLL : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLL hKleft.le) hV
      _ = _ := by ring
  have hres : 3 * r ≤ 3 * L ^ 2 * r := by
    have hsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg L]
    nlinarith [mul_nonneg (sq_nonneg L) hr]
  change ‖criticalPrefixPolynomial q X (1 : DirichletCharacter ℂ q) t‖ ≤
    C * L ^ 2 * (V + a + b + d + r)
  refine hraw'.trans ?_
  calc
    C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) + d) +
        (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi)) * V +
        ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
          (X : ℝ) t (canonicalRamachandraOffset x0)
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ + 3 * r ≤
      (2 * C319) * L ^ 2 * (b + d) +
        Kleft * L ^ 2 * V + Ch * L ^ 2 * (a + b) +
          3 * L ^ 2 * r :=
      add_le_add (add_le_add (add_le_add hperron hleft) hhoriz') hres
    _ ≤ C * L ^ 2 * (V + a + b + d + r) := by
      dsimp [C]
      nlinarith [mul_nonneg (sq_nonneg L) hV,
        mul_nonneg (sq_nonneg L) ha, mul_nonneg (sq_nonneg L) hb,
        mul_nonneg (sq_nonneg L) hd, mul_nonneg (sq_nonneg L) hr,
        hC319.le, hKleft.le, hCh.le]

/-- Full all-character fourth moment with the exact Holder kernel retained.
This theorem makes the principal obstruction minimal and mechanically
checkable: once `CanonicalPrincipalPointwiseSource` and Ramachandra Theorem 6
are available, no further analytic estimate remains in the BHP descent. -/
theorem allCharacter_selectedPrefixFourthMass_le_exactKernel
    (hPrincipal : CanonicalPrincipalPointwiseSource)
    (hRamachandra : RamachandraTheorem6K2Source)
    {q X : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T x0 K : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx0 : T ≤ x0) (hTwoTx : 2 * T ≤ x0)
    (hTX : T ≤ (X : ℝ))
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    ∃ C C₆ : ℝ, 0 < C ∧ 0 < C₆ ∧
      selectedPrefixFourthMass X S ≤
        64 * (C * (1 + Real.log x0) ^ 2) ^ 4 *
          (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
              (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
              ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
                Real.log x0 ^ 401) +
            (S.card : ℝ) *
              ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4) +
            (X : ℝ) ^ 2 * selectedPrincipalDecayMass S) := by
  classical
  obtain ⟨Cₚ, hCₚ, hprincipal⟩ := hPrincipal
  obtain ⟨C₆, hC₆, hVsum⟩ :=
    canonicalShiftedPerronConvolutionFourth_le_exactKernel
      hRamachandra hT (by linarith : 2 ≤ x0) hqx hTx0 hK hthreshold
      hqpoly hheight hsep
  let C₀ : ℝ := canonicalNonprincipalPointwiseConstant
  let C : ℝ := C₀ + Cₚ
  let L : ℝ := 1 + Real.log x0
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  let r : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    Real.sqrt (X : ℝ) * principalPerronWeight z
  let V : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    perronConvolution
      (shiftedCriticalLineLNorm z.1 (canonicalRamachandraOffset x0))
      (2 * T) z.2
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    exact canonicalNonprincipalPointwiseConstant_pos
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, C₆, hC, hC₆, ?_⟩
  have hL : 0 ≤ L := by
    dsimp [L]
    have := Real.log_nonneg (show (1 : ℝ) ≤ x0 by linarith)
    linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr (z : DirichletCharacter ℂ q × ℝ) : 0 ≤ r z := by
    dsimp [r]
    exact mul_nonneg (Real.sqrt_nonneg _) (principalPerronWeight_nonneg z)
  have hV (z : DirichletCharacter ℂ q × ℝ) : 0 ≤ V z := by
    dsimp [V]
    exact perronConvolution_nonneg (fun _ => norm_nonneg _) (by linarith)
  have hpoint (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
        C * L ^ 2 * (V z + a + b + r z) := by
    by_cases hzprincipal : z.1 = 1
    · have hp := hprincipal q X z.1 z.2 T x0 hzprincipal hX hT hx0
        hqx hXx hTx0 hTwoTx hTX (hheight z hz)
      have hinner : 0 ≤ V z + a + b + r z :=
        add_nonneg (add_nonneg (add_nonneg (hV z) ha) hb) (hr z)
      have hCpC : Cₚ ≤ C := by dsimp [C]; linarith [hC₀.le]
      calc
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
            Cₚ * L ^ 2 * (V z + a + b + r z) := by
          simpa [L, V, a, b, r] using hp
        _ ≤ C * L ^ 2 * (V z + a + b + r z) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCpC (sq_nonneg L)) hinner
    · have hp := norm_criticalPrefixPolynomial_le_globalPolylog
        z.1 hzprincipal hX hT hx0 hqx hXx hTx0 hTwoTx hTX
          (hheight z hz)
      have hinner0 : 0 ≤ V z + a + b :=
        add_nonneg (add_nonneg (hV z) ha) hb
      have hinner : V z + a + b ≤ V z + a + b + r z :=
        le_add_of_nonneg_right (hr z)
      have hC₀C : C₀ ≤ C := by dsimp [C]; linarith [hCₚ.le]
      calc
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
            C₀ * L ^ 2 * (V z + a + b) := by
          simpa [C₀, L, V, a, b] using hp
        _ ≤ C * L ^ 2 * (V z + a + b) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC₀C (sq_nonneg L)) hinner0
        _ ≤ C * L ^ 2 * (V z + a + b + r z) :=
          mul_le_mul_of_nonneg_left hinner (mul_nonneg hC.le (sq_nonneg L))
  have hpoint4 (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
        64 * (C * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + r z ^ 4) := by
    have hp := pow_le_pow_left₀
      (norm_nonneg (criticalPrefixPolynomial q X z.1 z.2)) (hpoint z hz) 4
    have hsum := fourth_power_sum_four_le (hV z) ha hb (hr z)
    calc
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
          (C * L ^ 2 * (V z + a + b + r z)) ^ 4 := hp
      _ = (C * L ^ 2) ^ 4 * (V z + a + b + r z) ^ 4 := by ring
      _ ≤ (C * L ^ 2) ^ 4 *
          (64 * (V z ^ 4 + a ^ 4 + b ^ 4 + r z ^ 4)) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg (by positivity) 4)
      _ = 64 * (C * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + r z ^ 4) := by ring
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hTpos : 0 < T := by linarith
  have ha4 : a ^ 4 = (q : ℝ) ^ 2 / T ^ 2 := by
    dsimp [a]
    exact sqrt_ratio_fourth hq0 hTpos
  have hb4 : b ^ 4 = (X : ℝ) ^ 2 / T ^ 4 := by
    dsimp [b]
    rw [div_pow]
    rw [show Real.sqrt (X : ℝ) ^ 4 =
      (Real.sqrt (X : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hX0]
  have hrsum : (∑ z ∈ S, r z ^ 4) =
      (X : ℝ) ^ 2 * selectedPrincipalDecayMass S := by
    dsimp [r]
    simp_rw [mul_pow]
    rw [show Real.sqrt (X : ℝ) ^ 4 =
      (Real.sqrt (X : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hX0]
    rw [← Finset.mul_sum, sum_principalPerronWeight_fourth]
  unfold selectedPrefixFourthMass
  calc
    (∑ z ∈ S, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
        ∑ z ∈ S, 64 * (C * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + r z ^ 4) :=
      Finset.sum_le_sum fun z hz => hpoint4 z hz
    _ = 64 * (C * L ^ 2) ^ 4 *
        ((∑ z ∈ S, V z ^ 4) +
          (S.card : ℝ) * (a ^ 4 + b ^ 4) +
          ∑ z ∈ S, r z ^ 4) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 64 * (C * L ^ 2) ^ 4 *
        (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
            ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
              Real.log x0 ^ 401) +
          (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4) +
          (X : ℝ) ^ 2 * selectedPrincipalDecayMass S) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [ha4, hb4, hrsum]
      exact add_le_add (add_le_add hVsum (le_refl _)) (le_refl _)
    _ = _ := by rfl

end
end MAPBHPCanonicalAllCharacterFromPrincipal

#print axioms MAPBHPCanonicalAllCharacterFromPrincipal.isPrincipalCharacter_iff_eq_one
#print axioms MAPBHPCanonicalAllCharacterFromPrincipal.principalPerronWeight_eq_ite_eq_one
#print axioms MAPBHPCanonicalAllCharacterFromPrincipal.canonicalPrincipalPointwiseSourceLiteral_of_horizontal
#print axioms MAPBHPCanonicalAllCharacterFromPrincipal.allCharacter_selectedPrefixFourthMass_le_exactKernel
