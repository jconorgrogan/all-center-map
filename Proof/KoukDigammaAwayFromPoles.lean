import KoukGammaFactorLogDerivative
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Digamma growth away from the nonpositive integers

The recurrence part of the uniform digamma estimate is completely
deterministic.  This module records it with the exact fixed clearance needed
after the parity shift `z = (s+a)/2`.
-/

namespace KoukDigammaAwayFromPoles

open Complex
open scoped BigOperators

noncomputable section

/-- Iterated digamma recurrence, retaining every reciprocal correction. -/
theorem digamma_add_nat
    (z : ℂ) (n : ℕ)
    (hclear : ∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) :
    Complex.digamma (z + (n : ℂ)) =
      Complex.digamma z +
        ∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpole : ∀ m : ℕ, z + (n : ℂ) ≠ -(m : ℂ) := by
        intro m hnm
        have hz : z + ((n + m : ℕ) : ℂ) = 0 := by
          push_cast
          linear_combination hnm
        have hpos := hclear (n + m)
        rw [hz, norm_zero] at hpos
        norm_num at hpos
      have hrec := Complex.digamma_apply_add_one (z + (n : ℂ)) hpole
      rw [Nat.cast_succ]
      rw [show z + ((n : ℂ) + 1) = z + (n : ℂ) + 1 by ring]
      rw [hrec, ih, Finset.sum_range_succ]
      ring

/-- Equivalent solved form used to move an arbitrary point into the right
half-plane. -/
theorem digamma_eq_shifted_sub_reciprocal_sum
    (z : ℂ) (n : ℕ)
    (hclear : ∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) :
    Complex.digamma z =
      Complex.digamma (z + (n : ℂ)) -
        ∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹ := by
  rw [digamma_add_nat z n hclear]
  ring

/-- Fixed clearance gives the literal reciprocal cap used for the two terms
nearest the shifted strip. -/
theorem norm_inv_add_nat_le_four
    (z : ℂ)
    (hclear : ∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖)
    (k : ℕ) :
    ‖(z + (k : ℂ))⁻¹‖ ≤ 4 := by
  have hk := hclear k
  have hpos : 0 < ‖z + (k : ℂ)‖ := lt_of_lt_of_le (by norm_num) hk
  rw [norm_inv]
  exact (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 4)).2 (by
    norm_num
    exact hk)

/-- After shifting into `Re ≤ 2`, each reciprocal correction has a harmonic
majorant.  The constant eight simultaneously covers the two nearest poles and
the elementary real-part estimate for all remaining terms. -/
theorem norm_inv_add_nat_le_eight_div
    (z : ℂ) {n k : ℕ} (hk : k < n)
    (hclear : ∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖)
    (hupper : (z + (n : ℂ)).re ≤ 2) :
    ‖(z + (k : ℂ))⁻¹‖ ≤ 8 / (n - k : ℕ) := by
  let d : ℕ := n - k
  have hd : 0 < d := Nat.sub_pos_of_lt hk
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hquarter := hclear k
  have hnormPos : 0 < ‖z + (k : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) hquarter
  have hden : (d : ℝ) / 8 ≤ ‖z + (k : ℂ)‖ := by
    by_cases hd2 : d ≤ 2
    · have hd2Real : (d : ℝ) ≤ 2 := by exact_mod_cast hd2
      have : (d : ℝ) / 8 ≤ 1 / 4 := by linarith
      exact this.trans hquarter
    · have hd3 : 3 ≤ d := by omega
      have hreEq : (z + (k : ℂ)).re =
          (z + (n : ℂ)).re - (d : ℝ) := by
        change z.re + (k : ℝ) = z.re + (n : ℝ) - (d : ℝ)
        dsimp [d]
        rw [Nat.cast_sub hk.le]
        ring
      have hreUpper : (z + (k : ℂ)).re ≤ 2 - (d : ℝ) := by
        rw [hreEq]
        linarith
      have hreNonpos : (z + (k : ℂ)).re ≤ 0 := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
        linarith
      have habs : (d : ℝ) - 2 ≤ |(z + (k : ℂ)).re| := by
        rw [abs_of_nonpos hreNonpos]
        linarith
      have hfrac : (d : ℝ) / 8 ≤ (d : ℝ) - 2 := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
        linarith
      exact hfrac.trans (habs.trans (Complex.abs_re_le_norm _))
  rw [norm_inv]
  have heq : 8 / (d : ℝ) = ((d : ℝ) / 8)⁻¹ := by field_simp
  rw [show (n - k : ℕ) = d by rfl]
  rw [heq]
  exact (inv_le_inv₀ hnormPos (div_pos hdReal (by norm_num))).2 hden

/-- The entire recurrence correction is logarithmic in the shift length. -/
theorem sum_norm_inv_add_nat_le_eight_harmonic
    (z : ℂ) (n : ℕ)
    (hclear : ∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖)
    (hupper : (z + (n : ℂ)).re ≤ 2) :
    ∑ k ∈ Finset.range n, ‖(z + (k : ℂ))⁻¹‖ ≤
      8 * (harmonic n : ℝ) := by
  calc
    ∑ k ∈ Finset.range n, ‖(z + (k : ℂ))⁻¹‖ ≤
        ∑ k ∈ Finset.range n, 8 / ((n - k : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_inv_add_nat_le_eight_div z
        (Finset.mem_range.mp hk) hclear hupper
    _ = ∑ j ∈ Finset.range n, 8 / ((j + 1 : ℕ) : ℝ) := by
      have hreflect := Finset.sum_range_reflect
        (fun j : ℕ => (8 : ℝ) / ((j + 1 : ℕ) : ℝ)) n
      calc
        ∑ k ∈ Finset.range n, 8 / ((n - k : ℕ) : ℝ) =
            ∑ j ∈ Finset.range n,
              8 / ((n - 1 - j + 1 : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjn : j < n := Finset.mem_range.mp hj
          congr 3
          omega
        _ = ∑ j ∈ Finset.range n, 8 / ((j + 1 : ℕ) : ℝ) := hreflect
    _ = 8 * (harmonic n : ℝ) := by
      unfold harmonic
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjpos : (0 : ℝ) < j + 1 := by positivity
      field_simp

/-- Logarithmic recurrence bound once the shifted point lies in the unit-width
right-half-plane strip.  This is the exact deterministic interface between the
pole-clearance argument and the remaining analytic estimate for `digamma` in
`Re z ≥ 1`. -/
theorem norm_digamma_le_shifted_add_eight_harmonic
    (z : ℂ) (n : ℕ)
    (hclear : ∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖)
    (hupper : (z + (n : ℂ)).re ≤ 2) :
    ‖Complex.digamma z‖ ≤
      ‖Complex.digamma (z + (n : ℂ))‖ + 8 * (harmonic n : ℝ) := by
  rw [digamma_eq_shifted_sub_reciprocal_sum z n hclear]
  refine (norm_sub_le _ _).trans ?_
  have hsum : ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ ≤
      ∑ k ∈ Finset.range n, ‖(z + (k : ℂ))⁻¹‖ :=
    norm_sum_le _ _
  exact add_le_add (le_refl _)
    (hsum.trans (sum_norm_inv_add_nat_le_eight_harmonic z n hclear hupper))

/-- Canonical controlled shift into `1 ≤ Re z < 2`.  The shift length costs at
most the natural radial scale `‖z‖ + 2`. -/
theorem exists_nat_shift_to_right_strip (z : ℂ) (hz : z.re < 1) :
    ∃ n : ℕ,
      0 < n ∧
      1 ≤ (z + (n : ℂ)).re ∧
      (z + (n : ℂ)).re < 2 ∧
      (n : ℝ) ≤ ‖z‖ + 2 := by
  let n : ℕ := ⌈(1 - z.re : ℝ)⌉₊
  have hxpos : 0 < (1 - z.re : ℝ) := sub_pos.mpr hz
  have hnpos : 0 < n := (Nat.ceil_pos.mpr hxpos)
  have hxn : (1 - z.re : ℝ) ≤ n := Nat.le_ceil _
  have hnx : (n : ℝ) < (1 - z.re) + 1 :=
    Nat.ceil_lt_add_one hxpos.le
  have hnormRe : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  refine ⟨n, hnpos, ?_, ?_, ?_⟩
  · change 1 ≤ z.re + (n : ℝ)
    linarith
  · change z.re + (n : ℝ) < 2
    linarith
  · have hzneg : -z.re ≤ |z.re| := neg_le_abs z.re
    linarith

/-- The genuinely analytic base estimate left after recurrence has removed all
pole geometry.  Unlike the final away-from-poles statement, this has no
clearance hypothesis and lives entirely in the pole-free half-plane. -/
abbrev RightHalfPlaneDigammaLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.re →
    ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2)

/-- The right-half-plane estimate plus the certified recurrence implies the
uniform estimate at fixed distance from every nonpositive integer. -/
theorem awayFromPolesDigammaLogBound_of_rightHalfPlane
    (hRight : RightHalfPlaneDigammaLogBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  obtain ⟨C, hCpos, hC⟩ := hRight
  let ell2 : ℝ := Real.log 2
  have hell2pos : 0 < ell2 := Real.log_pos (by norm_num)
  let C' : ℝ := 2 * C + 8 * (1 / ell2 + 1)
  have hC'pos : 0 < C' := by
    dsimp [C']
    positivity
  refine ⟨C', hC'pos, ?_⟩
  intro z hclear
  let L : ℝ := Real.log (‖z‖ + 2)
  have ha2 : (2 : ℝ) ≤ ‖z‖ + 2 := by
    linarith [norm_nonneg z]
  have hapos : 0 < ‖z‖ + 2 := lt_of_lt_of_le (by norm_num) ha2
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith)
  have hell2le : ell2 ≤ L := by
    dsimp [ell2, L]
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < 2 by norm_num) hapos ha2
  by_cases hz : 1 ≤ z.re
  · have hbase := hC z hz
    have hCC' : C ≤ C' := by
      dsimp [C']
      have hinv : 0 < (1 / ell2 : ℝ) := one_div_pos.mpr hell2pos
      nlinarith
    exact hbase.trans (mul_le_mul_of_nonneg_right hCC' hLnonneg)
  · have hzlt : z.re < 1 := lt_of_not_ge hz
    obtain ⟨n, hnpos, hnlo, hnhi, hnscale⟩ :=
      exists_nat_shift_to_right_strip z hzlt
    let w : ℂ := z + (n : ℂ)
    have hwupper : w.re ≤ 2 := hnhi.le
    have hwbase := hC w hnlo
    have hnormw : ‖w‖ + 2 ≤ 2 * (‖z‖ + 2) := by
      have htri : ‖w‖ ≤ ‖z‖ + (n : ℝ) := by
        dsimp [w]
        simpa using norm_add_le z (n : ℂ)
      linarith
    have htwoa_sq : 2 * (‖z‖ + 2) ≤ (‖z‖ + 2) ^ 2 := by
      nlinarith
    have hlogw : Real.log (‖w‖ + 2) ≤ 2 * L := by
      have hwpos : 0 < ‖w‖ + 2 := by positivity
      have hmono : Real.log (‖w‖ + 2) ≤
          Real.log ((‖z‖ + 2) ^ 2) :=
        Real.strictMonoOn_log.monotoneOn hwpos
          (sq_pos_of_pos hapos)
          (hnormw.trans htwoa_sq)
      rw [Real.log_pow] at hmono
      simpa [L] using hmono
    have hbase : ‖Complex.digamma w‖ ≤ 2 * C * L := by
      calc
        ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := hwbase
        _ ≤ C * (2 * L) := mul_le_mul_of_nonneg_left hlogw hCpos.le
        _ = 2 * C * L := by ring
    have hnlog : Real.log (n : ℝ) ≤ L := by
      have hnrealpos : (0 : ℝ) < n := by exact_mod_cast hnpos
      dsimp [L]
      exact Real.strictMonoOn_log.monotoneOn hnrealpos hapos hnscale
    have hOne : (1 : ℝ) ≤ (1 / ell2) * L := by
      have : (1 : ℝ) ≤ L / ell2 :=
        (le_div_iff₀ hell2pos).2 (by simpa using hell2le)
      simpa [div_eq_mul_inv, mul_comm] using this
    have hharmonic : (harmonic n : ℝ) ≤ (1 / ell2 + 1) * L := by
      have hh := harmonic_le_one_add_log n
      calc
        (harmonic n : ℝ) ≤ 1 + Real.log (n : ℝ) := hh
        _ ≤ (1 / ell2) * L + L := add_le_add hOne hnlog
        _ = (1 / ell2 + 1) * L := by ring
    have hrec := norm_digamma_le_shifted_add_eight_harmonic
      z n hclear hwupper
    calc
      ‖Complex.digamma z‖ ≤ ‖Complex.digamma w‖ +
          8 * (harmonic n : ℝ) := hrec
      _ ≤ 2 * C * L + 8 * ((1 / ell2 + 1) * L) := by
        gcongr
      _ = C' * L := by
        dsimp [C']
        ring

/-- Coarse recurrence bound.  The sharper logarithmic summation is isolated
from the analytic right-half-plane estimate and can be improved independently.
-/
theorem norm_digamma_le_shifted_add_four_mul
    (z : ℂ) (n : ℕ)
    (hclear : ∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) :
    ‖Complex.digamma z‖ ≤
      ‖Complex.digamma (z + (n : ℂ))‖ + 4 * n := by
  rw [digamma_eq_shifted_sub_reciprocal_sum z n hclear]
  refine (norm_sub_le _ _).trans ?_
  have hsum : ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ ≤
      ∑ _k ∈ Finset.range n, (4 : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    exact norm_inv_add_nat_le_four z hclear k
  calc
    ‖Complex.digamma (z + (n : ℂ))‖ +
        ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ ≤
      ‖Complex.digamma (z + (n : ℂ))‖ +
        ∑ _k ∈ Finset.range n, (4 : ℝ) := add_le_add_right hsum _
    _ = ‖Complex.digamma (z + (n : ℂ))‖ + 4 * n := by
      simp [nsmul_eq_mul, mul_comm]

end
end KoukDigammaAwayFromPoles

#print axioms KoukDigammaAwayFromPoles.digamma_add_nat
#print axioms KoukDigammaAwayFromPoles.sum_norm_inv_add_nat_le_eight_harmonic
#print axioms KoukDigammaAwayFromPoles.exists_nat_shift_to_right_strip
#print axioms KoukDigammaAwayFromPoles.awayFromPolesDigammaLogBound_of_rightHalfPlane
#print axioms KoukDigammaAwayFromPoles.norm_digamma_le_shifted_add_four_mul
