import MRTCorollary53SourceBridge
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Reduced Dirichlet approximation on the unit additive circle

This file proves the rational-center selection used by the MAP far-source
reduction. It contains no analytic estimate.
-/

namespace MAPFarRationalApproximation

open AddCircle Metric Set
open MAPMajorArcWeld MAPMRTCorollary53Source

noncomputable section

private theorem rat_remainder_coprime (r : ℚ) :
    (r.num % (r.den : ℤ)).natAbs.Coprime r.den := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : (r.num % (r.den : ℤ)).gcd (r.den : ℤ) = 1 := by
    rw [Int.gcd_emod]
    exact Int.isCoprime_iff_gcd_eq_one.mp r.isCoprime_num_den
  rw [Int.gcd_eq_natAbs] at hg
  simpa using hg

private theorem rat_remainder_lt_den (r : ℚ) :
    (r.num % (r.den : ℤ)).natAbs < r.den := by
  have hden : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hnonneg : 0 ≤ r.num % (r.den : ℤ) := Int.emod_nonneg _ hden
  have hlt : r.num % (r.den : ℤ) < (r.den : ℤ) := by
    simpa using Int.emod_lt r.num hden
  rw [← Int.ofNat_lt]
  simpa [Int.natAbs_of_nonneg hnonneg] using hlt

private theorem rat_cast_circle_eq_rationalCenter (r : ℚ) :
    (((r : ℝ) : UnitAddCircle)) =
      rationalCenter r.den (r.num % (r.den : ℤ)).natAbs := by
  let rem : ℤ := r.num % (r.den : ℤ)
  let quot : ℤ := r.num / (r.den : ℤ)
  have hdenZ : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hdenR : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hrem0 : 0 ≤ rem := Int.emod_nonneg _ hdenZ
  have hnum : rem + (r.den : ℤ) * quot = r.num := by
    exact Int.emod_add_ediv _ _
  have hdiff : (r : ℝ) - (rem.natAbs : ℝ) / r.den = (quot : ℝ) := by
    rw [Rat.cast_def]
    have hremCast : (rem.natAbs : ℝ) = (rem : ℝ) := by
      calc
        (rem.natAbs : ℝ) = (((rem.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
        _ = (rem : ℝ) := by rw [Int.natAbs_of_nonneg hrem0]
    rw [hremCast]
    have hnumR : (r.num : ℝ) = (rem : ℝ) + (r.den : ℝ) * (quot : ℝ) := by
      exact_mod_cast hnum.symm
    rw [hnumR]
    field_simp [hdenR]
    ring
  unfold rationalCenter
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub]
  apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2
  refine ⟨quot, ?_⟩
  simpa [hdiff] using hdiff.symm

/-- Real-line Dirichlet approximation, reduced and converted to the exact
`rationalCenter + beta` normalization used by the MAP source input. -/
theorem exists_reduced_rational_lift_real
    (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ q a : ℕ, ∃ beta : ℝ,
      1 ≤ q ∧ q ≤ n ∧ a < q ∧ a.Coprime q ∧
      (x : UnitAddCircle) = rationalCenter q a + (beta : UnitAddCircle) ∧
      |beta| ≤ 1 / (((n : ℝ) + 1) * q) := by
  obtain ⟨r, hr, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hn
  let q : ℕ := r.den
  let a : ℕ := (r.num % (r.den : ℤ)).natAbs
  let beta : ℝ := x - (r : ℝ)
  refine ⟨q, a, beta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [q]
    exact r.den_pos
  · exact hrden
  · exact rat_remainder_lt_den r
  · exact rat_remainder_coprime r
  · have hrat := rat_cast_circle_eq_rationalCenter r
    dsimp [beta]
    rw [← hrat]
    abel
  · simpa [beta] using hr

/-- Circle-valued version. The representative is eliminated by quotient
induction, so the theorem is uniform in the anonymous circle center. -/
theorem exists_reduced_rational_lift_circle
    (center : UnitAddCircle) {n : ℕ} (hn : 0 < n) :
    ∃ q a : ℕ, ∃ beta : ℝ,
      1 ≤ q ∧ q ≤ n ∧ a < q ∧ a.Coprime q ∧
      center = rationalCenter q a + (beta : UnitAddCircle) ∧
      |beta| ≤ 1 / (((n : ℝ) + 1) * q) := by
  induction center using Quotient.inductionOn with
  | _ x => exact exists_reduced_rational_lift_real x hn

/-- Real-cutoff form used by MAP: for every `Q≥1`, the reduced denominator is
at most `Q` and the error is at most `1/(qQ)`. -/
theorem exists_reduced_rational_lift_circle_realCutoff
    (center : UnitAddCircle) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ q a : ℕ, ∃ beta : ℝ,
      1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a < q ∧ a.Coprime q ∧
      center = rationalCenter q a + (beta : UnitAddCircle) ∧
      |beta| ≤ 1 / ((q : ℝ) * Q) := by
  let n : ℕ := ⌊Q⌋₊
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.floor_pos.mpr hQ
  obtain ⟨q, a, beta, hq, hqn, ha, hcop, hcenter, hbeta⟩ :=
    exists_reduced_rational_lift_circle center hn
  refine ⟨q, a, beta, hq, ?_, ha, hcop, hcenter, ?_⟩
  · exact (by exact_mod_cast hqn : (q : ℝ) ≤ n).trans (Nat.floor_le (by linarith : 0 ≤ Q))
  · have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hQpos : 0 < Q := zero_lt_one.trans_le hQ
    have hQlt : Q < (n : ℝ) + 1 := by
      dsimp [n]
      exact Nat.lt_floor_add_one Q
    have hdenle : (q : ℝ) * Q ≤ ((n : ℝ) + 1) * q := by
      nlinarith
    have hdenpos : 0 < (q : ℝ) * Q := mul_pos hqR hQpos
    have hinv : 1 / (((n : ℝ) + 1) * q) ≤ 1 / ((q : ℝ) * Q) := by
      exact one_div_le_one_div_of_le hdenpos hdenle
    exact hbeta.trans hinv

/-- A rational lift of a center outside the inner collar automatically has
stationary width beyond the paper's far threshold. -/
theorem far_width_of_not_innerRationalCollars
    {epsilon X Q H beta : ℝ} {B Cc q a : ℕ}
    (hQdef : Q = (Real.log X) ^ B)
    (hHdef : H = MAPAllCenterApertureTransfer.baseAperture epsilon X)
    (hH : 0 < H)
    (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q)
    (ha : a < q) (hcop : a.Coprime q)
    {center : UnitAddCircle}
    (hcenter : center = rationalCenter q a + (beta : UnitAddCircle))
    (houtside : center ∉
      MAPAllCenterNearFarTransfer.innerRationalCollars epsilon X B Cc) :
    2 * (Real.log X) ^ Cc < stationaryWidth beta H := by
  have hdist : dist center (rationalCenter q a) ≤ |beta| := by
    rw [hcenter, dist_eq_norm]
    have hsub : rationalCenter q a + (beta : UnitAddCircle) -
        rationalCenter q a = (beta : UnitAddCircle) := by abel
    rw [hsub]
    simpa [Real.norm_eq_abs] using
      (QuotientAddGroup.norm_mk_le_norm :
        ‖(beta : UnitAddCircle)‖ ≤ ‖beta‖)
  by_contra hnot
  have hwidth : stationaryWidth beta H ≤ 2 * (Real.log X) ^ Cc :=
    le_of_not_gt hnot
  have hbetaRadius : |beta| ≤
      2 * (Real.log X) ^ Cc /
        MAPAllCenterApertureTransfer.baseAperture epsilon X := by
    rw [← hHdef]
    apply (le_div_iff₀ hH).2
    simpa [stationaryWidth, mul_comm] using hwidth
  apply houtside
  refine ⟨q, a, hq, ?_, ha, hcop, hdist.trans hbetaRadius⟩
  simpa [hQdef] using hqQ

/-- Complete deterministic rational-center selection for the MAP far branch.
The only assumptions are positivity of the logarithmic cutoff and aperture and
that the center lies outside the declared collar. -/
theorem exists_far_reduced_rational_lift
    {epsilon X Q H : ℝ} {B Cc : ℕ}
    (hQdef : Q = (Real.log X) ^ B)
    (hHdef : H = MAPAllCenterApertureTransfer.baseAperture epsilon X)
    (hQ : 1 ≤ Q) (hH : 0 < H)
    (center : UnitAddCircle)
    (houtside : center ∉
      MAPAllCenterNearFarTransfer.innerRationalCollars epsilon X B Cc) :
    ∃ q a : ℕ, ∃ beta : ℝ,
      1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a < q ∧ a.Coprime q ∧
      center = rationalCenter q a + (beta : UnitAddCircle) ∧
      |beta| ≤ 1 / ((q : ℝ) * Q) ∧
      2 * (Real.log X) ^ Cc < stationaryWidth beta H := by
  obtain ⟨q, a, beta, hq, hqQ, ha, hcop, hcenter, hbeta⟩ :=
    exists_reduced_rational_lift_circle_realCutoff center hQ
  refine ⟨q, a, beta, hq, hqQ, ha, hcop, hcenter, hbeta, ?_⟩
  exact far_width_of_not_innerRationalCollars hQdef hHdef hH hq hqQ ha hcop
    hcenter houtside


end
end MAPFarRationalApproximation

#print axioms MAPFarRationalApproximation.exists_reduced_rational_lift_circle_realCutoff
#print axioms MAPFarRationalApproximation.far_width_of_not_innerRationalCollars
#print axioms MAPFarRationalApproximation.exists_far_reduced_rational_lift
