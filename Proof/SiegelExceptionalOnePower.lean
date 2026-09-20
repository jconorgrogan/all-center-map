import GoldfeldFourLogAbsorption

/-!
# One-power exceptional-zero decay for pointwise Siegel--Walfisz

The AP second-moment route naturally produces `X^(2*(beta-1))`.  A pointwise
explicit formula contains `x^beta`, so it needs the corresponding one-power
decay.  This file derives that form directly from the already certified
published Siegel zero-free region.
 -/

namespace MAPSiegelExceptionalOnePower

open Filter
open MAPSiegelExceptionalEndpoint MAPGoldfeldSiegel

noncomputable section

theorem PublishedSiegelRealZeroFreeRegion.eventually_prefactor_mul_onePower_le
    (hSiegel : PublishedSiegelRealZeroFreeRegion)
    {K A P : ℝ} (hK : 0 < K) (hA : 0 < A) (hP : 0 ≤ P) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
        (q : ℝ) ≤ Real.rpow (Real.log X) K →
        chi ≠ 1 → chi ^ 2 = 1 →
        DirichletCharacter.LFunction chi beta = 0 →
          Real.rpow (Real.log X) P * Real.rpow X (beta - 1) ≤
            Real.rpow (Real.log X) (-A) := by
  let nu : ℝ := 1 / (4 * K)
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hKnu : K * nu = 1 / 4 := by dsimp [nu]; field_simp
  have htheta : 0 < 1 - K * nu := by rw [hKnu]; norm_num
  rcases hSiegel.zero_gap hnu with ⟨c, hc, hgap⟩
  have htrade := eventually_exceptional_trade
    (A := A + P) (c := c / 2) (theta := 1 - K * nu)
    (add_pos_of_pos_of_nonneg hA hP) (half_pos hc) htheta
  filter_upwards [htrade, eventually_ge_atTop (Real.exp 1)] with X htradeX hX
  intro q _ chi beta hq hchi hreal hzero
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlogone : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlogone
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hqpow : Real.rpow (q : ℝ) nu ≤
      Real.rpow (Real.log X) (K * nu) := by
    calc
      Real.rpow (q : ℝ) nu ≤
          Real.rpow (Real.rpow (Real.log X) K) nu :=
        Real.rpow_le_rpow (Nat.cast_nonneg q) hq hnu.le
      _ = Real.rpow (Real.log X) (K * nu) :=
        (Real.rpow_mul hlogpos.le K nu).symm
  have hinv : Real.rpow (Real.log X) (-K * nu) ≤
      Real.rpow (q : ℝ) (-nu) := by
    calc
      Real.rpow (Real.log X) (-K * nu) =
          (Real.rpow (Real.log X) (K * nu))⁻¹ := by
        rw [show -K * nu = -(K * nu) by ring]
        exact Real.rpow_neg hlogpos.le (K * nu)
      _ ≤ (Real.rpow (q : ℝ) nu)⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos hlogpos (K * nu))
          (Real.rpow_pos_of_pos hqpos nu)).2 hqpow
      _ = Real.rpow (q : ℝ) (-nu) :=
        (Real.rpow_neg hqpos.le nu).symm
  have hgapX : c * Real.rpow (Real.log X) (-K * nu) ≤ 1 - beta :=
    (mul_le_mul_of_nonneg_left hinv hc.le).trans
      (hgap q chi hchi hreal beta hzero)
  have hmerge : Real.rpow (Real.log X) (1 - K * nu) =
      Real.log X * Real.rpow (Real.log X) (-K * nu) := by
    calc
      Real.rpow (Real.log X) (1 - K * nu) =
          Real.rpow (Real.log X) (1 + (-K * nu)) := by ring_nf
      _ = Real.rpow (Real.log X) 1 *
          Real.rpow (Real.log X) (-K * nu) :=
        Real.rpow_add hlogpos 1 (-K * nu)
      _ = Real.log X * Real.rpow (Real.log X) (-K * nu) := by simp
  rw [hmerge] at htradeX
  have hexponent : Real.log X * (beta - 1) ≤
      Real.log (Real.log X) * (-(A + P)) := by
    have hscaled := mul_le_mul_of_nonneg_left hgapX hlogpos.le
    nlinarith
  have hpoint : Real.rpow X (beta - 1) ≤
      Real.rpow (Real.log X) (-(A + P)) := by
    calc
      Real.rpow X (beta - 1) =
          Real.exp (Real.log X * (beta - 1)) :=
        Real.rpow_def_of_pos hXpos _
      _ ≤ Real.exp (Real.log (Real.log X) * (-(A + P))) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.rpow (Real.log X) (-(A + P)) :=
        (Real.rpow_def_of_pos hlogpos _).symm
  calc
    Real.rpow (Real.log X) P * Real.rpow X (beta - 1) ≤
        Real.rpow (Real.log X) P *
          Real.rpow (Real.log X) (-(A + P)) :=
      mul_le_mul_of_nonneg_left hpoint (Real.rpow_nonneg hlogpos.le P)
    _ = Real.rpow (Real.log X) (P + -(A + P)) :=
      (Real.rpow_add hlogpos P (-(A + P))).symm
    _ = Real.rpow (Real.log X) (-A) := by ring_nf

theorem eventually_prefactor_mul_onePower_le
    {K A P : ℝ} (hK : 0 < K) (hA : 0 < A) (hP : 0 ≤ P) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
        (q : ℝ) ≤ Real.rpow (Real.log X) K →
        chi ≠ 1 → chi ^ 2 = 1 →
        DirichletCharacter.LFunction chi beta = 0 →
          Real.rpow (Real.log X) P * Real.rpow X (beta - 1) ≤
            Real.rpow (Real.log X) (-A) :=
  PublishedSiegelRealZeroFreeRegion.eventually_prefactor_mul_onePower_le
    publishedSiegelRealZeroFreeRegion hK hA hP

end
end MAPSiegelExceptionalOnePower

#print axioms MAPSiegelExceptionalOnePower.PublishedSiegelRealZeroFreeRegion.eventually_prefactor_mul_onePower_le
#print axioms MAPSiegelExceptionalOnePower.eventually_prefactor_mul_onePower_le
