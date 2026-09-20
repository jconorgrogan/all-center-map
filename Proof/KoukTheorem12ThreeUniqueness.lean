import KoukTheorem12ThreeGlobal

/-!
# Uniqueness of the primitive exceptional zero

This is the remaining same-character uniqueness clause in Koukoulopoulos,
Theorem 12.3.  Two distinct real near-one zeros would contribute two poles
to the character term in `3-4-1`, while zeta and the principal square together
supply only four copies of the pole at the auxiliary displacement.
-/

namespace MAPKoukTheorem12ThreeUniqueness

set_option maxHeartbeats 600000

open Complex Set DirichletZeros MAPLocalZeroWindow MAPMellinDetectorLeaf
open MAPZeroFreeSiegelSpine MAPKoukTheorem12ThreePrimitive
open MAPKoukTheorem12ThreeGlobal
open MAPPrimitiveLogDerivativeRemainderUnconditional
open scoped BigOperators

noncomputable section

/-- The centered pole sum contains two distinct real zeros. -/
theorem re_centeredZeroPoleSum_ge_two_real
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u : ℝ} {rho₁ rho₂ : ℂ}
    (hu : 1 ≤ u)
    (h₁ : rho₁ ∈ centeredUnitWindowSupport chi (1 / 2) 0)
    (h₂ : rho₂ ∈ centeredUnitWindowSupport chi (1 / 2) 0)
    (him₁ : rho₁.im = 0) (him₂ : rho₂.im = 0)
    (hne : rho₁ ≠ rho₂) :
    1 / (u - rho₁.re) + 1 / (u - rho₂.re) ≤
      (centeredZeroPoleSum chi 0 (u : ℂ)).re := by
  let S := centeredUnitWindowSupport chi (1 / 2) 0
  let w : ℂ → ℝ := fun z =>
    (((zeroMultiplicity chi (1 / 2) (windowHeight (0 - 1 / 2)) z : ℂ) /
      ((u : ℂ) - z)).re)
  have hsub : ({rho₁, rho₂} : Finset ℂ) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact h₁
    · exact h₂
  have hw_nonneg : ∀ z ∈ S, 0 ≤ w z := by
    intro z hz
    simpa [w] using re_centeredZeroPoleTerm_nonneg chi hu hz
  have hsum : ∑ z ∈ ({rho₁, rho₂} : Finset ℂ), w z ≤ ∑ z ∈ S, w z :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z _ _ => hw_nonneg z ‹z ∈ S›)
  have hm₁ : (1 : ℝ) ≤ zeroMultiplicity chi (1 / 2)
      (windowHeight (0 - 1 / 2)) rho₁ := by
    have hpNat : 0 < zeroMultiplicity chi (1 / 2)
        (windowHeight (0 - 1 / 2)) rho₁ := zeroMultiplicity_pos_of_mem chi _ _
      (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi h₁)
    have hOneNat : 1 ≤ zeroMultiplicity chi (1 / 2)
        (windowHeight (0 - 1 / 2)) rho₁ := Nat.one_le_iff_ne_zero.mpr hpNat.ne'
    exact_mod_cast hOneNat
  have hm₂ : (1 : ℝ) ≤ zeroMultiplicity chi (1 / 2)
      (windowHeight (0 - 1 / 2)) rho₂ := by
    have hpNat : 0 < zeroMultiplicity chi (1 / 2)
        (windowHeight (0 - 1 / 2)) rho₂ := zeroMultiplicity_pos_of_mem chi _ _
      (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi h₂)
    have hOneNat : 1 ≤ zeroMultiplicity chi (1 / 2)
        (windowHeight (0 - 1 / 2)) rho₂ := Nat.one_le_iff_ne_zero.mpr hpNat.ne'
    exact_mod_cast hOneNat
  have hre₁ := re_lt_one_of_mem_zeroSupport chi
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi h₁)
  have hre₂ := re_lt_one_of_mem_zeroSupport chi
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi h₂)
  have ha₁ : 0 < u - rho₁.re := by linarith
  have ha₂ : 0 < u - rho₂.re := by linarith
  have hw₁ : 1 / (u - rho₁.re) ≤ w rho₁ := by
    have heq := re_centeredZeroPoleTerm_eq_reciprocal_of_im_eq
      chi (by linarith : rho₁.re < u) (ρ := rho₁) (t := 0) him₁
    have heq' :
        (((zeroMultiplicity chi (1 / 2) (windowHeight (0 - 1 / 2)) rho₁ : ℂ) /
          ((u : ℂ) - rho₁)).re) =
          (zeroMultiplicity chi (1 / 2) (windowHeight (0 - 1 / 2)) rho₁ : ℝ) /
            (u - rho₁.re) := by
      simpa using heq
    dsimp [w]
    rw [heq']
    exact div_le_div_of_nonneg_right hm₁ ha₁.le
  have hw₂ : 1 / (u - rho₂.re) ≤ w rho₂ := by
    have heq := re_centeredZeroPoleTerm_eq_reciprocal_of_im_eq
      chi (by linarith : rho₂.re < u) (ρ := rho₂) (t := 0) him₂
    have heq' :
        (((zeroMultiplicity chi (1 / 2) (windowHeight (0 - 1 / 2)) rho₂ : ℂ) /
          ((u : ℂ) - rho₂)).re) =
          (zeroMultiplicity chi (1 / 2) (windowHeight (0 - 1 / 2)) rho₂ : ℝ) /
            (u - rho₂.re) := by
      simpa using heq
    dsimp [w]
    rw [heq']
    exact div_le_div_of_nonneg_right hm₂ ha₂.le
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton] at hsum
  have hsum' : w rho₁ + w rho₂ ≤
      (centeredZeroPoleSum chi 0 (u : ℂ)).re := by
    rw [centeredZeroPoleSum, Complex.re_sum]
    change w rho₁ + w rho₂ ≤ ∑ z ∈ S, w z
    exact hsum
  exact (add_le_add hw₁ hw₂).trans hsum'

/-- Pair-selected form of Lemma 12.2 for two distinct real zeros. -/
theorem neg_logDeriv_two_real_re_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {u : ℝ} {rho₁ rho₂ : ℂ}
    (hu : 1 < u) (hu2 : u ≤ 2)
    (h₁ : rho₁ ∈ centeredUnitWindowSupport chi (1 / 2) 0)
    (h₂ : rho₂ ∈ centeredUnitWindowSupport chi (1 / 2) 0)
    (him₁ : rho₁.im = 0) (him₂ : rho₂.im = 0)
    (hne : rho₁ ≠ rho₂) :
    (-logDeriv (DirichletCharacter.LFunction chi) (u : ℂ)).re ≤
      17000 * Real.log (arithmeticScale q 0) -
        (1 / (u - rho₁.re) + 1 / (u - rho₂.re)) := by
  have hformula := neg_logDeriv_LFunction_eq_centeredZeroSum_add_remainder
    chi hchi hu.le 0
  have hpairs := re_centeredZeroPoleSum_ge_two_real chi hu.le
    h₁ h₂ him₁ him₂ hne
  have hrem := primitiveLogDerivativeRemainder_le chi hprim hchi
    (t := 0) hu hu2
  have hremRe := (Complex.re_le_norm _).trans hrem
  norm_num at hformula hpairs ⊢
  have hre := congrArg Complex.re hformula
  simp only [Complex.neg_re, Complex.add_re] at hre
  linarith

/-- Two real zeros in the Theorem 12.3 collar coincide. -/
theorem primitive_nearOne_real_zero_unique
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    (hsq : chi ^ 2 = 1)
    {rho₁ rho₂ : ℂ}
    (h₁ : rho₁ ∈ centeredUnitWindowSupport chi (1 / 2) 0)
    (h₂ : rho₂ ∈ centeredUnitWindowSupport chi (1 / 2) 0)
    (him₁ : rho₁.im = 0) (him₂ : rho₂.im = 0)
    (hnear₁ : 1 - rho₁.re <
      1 / (100000000000 * Real.log (arithmeticScale q 0)))
    (hnear₂ : 1 - rho₂.re <
      1 / (100000000000 * Real.log (arithmeticScale q 0))) :
    rho₁ = rho₂ := by
  by_contra hne
  let L := Real.log (arithmeticScale q 0)
  let delta := 1 / (1000000000 * L)
  let u := 1 + delta
  have hS2 := two_le_arithmeticScale (q := q) 0
  have hlog2le : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hS2
  have hL : 1 / 2 < L := by nlinarith [Real.log_two_gt_d9]
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta_inv : 1 / delta = 1000000000 * L := by
    dsimp [delta]
    field_simp
  have hu : 1 < u := by dsimp [u]; linarith
  have hu2 : u ≤ 2 := by
    have hden : 1 ≤ 1000000000 * L := by nlinarith
    have hdle : delta ≤ 1 := by
      dsimp [delta]
      exact (div_le_one (by positivity)).2 hden
    dsimp [u]
    linarith
  let a₁ := u - rho₁.re
  let a₂ := u - rho₂.re
  have hre₁ := re_lt_one_of_mem_zeroSupport chi
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi h₁)
  have hre₂ := re_lt_one_of_mem_zeroSupport chi
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi h₂)
  have ha₁ : 0 < a₁ := by dsimp [a₁, u]; linarith
  have ha₂ : 0 < a₂ := by dsimp [a₂, u]; linarith
  have hnear₁' : 1 - rho₁.re < delta / 100 := by
    dsimp [delta, L] at hnear₁ ⊢
    convert hnear₁ using 1 <;> ring
  have hnear₂' : 1 - rho₂.re < delta / 100 := by
    dsimp [delta, L] at hnear₂ ⊢
    convert hnear₂ using 1 <;> ring
  have ha₁Upper : a₁ < (101 / 100 : ℝ) * delta := by
    dsimp [a₁, u]
    linarith
  have ha₂Upper : a₂ < (101 / 100 : ℝ) * delta := by
    dsimp [a₂, u]
    linarith
  have hr₁ : 3900000000 * L < 4 / a₁ := by
    have hraw : 39 / (10 * delta) < 4 / a₁ := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 10 * delta) ha₁]
      nlinarith
    calc
      3900000000 * L = 39 / (10 * delta) := by
        rw [show 39 / (10 * delta) = (39 / 10) * (1 / delta) by field_simp]
        rw [hdelta_inv]
        ring
      _ < 4 / a₁ := hraw
  have hr₂ : 3900000000 * L < 4 / a₂ := by
    have hraw : 39 / (10 * delta) < 4 / a₂ := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 10 * delta) ha₂]
      nlinarith
    calc
      3900000000 * L = 39 / (10 * delta) := by
        rw [show 39 / (10 * delta) = (39 / 10) * (1 / delta) by field_simp]
        rw [hdelta_inv]
        ring
      _ < 4 / a₂ := hraw
  have hzeta0 := neg_logDeriv_riemannZeta_re_le hu hu2
  have hzeta : (-logDeriv riemannZeta (u : ℂ)).re ≤
      1 / delta + 100000 * L := by
    dsimp [u] at hzeta0 ⊢
    rw [show 1 + delta - 1 = delta by ring] at hzeta0
    exact hzeta0.trans (by nlinarith)
  have hchiBound := neg_logDeriv_two_real_re_le chi hprim hchi hu hu2
    h₁ h₂ him₁ him₂ hne
  have hchiBound' :
      (-logDeriv (DirichletCharacter.LFunction chi) (u : ℂ)).re ≤
      17000 * L - (1 / a₁ + 1 / a₂) := by
    simpa [L, a₁, a₂] using hchiBound
  have hsquare := neg_logDeriv_square_re_le chi hu hu2 (t := 0)
  have hpole :
      (1 / (((u : ℂ) + Complex.I * (2 * (0 : ℝ))) - 1)).re =
        1 / delta := by
    dsimp [u]
    norm_num
  rw [if_pos hsq, hpole] at hsquare
  have hsquareBound :
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 2)) (u : ℂ)).re ≤
      1 / delta + 204004 * L := by
    simpa [L] using hsquare
  have hpos : 0 ≤
      3 * (-logDeriv riemannZeta (u : ℂ)).re +
      4 * (-logDeriv (DirichletCharacter.LFunction chi) (u : ℂ)).re +
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 2)) (u : ℂ)).re := by
    simpa using threeCharacter_neg_logDeriv_re_nonneg chi hu 0
  have hup : 0 ≤
      3 * (1 / delta + 100000 * L) +
      4 * (17000 * L - (1 / a₁ + 1 / a₂)) +
      (1 / delta + 204004 * L) := by
    linarith [hpos, hzeta, hchiBound', hsquareBound]
  rw [hdelta_inv] at hup
  simp only [div_eq_mul_inv] at hr₁ hr₂ hup
  linarith

#print axioms MAPKoukTheorem12ThreeUniqueness.neg_logDeriv_two_real_re_le
#print axioms MAPKoukTheorem12ThreeUniqueness.primitive_nearOne_real_zero_unique

end

end MAPKoukTheorem12ThreeUniqueness
