import GoldfeldLemma11TwoFinite
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Conditional Dirichlet-series continuation for nonprincipal characters

The source proof of Koukoulopoulos, Lemma 11.2 differentiates the ordered
Dirichlet series in `Re s > 0`.  Mathlib's `LSeries` API is intentionally
restricted to absolute convergence.  Here we construct the missing
continuation connector by summing complete residue blocks.
-/

namespace MAPGoldfeldSiegel

open Complex Set LSeries Filter Topology
open scoped BigOperators

noncomputable section

/-- A complete modulus block of the character Dirichlet series. -/
def characterLBlock {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, LSeries.term (fun n : ℕ => chi n) s (j.val + N * m)

/-- In the half-plane of absolute convergence, summing complete blocks is
exactly the ordinary L-series. -/
theorem tsum_characterLBlock_eq_LSeries_of_one_lt_re
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' m : ℕ, characterLBlock chi m s) =
      LSeries (fun n : ℕ => chi n) s := by
  have hsum : Summable (LSeries.term (fun n : ℕ => chi n) s) :=
    ZMod.LSeriesSummable_of_one_lt_re chi hs
  have hj : ∀ j : ZMod N,
      Summable (fun m : ℕ =>
        LSeries.term (fun n : ℕ => chi n) s (j.val + N * m)) := by
    intro j
    apply hsum.comp_injective
    intro a b hab
    have hmul : N * a = N * b := Nat.add_left_cancel hab
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos N) hmul
  simp only [characterLBlock]
  rw [Summable.tsum_finsetSum (fun j _ => hj j)]
  rw [← Nat.sumByResidueClasses hsum N]
  rfl

/-- A complete positive block after subtracting a common endpoint weight.
The subtraction exposes the extra factor `m⁻¹` responsible for convergence
throughout `Re s > 0`. -/
def centeredCharacterLBlock {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, chi j *
    (((j.val + N * (m + 1) : ℕ) : ℂ) ^ (-s) -
      (((N * (m + 2) : ℕ) : ℂ) ^ (-s)))

/-- Centering does not change a positive complete block for a nonprincipal
character. -/
theorem centeredCharacterLBlock_eq
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    (m : ℕ) (s : ℂ) :
    centeredCharacterLBlock chi m s = characterLBlock chi (m + 1) s := by
  have hsum : ∑ j : ZMod N, chi j = 0 :=
    MulChar.sum_eq_zero_of_ne_one hchi
  rw [centeredCharacterLBlock, characterLBlock]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hn : j.val + N * (m + 1) ≠ 0 := by
    have hmul : 0 < N * (m + 1) := Nat.mul_pos (NeZero.pos N) (Nat.succ_pos m)
    omega
  rw [LSeries.term_of_ne_zero hn]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  rw [show ((j.val + N * (m + 1) : ℕ) : ZMod N) = j by simp]

/-- The block sum continuation, with the first block kept finite. -/
def conditionalCharacterLSeries {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  characterLBlock chi 0 s + ∑' m : ℕ, centeredCharacterLBlock chi m s

/-- The conditional block continuation agrees with the ordinary L-series on
`Re s > 1`. -/
theorem conditionalCharacterLSeries_eq_LSeries_of_one_lt_re
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    conditionalCharacterLSeries chi s = LSeries (fun n : ℕ => chi n) s := by
  have hblocks : Summable (fun m : ℕ => characterLBlock chi m s) := by
    have hsum : Summable (LSeries.term (fun n : ℕ => chi n) s) :=
      ZMod.LSeriesSummable_of_one_lt_re chi hs
    have hj : ∀ j : ZMod N,
        Summable (fun m : ℕ =>
          LSeries.term (fun n : ℕ => chi n) s (j.val + N * m)) := by
      intro j
      apply hsum.comp_injective
      intro a b hab
      exact Nat.eq_of_mul_eq_mul_left (NeZero.pos N) (Nat.add_left_cancel hab)
    exact summable_sum (fun j _ => hj j)
  rw [conditionalCharacterLSeries]
  simp_rw [centeredCharacterLBlock_eq chi hchi]
  calc
    characterLBlock chi 0 s + ∑' m : ℕ, characterLBlock chi (m + 1) s =
        ∑' m : ℕ, characterLBlock chi m s := by
      simpa using hblocks.sum_add_tsum_nat_add 1
    _ = LSeries (fun n : ℕ => chi n) s :=
      tsum_characterLBlock_eq_LSeries_of_one_lt_re chi hs

/-- A quantitative real-segment mean-value estimate for complex powers. -/
theorem norm_cpow_neg_sub_cpow_neg_le
    {a B x y : ℝ} {s : ℂ}
    (ha : 0 < a) (hsre : a ≤ s.re) (hsnorm : ‖s‖ ≤ B)
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      B * (y - x) * Real.rpow x (-a - 1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsne : s ≠ 0 := by
    intro hs0
    subst s
    simp at hsre
    linarith
  have hB : 0 ≤ B := (norm_nonneg s).trans hsnorm
  have hdiff : ∀ t ∈ Set.Icc x y,
      HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc x y) t := by
    intro t ht
    have htpos : 0 < t := hxpos.trans_le ht.1
    exact (hasDerivAt_ofReal_cpow_const htpos.ne' (neg_ne_zero.mpr hsne)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico x y,
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ B * Real.rpow x (-a - 1) := by
    intro t ht
    have htpos : 0 < t := hxpos.trans_le ht.1
    have htOne : 1 ≤ t := hx.trans ht.1
    have hexp : -s.re - 1 ≤ -a - 1 := by linarith
    have hpowExp : Real.rpow t (-s.re - 1) ≤ Real.rpow t (-a - 1) :=
      Real.rpow_le_rpow_of_exponent_le htOne hexp
    have hpowBase : Real.rpow t (-a - 1) ≤ Real.rpow x (-a - 1) := by
      exact Real.rpow_le_rpow_of_nonpos hxpos ht.1 (by linarith)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    simp only [neg_re, sub_re, one_re]
    exact (mul_le_mul_of_nonneg_left (hpowExp.trans hpowBase) (norm_nonneg s)).trans
      (mul_le_mul_of_nonneg_right hsnorm (Real.rpow_nonneg hxpos.le _))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hdiff hbound y
    (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev]
  exact hmv.trans_eq (by ring)

/-- Locally uniform `m⁻¹⁻ᵃ` majorant for centered complete blocks. -/
theorem norm_centeredCharacterLBlock_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {a B : ℝ} (ha : 0 < a) {s : ℂ}
    (hsre : a ≤ s.re) (hsnorm : ‖s‖ ≤ B) (m : ℕ) :
    ‖centeredCharacterLBlock chi m s‖ ≤
      B * (N : ℝ) ^ 2 * Real.rpow (m + 1 : ℝ) (-a - 1) := by
  have hN : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  rw [centeredCharacterLBlock]
  calc
    ‖∑ j : ZMod N, chi j *
        (((j.val + N * (m + 1) : ℕ) : ℂ) ^ (-s) -
          (((N * (m + 2) : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ j : ZMod N, ‖chi j *
          (((j.val + N * (m + 1) : ℕ) : ℂ) ^ (-s) -
            (((N * (m + 2) : ℕ) : ℂ) ^ (-s)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
          B * (N : ℝ) * Real.rpow (m + 1 : ℝ) (-a - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      let x : ℕ := j.val + N * (m + 1)
      let y : ℕ := N * (m + 2)
      have hxOne : 1 ≤ x := by
        dsimp [x]
        have : 0 < N * (m + 1) := Nat.mul_pos hN (Nat.succ_pos m)
        omega
      have hxy : x ≤ y := by
        dsimp [x, y]
        have hjlt := j.val_lt
        rw [show N * (m + 2) = N * (m + 1) + N by ring]
        omega
      have hgap : (y : ℝ) - x ≤ (N : ℝ) := by
        have hgapNat : y - x ≤ N := by
          dsimp [x, y]
          rw [show N * (m + 2) = N * (m + 1) + N by ring]
          omega
        exact_mod_cast hgapNat
      have hbase : (m + 1 : ℝ) ≤ x := by
        exact_mod_cast (show m + 1 ≤ x by
          dsimp [x]
          have hNOne : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
          nlinarith)
      have hpow : Real.rpow (x : ℝ) (-a - 1) ≤
          Real.rpow (m + 1 : ℝ) (-a - 1) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
      have hdiff := norm_cpow_neg_sub_cpow_neg_le ha hsre hsnorm
        (show (1 : ℝ) ≤ x by exact_mod_cast hxOne)
        (show (x : ℝ) ≤ y by exact_mod_cast hxy)
      rw [norm_mul]
      calc
        ‖chi j‖ * ‖((x : ℂ) ^ (-s) - (y : ℂ) ^ (-s))‖
            ≤ 1 * ‖((x : ℂ) ^ (-s) - (y : ℂ) ^ (-s))‖ := by
              exact mul_le_mul_of_nonneg_right (chi.norm_le_one j) (norm_nonneg _)
        _ ≤ 1 * (B * ((y : ℝ) - x) * Real.rpow (x : ℝ) (-a - 1)) := by
              exact mul_le_mul_of_nonneg_left hdiff (by norm_num)
        _ ≤ B * (N : ℝ) * Real.rpow (m + 1 : ℝ) (-a - 1) := by
          have hB : 0 ≤ B := (norm_nonneg s).trans hsnorm
          have hp : 0 ≤ Real.rpow (x : ℝ) (-a - 1) :=
            Real.rpow_nonneg (Nat.cast_nonneg x) _
          calc
            1 * (B * ((y : ℝ) - x) * Real.rpow (x : ℝ) (-a - 1))
                ≤ B * (N : ℝ) * Real.rpow (x : ℝ) (-a - 1) := by
                  simpa only [one_mul] using mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hgap hB) hp
            _ ≤ B * (N : ℝ) * Real.rpow (m + 1 : ℝ) (-a - 1) := by
                  exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hB hNR.le)
    _ = B * (N : ℝ) ^ 2 * Real.rpow (m + 1 : ℝ) (-a - 1) := by
      simp [ZMod.card]
      ring

theorem summable_centeredBlockMajorant
    {N : ℕ} [NeZero N] {a B : ℝ} (ha : 0 < a) :
    Summable (fun m : ℕ =>
      B * (N : ℝ) ^ 2 * Real.rpow (m + 1 : ℝ) (-a - 1)) := by
  have hbase : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-a - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun m : ℕ => Real.rpow (m + 1 : ℝ) (-a - 1)) := by
    convert (summable_nat_add_iff 1).mpr hbase using 1
    ext m
    norm_num
  exact hshift.mul_left (B * (N : ℝ) ^ 2)

theorem differentiable_centeredCharacterLBlock
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (m : ℕ) :
    Differentiable ℂ (centeredCharacterLBlock chi m) := by
  unfold centeredCharacterLBlock
  apply Differentiable.fun_sum
  intro j hj
  fun_prop

/-- The complete-block continuation is holomorphic at every point of the
open right half-plane. -/
theorem differentiableAt_conditionalCharacterLSeries_of_pos_re
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (conditionalCharacterLSeries chi) s := by
  let a : ℝ := s.re / 2
  let B : ℝ := ‖s‖ + a
  let U : Set ℂ := Metric.ball s a
  have ha : 0 < a := by dsimp [a]; linarith
  have hU : IsOpen U := Metric.isOpen_ball
  have hsU : s ∈ U := Metric.mem_ball_self ha
  have hmajor : Summable (fun m : ℕ =>
      B * (N : ℝ) ^ 2 * Real.rpow (m + 1 : ℝ) (-a - 1)) :=
    summable_centeredBlockMajorant ha
  have hdiffTsum : DifferentiableOn ℂ
      (fun w : ℂ => ∑' m : ℕ, centeredCharacterLBlock chi m w) U := by
    apply differentiableOn_tsum_of_summable_norm hmajor
    · intro m
      exact (differentiable_centeredCharacterLBlock chi m).differentiableOn
    · exact hU
    · intro m w hw
      have hd : ‖w - s‖ < a := by simpa [U, dist_eq_norm] using hw
      have hre : a ≤ w.re := by
        have hreDiff : |w.re - s.re| ≤ ‖w - s‖ := by
          calc
            |w.re - s.re| = |(w - s).re| := by simp
            _ ≤ ‖w - s‖ := Complex.abs_re_le_norm _
        rw [abs_le] at hreDiff
        dsimp [a] at hd ⊢
        linarith
      have hnorm : ‖w‖ ≤ B := by
        calc
          ‖w‖ = ‖(w - s) + s‖ := by congr 1 <;> ring
          _ ≤ ‖w - s‖ + ‖s‖ := norm_add_le _ _
          _ ≤ B := by dsimp [B]; linarith
      exact norm_centeredCharacterLBlock_le chi ha hre hnorm m
  have hfirst : Differentiable ℂ (characterLBlock chi 0) := by
    unfold characterLBlock
    apply Differentiable.fun_sum
    intro j hj
    intro z
    exact (LSeries.hasDerivAt_term (fun n : ℕ => chi n) j.val z).differentiableAt
  unfold conditionalCharacterLSeries
  exact hfirst.differentiableAt.add
    (hdiffTsum.differentiableAt (hU.mem_nhds hsU))

/-- Identification of the block continuation with Mathlib's Dirichlet
`LFunction` throughout the open right half-plane. -/
theorem conditionalCharacterLSeries_eq_LFunction_of_pos_re
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    conditionalCharacterLSeries chi s = DirichletCharacter.LFunction chi s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let V : Set ℂ := {z : ℂ | 1 < z.re}
  let f := conditionalCharacterLSeries chi
  let g := DirichletCharacter.LFunction chi
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ f U := by
    apply DifferentiableOn.analyticOnNhd
    · intro z hz
      exact (differentiableAt_conditionalCharacterLSeries_of_pos_re chi hz).differentiableWithinAt
    · exact hUo
  have hg : AnalyticOnNhd ℂ g U := by
    exact DifferentiableOn.analyticOnNhd
      (DirichletCharacter.differentiable_LFunction hchi).differentiableOn hUo
  have hUc : IsPreconnected U := by
    exact (convex_halfSpace_re_gt 0).isPreconnected
  have hV : V ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  have hUmem : (2 : ℂ) ∈ U := by norm_num [U]
  have hsU : s ∈ U := hs
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hUmem ?_ hsU
  filter_upwards [hV] with z hz
  dsimp [f, g]
  rw [conditionalCharacterLSeries_eq_LSeries_of_one_lt_re chi hchi hz]
  exact (DirichletCharacter.LFunction_eq_LSeries chi hz).symm

/-- Consequently the derivatives of the two continuations agree on the
positive real half-plane. -/
theorem deriv_conditionalCharacterLSeries_eq_deriv_LFunction_of_pos_re
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    deriv (conditionalCharacterLSeries chi) s =
      deriv (DirichletCharacter.LFunction chi) s := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact conditionalCharacterLSeries_eq_LFunction_of_pos_re chi hchi hz

/-- Termwise differentiation of the centered block series at every point of
the open right half-plane. -/
theorem hasSum_deriv_centeredCharacterLBlock_of_pos_re
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun m : ℕ => deriv (centeredCharacterLBlock chi m) s)
      (deriv (fun w : ℂ => ∑' m : ℕ, centeredCharacterLBlock chi m w) s) := by
  let a : ℝ := s.re / 2
  let B : ℝ := ‖s‖ + a
  let U : Set ℂ := Metric.ball s a
  have ha : 0 < a := by dsimp [a]; linarith
  have hU : IsOpen U := Metric.isOpen_ball
  have hsU : s ∈ U := Metric.mem_ball_self ha
  have hmajor : Summable (fun m : ℕ =>
      B * (N : ℝ) ^ 2 * Real.rpow (m + 1 : ℝ) (-a - 1)) :=
    summable_centeredBlockMajorant ha
  apply Complex.hasSum_deriv_of_summable_norm
    (U := U) (z := s) (F := centeredCharacterLBlock chi) hmajor
  · intro m
    exact (differentiable_centeredCharacterLBlock chi m).differentiableOn
  · exact hU
  · intro m w hw
    have hd : ‖w - s‖ < a := by simpa [U, dist_eq_norm] using hw
    have hre : a ≤ w.re := by
      have hreDiff : |w.re - s.re| ≤ ‖w - s‖ := by
        calc
          |w.re - s.re| = |(w - s).re| := by simp
          _ ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      rw [abs_le] at hreDiff
      dsimp [a] at hd ⊢
      linarith
    have hnorm : ‖w‖ ≤ B := by
      calc
        ‖w‖ = ‖(w - s) + s‖ := by congr 1 <;> ring
        _ ≤ ‖w - s‖ + ‖s‖ := norm_add_le _ _
        _ ≤ B := by dsimp [B]; linarith
    exact norm_centeredCharacterLBlock_le chi ha hre hnorm m
  · exact hsU

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.tsum_characterLBlock_eq_LSeries_of_one_lt_re
#print axioms MAPGoldfeldSiegel.centeredCharacterLBlock_eq
#print axioms MAPGoldfeldSiegel.norm_cpow_neg_sub_cpow_neg_le
#print axioms MAPGoldfeldSiegel.norm_centeredCharacterLBlock_le
#print axioms MAPGoldfeldSiegel.differentiableAt_conditionalCharacterLSeries_of_pos_re
#print axioms MAPGoldfeldSiegel.conditionalCharacterLSeries_eq_LFunction_of_pos_re
#print axioms MAPGoldfeldSiegel.deriv_conditionalCharacterLSeries_eq_deriv_LFunction_of_pos_re
#print axioms MAPGoldfeldSiegel.hasSum_deriv_centeredCharacterLBlock_of_pos_re
