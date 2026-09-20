import KoukTheorem12ThreePrimitive

/-!
# Certified primitive regular low-height gap

The optimized McCurley constant is unnecessary for the MAP endpoint.  This
file converts the already certified primitive form of Koukoulopoulos Theorem
12.3 into a coarse reciprocal-`log (8q)` gap on `|Im rho| < 3`.

The only exceptional shape left by Theorem 12.3 is a real zero of a real
nonprincipal character, exactly the shape removed from the regular branch.
-/

namespace MAPAPPrimitiveRegularLowGap

open Complex Set Filter Asymptotics
open DirichletZeros MAPLocalZeroWindow MAPMellinDetectorLeaf
open MAPKoukTheorem12ThreePrimitive
open MAPPrimitiveLogDerivativeRemainderUnconditional

noncomputable section

/-- A zero in a global rectangle, whose real part is at least `1/2` and whose
ordinate lies in the centered unit interval, belongs to the literal centered
divisor support. -/
theorem mem_centeredUnitWindowSupport_of_mem_zeroSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {T t : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi 0 T)
    (hre : 1 / 2 ≤ rho.re)
    (himLower : t - 1 / 2 ≤ rho.im)
    (himUpper : rho.im ≤ t + 1 / 2) :
    rho ∈ centeredUnitWindowSupport chi (1 / 2) t := by
  have hglobalRect : rho ∈ zeroRectangle 0 T :=
    (zeroDivisor chi 0 T).supportWithinDomain
      ((zeroSupport_mem_iff chi 0 T rho).mp hrho)
  have hheight : |rho.im| ≤ windowHeight (t - 1 / 2) := by
    unfold windowHeight
    have hleft : -(|t - 1 / 2| + 1) ≤ rho.im := by
      have habs : -(t - 1 / 2) ≤ |t - 1 / 2| := neg_le_abs (t - 1 / 2)
      linarith
    have hright : rho.im ≤ |t - 1 / 2| + 1 := by
      have habs : t - 1 / 2 ≤ |t - 1 / 2| := le_abs_self (t - 1 / 2)
      linarith
    exact abs_le.mpr ⟨hleft, hright⟩
  have htargetRect :
      rho ∈ zeroRectangle (1 / 2) (windowHeight (t - 1 / 2)) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hre, hglobalRect.1.2⟩, abs_le.mp hheight⟩
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport chi 0 T hrho
  rw [centeredUnitWindowSupport, closedUnitWindowSupport, Finset.mem_filter]
  refine ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero chi
    (1 / 2) (windowHeight (t - 1 / 2)) htargetRect).mpr hzero, ?_⟩
  constructor <;> linarith

/-- A supported zero of the regularized function is an ordinary L-function
zero.  In the principal case the patched nonzero value at one removes the
only possible extra factor. -/
theorem LFunction_eq_zero_of_mem_zeroSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi sigma T) :
    DirichletCharacter.LFunction chi rho = 0 := by
  have hreg : regularizedLFunction chi rho = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport chi sigma T hrho
  by_cases hchi : chi = 1
  · have hrhoOne : rho ≠ 1 := by
      intro h
      subst rho
      exact MAPAPZeroDensityCert.regularizedLFunction_one_ne_zero chi hreg
    have hprod : (rho - 1) * DirichletCharacter.LFunction chi rho = 0 := by
      simpa [regularizedLFunction, hchi,
        DirichletCharacter.LFunctionTrivChar₁,
        Function.update_of_ne hrhoOne] using hreg
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hrhoOne)
  · simpa [regularizedLFunction, hchi] using hreg

/-- At bounded ordinate, the arithmetic scale in Theorem 12.3 is at most
`8q`. -/
theorem log_arithmeticScale_le_log_eight_mul
    {q : ℕ} [NeZero q] {t : ℝ} (ht : |t| ≤ 3) :
    Real.log (arithmeticScale q t) ≤ Real.log (8 * (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hscalePos : 0 < arithmeticScale q t := by
    unfold arithmeticScale
    positivity
  apply Real.log_le_log hscalePos
  unfold arithmeticScale
  have hfactor : |t| + 2 ≤ 8 := by linarith
  nlinarith

theorem log_eight_mul_pos (q : ℕ) [NeZero q] :
    0 < Real.log (8 * (q : ℝ)) := by
  apply Real.log_pos
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith

/-- Coarse source-normalized low-height collar supplied by the certified
Theorem 12.3 proof. -/
def regularLowGap (q : ℕ) : ℝ :=
  1 / (100000000000 * Real.log (8 * (q : ℝ)))

theorem regularLowGap_pos (q : ℕ) [NeZero q] :
    0 < regularLowGap q := by
  unfold regularLowGap
  exact one_div_pos.mpr (mul_pos (by norm_num) (log_eight_mul_pos q))

theorem log_eight_mul_le_loglog
    {K X : ℝ} {q : ℕ} [NeZero q]
    (hlogX : 1 ≤ Real.log X)
    (hloglog : 1 ≤ Real.log (Real.log X))
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K) :
    Real.log (8 * (q : ℝ)) ≤
      (K + Real.log 8) * Real.log (Real.log X) := by
  have hpowPos : 0 < Real.rpow (Real.log X) K :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogX) K
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hargPos : 0 < 8 * (q : ℝ) := by positivity
  have hmono : Real.log (8 * (q : ℝ)) ≤
      Real.log (8 * Real.rpow (Real.log X) K) := by
    apply Real.log_le_log hargPos
    exact mul_le_mul_of_nonneg_left hq (by norm_num)
  have hprod : Real.log (8 * Real.rpow (Real.log X) K) =
      Real.log 8 + K * Real.log (Real.log X) := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hpowPos.ne']
    congr 1
    exact Real.log_rpow (zero_lt_one.trans_le hlogX) K
  rw [hprod] at hmono
  have hlogEight : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  nlinarith

private theorem eventually_loglog_le_quarter_log_rpow :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) ≤
        Real.rpow (Real.log X) (1 / 4 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).eventuallyLE
  exact Real.tendsto_log_atTop.eventually (by
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hL hL1
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1.le
    have hrpow0 : 0 ≤ Real.rpow L (1 / 4 : ℝ) :=
      Real.rpow_nonneg (zero_lt_one.trans hL1).le _
    have hL' : Real.log L ≤ |Real.rpow L (1 / 4 : ℝ)| := by
      simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlog0] using hL
    rwa [abs_of_nonneg hrpow0] at hL')

/-- On a polylogarithmic conductor range, the certified Theorem 12.3 collar
dominates a fixed multiple of `(log X)^(-1/4)`. -/
theorem weakGap_le_regularLowGap
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      (1 / (100000000000 * (K + Real.log 8))) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤ regularLowGap q := by
  filter_upwards [eventually_loglog_le_quarter_log_rpow,
      eventually_gt_atTop (Real.exp (Real.exp 1))] with X hquarter hX q _inst hq
  have hXpos : 0 < X := (Real.exp_pos _).trans hX
  have hXone : 1 < X :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans hX
  have hlogXexp : Real.exp 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hlogXone : 1 < Real.log X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans hlogXexp
  have hloglogOne : 1 < Real.log (Real.log X) := by
    rw [Real.lt_log_iff_exp_lt (Real.log_pos hXone)]
    exact hlogXexp
  have hlogBound := log_eight_mul_le_loglog hlogXone.le
    hloglogOne.le hq
  have hCpos : 0 < K + Real.log 8 :=
    add_pos_of_nonneg_of_pos hK (Real.log_pos (by norm_num))
  have hpowPos : 0 < Real.rpow (Real.log X) (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hlogXone) _
  have hdenUpper :
      100000000000 * Real.log (8 * (q : ℝ)) ≤
        100000000000 * (K + Real.log 8) *
          Real.rpow (Real.log X) (1 / 4 : ℝ) := by
    calc
      100000000000 * Real.log (8 * (q : ℝ)) ≤
          100000000000 * ((K + Real.log 8) *
            Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left hlogBound (by norm_num)
      _ ≤ 100000000000 * ((K + Real.log 8) *
            Real.rpow (Real.log X) (1 / 4 : ℝ)) := by gcongr
      _ = _ := by ring
  have hdenPos : 0 < 100000000000 * Real.log (8 * (q : ℝ)) := by
    have hqOne : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact mul_pos (by norm_num) (Real.log_pos (by nlinarith))
  have hinv :
      1 / (100000000000 * (K + Real.log 8) *
          Real.rpow (Real.log X) (1 / 4 : ℝ)) ≤
        regularLowGap q := by
    unfold regularLowGap
    exact one_div_le_one_div_of_le hdenPos hdenUpper
  have hid :
      (1 / (100000000000 * (K + Real.log 8))) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) =
        1 / (100000000000 * (K + Real.log 8) *
          Real.rpow (Real.log X) (1 / 4 : ℝ)) := by
    have hneg := Real.rpow_neg (Real.log_pos hXone).le (1 / 4 : ℝ)
    calc
      (1 / (100000000000 * (K + Real.log 8))) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) =
        (1 / (100000000000 * (K + Real.log 8))) *
          (Real.rpow (Real.log X) (1 / 4 : ℝ))⁻¹ :=
        congrArg (fun z : ℝ =>
          (1 / (100000000000 * (K + Real.log 8))) * z) hneg
      _ = _ := by field_simp
  rw [hid]
  exact hinv

/-- Every fixed positive gap eventually dominates the weak-VK mesh gap. -/
theorem eventually_weakGap_le_constant (c₀ c : ℝ)
    (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop,
      c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ c₀ := by
  have hsmallL : ∀ᶠ L : ℝ in atTop,
      Real.rpow L (-(3 / 4 : ℝ)) ≤ c₀ / c := by
    have ht := tendsto_rpow_neg_atTop
      (show 0 < (3 / 4 : ℝ) by norm_num)
    have hnhds : Set.Iio (c₀ / c) ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds (div_pos hc₀ hc)
    exact (ht.eventually hnhds).mono fun _ h => h.le
  have hsmallX := Real.tendsto_log_atTop.eventually hsmallL
  filter_upwards [hsmallX] with X hX
  have := mul_le_mul_of_nonneg_left hX hc.le
  field_simp [hc.ne'] at this ⊢
  nlinarith

/-- Every primitive nonprincipal zero in the regular bounded-height branch
has the coarse reciprocal-logarithmic gap.  Analytic multiplicity remains in
the source theorem and is not discarded by this bridge. -/
theorem primitive_nonprincipal_regular_low_gap
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi 0 T)
    (hbeta : 4 / 5 < rho.re) (hheight : |rho.im| < 3)
    (hregular : ¬ (chi ^ 2 = 1 ∧ rho.im = 0)) :
    regularLowGap q ≤ 1 - rho.re := by
  have hcenter : rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im := by
    apply mem_centeredUnitWindowSupport_of_mem_zeroSupport chi hrho
    · linarith
    · linarith
    · linarith
  have hscale := log_arithmeticScale_le_log_eight_mul
    (q := q) (t := rho.im) hheight.le
  have hlogScalePos : 0 < Real.log (arithmeticScale q rho.im) := by
    have htwo := two_le_arithmeticScale (q := q) rho.im
    exact Real.log_pos (one_lt_two.trans_le htwo)
  have hlogEightPos := log_eight_mul_pos q
  have hcollar : regularLowGap q ≤
      1 / (100000000000 *
        Real.log (arithmeticScale q rho.im)) := by
    unfold regularLowGap
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_left hscale (by norm_num)
  by_contra hgap
  have hnearEight : 1 - rho.re < regularLowGap q := lt_of_not_ge hgap
  have hnear : 1 - rho.re <
      1 / (100000000000 *
        Real.log (arithmeticScale q rho.im)) :=
    hnearEight.trans_le hcollar
  have hexceptional := primitive_nearOne_zero_is_exceptional
    chi hprim hchi hcenter hnear
  exact hregular ⟨hexceptional.1, hexceptional.2.1⟩

/-! ## The fixed conductor-one principal branch -/

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

/-- The literal finite set containing every principal zero used in the
bounded-height regular branch. -/
def principalLowSupport : Finset ℂ :=
  zeroSupport (1 : DirichletCharacter ℂ 1) (4 / 5) 3

/-- Finiteness and Euler-product nonvanishing on `Re s ≥ 1` give a fixed
positive gap for the conductor-one principal support.  This is a deterministic
compactness step, not a new analytic zero-free input. -/
theorem exists_principalLowGap :
    ∃ c : ℝ, 0 < c ∧
      ∀ rho ∈ principalLowSupport, c ≤ 1 - rho.re := by
  classical
  by_cases hnonempty : principalLowSupport.Nonempty
  · obtain ⟨rho, hrho, hmin⟩ :=
      Finset.exists_min_image principalLowSupport (fun z : ℂ => 1 - z.re)
        hnonempty
    refine ⟨1 - rho.re, ?_, ?_⟩
    · have hre := re_lt_one_of_mem_zeroSupport
        (1 : DirichletCharacter ℂ 1) hrho
      linarith
    · intro z hz
      exact hmin z hz
  · refine ⟨1, by norm_num, ?_⟩
    intro rho hrho
    exact (hnonempty ⟨rho, hrho⟩).elim

/-- A primitive principal character has conductor one, so the preceding fixed
finite gap controls all of its bounded-height near-one zeros. -/
theorem exists_primitive_principal_regular_low_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi.IsPrimitive → chi = 1 →
        ∀ (T : ℝ) (rho : ℂ),
          rho ∈ zeroSupport chi 0 T →
          4 / 5 < rho.re → |rho.im| < 3 →
            c ≤ 1 - rho.re := by
  obtain ⟨c, hc, hprincipal⟩ := exists_principalLowGap
  refine ⟨c, hc, ?_⟩
  intro q _inst chi hprim hchi T rho hrho hbeta hheight
  have hq : q = 1 := by
    have hcond : chi.conductor = q := hprim
    rw [hchi, DirichletCharacter.conductor_one] at hcond
    exact hcond.symm
  subst q
  subst chi
  have hglobalRect : rho ∈ zeroRectangle 0 T :=
    (zeroDivisor (1 : DirichletCharacter ℂ 1) 0 T).supportWithinDomain
      ((zeroSupport_mem_iff (1 : DirichletCharacter ℂ 1) 0 T rho).mp hrho)
  have htargetRect : rho ∈ zeroRectangle (4 / 5) 3 := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hbeta.le, hglobalRect.1.2⟩, abs_le.mp hheight.le⟩
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    (1 : DirichletCharacter ℂ 1) 0 T hrho
  have htarget : rho ∈ principalLowSupport := by
    unfold principalLowSupport
    exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      (1 : DirichletCharacter ℂ 1) (4 / 5) 3 htargetRect).mpr hzero
  exact hprincipal rho htarget

end
end MAPAPPrimitiveRegularLowGap

#print axioms MAPAPPrimitiveRegularLowGap.mem_centeredUnitWindowSupport_of_mem_zeroSupport
#print axioms MAPAPPrimitiveRegularLowGap.primitive_nonprincipal_regular_low_gap
#print axioms MAPAPPrimitiveRegularLowGap.exists_principalLowGap
#print axioms MAPAPPrimitiveRegularLowGap.exists_primitive_principal_regular_low_gap
