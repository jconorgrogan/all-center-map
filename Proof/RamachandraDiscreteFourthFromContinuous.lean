import HolomorphicStripDerivativeFourth
import RamachandraTheorem6Unconditional
import APWeightedZeroMassDirectFourthMomentAdapter

/-!
# Discrete fourth moments from Ramachandra's continuous shifted-strip theorem
-/
namespace RamachandraDiscreteFourthFromContinuous

open Complex MeasureTheory
open scoped BigOperators
open CGLProofDAG
open RamachandraTheorem6ShiftedStripSource
open FixedCharacterFourthMomentFromAFE
open MAPPrincipalZetaStructuredSplitFromFourthMoment
open MAPAPWeightedZeroMassDirectFourthMomentAdapter

noncomputable section

/-- The Euler envelope in Ramachandra's theorem is subpower, with an explicit
constant uniform for every `x ≥ 1`. -/
theorem exp_sqrt_log_le_const_rpow
    {x eta : ℝ} (hx : 1 ≤ x) (heta : 0 < eta) :
    Real.exp (Real.sqrt (Real.log x)) ≤
      Real.exp ((4 * eta)⁻¹) * Real.rpow x eta := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsqrtSq : Real.sqrt (Real.log x) ^ 2 = Real.log x :=
    Real.sq_sqrt hlog
  have hsq : 0 ≤ (2 * eta * Real.sqrt (Real.log x) - 1) ^ 2 := sq_nonneg _
  have hsqrt : Real.sqrt (Real.log x) ≤
      eta * Real.log x + (4 * eta)⁻¹ := by
    have heta4 : 0 < 4 * eta := by positivity
    have haux : Real.sqrt (Real.log x) - eta * Real.log x ≤
        1 / (4 * eta) := by
      apply (le_div_iff₀ heta4).2
      ring_nf at hsq ⊢
      rw [hsqrtSq] at hsq
      nlinarith
    rw [inv_eq_one_div]
    linarith
  have hexp := Real.exp_le_exp.mpr hsqrt
  calc
    Real.exp (Real.sqrt (Real.log x)) ≤
        Real.exp (eta * Real.log x + (4 * eta)⁻¹) := hexp
    _ = Real.exp ((4 * eta)⁻¹) * Real.rpow x eta := by
      rw [Real.exp_add,
        show Real.rpow x eta = Real.exp (Real.log x * eta) from
          Real.rpow_def_of_pos hxpos eta]
      rw [mul_comm eta (Real.log x)]
      ring

/-- A single character's fourth moment on a subinterval is bounded by the
all-character Ramachandra integral on the containing symmetric interval. -/
theorem singleCharacter_interval_le_allCharacter
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U a b sigma : ℝ}
    (hU : 0 ≤ U) (hab : a ≤ b) (ha : -U ≤ a) (hb : b ≤ U)
    (hcont : Continuous (fun t : ℝ => shiftedStripLFourth chi sigma t)) :
    (∫ t in a..b, shiftedStripLFourth chi sigma t) ≤
      allCharacterShiftedStripFourthIntegral q U sigma := by
  have hfullInt : IntervalIntegrable
      (fun t : ℝ => shiftedStripLFourth chi sigma t) volume (-U) U :=
    hcont.intervalIntegrable _ _
  have hsub :
      (∫ t in a..b, shiftedStripLFourth chi sigma t) ≤
        ∫ t in (-U)..U, shiftedStripLFourth chi sigma t := by
    exact intervalIntegral.integral_mono_interval ha hab hb
      (Filter.Eventually.of_forall (fun t => pow_nonneg (norm_nonneg _) 4))
      hfullInt
  have hsingle :
      (∫ t in (-U)..U, shiftedStripLFourth chi sigma t) ≤
        ∑ psi : DirichletCharacter ℂ q,
          ∫ t in (-U)..U, shiftedStripLFourth psi sigma t := by
    have hall : ∀ psi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        0 ≤ ∫ t in (-U)..U, shiftedStripLFourth psi sigma t := by
      intro psi _
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => pow_nonneg (norm_nonneg _) 4)
    have hs := Finset.single_le_sum hall (Finset.mem_univ chi)
    simpa using hs
  exact hsub.trans (by simpa [allCharacterShiftedStripFourthIntegral] using hsingle)

/-- Raw, pre-absorption nonprincipal discrete fourth moment.  It records the
exact Cauchy radius loss and the literal Ramachandra scale at height `4T`. -/
theorem nonprincipalDiscreteFourth_raw
    {C₆ : ℝ} (hC₆ : 0 < C₆)
    (hsource :
      ∀ (q : ℕ) [NeZero q] (V sigma : ℝ),
        3 ≤ V →
        |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * V))⁻¹ →
        allCharacterShiftedStripFourthIntegral q V sigma ≤
          C₆ * ramachandraTheorem6K2Scale q V)
    {T : ℝ} {r : ℕ} [NeZero r]
    (chi : DirichletCharacter ℂ r) (W : Finset ℝ)
    (hT : 3 ≤ T) (hchi : chi ≠ 1) (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, |t| ≤ T) :
    let U : ℝ := 4 * T
    let R : ℝ := (100 * Real.log ((r : ℝ) * U))⁻¹
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 4) ≤
        (4 + 2 * R⁻¹ ^ 4) *
          (C₆ * ramachandraTheorem6K2Scale r U) := by
  dsimp
  let U : ℝ := 4 * T
  let R : ℝ := (100 * Real.log ((r : ℝ) * U))⁻¹
  have hrNat : 0 < r := NeZero.pos r
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrNat
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrNat
  have hTpos : 0 < T := by linarith
  have hU : 3 ≤ U := by dsimp [U]; linarith
  have hprod : 1 < (r : ℝ) * U := by
    have : 3 ≤ (r : ℝ) * U := by nlinarith
    linarith
  have hlog : 0 < Real.log ((r : ℝ) * U) := Real.log_pos hprod
  have hR : 0 < R := by dsimp [R]; positivity
  have hRle : R ≤ 1 := by
    have hthree : (3 : ℝ) ≤ (r : ℝ) * U := by nlinarith
    have hexp : Real.exp 1 < (r : ℝ) * U :=
      Real.exp_one_lt_d9.trans_le (by linarith)
    have hlogone : 1 < Real.log ((r : ℝ) * U) := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log
        (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
        (show (r : ℝ) * U ∈ Set.Ioi (0 : ℝ) from
          mul_pos hrpos (by linarith [hU])) hexp
    dsimp [R]
    apply (inv_le_one₀ (by positivity)).2
    nlinarith
  have hF : Differentiable ℂ (DirichletCharacter.LFunction chi) :=
    DirichletCharacter.differentiable_LFunction hchi
  apply HolomorphicStripDerivativeFourth.sum_verticalTrace_fourth_le_of_circleSlices
    hF (sigma := (1 / 2 : ℝ)) (A := -T) (B := T) (R := R)
    (M := C₆ * ramachandraTheorem6K2Scale r U)
  · linarith
  · exact hR
  · have hscale : 0 ≤ ramachandraTheorem6K2Scale r U := by
      have hlog' : 0 ≤ Real.log ((r : ℝ) * U) := hlog.le
      unfold ramachandraTheorem6K2Scale
      positivity
    positivity
  · exact hsep
  · intro t ht
    have habs := hheight t ht
    exact (abs_le.mp habs)
  · have hstrip0 : |(1 / 2 : ℝ) - 1 / 2| ≤
        (100 * Real.log ((r : ℝ) * U))⁻¹ := by
      rw [sub_self, abs_zero]
      exact inv_nonneg.mpr (mul_nonneg (by norm_num) hlog.le)
    have hsrc := hsource r U (1 / 2 : ℝ) hU hstrip0
    have hsub := singleCharacter_interval_le_allCharacter chi
      (U := U) (a := -T) (b := T + 1) (sigma := (1 / 2 : ℝ))
      (by positivity) (by linarith) (by dsimp [U]; linarith)
      (by dsimp [U]; linarith)
      (by
        unfold shiftedStripLFourth
        exact ((hF.continuous.comp (by fun_prop)).norm.pow 4))
    simpa [shiftedStripLFourth] using hsub.trans hsrc
  · intro theta
    have hsigma :
        |((1 / 2 : ℝ) + R * Real.cos theta) - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((r : ℝ) * U))⁻¹ := by
      rw [add_sub_cancel_left, abs_mul]
      have hc : |Real.cos theta| ≤ 1 := Real.abs_cos_le_one theta
      calc
        |R| * |Real.cos theta| ≤ R := by
          rw [abs_of_pos hR]
          exact mul_le_of_le_one_right hR.le hc
        _ = (100 * Real.log ((r : ℝ) * U))⁻¹ := rfl
    have hsrc := hsource r U ((1 / 2 : ℝ) + R * Real.cos theta) hU hsigma
    have hsub := singleCharacter_interval_le_allCharacter chi
      (U := U) (a := -T + R * Real.sin theta)
      (b := T + 1 + R * Real.sin theta)
      (sigma := (1 / 2 : ℝ) + R * Real.cos theta)
      (by positivity) (by linarith)
      (by have hs : -1 ≤ Real.sin theta := Real.neg_one_le_sin theta
          dsimp [U]
          nlinarith)
      (by have hs : Real.sin theta ≤ 1 := Real.sin_le_one theta
          dsimp [U]
          nlinarith)
      (by
        unfold shiftedStripLFourth
        exact ((hF.continuous.comp (by fun_prop)).norm.pow 4))
    simpa [shiftedStripLFourth] using hsub.trans hsrc

/-- The exact nonprincipal discrete fourth moment consumed by the post-A.5
split, obtained from the premise-free continuous Ramachandra theorem. -/
theorem nonprincipalFixedCharacterDiscreteFourthMoment_proved :
    NonprincipalFixedCharacterDiscreteFourthMoment := by
  classical
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 3
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hpoly := ZeroDensityArithmetic.polylog_absorption 404 eta heta
  obtain ⟨Xlog, hXlog⟩ := Filter.eventually_atTop.1 hpoly
  obtain ⟨C₆, hC₆, hsource⟩ :=
    RamachandraTheorem6Unconditional.ramachandraTheorem6K2Source_proved
  let K : ℝ := 6 * 100 ^ 4 * C₆ * Real.exp ((4 * eta)⁻¹)
  let C : ℝ := K * Real.rpow 4 (1 + 2 * eta)
  let T₀ : ℝ := max 3 Xlog
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hT₀ : 2 ≤ T₀ := by dsimp [T₀]; linarith [le_max_left 3 Xlog]
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T r _inst chi W hT hprimitive hnonprincipal hsep hheight
  have hTthree : 3 ≤ T := (le_max_left 3 Xlog).trans hT
  have hTpos : 0 < T := by linarith
  have hrNat : 0 < r := NeZero.pos r
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrNat
  have hrone : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrNat
  let S : ℝ := (r : ℝ) * T
  let X : ℝ := (r : ℝ) * (4 * T)
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hSone : 1 ≤ S := by dsimp [S]; nlinarith
  have hXeq : X = 4 * S := by dsimp [X, S]; ring
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hXone : 1 ≤ X := by rw [hXeq]; nlinarith
  have hXlogThreshold : Xlog ≤ X := by
    have hXL : Xlog ≤ T := (le_max_right 3 Xlog).trans hT
    dsimp [X]
    nlinarith [mul_le_mul_of_nonneg_right hrone hTpos.le]
  have hlogAbs : (Real.log X) ^ 404 ≤ Real.rpow X eta := by
    rw [← Real.rpow_natCast]
    exact hXlog X hXlogThreshold
  have hrX : (r : ℝ) ≤ X := by
    dsimp [X]
    nlinarith
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrone
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hlog_le : Real.log (r : ℝ) ≤ Real.log X :=
    Real.strictMonoOn_log.monotoneOn hrpos hXpos hrX
  have hexpMono : Real.exp (Real.sqrt (Real.log (r : ℝ))) ≤
      Real.exp (Real.sqrt (Real.log X)) :=
    Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlog_le)
  have hexpSub : Real.exp (Real.sqrt (Real.log (r : ℝ))) ≤
      Real.exp ((4 * eta)⁻¹) * Real.rpow X eta :=
    hexpMono.trans (exp_sqrt_log_le_const_rpow hXone heta)
  have hraw := nonprincipalDiscreteFourth_raw hC₆ hsource chi W
    hTthree hnonprincipal hsep hheight
  have hlogOne : 1 ≤ Real.log X := by
    have hexp : Real.exp 1 < X := by
      rw [hXeq]
      exact Real.exp_one_lt_d9.trans_le (by nlinarith)
    rw [← Real.log_exp 1]
    exact (Real.strictMonoOn_log
      (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
      (show X ∈ Set.Ioi (0 : ℝ) from hXpos) hexp).le
  have hradiusFactor :
      4 + 2 * ((100 * Real.log X)⁻¹)⁻¹ ^ 4 ≤
        6 * 100 ^ 4 * (Real.log X) ^ 4 := by
    have hden : 100 * Real.log X ≠ 0 := by positivity
    rw [inv_inv]
    have hpowone : 1 ≤ (100 * Real.log X) ^ 4 := by
      exact one_le_pow₀ (n := 4) (by nlinarith)
    have hid : (100 * Real.log X) ^ 4 = 100 ^ 4 * (Real.log X) ^ 4 :=
      mul_pow _ _ _
    calc
      4 + 2 * (100 * Real.log X) ^ 4 ≤
          6 * (100 * Real.log X) ^ 4 := by nlinarith
      _ = 6 * 100 ^ 4 * (Real.log X) ^ 4 := by
        rw [show (100 * Real.log X) ^ 4 =
          100 ^ 4 * (Real.log X) ^ 4 from hid]
        ring
  have hraw' :
      (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 4) ≤
        (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 *
          Real.exp (Real.sqrt (Real.log (r : ℝ))) := by
    calc
      _ ≤ (4 + 2 * ((100 * Real.log X)⁻¹)⁻¹ ^ 4) *
          (C₆ * (X * Real.log X ^ 400 *
            Real.exp (Real.sqrt (Real.log (r : ℝ))))) := by
        simpa [X, ramachandraTheorem6K2Scale] using hraw
      _ ≤ (6 * 100 ^ 4 * (Real.log X) ^ 4) *
          (C₆ * (X * Real.log X ^ 400 *
            Real.exp (Real.sqrt (Real.log (r : ℝ))))) := by
        gcongr
      _ = (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 *
          Real.exp (Real.sqrt (Real.log (r : ℝ))) := by ring
  have htoPower :
      (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 *
          Real.exp (Real.sqrt (Real.log (r : ℝ))) ≤
        K * Real.rpow X (1 + 2 * eta) := by
    have hXeta : 0 ≤ Real.rpow X eta := Real.rpow_nonneg hXpos.le _
    have hbaseNonneg :
        0 ≤ (6 * 100 ^ 4 * C₆) * X * Real.rpow X eta := by
      exact mul_nonneg (mul_nonneg (by positivity) hXpos.le) hXeta
    have hcombine : X * Real.rpow X eta * Real.rpow X eta =
        Real.rpow X (1 + 2 * eta) := by
      have hone : X * Real.rpow X eta = Real.rpow X (1 + eta) := by
        calc
          X * Real.rpow X eta =
              (X ^ (1 : ℝ)) * Real.rpow X eta :=
            congrArg (fun y : ℝ => y * Real.rpow X eta)
              (Real.rpow_one X).symm
          _ = Real.rpow X (1 + eta) :=
            (Real.rpow_add hXpos 1 eta).symm
      calc
        X * Real.rpow X eta * Real.rpow X eta =
            Real.rpow X (1 + eta) * Real.rpow X eta := by
              exact congrArg (fun y : ℝ => y * Real.rpow X eta) hone
        _ = Real.rpow X ((1 + eta) + eta) := by
              exact (Real.rpow_add hXpos (1 + eta) eta).symm
        _ = Real.rpow X (1 + 2 * eta) := by ring_nf
    calc
      _ ≤ (6 * 100 ^ 4 * C₆) * X * Real.rpow X eta *
          (Real.exp ((4 * eta)⁻¹) * Real.rpow X eta) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hlogAbs
                (by positivity : 0 ≤ (6 * 100 ^ 4 * C₆) * X)
            · exact hexpSub
            · positivity
            · exact hbaseNonneg
      _ = K * Real.rpow X (1 + 2 * eta) := by
        dsimp [K]
        calc
          (6 * 100 ^ 4 * C₆) * X * Real.rpow X eta *
              (Real.exp ((4 * eta)⁻¹) * Real.rpow X eta) =
              (6 * 100 ^ 4 * C₆ * Real.exp ((4 * eta)⁻¹)) *
                (X * Real.rpow X eta * Real.rpow X eta) := by ring
          _ = (6 * 100 ^ 4 * C₆ * Real.exp ((4 * eta)⁻¹)) *
                Real.rpow X (1 + 2 * eta) := by rw [hcombine]
  have hsplit : Real.rpow X (1 + 2 * eta) =
      Real.rpow 4 (1 + 2 * eta) * Real.rpow S (1 + 2 * eta) := by
    rw [hXeq]
    exact Real.mul_rpow (by norm_num) hSpos.le
  have hexponents : 1 + 2 * eta ≤ 1 + epsilon := by
    dsimp [eta]
    linarith
  have hmono : Real.rpow S (1 + 2 * eta) ≤
      Real.rpow S (1 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hSone hexponents
  calc
    _ ≤ (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 *
          Real.exp (Real.sqrt (Real.log (r : ℝ))) := hraw'
    _ ≤ K * Real.rpow X (1 + 2 * eta) := htoPower
    _ = C * Real.rpow S (1 + 2 * eta) := by
      rw [hsplit]
      dsimp [C]
      ring
    _ ≤ C * Real.rpow S (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hmono hC.le
    _ = C * Real.rpow ((r : ℝ) * T) (1 + epsilon) := by rfl

end
end RamachandraDiscreteFourthFromContinuous

#print axioms RamachandraDiscreteFourthFromContinuous.singleCharacter_interval_le_allCharacter
#print axioms RamachandraDiscreteFourthFromContinuous.exp_sqrt_log_le_const_rpow
#print axioms RamachandraDiscreteFourthFromContinuous.nonprincipalDiscreteFourth_raw
#print axioms RamachandraDiscreteFourthFromContinuous.nonprincipalFixedCharacterDiscreteFourthMoment_proved
