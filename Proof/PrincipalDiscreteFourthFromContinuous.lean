import RamachandraDiscreteFourthFromContinuous

namespace PrincipalDiscreteFourthFromContinuous

open Complex MeasureTheory
open scoped BigOperators
open CGLProofDAG
open RamachandraTheorem6ShiftedStripSource
open MAPPrincipalZetaStructuredSplitFromFourthMoment

noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "F" => DirichletCharacter.LFunction chiOne

private theorem principal_analytic_off_one :
    AnalyticOnNhd ℂ F {z : ℂ | z ≠ 1} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction chiOne z
      (Or.inl hz)).differentiableWithinAt
  · exact isClosed_singleton.isOpen_compl

private theorem half_vertical_ne_one (t : ℝ) :
    ((1 / 2 : ℝ) : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

private theorem hasDerivAt_principal_vertical (t : ℝ) :
    HasDerivAt (fun u : ℝ => F (((1 / 2 : ℝ) : ℂ) + u * I))
      (deriv F (((1 / 2 : ℝ) : ℂ) + t * I) * I) t := by
  have hline : HasDerivAt (fun u : ℝ => (((1 / 2 : ℝ) : ℂ) + u * I)) I t := by
    convert (hasDerivAt_id t).ofReal_comp.mul_const I |>.const_add (((1 / 2 : ℝ) : ℂ)) using 1 <;> simp <;> ring
  exact ((DirichletCharacter.differentiableAt_LFunction chiOne _
    (Or.inl (half_vertical_ne_one t))).hasDerivAt.comp t hline)

private theorem continuous_principal_vertical_deriv :
    Continuous (fun t : ℝ => deriv F (((1 / 2 : ℝ) : ℂ) + t * I) * I) := by
  have hd := principal_analytic_off_one.deriv.continuousOn
  have hcomp : Continuous (fun t : ℝ =>
      deriv F (((1 / 2 : ℝ) : ℂ) + t * I)) := by
    simpa only [Function.comp_def] using! hd.comp_continuous (by fun_prop)
      (fun t => half_vertical_ne_one t)
  exact hcomp.mul continuous_const

private theorem principal_circle_ne_one
    {R t theta : ℝ} (hRpos : 0 ≤ R) (hR : R < 1 / 2) :
    circleMap (((1 / 2 : ℝ) : ℂ) + t * I) R theta ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [HolomorphicStripDerivativeFourth.circleMap_vertical_coordinates] at hre
  have hre' : (1 / 2 : ℝ) + R * Real.cos theta = 1 := by
    simpa [Complex.cos_ofReal_re] using hre
  have hc := Real.cos_le_one theta
  have hmul : R * Real.cos theta ≤ R :=
    mul_le_of_le_one_right hRpos hc
  nlinarith

private theorem continuous_principal_circle {R : ℝ} (hRpos : 0 ≤ R)
    (hR : R < 1 / 2) :
    Continuous (Function.uncurry (fun t theta : ℝ =>
      ‖F (circleMap (((1 / 2 : ℝ) : ℂ) + t * I) R theta)‖ ^ 4)) := by
  let phi : ℝ × ℝ → ℂ := fun p =>
    circleMap (((1 / 2 : ℝ) : ℂ) + p.1 * I) R p.2
  have hphi : Continuous phi := by
    dsimp [phi, circleMap]
    fun_prop
  have hrange : ∀ p, phi p ∈ {z : ℂ | z ≠ 1} := by
    intro p
    exact principal_circle_ne_one (t := p.1) (theta := p.2) hRpos hR
  have hbase : Continuous (F ∘ phi) :=
    principal_analytic_off_one.continuousOn.comp_continuous hphi hrange
  change Continuous (fun p : ℝ × ℝ => ‖F (phi p)‖ ^ 4)
  exact hbase.norm.pow 4

private theorem principal_differentiableOn_closedBall
    {R t : ℝ} (hRpos : 0 < R) (hR : R < 1 / 2) :
    DifferentiableOn ℂ F
      (Metric.closedBall (((1 / 2 : ℝ) : ℂ) + t * I) R) := by
  intro z hz
  apply (DirichletCharacter.differentiableAt_LFunction chiOne z ?_).differentiableWithinAt
  left
  intro hz1
  subst z
  have hdist := Metric.mem_closedBall.mp hz
  have hre : dist (1 : ℂ) (((1 / 2 : ℝ) : ℂ) + t * I) ≥ 1 / 2 := by
    rw [dist_eq_norm]
    have hle := Complex.abs_re_le_norm ((1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + t * I))
    norm_num at hle ⊢
    exact hle
  linarith


private theorem continuous_principal_shifted {sigma : ℝ} (hsigma : sigma < 1) :
    Continuous (fun t : ℝ =>
      RamachandraTheorem6ShiftedStripSource.shiftedStripLFourth chiOne sigma t) := by
  have hmap : Continuous (fun t : ℝ => (sigma : ℂ) + t * I) := by fun_prop
  have hrange : ∀ t : ℝ, ((sigma : ℂ) + t * I) ∈ {z : ℂ | z ≠ 1} := by
    intro t h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hc : Continuous (F ∘ fun t : ℝ => (sigma : ℂ) + t * I) :=
    principal_analytic_off_one.continuousOn.comp_continuous hmap hrange
  unfold RamachandraTheorem6ShiftedStripSource.shiftedStripLFourth
  exact hc.norm.pow 4

/-- Raw principal discrete fourth moment, before absorbing the explicit
Cauchy radius and logarithmic factors. -/
theorem principalDiscreteFourth_raw
    {C₆ : ℝ} (hC₆ : 0 < C₆)
    (hsource :
      ∀ (q : ℕ) [NeZero q] (V sigma : ℝ), 3 ≤ V →
        |sigma - (1 / 2 : ℝ)| ≤ (100 * Real.log ((q : ℝ) * V))⁻¹ →
        RamachandraTheorem6ShiftedStripSource.allCharacterShiftedStripFourthIntegral q V sigma ≤
          C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale q V)
    {T : ℝ} (W : Finset ℝ) (hT : 3 ≤ T)
    (hsep : OneSeparated W) (hheight : ∀ t ∈ W, |t| ≤ T) :
    let U : ℝ := 4 * T
    let R : ℝ := (100 * Real.log U)⁻¹
    (∑ t ∈ W, ‖F (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 4) ≤
      (4 + 2 * R⁻¹ ^ 4) *
        (C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale 1 U) := by
  dsimp
  let U : ℝ := 4 * T
  let R : ℝ := (100 * Real.log U)⁻¹
  have hTpos : 0 < T := by linarith
  have hU : 3 ≤ U := by dsimp [U]; linarith
  have hUone : 1 < U := by linarith
  have hlog : 0 < Real.log U := Real.log_pos hUone
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRhalf : R < 1 / 2 := by
    have hexp : Real.exp 1 < U := Real.exp_one_lt_d9.trans_le (by linarith)
    have hlogone : 1 < Real.log U := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log
        (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
        (show U ∈ Set.Ioi (0 : ℝ) from (show 0 < U by linarith)) hexp
    dsimp [R]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_lt_inv₀ (by positivity) (by norm_num)).2 (by nlinarith)
  have hMnonneg : 0 ≤ C₆ * ramachandraTheorem6K2Scale 1 U := by
    have hlog' : 0 ≤ Real.log U := hlog.le
    unfold ramachandraTheorem6K2Scale
    norm_num
    positivity
  apply @HolomorphicStripDerivativeFourth.sum_verticalTrace_fourth_le_of_circleSlices_on
    (DirichletCharacter.LFunction chiOne) (1 / 2 : ℝ) (-T) T R
    (C₆ * ramachandraTheorem6K2Scale 1 U) W
  · linarith
  · exact hRpos
  · exact hasDerivAt_principal_vertical
  · exact continuous_principal_vertical_deriv
  · exact continuous_principal_circle hRpos.le hRhalf
  · exact fun t => principal_differentiableOn_closedBall hRpos hRhalf
  · exact hsep
  · intro t ht
    exact abs_le.mp (hheight t ht)
  · have hstrip0 : |(1 / 2 : ℝ) - 1 / 2| ≤ (100 * Real.log U)⁻¹ := by
      rw [sub_self, abs_zero]
      positivity
    have hs := hsource 1 U (1 / 2 : ℝ) hU (by simpa using hstrip0)
    have hsub := RamachandraDiscreteFourthFromContinuous.singleCharacter_interval_le_allCharacter
      chiOne (U := U) (a := -T) (b := T + 1) (sigma := (1 / 2 : ℝ))
      (by positivity) (by linarith) (by dsimp [U]; linarith)
      (by dsimp [U]; linarith) (continuous_principal_shifted (by norm_num))
    simpa [RamachandraTheorem6ShiftedStripSource.shiftedStripLFourth] using hsub.trans hs
  · intro theta
    have hsigma : |((1 / 2 : ℝ) + R * Real.cos theta) - 1 / 2| ≤
        (100 * Real.log U)⁻¹ := by
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hRpos]
      calc
        R * |Real.cos theta| ≤ R :=
          mul_le_of_le_one_right hRpos.le (Real.abs_cos_le_one theta)
        _ = (100 * Real.log U)⁻¹ := rfl
    have hs := hsource 1 U ((1 / 2 : ℝ) + R * Real.cos theta) hU (by simpa using hsigma)
    have hsigmaLt : (1 / 2 : ℝ) + R * Real.cos theta < 1 := by
      have hm := mul_le_of_le_one_right hRpos.le (Real.cos_le_one theta)
      linarith
    have hsub := RamachandraDiscreteFourthFromContinuous.singleCharacter_interval_le_allCharacter
      chiOne (U := U) (a := -T + R * Real.sin theta)
      (b := T + 1 + R * Real.sin theta)
      (sigma := (1 / 2 : ℝ) + R * Real.cos theta)
      (by positivity) (by linarith)
      (by have hsin := Real.neg_one_le_sin theta; dsimp [U]; nlinarith)
      (by have hsin := Real.sin_le_one theta; dsimp [U]; nlinarith)
      (continuous_principal_shifted hsigmaLt)
    simpa [RamachandraTheorem6ShiftedStripSource.shiftedStripLFourth] using hsub.trans hs


/-- Premise-free principal zeta discrete fourth moment.  The pole at `s=1`
never enters: every Cauchy disk is contained in `Re(s)<1`, so it creates no
residue or quantitative error term. -/
theorem principalZetaDiscreteFourthMoment_proved :
    PrincipalZetaDiscreteFourthMoment := by
  classical
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hpoly := ZeroDensityArithmetic.polylog_absorption 404 eta heta
  obtain ⟨Xlog, hXlog⟩ := Filter.eventually_atTop.1 hpoly
  obtain ⟨C₆, hC₆, hsource⟩ :=
    RamachandraTheorem6Unconditional.ramachandraTheorem6K2Source_proved
  let K : ℝ := 6 * 100 ^ 4 * C₆
  let C : ℝ := K * Real.rpow 4 (1 + eta)
  let T₀ : ℝ := max 3 Xlog
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hT₀ : 2 ≤ T₀ := by dsimp [T₀]; linarith [le_max_left 3 Xlog]
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T W hT hsep hheight
  have hTthree : 3 ≤ T := (le_max_left 3 Xlog).trans hT
  have hTpos : 0 < T := by linarith
  let X : ℝ := 4 * T
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hXone : 1 ≤ X := by dsimp [X]; linarith
  have hXlogThreshold : Xlog ≤ X := by
    have hXL : Xlog ≤ T := (le_max_right 3 Xlog).trans hT
    dsimp [X]
    linarith
  have hlogAbs : (Real.log X) ^ 404 ≤ Real.rpow X eta := by
    rw [← Real.rpow_natCast]
    exact hXlog X hXlogThreshold
  have hraw := principalDiscreteFourth_raw hC₆ hsource W hTthree hsep hheight
  have hlogOne : 1 ≤ Real.log X := by
    have hexp : Real.exp 1 < X :=
      Real.exp_one_lt_d9.trans_le (by dsimp [X]; linarith)
    rw [← Real.log_exp 1]
    exact (Real.strictMonoOn_log
      (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
      (show X ∈ Set.Ioi (0 : ℝ) from hXpos) hexp).le
  have hradiusFactor :
      4 + 2 * ((100 * Real.log X)⁻¹)⁻¹ ^ 4 ≤
        6 * 100 ^ 4 * (Real.log X) ^ 4 := by
    rw [inv_inv]
    have hpowone : 1 ≤ (100 * Real.log X) ^ 4 :=
      one_le_pow₀ (n := 4) (by nlinarith)
    have hid : (100 * Real.log X) ^ 4 =
        100 ^ 4 * (Real.log X) ^ 4 := mul_pow _ _ _
    calc
      4 + 2 * (100 * Real.log X) ^ 4 ≤
          6 * (100 * Real.log X) ^ 4 := by nlinarith
      _ = 6 * 100 ^ 4 * (Real.log X) ^ 4 := by rw [hid]; ring
  have hraw' :
      (∑ t ∈ W, ‖F (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 4) ≤
        (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 := by
    calc
      _ ≤ (4 + 2 * ((100 * Real.log X)⁻¹)⁻¹ ^ 4) *
          (C₆ * (X * Real.log X ^ 400)) := by
        simpa [X, ramachandraTheorem6K2Scale] using hraw
      _ ≤ (6 * 100 ^ 4 * (Real.log X) ^ 4) *
          (C₆ * (X * Real.log X ^ 400)) := by gcongr
      _ = (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 := by ring
  have htoPower :
      (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 ≤
        K * Real.rpow X (1 + eta) := by
    calc
      _ ≤ (6 * 100 ^ 4 * C₆) * X * Real.rpow X eta := by gcongr
      _ = K * Real.rpow X (1 + eta) := by
        have hpair : X * Real.rpow X eta = Real.rpow X (1 + eta) := by
          calc
            X * Real.rpow X eta =
                (X ^ (1 : ℝ)) * Real.rpow X eta :=
              congrArg (fun y : ℝ => y * Real.rpow X eta)
                (Real.rpow_one X).symm
            _ = Real.rpow X (1 + eta) :=
              (Real.rpow_add hXpos 1 eta).symm
        dsimp [K]
        calc
          (6 * 100 ^ 4 * C₆) * X * Real.rpow X eta =
              (6 * 100 ^ 4 * C₆) * (X * Real.rpow X eta) := by ring
          _ = (6 * 100 ^ 4 * C₆) * Real.rpow X (1 + eta) := by rw [hpair]
  have hsplit : Real.rpow X (1 + eta) =
      Real.rpow 4 (1 + eta) * Real.rpow T (1 + eta) := by
    dsimp [X]
    exact Real.mul_rpow (by norm_num) hTpos.le
  have hexponents : 1 + eta ≤ 1 + epsilon := by dsimp [eta]; linarith
  have hmono : Real.rpow T (1 + eta) ≤ Real.rpow T (1 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexponents
  calc
    _ ≤ (6 * 100 ^ 4 * C₆) * X * (Real.log X) ^ 404 := hraw'
    _ ≤ K * Real.rpow X (1 + eta) := htoPower
    _ = C * Real.rpow T (1 + eta) := by
      rw [hsplit]
      dsimp [C]
      ring
    _ ≤ C * Real.rpow T (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hmono hC.le

/-- The exact zero-argument pair consumed by the direct post-A.5 adapter. -/
theorem directDiscreteFourthMomentPair_proved :
    MAPAPWeightedZeroMassDirectFourthMomentAdapter.DirectDiscreteFourthMomentPair :=
  { principal := principalZetaDiscreteFourthMoment_proved
    nonprincipal :=
      RamachandraDiscreteFourthFromContinuous.nonprincipalFixedCharacterDiscreteFourthMoment_proved }

end
end PrincipalDiscreteFourthFromContinuous

#print axioms PrincipalDiscreteFourthFromContinuous.hasDerivAt_principal_vertical
#print axioms PrincipalDiscreteFourthFromContinuous.continuous_principal_vertical_deriv
#print axioms PrincipalDiscreteFourthFromContinuous.continuous_principal_circle
#print axioms PrincipalDiscreteFourthFromContinuous.principal_differentiableOn_closedBall
#print axioms PrincipalDiscreteFourthFromContinuous.principalDiscreteFourth_raw
#print axioms PrincipalDiscreteFourthFromContinuous.principalZetaDiscreteFourthMoment_proved
#print axioms PrincipalDiscreteFourthFromContinuous.directDiscreteFourthMomentPair_proved
