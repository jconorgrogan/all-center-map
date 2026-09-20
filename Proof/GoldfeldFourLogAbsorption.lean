import GoldfeldCrossLevelComparison

/-!
# Goldfeld comparison to the all-but-one zero-free region

This file isolates the genuine analytic output of the smoothed four-L contour
argument in Koukoulopoulos, Theorem 12.9.  Everything after that comparison --
logarithm absorption, the near-one derivative step, the fixed exceptional
character, and imprimitive Euler factors -- is formalized in the map.
-/

namespace MAPGoldfeldSiegel

open Filter Asymptotics

noncomputable section

/-- A positive power absorbs the fourth logarithmic power in Goldfeld's comparison,
with a completely explicit constant. -/
theorem log_two_mul_fourth_le_const_mul_rpow
    {theta x : ℝ} (htheta : 0 < theta) (hx : 1 ≤ x) :
    (Real.log (2 * x)) ^ 4 ≤
      (Real.rpow 2 theta / (theta / 4) ^ 4) * Real.rpow x theta := by
  let r : ℝ := theta / 4
  have hr : 0 < r := div_pos htheta (by norm_num)
  have hy : 0 < 2 * x := mul_pos (by norm_num) (zero_lt_one.trans_le hx)
  have hyOne : 1 ≤ 2 * x := by nlinarith
  have hlog0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg hyOne
  have hyrPos : 0 < Real.rpow (2 * x) r := Real.rpow_pos_of_pos hy r
  have hlogBound : Real.log (2 * x) ≤ Real.rpow (2 * x) r / r := by
    apply (le_div_iff₀ hr).2
    calc
      Real.log (2 * x) * r = r * Real.log (2 * x) := by ring
      _ = Real.log (Real.rpow (2 * x) r) :=
        (Real.log_rpow hy r).symm
      _ ≤ Real.rpow (2 * x) r - 1 :=
        Real.log_le_sub_one_of_pos hyrPos
      _ ≤ Real.rpow (2 * x) r := by linarith
  have hfourth := pow_le_pow_left₀ hlog0 hlogBound 4
  calc
    (Real.log (2 * x)) ^ 4 ≤ (Real.rpow (2 * x) r / r) ^ 4 := hfourth
    _ = (Real.rpow 2 theta / (theta / 4) ^ 4) * Real.rpow x theta := by
      have htwo : 0 ≤ (2 : ℝ) := by norm_num
      have hx0 : 0 ≤ x := (zero_lt_one.trans_le hx).le
      have hmul : Real.rpow (2 * x) r =
          Real.rpow 2 r * Real.rpow x r := Real.mul_rpow htwo hx0
      rw [hmul]
      dsimp [r]
      rw [div_pow]
      have hpow2 : (Real.rpow 2 (theta / 4)) ^ 4 = Real.rpow 2 theta := by
        calc
          (Real.rpow 2 (theta / 4)) ^ 4 =
              Real.rpow (Real.rpow 2 (theta / 4)) (4 : ℝ) :=
            (Real.rpow_natCast _ 4).symm
          _ = Real.rpow 2 ((theta / 4) * 4) :=
            (Real.rpow_mul htwo (theta / 4) 4).symm
          _ = Real.rpow 2 theta := by congr 1 <;> ring
      have hpowx : (Real.rpow x (theta / 4)) ^ 4 = Real.rpow x theta := by
        calc
          (Real.rpow x (theta / 4)) ^ 4 =
              Real.rpow (Real.rpow x (theta / 4)) (4 : ℝ) :=
            (Real.rpow_natCast _ 4).symm
          _ = Real.rpow x ((theta / 4) * 4) :=
            (Real.rpow_mul hx0 (theta / 4) 4).symm
          _ = Real.rpow x theta := by congr 1 <;> ring
      rw [mul_pow]
      change (Real.rpow 2 (theta / 4)) ^ 4 *
          (Real.rpow x (theta / 4)) ^ 4 / (theta / 4) ^ 4 = _
      rw [hpow2, hpowx]
      change Real.rpow 2 theta * Real.rpow x theta / (theta / 4) ^ 4 =
        (Real.rpow 2 theta / (theta / 4) ^ 4) * Real.rpow x theta
      ring

/-- The raw comparison estimate implies the source's customary subpower
L-value lower bound for every character different from the selected one. -/
theorem GoldfeldComparisonEstimateFourLog.lvalue_power_lower
    (hGoldfeld : GoldfeldComparisonEstimateFourLog)
    {nu : ℝ} (hnu : 0 < nu) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      ∀ (exceptional a : PrimitiveRealCharacter),
        exceptional.level ≤ a.level → a ≠ exceptional →
        ∀ betaExceptional : ℝ,
          1 / 2 < betaExceptional → betaExceptional < 1 →
          exceptional.LFunction betaExceptional = 0 →
            C * Real.rpow (a.level : ℝ)
                (-(A * (1 - betaExceptional) + nu)) ≤
              ‖a.LFunction 1‖ := by
  rcases hGoldfeld with ⟨A, C0, hA, hC0, hcomparison⟩
  let D : ℝ := Real.rpow 2 nu / (nu / 4) ^ 4
  have hD : 0 < D := div_pos (Real.rpow_pos_of_pos (by norm_num) nu)
    (pow_pos (div_pos hnu (by norm_num)) 4)
  let C : ℝ := C0 / D
  have hC : 0 < C := div_pos hC0 hD
  refine ⟨A, C, hA, hC, ?_⟩
  intro exceptional a hlevel hne beta hbetaHalf hbetaOne hzero
  have hqOne : (1 : ℝ) ≤ (a.level : ℝ) := by
    exact_mod_cast (NeZero.one_le : 1 ≤ a.level)
  have hlogCube := log_two_mul_fourth_le_const_mul_rpow hnu hqOne
  change (Real.log (2 * (a.level : ℝ))) ^ 4 ≤
    D * Real.rpow (a.level : ℝ) nu at hlogCube
  have hlogPos : 0 < Real.log (2 * (a.level : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ a.level := hqOne
    nlinarith
  have hqPos : 0 < (a.level : ℝ) := zero_lt_one.trans_le hqOne
  have hraw := hcomparison exceptional a hlevel hne beta
    hbetaHalf hbetaOne hzero
  have hnumNonneg :
      0 ≤ C0 * Real.rpow (a.level : ℝ) (-A * (1 - beta)) :=
    mul_nonneg hC0.le (Real.rpow_nonneg hqPos.le _)
  have hinv :
      (D * Real.rpow (a.level : ℝ) nu)⁻¹ ≤
        ((Real.log (2 * (a.level : ℝ))) ^ 4)⁻¹ := by
    exact (inv_le_inv₀
      (mul_pos hD (Real.rpow_pos_of_pos hqPos nu))
      (pow_pos hlogPos 4)).2 hlogCube
  have hmerge :
      C * Real.rpow (a.level : ℝ) (-(A * (1 - beta) + nu)) =
        (C0 * Real.rpow (a.level : ℝ) (-A * (1 - beta))) *
          (D * Real.rpow (a.level : ℝ) nu)⁻¹ := by
    dsimp [C]
    rw [show -(A * (1 - beta) + nu) = -A * (1 - beta) + (-nu) by ring]
    rw [Real.rpow_add hqPos, Real.rpow_neg hqPos.le]
    field_simp
  rw [hmerge]
  calc
    (C0 * Real.rpow (a.level : ℝ) (-A * (1 - beta))) *
          (D * Real.rpow (a.level : ℝ) nu)⁻¹ ≤
        (C0 * Real.rpow (a.level : ℝ) (-A * (1 - beta))) *
          ((Real.log (2 * (a.level : ℝ))) ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hnumNonneg
    _ = C0 * Real.rpow (a.level : ℝ) (-A * (1 - beta)) /
          (Real.log (2 * (a.level : ℝ))) ^ 4 := by rw [div_eq_mul_inv]
    _ ≤ ‖a.LFunction 1‖ := hraw

/-- Minimal-conductor selection, following the first paragraph of the proof
of Theorem 12.9.  Away from one selected character, a smaller conductor has
no zero in the chosen near-one interval, while a larger conductor receives
the Goldfeld L-value lower bound. -/
theorem GoldfeldComparisonEstimateFourLog.exists_allButOne_nearOne_or_lvalue
    (hGoldfeld : GoldfeldComparisonEstimateFourLog)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 / 2 ∧
      ∃ exception : Option PrimitiveRealCharacter,
        ∀ a : PrimitiveRealCharacter, some a ≠ exception →
          (∀ beta : ℝ, 1 - delta ≤ beta → beta < 1 →
              a.LFunction beta ≠ 0) ∨
            C * Real.rpow (a.level : ℝ) (-epsilon / 2) ≤
              ‖a.LFunction 1‖ := by
  rcases hGoldfeld.lvalue_power_lower (show 0 < epsilon / 4 by positivity) with
    ⟨A, C, hA, hC, hlower⟩
  let delta : ℝ := min (1 / 4) (epsilon / (4 * A))
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  have hdeltaQuarter : delta ≤ 1 / 4 := min_le_left _ _
  have hdeltaHalf : delta ≤ 1 / 2 := hdeltaQuarter.trans (by norm_num)
  have hAdelta : A * delta ≤ epsilon / 4 := by
    have hd := min_le_right (1 / 4 : ℝ) (epsilon / (4 * A))
    calc
      A * delta ≤ A * (epsilon / (4 * A)) :=
        mul_le_mul_of_nonneg_left hd hA.le
      _ = epsilon / 4 := by field_simp
  let BadLevel : ℕ → Prop := fun q =>
    ∃ (a : PrimitiveRealCharacter) (beta : ℝ),
      a.level = q ∧ 1 - delta ≤ beta ∧ beta < 1 ∧
        a.LFunction beta = 0
  classical
  by_cases hbad : ∃ q, BadLevel q
  · let qExceptional : ℕ := Nat.find hbad
    rcases Nat.find_spec hbad with
      ⟨exceptional, betaExceptional, hlevelExceptional,
        hbetaLo, hbetaHi, hbetaZero⟩
    have hbetaHalfStrict : 1 / 2 < betaExceptional := by
      linarith
    refine ⟨C, delta, hC, hdelta, hdeltaHalf, some exceptional, ?_⟩
    intro a hne
    have hane : a ≠ exceptional := by simpa using hne
    by_cases hlevel : a.level < qExceptional
    · left
      intro beta hbetaLo' hbetaHi' hbetaZero'
      have hBadA : BadLevel a.level :=
        ⟨a, beta, rfl, hbetaLo', hbetaHi', hbetaZero'⟩
      exact (Nat.find_min hbad hlevel) hBadA
    · right
      have hqOrder : exceptional.level ≤ a.level := by
        rw [hlevelExceptional]
        exact not_lt.mp hlevel
      have hsource := hlower exceptional a hqOrder hane betaExceptional
        hbetaHalfStrict hbetaHi hbetaZero
      have hgapDelta : 1 - betaExceptional ≤ delta := by linarith
      have hexponent :
          A * (1 - betaExceptional) + epsilon / 4 ≤ epsilon / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hgapDelta hA.le
        linarith
      have hqOne : (1 : ℝ) ≤ (a.level : ℝ) := by
        exact_mod_cast (NeZero.one_le : 1 ≤ a.level)
      have hpow :
          Real.rpow (a.level : ℝ) (-epsilon / 2) ≤
            Real.rpow (a.level : ℝ)
              (-(A * (1 - betaExceptional) + epsilon / 4)) := by
        apply Real.rpow_le_rpow_of_exponent_le hqOne
        linarith
      exact (mul_le_mul_of_nonneg_left hpow hC.le).trans hsource
  · refine ⟨C, delta, hC, hdelta, hdeltaHalf, none, ?_⟩
    intro a _ha
    left
    intro beta hbetaLo hbetaHi hbetaZero
    exact hbad ⟨a.level, a, beta, rfl, hbetaLo, hbetaHi, hbetaZero⟩

/-- The Goldfeld comparison implies the complete primitive all-but-one
zero-free region of Koukoulopoulos Theorem 12.9.  This theorem performs all
minimal-conductor, logarithmic-absorption, and near-one derivative
bookkeeping; only the smoothed contour comparison remains as input. -/
theorem GoldfeldComparisonEstimateFourLog.to_allButOneZeroFree
    (hGoldfeld : GoldfeldComparisonEstimateFourLog) :
    GoldfeldPrimitiveAllButOneZeroFree := by
  intro epsilon hepsilon
  have hquarter : 0 < epsilon / 4 := by positivity
  rcases MAPZeroFreeSiegelSpine.exists_nearOne_derivative_subpower_bound
      hquarter with ⟨M, eta, hM, heta, hderiv⟩
  rcases hGoldfeld.exists_allButOne_nearOne_or_lvalue hepsilon with
    ⟨C, delta, hC, hdelta, hdeltaHalf, exception, hcontrol⟩
  let c : ℝ := min delta (min eta (C / M))
  have hc : 0 < c := lt_min hdelta (lt_min heta (div_pos hC hM))
  refine ⟨c, hc, exception, ?_⟩
  intro a hne sigma hsigma
  by_cases hsigmaOne : 1 ≤ sigma
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re
      a.chi (.inl a.nonprincipal) (by simpa using hsigmaOne)
  · intro hzeroPackaged
    have hzero : DirichletCharacter.LFunction a.chi sigma = 0 := by
      simpa [PrimitiveRealCharacter.LFunction] using hzeroPackaged
    have hqOne : (1 : ℝ) ≤ (a.level : ℝ) := by
      exact_mod_cast (NeZero.one_le : 1 ≤ a.level)
    have hqPos : 0 < (a.level : ℝ) := zero_lt_one.trans_le hqOne
    have hpowLeOne : Real.rpow (a.level : ℝ) (-epsilon) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hqOne
        (neg_nonpos.mpr hepsilon.le)
    have hcDelta : c ≤ delta := min_le_left _ _
    have hcEta : c ≤ eta :=
      (min_le_right delta (min eta (C / M))).trans (min_le_left _ _)
    have hcCM : c ≤ C / M :=
      (min_le_right delta (min eta (C / M))).trans (min_le_right _ _)
    have hscaleDelta : c * Real.rpow (a.level : ℝ) (-epsilon) ≤ delta := by
      calc
        c * Real.rpow (a.level : ℝ) (-epsilon) ≤ c * 1 :=
          mul_le_mul_of_nonneg_left hpowLeOne hc.le
        _ ≤ delta := by simpa using hcDelta
    have hscaleEta : c * Real.rpow (a.level : ℝ) (-epsilon) ≤ eta := by
      calc
        c * Real.rpow (a.level : ℝ) (-epsilon) ≤ c * 1 :=
          mul_le_mul_of_nonneg_left hpowLeOne hc.le
        _ ≤ eta := by simpa using hcEta
    have hsigmaLoDelta : 1 - delta ≤ sigma := by linarith
    have hsigmaLoEta : 1 - eta ≤ sigma := by linarith
    have hsigmaHi : sigma ≤ 1 := le_of_not_ge hsigmaOne
    rcases hcontrol a hne with hzeroFree | hLvalue
    · exact (hzeroFree sigma hsigmaLoDelta (lt_of_le_of_ne hsigmaHi
        (Ne.symm (fun hs => by subst sigma; exact hsigmaOne le_rfl))))
        hzeroPackaged
    · have hD := hderiv a.level a.chi a.primitive a.nonprincipal a.real
          sigma hsigmaLoEta hsigmaHi hzero
      have hLvalue' :
          C * Real.rpow (a.level : ℝ) (-(epsilon / 2)) ≤
            ‖DirichletCharacter.LFunction a.chi 1‖ := by
        change C * Real.rpow (a.level : ℝ) (-epsilon / 2) ≤
          ‖DirichletCharacter.LFunction a.chi 1‖ at hLvalue
        convert hLvalue using 1 <;> ring
      have hgap := MAPZeroFreeSiegelSpine.zero_gap_lower_of_siegel_power_bound
        (c := C) (ε := epsilon / 2) a.chi a.nonprincipal hsigmaHi
          (mul_pos hM (Real.rpow_pos_of_pos hqPos (epsilon / 4)))
          hzero hD hLvalue'
      have hmerge :
          (C * Real.rpow (a.level : ℝ) (-(epsilon / 2))) /
              (M * Real.rpow (a.level : ℝ) (epsilon / 4)) =
            (C / M) * Real.rpow (a.level : ℝ) (-(3 * epsilon / 4)) := by
        have hinvPow :
            (Real.rpow (a.level : ℝ) (epsilon / 4))⁻¹ =
              Real.rpow (a.level : ℝ) (-(epsilon / 4)) :=
          (Real.rpow_neg hqPos.le (epsilon / 4)).symm
        have hprodPow :
            Real.rpow (a.level : ℝ) (-(epsilon / 2)) *
                Real.rpow (a.level : ℝ) (-(epsilon / 4)) =
              Real.rpow (a.level : ℝ)
                (-(epsilon / 2) + -(epsilon / 4)) :=
          (Real.rpow_add hqPos (-(epsilon / 2)) (-(epsilon / 4))).symm
        calc
          (C * Real.rpow (a.level : ℝ) (-(epsilon / 2))) /
                (M * Real.rpow (a.level : ℝ) (epsilon / 4)) =
              (C / M) *
                (Real.rpow (a.level : ℝ) (-(epsilon / 2)) /
                  Real.rpow (a.level : ℝ) (epsilon / 4)) := by
            field_simp
          _ = (C / M) *
                (Real.rpow (a.level : ℝ) (-(epsilon / 2)) *
                  Real.rpow (a.level : ℝ) (-(epsilon / 4))) := by
            congr 1
            rw [div_eq_mul_inv, hinvPow]
          _ = (C / M) * Real.rpow (a.level : ℝ)
                (-(epsilon / 2) + -(epsilon / 4)) := by
            congr 1
          _ = (C / M) * Real.rpow (a.level : ℝ)
                (-(3 * epsilon / 4)) := by congr 2 <;> ring
      change (C * Real.rpow (a.level : ℝ) (-(epsilon / 2))) /
          (M * Real.rpow (a.level : ℝ) (epsilon / 4)) ≤ 1 - sigma at hgap
      rw [hmerge] at hgap
      have hpowCompare :
          Real.rpow (a.level : ℝ) (-epsilon) ≤
            Real.rpow (a.level : ℝ) (-(3 * epsilon / 4)) := by
        apply Real.rpow_le_rpow_of_exponent_le hqOne
        linarith
      have htarget :
          c * Real.rpow (a.level : ℝ) (-epsilon) ≤ 1 - sigma := by
        calc
          c * Real.rpow (a.level : ℝ) (-epsilon) ≤
              (C / M) * Real.rpow (a.level : ℝ) (-epsilon) :=
            mul_le_mul_of_nonneg_right hcCM
              (Real.rpow_nonneg hqPos.le _)
          _ ≤ (C / M) * Real.rpow (a.level : ℝ)
                (-(3 * epsilon / 4)) :=
            mul_le_mul_of_nonneg_left hpowCompare (div_pos hC hM).le
          _ ≤ 1 - sigma := hgap
      linarith

/-- Theorem 12.10 and its exceptional-weight consequences now depend only on
the exact Goldfeld comparison theorem, never on the packaged
`PublishedSiegelRealZeroFreeRegion` premise. -/
theorem GoldfeldComparisonEstimateFourLog.to_publishedSiegelRealZeroFreeRegion
    (hGoldfeld : GoldfeldComparisonEstimateFourLog) :
    MAPSiegelExceptionalEndpoint.PublishedSiegelRealZeroFreeRegion :=
  hGoldfeld.to_allButOneZeroFree.to_publishedSiegelRealZeroFreeRegion

/-- Unconditional Koukoulopoulos Theorem 12.10 obtained from the completed
Goldfeld comparison chain. -/
theorem publishedSiegelRealZeroFreeRegion :
    MAPSiegelExceptionalEndpoint.PublishedSiegelRealZeroFreeRegion :=
  goldfeldComparisonEstimateFourLog.to_publishedSiegelRealZeroFreeRegion

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.log_two_mul_fourth_le_const_mul_rpow
#print axioms MAPGoldfeldSiegel.GoldfeldComparisonEstimateFourLog.lvalue_power_lower
#print axioms MAPGoldfeldSiegel.GoldfeldComparisonEstimateFourLog.exists_allButOne_nearOne_or_lvalue
#print axioms MAPGoldfeldSiegel.GoldfeldComparisonEstimateFourLog.to_allButOneZeroFree
#print axioms MAPGoldfeldSiegel.GoldfeldComparisonEstimateFourLog.to_publishedSiegelRealZeroFreeRegion
#print axioms MAPGoldfeldSiegel.publishedSiegelRealZeroFreeRegion
