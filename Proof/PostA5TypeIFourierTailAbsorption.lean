import PostA5TypeIFourierAssembly

/-!
# Eventual Type-I Fourier-tail absorption

This module combines the certified divisor-subpower coefficient mass with the
uniform arbitrary-moment Fourier tail.  The radius is the project power
`H=T^h`; a fixed sufficiently large moment `k` absorbs the coefficient mass,
the dyadic count, and all fixed constants while retaining the exact detector
threshold divided by `2 * detectorDyadicCount N`.
-/

namespace PostA5TypeIFourierTailAbsorption

open Filter Set MeasureTheory
open scoped BigOperators FourierTransform
open CGLProofDAG FixedCharacterPoweredBridge
open MAPAppendixA4PostA5SetAdapter PostA5TypeIFourierAssembly SchwartzMap

noncomputable section

/-- The common coefficient mass on a dyadic shell is at most
`K*2^e*T^(3/10+e)` throughout the high strip, provided the shell length is at
most `T`. -/
theorem detectorCommonCoefficientMass_le_time_power
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N D : ℕ} {Y sigma e K T : ℝ}
    (hY : 0 < Y) (hD : 1 ≤ D) (hDT : (D : ℝ) ≤ T)
    (hT : 1 ≤ T) (hsigmaLow : 7 / 10 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) (he : 0 < e) (hK : 0 < K)
    (hdiv : ∀ n : ℕ, 0 < n →
      (orderedDivisorCount 2 n : ℝ) ≤ K * Real.rpow n e) :
    (∑ n ∈ Finset.Ioc D (2 * D),
        ‖detectorCommonCoefficient chi U N Y sigma n‖) ≤
      K * Real.rpow 2 e * Real.rpow T (3 / 10 + e) := by
  have hmass := detectorCommonCoefficientMass_le (U := U) (N := N) chi hY hD
    (by linarith : 0 ≤ sigma) he.le hK.le
    (fun n hn => hdiv n (by
      have hnD := (Finset.mem_Ioc.mp hn).1
      omega))
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hD0 : (0 : ℝ) ≤ D := hDpos.le
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hexp0 : 0 ≤ 1 - sigma + e := by linarith
  have hexpLe : 1 - sigma + e ≤ 3 / 10 + e := by linarith
  have hDpow : Real.rpow D (1 - sigma + e) ≤
      Real.rpow T (1 - sigma + e) :=
    Real.rpow_le_rpow hD0 hDT hexp0
  have hTpow : Real.rpow T (1 - sigma + e) ≤
      Real.rpow T (3 / 10 + e) :=
    Real.rpow_le_rpow_of_exponent_le hT hexpLe
  have htwoD : Real.rpow (2 * (D : ℝ)) e =
      Real.rpow 2 e * Real.rpow D e := by
    exact Real.mul_rpow (by norm_num) hD0
  have hcombineD : (D : ℝ) * Real.rpow D (-sigma) * Real.rpow D e =
      Real.rpow D (1 - sigma + e) := by
    calc
      (D : ℝ) * Real.rpow D (-sigma) * Real.rpow D e =
          Real.rpow D 1 * Real.rpow D (-sigma) * Real.rpow D e := by
        exact congrArg (fun z : ℝ => z * Real.rpow D (-sigma) *
          Real.rpow D e) (Real.rpow_one D).symm
      _ = Real.rpow D (1 + -sigma) * Real.rpow D e := by
        exact congrArg (fun z : ℝ => z * Real.rpow D e)
          (Real.rpow_add hDpos 1 (-sigma)).symm
      _ = Real.rpow D ((1 + -sigma) + e) := by
        exact (Real.rpow_add hDpos (1 + -sigma) e).symm
      _ = Real.rpow D (1 - sigma + e) := by
        have hexp : (1 + -sigma) + e = 1 - sigma + e := by ring
        rw [hexp]
  calc
    (∑ n ∈ Finset.Ioc D (2 * D),
        ‖detectorCommonCoefficient chi U N Y sigma n‖) ≤
      (D : ℝ) * (Real.rpow D (-sigma) *
        (K * Real.rpow (2 * D) e)) := hmass
    _ = K * Real.rpow 2 e * Real.rpow D (1 - sigma + e) := by
      rw [htwoD]
      rw [← hcombineD]
      ring
    _ ≤ K * Real.rpow 2 e * Real.rpow T (1 - sigma + e) := by
      exact mul_le_mul_of_nonneg_left hDpow
        (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))
    _ ≤ K * Real.rpow 2 e * Real.rpow T (3 / 10 + e) := by
      exact mul_le_mul_of_nonneg_left hTpow
        (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))

theorem inv_pow_power_radius
    {T h : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    ((Real.rpow T h) ^ k)⁻¹ =
      Real.rpow T (-(h * (k : ℝ))) := by
  calc
    ((Real.rpow T h) ^ k)⁻¹ =
        (Real.rpow (Real.rpow T h) (k : ℝ))⁻¹ := by
      exact congrArg Inv.inv (Real.rpow_natCast (Real.rpow T h) k).symm
    _ = (Real.rpow T (h * (k : ℝ)))⁻¹ := by
      exact congrArg Inv.inv (Real.rpow_mul hT h (k : ℝ)).symm
    _ = Real.rpow T (-(h * (k : ℝ))) := by
      exact (Real.rpow_neg hT (h * (k : ℝ))).symm

/-- Uniform eventual absorption of the literal Fourier-product tail.  The
only size hypotheses left to the consumer are the elementary shell and
dyadic-count bounds `D≤T` and `J≤2T`. -/
theorem eventually_detectorCommonCoefficient_mul_fourierTail_le
    (e h delta : ℝ) (he : 0 < e) (hh : 0 < h) (hdelta : 0 < delta)
    (k : ℕ)
    (hgap : 3 / 10 + e - h * (k : ℝ) + 1 ≤ -delta - 2) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (U N : ℕ) (Y sigma : ℝ) (rho : ℂ)
        (j : Fin (detectorDyadicCount N)),
        4 ≤ T → 0 < Y → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        sigma ≤ rho.re → rho.re ≤ 1 →
        ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T →
        (detectorDyadicCount N : ℝ) ≤ 2 * T →
        (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
            ‖detectorCommonCoefficient chi U N Y sigma n‖) *
          (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
            ‖((𝓕 (detectorRealPartCutoff
              (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
            (Real.rpow T (-delta) /
              (detectorDyadicCount N : ℝ)) / 2 := by
  obtain ⟨K, hK, hdiv⟩ :=
    orderedDivisorCount_subpolynomial 2 (by omega) e he
  let C₀ : ℝ := K * Real.rpow 2 e * detectorFourierMomentConstant k
  filter_upwards [eventually_ge_atTop C₀, eventually_ge_atTop 4]
    with T hC₀ hTfour
  intro q _inst chi U N Y sigma rho j hT hY hsigmaLow hsigmaHigh
    hbetaLow hbetaHigh hDT hJ
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hT0 : 0 ≤ T := hTpos.le
  have hD : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
  have ha0 : 0 ≤ rho.re - sigma := by linarith
  have ha : rho.re - sigma ≤ 3 / 10 := by linarith
  have hmass := detectorCommonCoefficientMass_le_time_power (U := U) (N := N)
    chi hY hD hDT
    hTone hsigmaLow hsigmaHigh he hK hdiv
  have hHpos : 0 < Real.rpow T h := Real.rpow_pos_of_pos hTpos _
  have htail :=
    integral_compl_Icc_norm_fourier_detectorRealPartCutoff_le
      hD ha0 ha k hHpos
  have hC₀nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    exact mul_nonneg
      (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))
      (detectorFourierMomentConstant_nonneg k)
  have hraw :
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        Real.rpow T (-delta - 2) := by
    calc
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (K * Real.rpow 2 e * Real.rpow T (3 / 10 + e)) *
            (((Real.rpow T h) ^ k)⁻¹ * detectorFourierMomentConstant k) :=
        mul_le_mul hmass htail
          (integral_nonneg fun _ => norm_nonneg _)
          (mul_nonneg
            (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))
            (Real.rpow_nonneg hT0 _))
      _ = C₀ * Real.rpow T (3 / 10 + e - h * (k : ℝ)) := by
        rw [inv_pow_power_radius hT0]
        have hcombineT : Real.rpow T (3 / 10 + e) *
            Real.rpow T (-(h * (k : ℝ))) =
            Real.rpow T (3 / 10 + e - h * (k : ℝ)) := by
          calc
            Real.rpow T (3 / 10 + e) *
                Real.rpow T (-(h * (k : ℝ))) =
                Real.rpow T ((3 / 10 + e) + -(h * (k : ℝ))) :=
              (Real.rpow_add hTpos (3 / 10 + e) (-(h * (k : ℝ)))).symm
            _ = Real.rpow T (3 / 10 + e - h * (k : ℝ)) := by
              have hexp : (3 / 10 + e) + -(h * (k : ℝ)) =
                  3 / 10 + e - h * (k : ℝ) := by ring
              rw [hexp]
        rw [← hcombineT]
        dsimp [C₀]
        ring
      _ ≤ T * Real.rpow T (3 / 10 + e - h * (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hC₀
          (Real.rpow_nonneg hT0 _)
      _ = Real.rpow T (3 / 10 + e - h * (k : ℝ) + 1) := by
        calc
          T * Real.rpow T (3 / 10 + e - h * (k : ℝ)) =
              Real.rpow T 1 *
                Real.rpow T (3 / 10 + e - h * (k : ℝ)) := by
            exact congrArg (fun z : ℝ => z *
              Real.rpow T (3 / 10 + e - h * (k : ℝ)))
                (Real.rpow_one T).symm
          _ = Real.rpow T (1 + (3 / 10 + e - h * (k : ℝ))) := by
            exact (Real.rpow_add hTpos 1
              (3 / 10 + e - h * (k : ℝ))).symm
          _ = Real.rpow T (3 / 10 + e - h * (k : ℝ) + 1) := by
            have hexp : 1 + (3 / 10 + e - h * (k : ℝ)) =
                3 / 10 + e - h * (k : ℝ) + 1 := by ring
            rw [hexp]
      _ ≤ Real.rpow T (-delta - 2) :=
        Real.rpow_le_rpow_of_exponent_le hTone hgap
  have hJposNat : 0 < detectorDyadicCount N := by
    unfold detectorDyadicCount
    omega
  have hJpos : (0 : ℝ) < detectorDyadicCount N := by exact_mod_cast hJposNat
  rw [div_div]
  apply (le_div_iff₀ (mul_pos hJpos (by norm_num))).2
  have hden : (detectorDyadicCount N : ℝ) * 2 ≤ 4 * T := by linarith
  have hfourT : 4 * T ≤ T ^ (2 : ℕ) := by nlinarith
  have hTtwo : T ^ (2 : ℕ) = Real.rpow T 2 := by
    exact (Real.rpow_natCast T 2).symm
  calc
    ((∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖)) *
          ((detectorDyadicCount N : ℝ) * 2) ≤
      Real.rpow T (-delta - 2) * (4 * T) :=
        mul_le_mul hraw hden (by positivity)
          (Real.rpow_nonneg hT0 _)
    _ ≤ Real.rpow T (-delta - 2) * (T ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hfourT (Real.rpow_nonneg hT0 _)
    _ = Real.rpow T (-delta) := by
      rw [hTtwo]
      calc
        Real.rpow T (-delta - 2) * Real.rpow T 2 =
            Real.rpow T ((-delta - 2) + 2) :=
          (Real.rpow_add hTpos (-delta - 2) 2).symm
        _ = Real.rpow T (-delta) := by
          have hexp : (-delta - 2) + 2 = -delta := by ring
          rw [hexp]

/-- A Fourier moment can always be chosen to save any prescribed positive
power at a fixed positive power radius. -/
theorem exists_fourierMoment_gap
    (e h delta : ℝ) (hh : 0 < h) :
    ∃ k : ℕ,
      3 / 10 + e - h * (k : ℝ) + 1 ≤ -delta - 2 := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((delta + 33 / 10 + e) / h)
  refine ⟨k, ?_⟩
  have hmul : delta + 33 / 10 + e < h * (k : ℝ) := by
    have h' := (div_lt_iff₀ hh).1 hk
    nlinarith
  linarith

/-- Consumer form of the tail absorption theorem.  The chosen moment depends
only on the fixed exponent data.  A literal detector lower bound
`T^-delta ≤ V` then gives exactly the `V / J / 2` tail premise required by the
common-dyadic Fourier extractor, uniformly in every arithmetic and zero
parameter. -/
theorem eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_value
    (e h delta : ℝ) (he : 0 < e) (hh : 0 < h) (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (U N : ℕ) (Y sigma : ℝ) (rho : ℂ)
        (j : Fin (detectorDyadicCount N)) (V : ℝ),
        4 ≤ T → 0 < Y → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        sigma ≤ rho.re → rho.re ≤ 1 →
        ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T →
        (detectorDyadicCount N : ℝ) ≤ 2 * T →
        Real.rpow T (-delta) ≤ V →
        (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
            ‖detectorCommonCoefficient chi U N Y sigma n‖) *
          (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
            ‖((𝓕 (detectorRealPartCutoff
              (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
            (V / (detectorDyadicCount N : ℝ)) / 2 := by
  obtain ⟨k, hgap⟩ := exists_fourierMoment_gap e h delta hh
  filter_upwards
      [eventually_detectorCommonCoefficient_mul_fourierTail_le
        e h delta he hh hdelta k hgap] with T htail
  intro q _inst chi U N Y sigma rho j V hT hY hsigmaLow hsigmaHigh
    hbetaLow hbetaHigh hDT hJ hV
  calc
    (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
        ‖detectorCommonCoefficient chi U N Y sigma n‖) *
      (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
        ‖((𝓕 (detectorRealPartCutoff
          (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        (Real.rpow T (-delta) /
          (detectorDyadicCount N : ℝ)) / 2 :=
      htail q chi U N Y sigma rho j hT hY hsigmaLow hsigmaHigh
        hbetaLow hbetaHigh hDT hJ
    _ ≤ (V / (detectorDyadicCount N : ℝ)) / 2 := by
      gcongr

/-- The exact project-budget specialization: the saved tail power is the
source-normalized detector loss `inputLoss kappa eta`. -/
theorem eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_inputLoss
    (kappa eta e h : ℝ)
    (hkappa : 0 < kappa) (heta : 0 < eta) (he : 0 < e) (hh : 0 < h) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (U N : ℕ) (Y sigma : ℝ) (rho : ℂ)
        (j : Fin (detectorDyadicCount N)) (V : ℝ),
        4 ≤ T → 0 < Y → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        sigma ≤ rho.re → rho.re ≤ 1 →
        ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T →
        (detectorDyadicCount N : ℝ) ≤ 2 * T →
        Real.rpow T (-inputLoss kappa eta) ≤ V →
        (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
            ‖detectorCommonCoefficient chi U N Y sigma n‖) *
          (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
            ‖((𝓕 (detectorRealPartCutoff
              (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
            (V / (detectorDyadicCount N : ℝ)) / 2 :=
  eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_value
    e h (inputLoss kappa eta) he hh (inputLoss_pos hkappa heta)

end
end PostA5TypeIFourierTailAbsorption

#print axioms PostA5TypeIFourierTailAbsorption.detectorCommonCoefficientMass_le_time_power
#print axioms PostA5TypeIFourierTailAbsorption.inv_pow_power_radius
#print axioms PostA5TypeIFourierTailAbsorption.eventually_detectorCommonCoefficient_mul_fourierTail_le
#print axioms PostA5TypeIFourierTailAbsorption.exists_fourierMoment_gap
#print axioms PostA5TypeIFourierTailAbsorption.eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_value
#print axioms PostA5TypeIFourierTailAbsorption.eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_inputLoss
