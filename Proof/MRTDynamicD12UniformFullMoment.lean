import MRTDynamicD12FullMoment
import MRTDynamicD12SmoothFactorMoment

/-! # Uniform d1/d2 Cauchy bound with both actual moment inputs discharged -/
namespace MRTDynamicD12UniformFullMoment

open scoped BigOperators ArithmeticFunction
open MeasureTheory ArithmeticFunction MixedMeanFrontend
open MAPMRTProposition61TypeD1Factorization MAPMRTProposition61TypeD1FirstInequality
open MAPMRTCorollary25Minkowski
open MRTDynamicD12PolynomialFactorization MRTDynamicD12FullMoment
open MRTDynamicD12ShortPrefix MRTDynamicD12SmoothFactorMoment
open MRTDynamicD12FactorExtraction MRTDynamicD12MomentSource
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicSupportV3

noncomputable section
set_option maxHeartbeats 1000000

def sourceSmoothNorm (q : ℕ) (f : NatDyadicFactor)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ‖dyadicFactorPolynomial (f.length : ℝ) (fun n => chi n) f.coeff t‖

def optionalSmoothNorm (q : ℕ) : Option NatDyadicFactor → DirichletCharacter ℂ q → ℝ → ℝ
  | none => fun _ _ => 1
  | some f => sourceSmoothNorm q f

theorem continuous_sourceSmoothNorm (q : ℕ) (f : NatDyadicFactor)
    (chi : DirichletCharacter ℂ q) : Continuous (sourceSmoothNorm q f chi) := by
  unfold sourceSmoothNorm dyadicFactorPolynomial normalizedTwistedTerm mellinPhase
  fun_prop

/-- `gamma = none` is the actual d1 dummy factor; `some gamma` is d2.
The short coefficient is the literal scalar-weighted classifier prefix.
All analytic constants precede every ambient/source parameter. -/
theorem exists_uniform_factoredD12Moment (hbK : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ,
    ∀ {X delta U T rho a b exponent : ℝ} {k q : ℕ} [NeZero q],
      3 ≤ X → 0 ≤ delta → delta ≤ 1 → k < hbK → 0 ≤ U →
      DynamicD12MomentRange (8*X) T exponent q (hbFactorCutoff X) →
      0 < rho → rho ≤ T → 2*X ≤ rho^2 →
      a ≤ b → (b+U)-(a-U)+1 ≤ T →
      (∀ t ∈ Set.Icc (a-U) (b+U), rho ≤ |t| ∧ |t| ≤ T) →
      ∀ (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
      (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X hbK⌋₊))) (k+1))
      (beta : NatDyadicFactor) (gamma : Option NatDyadicFactor),
      IsSourceSmoothFactor X logIndex beta → 2 ≤ beta.length →
      (∀ f, gamma = some f → IsSourceSmoothFactor X logIndex f ∧ 2 ≤ f.length) →
      let small := classifierShortPrefix (delta := delta) logIndex zbag mbag
      (∫ t in a..b,
        (factoredTypeD12Mass
          (shortPrefixNormField q (factorUpperProduct small) (shortPrefixCoefficient zbag mbag small))
          (sourceSmoothNorm q beta) (optionalSmoothNorm q gamma) U t)^2) ≤
        C*((q:ℝ)*U+Real.rpow X delta)*U*((q:ℝ)*T)*(1+Real.log (8*X))^B := by
  obtain ⟨Ca,hCa,Ba,ha⟩ := exists_classifierShortPrefix_localMeanSquare hbK
  obtain ⟨Cb,hCb,Bb,hBb,hb⟩ := dynamicD12SourceSmoothFactorMoment_proved
  let D := max 1 Cb
  refine ⟨2*Ca*D, by dsimp [D]; positivity, Ba+Bb, ?_⟩
  intro X delta U T rho a b exponent k q inst hX hd hd1 hk hU hrange hrho hrhoT hXrho
    hab hlen hann logIndex zbag mbag beta gamma hbeta hbetaLen hgamma
  dsimp only
  let small := classifierShortPrefix (delta := delta) logIndex zbag mbag
  let alpha := shortPrefixNormField q (factorUpperProduct small) (shortPrefixCoefficient zbag mbag small)
  let L := 1+Real.log (8*X)
  let P := Ca*((q:ℝ)*U+Real.rpow X delta)*L^Ba
  let Q := D*((q:ℝ)*T)*L^Bb
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogL : Real.log X ≤ L := by
    have h := Real.log_le_log (by linarith : 0 < X) (show X ≤ 8*X by linarith)
    dsimp [L]
    linarith
  have hL : 1 ≤ L := by
    dsimp [L]
    have h := Real.log_nonneg (show 1 ≤ 8*X by linarith)
    linarith
  have hT : 0 ≤ T := by linarith [hrange.T_ge_two]
  have hD : 1 ≤ D := le_max_left _ _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have halpha : ∀ chi, Continuous (alpha chi) := fun chi =>
    continuous_shortPrefixNormField _ _ _ _
  have hbcont : ∀ chi, Continuous (sourceSmoothNorm q beta chi) :=
    fun chi => continuous_sourceSmoothNorm _ _ _
  have hgcont : ∀ chi, Continuous (optionalSmoothNorm q gamma chi) := by
    intro chi
    cases gamma with
    | none => exact continuous_const
    | some f => exact continuous_sourceSmoothNorm _ _ _
  have hlocal : ∀ t ∈ Set.uIcc a b, alphaLocalSquareMass alpha U t ≤ P := by
    intro t ht
    unfold alphaLocalSquareMass
    rw [← intervalIntegral.integral_finsetSum]
    · have h := ha (q := q) (delta := delta) hX hd hd1 hk hU t logIndex zbag mbag
      exact h.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlogX hlogL Ba)
        (mul_nonneg hCa.le (add_nonneg (mul_nonneg (Nat.cast_nonneg q) hU)
          (Real.rpow_nonneg (by linarith) delta))))
    · intro chi hchi
      exact ((halpha chi).pow 2).intervalIntegrable _ _
  have hsmooth (f : NatDyadicFactor) (hf : IsSourceSmoothFactor X logIndex f)
      (hfLen : 2 ≤ f.length) :
      (∫ t in (a-U)..(b+U), ∑ chi : DirichletCharacter ℂ q,
        (sourceSmoothNorm q f chi t)^4) ≤ Q := by
    rw [intervalIntegral.integral_finsetSum]
    · have h := hb logIndex f hX hrange hf hfLen hrho hrhoT hXrho
        (by linarith) hlen hann
      apply h.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 Cb) (by positivity)) (by positivity)
    · intro chi hchi
      exact ((continuous_sourceSmoothNorm q f chi).pow 4).intervalIntegrable _ _
  have hfourth1 := hsmooth beta hbeta hbetaLen
  have hfourth2 :
      (∫ t in (a-U)..(b+U), ∑ chi : DirichletCharacter ℂ q,
        (optionalSmoothNorm q gamma chi t)^4) ≤ Q := by
    cases gamma with
    | some f => exact hsmooth f (hgamma f rfl).1 (hgamma f rfl).2
    | none =>
      have hc := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      rw [Nat.card_eq_fintype_card] at hc
      have hc' : (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ q := by
        exact_mod_cast hc.le.trans (Nat.totient_le q)
      have hduration : 0 ≤ (b+U)-(a-U) := by linarith
      have hdurationT : (b+U)-(a-U) ≤ T := by linarith
      have hbase : (q:ℝ)*T ≤ Q := by
        have hpow : 1 ≤ L^Bb := one_le_pow₀ hL
        dsimp [Q]
        nlinarith [mul_nonneg (by positivity : 0 ≤ (q:ℝ)*T) (sub_nonneg.mpr hD),
          mul_nonneg (by positivity : 0 ≤ D*((q:ℝ)*T)) (sub_nonneg.mpr hpow)]
      simp only [optionalSmoothNorm, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, intervalIntegral.integral_const, smul_eq_mul]
      exact (mul_le_mul hdurationT hc' (by positivity) hT).trans
        (by simpa only [mul_comm] using hbase)
  have hmass := typeD12_outerMass_le_of_meanValue_and_fourthMoments
    halpha hbcont hgcont
    (fun chi t => norm_nonneg _) (fun chi t => norm_nonneg _)
    (fun chi t => by cases gamma <;> simp [optionalSmoothNorm, sourceSmoothNorm])
    hab hU hP hQ hlocal hfourth1 hfourth2
  have hsqrt : Real.sqrt Q * Real.sqrt Q = Q := by
    simpa only [pow_two] using Real.sq_sqrt hQ
  rw [hsqrt] at hmass
  calc
    _ ≤ 2*U*P*Q := hmass
    _ = _ := by dsimp [P,Q,L,D]; rw [pow_add]; ring

/-- The exact d1 polynomial source supplies the factored moving mass. -/
theorem characterMovingMass_prefix_tail_one {q : ℕ} (c : ℂ)
    (factors : List NatDyadicFactor) (hone : ∀ f ∈ factors, 1 ≤ f.length)
    (s : ℕ) (beta : NatDyadicFactor) (htail : factors.drop s = [beta]) (U t : ℝ) :
    characterMovingMass (fun chi : DirichletCharacter ℂ q => fun v =>
      ‖prefixPolynomial q (factorUpperProduct factors) (c • factorConvolution factors) chi v‖) U t =
    factoredTypeD12Mass (fun chi : DirichletCharacter ℂ q => fun v =>
      ‖prefixPolynomial q (factorUpperProduct (factors.take s))
        (c • factorConvolution (factors.take s)) chi v‖)
      (sourceSmoothNorm q beta) (optionalSmoothNorm q none) U t := by
  unfold characterMovingMass factoredTypeD12Mass movingIntegral
  apply Finset.sum_congr rfl
  intro chi hchi
  apply intervalIntegral.integral_congr
  intro v hv
  simpa only [sourceSmoothNorm, optionalSmoothNorm, mul_one] using
    norm_prefix_tail_one c factors hone s beta htail chi v

/-- The exact d2 polynomial source supplies the factored moving mass. -/
theorem characterMovingMass_prefix_tail_two {q : ℕ} (c : ℂ)
    (factors : List NatDyadicFactor) (hone : ∀ f ∈ factors, 1 ≤ f.length)
    (s : ℕ) (beta gamma : NatDyadicFactor) (htail : factors.drop s = [beta,gamma]) (U t : ℝ) :
    characterMovingMass (fun chi : DirichletCharacter ℂ q => fun v =>
      ‖prefixPolynomial q (factorUpperProduct factors) (c • factorConvolution factors) chi v‖) U t =
    factoredTypeD12Mass (fun chi : DirichletCharacter ℂ q => fun v =>
      ‖prefixPolynomial q (factorUpperProduct (factors.take s))
        (c • factorConvolution (factors.take s)) chi v‖)
      (sourceSmoothNorm q beta) (optionalSmoothNorm q (some gamma)) U t := by
  unfold characterMovingMass factoredTypeD12Mass movingIntegral
  apply Finset.sum_congr rfl
  intro chi hchi
  apply intervalIntegral.integral_congr
  intro v hv
  simpa only [sourceSmoothNorm, optionalSmoothNorm, mul_assoc] using
    norm_prefix_tail_two c factors hone s beta gamma htail chi v


end
end MRTDynamicD12UniformFullMoment

#print axioms MRTDynamicD12UniformFullMoment.exists_uniform_factoredD12Moment

#print axioms MRTDynamicD12UniformFullMoment.characterMovingMass_prefix_tail_two
