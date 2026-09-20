import GuthMaynardLemma2910SourceBound
import GuthMaynardLemma2910AnchorScale
import GuthMaynardJutilaOneSpacingWeld

namespace GuthMaynardLemma2910OptimizedAnchor

open GuthMaynardJutilaReflection2941
open GuthMaynardLengthComparison
open GuthMaynardHeathBrownMajorant
open GuthMaynardLemma2910Absorption
open GuthMaynardLemma2910SourceBound
open GuthMaynardLemma2910HighRangeFromAFE
open GuthMaynardTPowerCardinality
open GuthMaynardLowAnchorTransfer

noncomputable section

/-- The balancing anchor, with a fixed collar to make arbitrary-length
comparison legal. -/
def balancedAnchor (N A R : ℝ) := max N (max 2 (Real.sqrt (A*Real.sqrt R)))

/-- The reciprocal term at the balancing anchor is at most its linear term. -/
theorem balancedAnchor_reciprocal_le
    {N A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    R*Real.sqrt R*(A / balancedAnchor N A R) ≤
      R*Real.sqrt (A*Real.sqrt R) := by
  let P := balancedAnchor N A R
  have hPtwo : 2 ≤ P := (le_max_left _ _).trans (le_max_right _ _)
  have hrootP : Real.sqrt (A*Real.sqrt R) ≤ P :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hroot : (Real.sqrt (A*Real.sqrt R))^2 = A*Real.sqrt R :=
    Real.sq_sqrt (by positivity)
  have hprod := mul_le_mul_of_nonneg_left hrootP (Real.sqrt_nonneg (A*Real.sqrt R))
  have hdiv : A*Real.sqrt R/P ≤ Real.sqrt (A*Real.sqrt R) := by
    apply (div_le_iff₀ (by linarith : 0<P)).2
    nlinarith only [hprod,hroot]
  have hm := mul_le_mul_of_nonneg_left hdiv hR
  calc
    _ = R*(A*Real.sqrt R/P) := by ring
    _ ≤ _ := hm

/-- A coarse square cap suffices for the certified low-length transfer. -/
theorem balancedAnchor_le_square
    {T N A R : ℝ} (hT : 2 ≤ T) (hNT : N ≤ T)
    (hA : 0 ≤ A) (hAT : A ≤ T^2) (hR : 0 ≤ R) (hRT : R ≤ T^2) :
    balancedAnchor N A R ≤ T^2 := by
  have hT0 : 0 ≤ T := by linarith
  have hsR : Real.sqrt R ≤ T := (Real.sqrt_le_iff).2 ⟨hT0,hRT⟩
  have hroot : Real.sqrt (A*Real.sqrt R) ≤ T^2 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨sq_nonneg _, ?_⟩
    have hm := mul_le_mul hAT hsR (Real.sqrt_nonneg R) (sq_nonneg T)
    have hT1 : T ≤ T^2 := by nlinarith
    have hm₂ := mul_le_mul_of_nonneg_left hT1 (sq_nonneg T)
    nlinarith only [hm,hm₂]
  unfold balancedAnchor
  exact max_le (by nlinarith) (max_le (by nlinarith) hroot)

/-- Exact finite optimization before the time exponent is absorbed. -/
theorem balancedAnchor_shape_le
    {N A R : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hR : 1 ≤ R) :
    R*balancedAnchor N A R + R^2 +
        R*Real.sqrt R*(A/balancedAnchor N A R)+1 ≤
      5*(R*N+R^2+R*Real.sqrt (A*Real.sqrt R)) := by
  have hR0 : 0 ≤ R := by linarith
  have hroot0 := Real.sqrt_nonneg (A*Real.sqrt R)
  have hP : balancedAnchor N A R ≤ N+2+Real.sqrt (A*Real.sqrt R) := by
    unfold balancedAnchor
    apply max_le
    · linarith
    · apply max_le <;> linarith
  have hm := mul_le_mul_of_nonneg_left hP hR0
  have hr := balancedAnchor_reciprocal_le hA hR0 (N := N)
  have hRN : 0 ≤ R*N := by positivity
  have hRroot : 0 ≤ R*Real.sqrt (A*Real.sqrt R) := by positivity
  nlinarith [sq_nonneg (R-1)]

/-- The square-root anchor has exactly the required quarter-cardinality power. -/
theorem root_anchor_eq (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) :
    R*Real.sqrt (A*Real.sqrt R) = Real.rpow R (5/4 : ℝ)*Real.sqrt A := by
  rw [Real.sqrt_mul hA]
  have hquarter : Real.sqrt (Real.sqrt R) = Real.rpow R (1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    calc
      _ = Real.rpow R ((1/2 : ℝ)*(1/2)) := (Real.rpow_mul hR _ _).symm
      _ = Real.rpow R (1/4 : ℝ) := by norm_num
  rw [hquarter]
  have hproduct : R*Real.rpow R (1/4 : ℝ) = Real.rpow R (5/4 : ℝ) := by
    by_cases hRzero : R=0
    · subst R
      norm_num
    · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
      calc
        _ = Real.rpow R 1*Real.rpow R (1/4 : ℝ) := congrArg (fun x : ℝ => x*Real.rpow R (1/4 : ℝ)) (Real.rpow_one R).symm
        _ = Real.rpow R ((1:ℝ)+1/4) := (Real.rpow_add hRpos _ _).symm
        _ = Real.rpow R (5/4 : ℝ) := by norm_num
  calc
    R*(Real.sqrt A*Real.rpow R (1/4 : ℝ)) = (R*Real.rpow R (1/4 : ℝ))*Real.sqrt A := by ring
    _ = _ := by rw [hproduct]


set_option maxHeartbeats 1200000 in
/-- The complete real-length Lemma 29.10 below the aperture, assuming only
the corrected exact-M AFE. All reflection, bootstrap and anchor losses are
absorbed uniformly in the prescribed exponent. -/
theorem real_below_aperture_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {eta delta : ℝ} (heta : 0 < eta) (hdelta : 0 < delta) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T N : ℝ) (G : Finset ℝ),
      T₀ ≤ T → 1 ≤ N → N < T →
      TPowerSeparated G T delta → InOpenClosedZeroT G T →
      jutilaSecondMoment N G ≤ Real.rpow T eta *
        GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T N G := by
  let a := eta/4
  let epsilon := min a 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hepsilon : 0 < epsilon := lt_min ha (by norm_num)
  have hepsilonOne : epsilon ≤ 1 := min_le_right _ _
  obtain ⟨Cs,Ts,hCs,hTs,hsource⟩ :=
    source_bound_of_exactAFE hAFE hdelta hepsilon hepsilonOne ha
  obtain ⟨L,hL,htransfer⟩ := jutilaSecondMoment_low_anchor_time_squared_certified
  let H : ℝ := 252+252*Classical.choose
    MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  let C := Cs+|H|+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCsC : Cs ≤ C := by dsimp [C]; linarith [abs_nonneg H]
  have hHC : H ≤ C := by dsimp [C]; linarith [le_abs_self H]
  obtain ⟨Ta,hTa⟩ := Filter.eventually_atTop.mp
    (PostA5HighStripSplitReductionFromFourthMoment.eventually_const_mul_polylog_le_rpow
      (5*L*C) 3 a (by positivity) ha)
  refine ⟨max Ts Ta,hTs.trans (le_max_left _ _),?_⟩
  intro T N G hT hN hNT hsep hheight
  have hTsT : Ts ≤ T := (le_max_left _ _).trans hT
  have hTaT : Ta ≤ T := (le_max_right _ _).trans hT
  have hTtwo : 2 ≤ T := hTs.trans hTsT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  by_cases hempty : G=∅
  · subst G
    simp [jutilaSecondMoment,realGramQuadratic,
      GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape]
  have hRone : (1:ℝ) ≤ G.card := by
    exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  let R : ℝ := G.card
  let A := sourceReflectionNumerator29_40 T epsilon
  let P := balancedAnchor N A R
  let F := Real.rpow T a
  let X := R*P+R^2+R*Real.sqrt R*(A/P)+1
  let Y := R*N+R^2+R*Real.sqrt (A*Real.sqrt R)
  let Z := GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T N G
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hA : 0 ≤ A := Real.rpow_nonneg hTpos.le _
  have hPtwo : 2 ≤ P := (le_max_left _ _).trans (le_max_right _ _)
  have hPone : 1 ≤ P := by linarith
  have hNP : N ≤ P := le_max_left _ _
  have hAT : A ≤ T^2 := sourceNumerator_le_square hTone hepsilonOne
  have hRT : R ≤ T^2 := by
    have hh := card_cast_le_two_mul_T hTtwo hdelta.le hsep hheight
    change R ≤ 2*T at hh
    nlinarith
  have hPTsq : P ≤ T^2 := balancedAnchor_le_square hTtwo hNT.le hA hAT hR hRT
  have hFone : 1 ≤ F := Real.one_le_rpow hTone ha.le
  have hF : 0 ≤ F := by linarith
  have hX : 0 ≤ X := by
    dsimp [X]
    exact add_nonneg (add_nonneg (add_nonneg (by positivity) (sq_nonneg R))
      (mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg R)) (div_nonneg hA (by linarith)))) (by norm_num)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hZ : 0 ≤ Z := by
    dsimp [Z,GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape]
    exact add_nonneg (add_nonneg (by positivity)
      (mul_nonneg (Real.rpow_nonneg hR _) (Real.rpow_nonneg hTpos.le _))) (sq_nonneg R)
  have hbound : jutilaSecondMoment P G ≤ C*F*X := by
    by_cases hPT : P<T
    · have hs := hsource T P G hTsT hPone hPT hsep hheight
      have hm := mul_le_mul_of_nonneg_right hCsC (mul_nonneg hF hX)
      change jutilaSecondMoment P G ≤ Cs*F*X at hs
      nlinarith only [hs,hm]
    · have hh := jutilaSecondMoment_real_highRange_le hTone hdelta.le hPone
        (le_of_not_gt hPT) hsep hheight
      have hh' : jutilaSecondMoment P G ≤ H*(R*P) := by simpa [H,R,mul_assoc] using hh
      have hRP : R*P ≤ X := by
        dsimp [X]
        have := mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg R)) (div_nonneg hA (by linarith : 0≤P))
        nlinarith [sq_nonneg R]
      have hm₁ := mul_le_mul_of_nonneg_right hHC (show 0 ≤ R*P by positivity)
      have hm₂ := mul_le_mul_of_nonneg_left hRP hC.le
      have hm₃ := mul_le_mul_of_nonneg_left hFone (show 0 ≤ C*X by positivity)
      nlinarith only [hh',hm₁,hm₂,hm₃]
  have hXY : X ≤ 5*Y := balancedAnchor_shape_le hN hA hRone
  have htrans := htransfer T N P G hTtwo hN hNP hPtwo hPTsq
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hTone
  have hpoly : 5*L*C*(Real.log T)^3 ≤ F := by
    have hp := hTa T hTaT
    have heq : Real.rpow (Real.log T) 3 = (Real.log T)^3 := Real.rpow_natCast _ 3
    simpa only [heq] using hp
  have hS : jutilaSecondMoment N G ≤ F^2*Y := by
    have hm₁ := mul_le_mul_of_nonneg_left hbound (show 0 ≤ L*(Real.log T)^3 by positivity)
    have hm₂ := mul_le_mul_of_nonneg_left hXY (show 0 ≤ L*(Real.log T)^3*(C*F) by positivity)
    have hm₃ := mul_le_mul_of_nonneg_right hpoly (mul_nonneg hF hY)
    nlinarith only [htrans,hm₁,hm₂,hm₃]
  have hsqrtA : Real.sqrt A ≤ F*Real.rpow T (1/2 : ℝ) := by
    have hepsa : epsilon ≤ a := min_le_left _ _
    calc
      _ = Real.rpow T ((1+epsilon)*(1/2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        exact (Real.rpow_mul hTpos.le _ _).symm
      _ ≤ Real.rpow T (a+1/2) :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      _ = _ := Real.rpow_add hTpos _ _
  have hYZ : Y ≤ F*Z := by
    have hroot := root_anchor_eq A R hA hR
    have hm := mul_le_mul_of_nonneg_left hsqrtA (Real.rpow_nonneg hR (5/4 : ℝ))
    change Real.rpow R (5/4 : ℝ)*Real.sqrt A ≤
      Real.rpow R (5/4 : ℝ)*(F*Real.rpow T (1/2 : ℝ)) at hm
    have hlin := mul_le_mul_of_nonneg_left hFone (show 0 ≤ R*N+R^2 by positivity)
    dsimp [Y,Z,GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape]
    change R*N+R^2+R*Real.sqrt (A*Real.sqrt R) ≤
      F*(R*N+Real.rpow R (5/4 : ℝ)*Real.rpow T (1/2 : ℝ)+R^2)
    nlinarith only [hm,hlin,hroot]
  have hFcube : F^3 ≤ Real.rpow T eta := by
    calc
      _ = Real.rpow T (a*3) := by
        calc
          _ = Real.rpow F 3 := (Real.rpow_natCast F 3).symm
          _ = Real.rpow T (a*3) := (Real.rpow_mul hTpos.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hTone (by dsimp [a]; linarith)
  have hm₁ := mul_le_mul_of_nonneg_left hYZ (sq_nonneg F)
  have hm₂ := mul_le_mul_of_nonneg_right hFcube hZ
  nlinarith only [hS,hm₁,hm₂]

end
end GuthMaynardLemma2910OptimizedAnchor

#print axioms GuthMaynardLemma2910OptimizedAnchor.real_below_aperture_of_exactAFE
