import GuthMaynardLemma2910Absorption

namespace GuthMaynardLemma2910SourceBound

open GuthMaynardJutilaReflection2941
open GuthMaynardLengthComparison
open GuthMaynardJutilaTransference
open GuthMaynardHeathBrownMajorant
open GuthMaynardLemma2910Absorption
open GuthMaynardLemma2910ConcreteAssembly
open GuthMaynardLemma2910HighRangeFromAFE
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardLemma2910ScalarClosure

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The source moment after direct feedback, finite collar, and the exact
four-square bootstrap have been combined. Only low-anchor optimization remains. -/
theorem source_bound_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon a : ℝ} (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) (ha : 0 < a) :
    ∃ K T₀ : ℝ, 0 < K ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → N < T →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        jutilaSecondMoment N G ≤
          K * Real.rpow T a *
            ((G.card : ℝ)*N + (G.card : ℝ)^2 +
              (G.card : ℝ)*Real.sqrt (G.card : ℝ)*
                reflectedLength29_40 T epsilon N + 1) := by
  obtain ⟨D₁,D₂,Dp,Td,Md,hD₁,hD₂,hDp,hTd,hMd,hdirect⟩ :=
    lemma2910_direct_oneScale_of_exactAFE hAFE hdelta hepsilon
      (by norm_num : (0:ℝ)<1) (by positivity : 0<a/12)
  obtain ⟨B₁,B₂,Bp,Tb,Mb,hB₁,hB₂,hBp,hTb,hMb,hboot⟩ :=
    lemma2910_bootstrap_at_four_square_of_exactAFE hAFE hdelta hepsilon
      (by norm_num : (0:ℝ)<1) (by positivity : 0<a/12)
  obtain ⟨Kt,Tt,hKt,hTt,htarget⟩ :=
    bootstrap_target_subpower_of_exactAFE hAFE hdelta hepsilon hepsilonOne ha
  obtain ⟨Cf,Tf,hCf,hTf,hfinite⟩ :=
    jutilaSecondMoment_le_finitePrefixCollar_of_exactM hAFE hdelta hepsilon
      (by norm_num : (0:ℝ)<1)
  obtain ⟨Ta, hTa⟩ := Filter.eventually_atTop.mp
    (eventually_bootstrapDirectRaw_le D₁ D₂ Dp a 1 hD₁.le hDp.le ha (by norm_num))
  obtain ⟨Tc, hTc⟩ := Filter.eventually_atTop.mp
    (eventually_reflection_powering_coefficient_le_rpow B₁ B₂ Bp a hBp.le ha)
  let M₀ := max Md Mb
  let Q : ℝ := ((Nat.ceil M₀+1 : ℕ) : ℝ)^2
  let K : ℝ := 2*D₁+1 + B₁+4*(Kt+1) + Cf+Cf*Q
  have hQ : 0 ≤ Q := sq_nonneg _
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, max (max (max Td Tb) (max Tt Tf)) (max Ta Tc), hK, ?_, ?_⟩
  · exact hTd.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  intro T N G hT hN hNT hsep hheight
  have hTdT : Td ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hT))
  have hTbT : Tb ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hT))
  have hTtT : Tt ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hT))
  have hTfT : Tf ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hT))
  have hTaT : Ta ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTcT : Tc ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hTone : 1 ≤ T := by linarith [hTd.trans hTdT]
  have hT0 : 0 ≤ T := by linarith
  have hNupper : N ≤ sourceReflectionNumerator29_40 T epsilon :=
    hNT.le.trans (GuthMaynardLemma2910RegimeGeometry.aperture_le_sourceNumerator hTone hepsilon.le)
  let M := reflectedLength29_40 T epsilon N
  let R : ℝ := G.card
  let F := Real.rpow T a
  let X : ℝ := R*N+R^2+R*Real.sqrt R*M+1
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hM : 0 ≤ M := by
    dsimp [M,reflectedLength29_40,sourceReflectionNumerator29_40]
    exact div_nonneg (Real.rpow_nonneg hT0 _) (by linarith)
  have hFs : 1 ≤ F := Real.one_le_rpow hTone ha.le
  have hF : 0 ≤ F := by linarith
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hRX : R*N+1 ≤ X := by
    dsimp [X]
    nlinarith [sq_nonneg R, mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg R)) hM]
  have hR2X : R^2 ≤ X := by
    dsimp [X]
    nlinarith [mul_nonneg hR (show 0 ≤ N by linarith),
      mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg R)) hM]
  have hXX : X ≤ F*X := by nlinarith
  have hMupper : M ≤ T^2 := reflected_target_le_square hTone hepsilonOne hN
  change jutilaSecondMoment N G ≤ K*F*X
  by_cases hlarge : M₀ ≤ M
  · have hMdM : Md ≤ M := (le_max_left _ _).trans hlarge
    have hMbM : Mb ≤ M := (le_max_right _ _).trans hlarge
    have hMtwo : 2 ≤ M := hMd.trans hMdM
    by_cases hdir : 1 ≤ kTwoPrimeLower M N
    · have hd := hdirect T N G hTdT hN hNupper hsep hheight hMdM hdir
      have ha' := hTa T hTaT N M G hN hNT hMtwo hMupper
      have hh : jutilaSecondMoment N G ≤ 2*D₁*(R*N+1)+F*R^2 := hd.trans ha'
      have hKdir : 2*D₁+1 ≤ K := by dsimp [K]; nlinarith [mul_nonneg hCf.le hQ]
      have hm₁ := mul_le_mul_of_nonneg_left hRX hD₁.le
      have hm₂ := mul_le_mul_of_nonneg_left hR2X hF
      have hm₃ := mul_le_mul_of_nonneg_left hXX hD₁.le
      have hm₄ := mul_le_mul_of_nonneg_right hKdir (mul_nonneg hF hX)
      nlinarith only [hh,hm₁,hm₂,hm₃,hm₄]
    · have ht := htarget T N G hTtT hN hNT hsep hheight (lt_of_not_ge hdir)
      have hb := hboot T N (Kt*F*(R*(4*M^2)+R^2+1)) G
        hTbT hN hNupper hsep hheight hMbM ht
      have hc := hTc T hTcT N M hN hNT hMtwo hMupper
      have hlog : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
      have hs := bootstrap_root_le hR hM hF hKt.le
        (show 0 ≤ B₁*B₂*(Real.log M)^5 by positivity)
        (show 0 ≤ Bp*Real.rpow (4*M^2) (a/12) from
          mul_nonneg hBp.le (Real.rpow_nonneg (by positivity) _)) hc
      have he := mul_le_mul_of_nonneg_left (negative_power_le_one hTone (by norm_num : (0:ℝ)≤1)) hB₁.le
      have hh : jutilaSecondMoment N G ≤ B₁*(R*N+1)+
          (Kt+1)*F*(2*R*Real.sqrt R*M+R^2+R) := by
        have hb' : jutilaSecondMoment N G ≤ B₁*R*N+B₁*Real.rpow T (-1)+
          (B₁*B₂*(Real.log M)^5)*Real.sqrt
            ((Bp*Real.rpow (4*M^2) (a/12))*R^2*(Kt*F*(R*(4*M^2)+R^2+1))) := by
          simpa only [M,R,mul_assoc,mul_left_comm,mul_comm] using hb
        linarith
      have hRsmall : R ≤ R^2+1 := by nlinarith [sq_nonneg (R-1)]
      have hsX : 2*R*Real.sqrt R*M+R^2+R ≤ 4*X := by
        dsimp [X]
        nlinarith [mul_nonneg hR (show 0 ≤ N by linarith),
          mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg R)) hM]
      have hm₁ := mul_le_mul_of_nonneg_left hRX hB₁.le
      have hm₂ := mul_le_mul_of_nonneg_left hXX hB₁.le
      have hm₃ := mul_le_mul_of_nonneg_left hsX (show 0 ≤ (Kt+1)*F by positivity)
      have hKb : B₁+4*(Kt+1) ≤ K := by dsimp [K]; nlinarith [mul_nonneg hCf.le hQ]
      have hm₄ := mul_le_mul_of_nonneg_right hKb (mul_nonneg hF hX)
      nlinarith only [hh,hm₁,hm₂,hm₃,hm₄]
  · have hf := hfinite T N G hTfT hN hNupper hsep hheight
    have hn := card_natRealIoc_zero_le_ceil_add_one (lt_of_not_ge hlarge).le
    have hnR : ((natRealIoc 0 M).card : ℝ) ≤ (Nat.ceil M₀+1 : ℕ) := by exact_mod_cast hn
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ((natRealIoc 0 M).card : ℝ)) hnR 2
    have he := mul_le_mul_of_nonneg_left (negative_power_le_one hTone (by norm_num : (0:ℝ)≤1)) hCf.le
    have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ Cf*R^2 by positivity)
    have hh : jutilaSecondMoment N G ≤ Cf*(R*N+1)+Cf*Q*R^2 := by
      dsimp [M,R,Q] at hm ⊢
      nlinarith only [hf,he,hm]
    have hm₁ := mul_le_mul_of_nonneg_left hRX hCf.le
    have hm₂ := mul_le_mul_of_nonneg_left hR2X (show 0 ≤ Cf*Q by positivity)
    have hKf : Cf+Cf*Q ≤ K := by dsimp [K]; linarith
    have hm₃ := mul_le_mul_of_nonneg_right hKf hX
    have hm₄ := mul_le_mul_of_nonneg_left hXX hK.le
    nlinarith only [hh,hm₁,hm₂,hm₃,hm₄]

end
end GuthMaynardLemma2910SourceBound

#print axioms GuthMaynardLemma2910SourceBound.source_bound_of_exactAFE
