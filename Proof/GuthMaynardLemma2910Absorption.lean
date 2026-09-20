import GuthMaynardLemma2910BootstrapTarget
import PostA5HighStripSplitReductionFromFourthMoment

namespace GuthMaynardLemma2910Absorption

open GuthMaynardJutilaReflection2941
open GuthMaynardLengthComparison

noncomputable section

theorem sourceNumerator_le_square
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : epsilon ≤ 1) :
    sourceReflectionNumerator29_40 T epsilon ≤ T ^ 2 := by
  unfold sourceReflectionNumerator29_40
  calc
    Real.rpow T (1 + epsilon) ≤ Real.rpow T 2 :=
      Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    _ = T ^ 2 := Real.rpow_natCast T 2

theorem reflected_target_le_square
    {T epsilon P : ℝ} (hT : 1 ≤ T) (hepsilon : epsilon ≤ 1)
    (hP : 1 ≤ P) :
    sourceReflectionNumerator29_40 T epsilon / P ≤ T ^ 2 := by
  have hA0 : 0 ≤ sourceReflectionNumerator29_40 T epsilon := by
    unfold sourceReflectionNumerator29_40
    exact Real.rpow_nonneg (by linarith) _
  calc
    sourceReflectionNumerator29_40 T epsilon / P ≤
        sourceReflectionNumerator29_40 T epsilon := by
      exact div_le_self hA0 hP
    _ ≤ T ^ 2 := sourceNumerator_le_square hT hepsilon

/-- The literal fixed logarithmic loss in the direct target branch is at
most a thirteenth power of `log T`, with an explicit harmless constant. -/
theorem direct_log_product_le
    {T P L : ℝ} (hT : Real.exp 1 ≤ T) (hP : 1 ≤ P) (hPT : P < T)
    (hL : 2 ≤ L) (hLT : L ≤ T ^ 2) :
    (Real.log L) ^ (10 : ℕ) * (1 + Real.log P) ^ (3 : ℕ) ≤
      (2 : ℝ) ^ (13 : ℕ) * (Real.log T) ^ (13 : ℕ) := by
  have hTone : 1 ≤ T := by have := Real.exp_one_gt_d9; linarith
  have hlogT : 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT
    simpa using this
  have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg hP
  have hlogPT : Real.log P ≤ Real.log T :=
    Real.log_le_log (by linarith) hPT.le
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hTpos : 0 < T := by linarith
  have hlogL : Real.log L ≤ 2 * Real.log T := by
    have hm := Real.log_le_log (by linarith : 0 < L) hLT
    rw [Real.log_pow] at hm
    norm_num at hm
    linarith
  have hPtwo : 1 + Real.log P ≤ 2 * Real.log T := by linarith
  have hten := pow_le_pow_left₀ hlogL0 hlogL 10
  have hthree := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log P) hPtwo 3
  calc
    (Real.log L) ^ (10 : ℕ) * (1 + Real.log P) ^ (3 : ℕ) ≤
        (2 * Real.log T) ^ (10 : ℕ) *
          (2 * Real.log T) ^ (3 : ℕ) :=
      mul_le_mul hten hthree (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (13 : ℕ) * (Real.log T) ^ (13 : ℕ) := by ring


/-- Uniform absorption of the literal direct-feedback loss. Both length
variables remain quantified after the threshold is selected. -/
theorem eventually_direct_coefficient_le_rpow
    (C₁ C₂ Cp a : ℝ) (hCp : 0 ≤ Cp) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ P L : ℝ,
      1 ≤ P → P < T → 2 ≤ L → L ≤ T^2 →
      (C₁ * C₂ * (Real.log L)^5)^2 *
          (Cp * (1 + Real.log P)^3 * Real.rpow (4*L^2) (a/12)) ≤
        Real.rpow T a := by
  have habs := PostA5HighStripSplitReductionFromFourthMoment.eventually_const_mul_polylog_le_rpow
    ((C₁*C₂)^2 * Cp * 2^13) 13 (a/2) (by positivity) (by positivity)
  filter_upwards [habs, Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_ge_atTop (2 : ℝ)] with T hpoly hTexp hTtwo
  intro P L hP hPT hL hLT
  have hTpos : 0 < T := by linarith
  have hlog := direct_log_product_le hTexp hP hPT hL hLT
  have hbase : 4*L^2 ≤ T^6 := by
    have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ L) hLT 2
    have hfour : (4:ℝ) ≤ T^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hfour (sq_nonneg (T^2))
    nlinarith [sq_nonneg (T^2)]
  have hp : Real.rpow (4*L^2) (a/12) ≤ Real.rpow T (a/2) := by
    calc
      _ ≤ Real.rpow (T^6) (a/12) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = Real.rpow T (a/2) := by
        calc
          _ = Real.rpow (Real.rpow T 6) (a/12) :=
            congrArg (fun x : ℝ => Real.rpow x (a/12)) (Real.rpow_natCast T 6).symm
          _ = Real.rpow T ((6:ℝ)*(a/12)) := (Real.rpow_mul hTpos.le _ _).symm
          _ = Real.rpow T (a/2) := by congr 1; ring
  have hpoly' : (C₁*C₂)^2 * Cp * (2^13 * (Real.log T)^13) ≤
      Real.rpow T (a/2) := by
    have heq : Real.rpow (Real.log T) 13 = (Real.log T)^13 := Real.rpow_natCast _ 13
    rw [heq] at hpoly
    simpa only [mul_assoc] using hpoly
  have hfirst : (C₁*C₂)^2 * Cp *
      ((Real.log L)^10 * (1+Real.log P)^3) ≤ Real.rpow T (a/2) :=
    (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hpoly'
  calc
    _ = ((C₁*C₂)^2 * Cp * ((Real.log L)^10 * (1+Real.log P)^3)) *
        Real.rpow (4*L^2) (a/12) := by ring
    _ ≤ Real.rpow T (a/2) * Real.rpow T (a/2) :=
      mul_le_mul hfirst hp (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hTpos.le _)
    _ = Real.rpow T a := by
      calc
        _ = Real.rpow T (a/2+a/2) := (Real.rpow_add hTpos _ _).symm
        _ = Real.rpow T a := by congr 1; ring

/-- A decaying AFE remainder is uniformly bounded by one. -/
theorem negative_power_le_one {T B : ℝ} (hT : 1 ≤ T) (hB : 0 ≤ B) :
    Real.rpow T (-B) ≤ 1 := by
  calc
    _ ≤ Real.rpow T 0 := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    _ = 1 := Real.rpow_zero T

/-- The direct target estimate after all logarithmic and multiplicity
losses have been absorbed into the prescribed subpower. -/
theorem eventually_bootstrapDirectRaw_le
    (C₁ C₂ Cp a B : ℝ) (hC₁ : 0 ≤ C₁) (hCp : 0 ≤ Cp)
    (ha : 0 < a) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (P L : ℝ) (G : Finset ℝ),
      1 ≤ P → P < T → 2 ≤ L → L ≤ T^2 →
      GuthMaynardLemma2910BootstrapTarget.bootstrapDirectRaw
          C₁ C₂ Cp T P L (a/12) B G ≤
        2*C₁*((G.card : ℝ)*P + 1) + Real.rpow T a * (G.card : ℝ)^2 := by
  filter_upwards [eventually_direct_coefficient_le_rpow C₁ C₂ Cp a hCp ha,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hcoeff hT
  intro P L G hP hPT hL hLT
  have hc := mul_le_mul_of_nonneg_right (hcoeff P L hP hPT hL hLT)
    (sq_nonneg (G.card : ℝ))
  have he := mul_le_mul_of_nonneg_left (negative_power_le_one hT hB) hC₁
  unfold GuthMaynardLemma2910BootstrapTarget.bootstrapDirectRaw
  nlinarith [hc]



theorem eventually_reflection_powering_coefficient_le_rpow
    (C₁ C₂ Cp a : ℝ) (hCp : 0 ≤ Cp) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ N M : ℝ,
      1 ≤ N → N < T → 2 ≤ M → M ≤ T^2 →
      (C₁*C₂*(Real.log M)^5)^2 * (Cp*Real.rpow (4*M^2) (a/12)) ≤
        Real.rpow T a := by
  filter_upwards [eventually_direct_coefficient_le_rpow C₁ C₂ Cp a hCp ha]
    with T hT
  intro N M hN hNT hM hMT
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogPow : (1:ℝ) ≤ (1+Real.log N)^3 := by nlinarith [sq_nonneg (Real.log N)]
  have hscale := mul_le_mul_of_nonneg_left hlogPow
    (show 0 ≤ (C₁*C₂*(Real.log M)^5)^2 *
      (Cp*Real.rpow (4*M^2) (a/12)) by
      exact mul_nonneg (sq_nonneg _) (mul_nonneg hCp (Real.rpow_nonneg (by positivity) _)))
  calc
    _ ≤ (C₁*C₂*(Real.log M)^5)^2 *
        (Cp*(1+Real.log N)^3*Real.rpow (4*M^2) (a/12)) := by
      nlinarith only [hscale]
    _ ≤ Real.rpow T a := hT N M hN hNT hM hMT

set_option maxHeartbeats 800000 in
/-- All three legal bootstrap-target cases share one uniform subpower
bound. The only analytic hypothesis is the exact-reflected-length AFE. -/
theorem bootstrap_target_subpower_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon a : ℝ} (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) (ha : 0 < a) :
    ∃ K T₀ : ℝ, 0 < K ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → N < T →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let M := reflectedLength29_40 T epsilon N
        let P := 4 * M^2
        GuthMaynardJutilaLemma29NineKTwo.kTwoPrimeLower M N < 1 →
        jutilaSecondMoment P G ≤
          K * Real.rpow T a * ((G.card : ℝ)*P + (G.card : ℝ)^2 + 1) := by
  obtain ⟨C₁,C₂,Cp,Cf,Tb,M₀,hC₁,hC₂,hCp,hCf,hTb,hM₀,hraw⟩ :=
    GuthMaynardLemma2910BootstrapTarget.bootstrap_target_uniform_raw_of_exactAFE
      hAFE hdelta hepsilon (by norm_num : (0:ℝ)<1) (by positivity : 0<a/12)
  obtain ⟨Ta, hTa⟩ := Filter.eventually_atTop.mp
    (eventually_bootstrapDirectRaw_le C₁ C₂ Cp a 1 hC₁.le hCp.le ha (by norm_num))
  let H : ℝ := 252 + 252 * Classical.choose
    MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  let Q : ℝ := ((Nat.ceil M₀ + 1 : ℕ) : ℝ)^2
  let K : ℝ := 2*C₁ + Cf + Cf*Q + |H| + 1
  have hQ : 0 ≤ Q := sq_nonneg _
  have hK : 0 < K := by dsimp [K]; nlinarith [abs_nonneg H, mul_nonneg hCf.le hQ]
  refine ⟨K, max Tb Ta, hK, hTb.trans (le_max_left _ _), ?_⟩
  intro T N G hT hN hNT hsep hheight
  dsimp only
  intro hfail
  have hTbT : Tb ≤ T := (le_max_left _ _).trans hT
  have hTaT : Ta ≤ T := (le_max_right _ _).trans hT
  have hTone : 1 ≤ T := by linarith [hTb.trans hTbT]
  let M := reflectedLength29_40 T epsilon N
  let P := 4*M^2
  let R : ℝ := G.card
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hPow : 1 ≤ Real.rpow T a := Real.one_le_rpow hTone ha.le
  have hshape : 0 ≤ R*P+R^2+1 := by positivity
  have hKpow : K*(R*P+R^2+1) ≤ K*Real.rpow T a*(R*P+R^2+1) := by
    have hc : K ≤ K*Real.rpow T a := by nlinarith
    exact mul_le_mul_of_nonneg_right hc hshape
  have hK₁ : 2*C₁ ≤ K := by dsimp [K]; nlinarith [abs_nonneg H, mul_nonneg hCf.le hQ]
  have hKf : Cf ≤ K := by dsimp [K]; nlinarith [abs_nonneg H, mul_nonneg hCf.le hQ]
  have hKQ : Cf*Q ≤ K := by dsimp [K]; nlinarith [abs_nonneg H, mul_nonneg hCf.le hQ]
  have hKH : H ≤ K := by
    have := le_abs_self H
    dsimp [K]
    nlinarith [abs_nonneg H, mul_nonneg hCf.le hQ]
  have hKone : 1 ≤ K := by dsimp [K]; nlinarith [abs_nonneg H, mul_nonneg hCf.le hQ]
  rcases hraw T N G hTbT hN hNT hsep hheight hfail with hh | hd | hf
  · have hh' : jutilaSecondMoment P G ≤ H*(R*P) := by
      simpa [GuthMaynardLemma2910BootstrapTarget.bootstrapHighRaw, H, P, M, R,
        mul_assoc] using hh.2
    apply hh'.trans
    apply le_trans _ hKpow
    have hc := mul_le_mul_of_nonneg_right hKH (mul_nonneg hR hP)
    nlinarith [mul_nonneg hK.le (sq_nonneg R)]
  · obtain ⟨hPT,hL,hd⟩ := hd
    have hLtwo : 2 ≤ sourceReflectionNumerator29_40 T epsilon/P := hM₀.trans hL
    have hPone : 1 ≤ P := by
      have hg := GuthMaynardLemma2910RegimeGeometry.lt_four_square_of_primeScale_lt_one
        (M := M) (N := N)
      have hMpos : 0 < M := by
        dsimp [M, reflectedLength29_40, sourceReflectionNumerator29_40]
        exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)
      exact hN.trans (hg hMpos hfail).le
    have hLsq := reflected_target_le_square hTone hepsilonOne hPone
    have habs := hTa T hTaT P (sourceReflectionNumerator29_40 T epsilon/P) G
      hPone hPT hLtwo hLsq
    apply (hd.trans habs).trans
    have hc₁ := mul_le_mul_of_nonneg_right hK₁ (by positivity : 0 ≤ R*P+1)
    have hc₂ := mul_le_mul_of_nonneg_right hKone (sq_nonneg R)
    have hp₁ := mul_le_mul_of_nonneg_left hPow
      (by positivity : 0 ≤ K*(R*P+1))
    have hp₂ := mul_le_mul_of_nonneg_left hc₂ (Real.rpow_nonneg (by linarith : 0 ≤ T) a)
    change 2*C₁*(R*P+1)+Real.rpow T a*R^2 ≤ _
    nlinarith
  · obtain ⟨_,_,hf⟩ := hf
    have he := negative_power_le_one hTone (by norm_num : (0:ℝ)≤1)
    have hf' : jutilaSecondMoment P G ≤ Cf*(R*P)+Cf*Q*R^2+Cf := by
      unfold GuthMaynardLemma2910BootstrapTarget.bootstrapFiniteRaw at hf
      have he' := mul_le_mul_of_nonneg_left he hCf.le
      dsimp [P, M, R, Q] at *
      nlinarith
    apply hf'.trans
    apply le_trans _ hKpow
    have hc₁ := mul_le_mul_of_nonneg_right hKf (mul_nonneg hR hP)
    have hc₂ := mul_le_mul_of_nonneg_right hKQ (sq_nonneg R)
    nlinarith

end
end GuthMaynardLemma2910Absorption

#print axioms GuthMaynardLemma2910Absorption.sourceNumerator_le_square
#print axioms GuthMaynardLemma2910Absorption.reflected_target_le_square
#print axioms GuthMaynardLemma2910Absorption.direct_log_product_le

#print axioms GuthMaynardLemma2910Absorption.eventually_direct_coefficient_le_rpow
#print axioms GuthMaynardLemma2910Absorption.bootstrap_target_subpower_of_exactAFE
