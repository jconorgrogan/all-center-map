import GuthMaynardJIterationMediumPairCount
import GuthMaynardJIterationSigmaII
import GuthMaynardSourceDyadicRanges

open scoped BigOperators Real

noncomputable section
namespace GuthMaynardS3LiteralLemma92NonzeroMedium

open GuthMaynardJIteration

/-!
# Nonzero-product medium fibers

The zero product `s = m₁*ell = 0` is a genuine medium contribution when the
frequency cutoff does not dominate the localization radius.  This file keeps
that fiber separate and applies the signed-divisor injection only to the
`ell ≠ 0` slice.  No claim is made that the full medium pair set has uniformly
subpower cardinality.
-/

def nonzeroEllRange (ellRange : Finset ℤ) : Finset ℤ :=
  ellRange.filter (fun ell => ell ≠ 0)

/- Exact split of the literal pair set into the zero-ell and nonzero-ell
   slices.  The zero slice is retained as an explicit term for the later
   narrow-band/L¹ charge. -/
theorem card_sourceMediumLocalizedPairs_le_zeroEll_add_nonzeroEll
    {m1Range ellRange : Finset ℤ} {M3 B xi : ℝ} :
    (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card ≤
      (sourceMediumLocalizedPairs m1Range
        (ellRange.filter (fun ell => ell = 0)) M3 B xi).card +
      (sourceMediumLocalizedPairs m1Range (nonzeroEllRange ellRange)
        M3 B xi).card := by
  have hsplit :
      sourceMediumLocalizedPairs m1Range ellRange M3 B xi =
        sourceMediumLocalizedPairs m1Range
            (ellRange.filter (fun ell => ell = 0)) M3 B xi ∪
          sourceMediumLocalizedPairs m1Range (nonzeroEllRange ellRange)
            M3 B xi := by
    ext p
    by_cases hp : p.2 = 0
    · simp [sourceMediumLocalizedPairs, nonzeroEllRange, hp]
    · simp [sourceMediumLocalizedPairs, nonzeroEllRange, hp]
  rw [hsplit]
  exact Finset.card_union_le _ _

/- The actual product-fiber/divisor bound on the nonzero-ell slice.  The
   product-window count is supplied independently; `hdiv` is the signed
   divisor cap for each nonzero product. -/
theorem card_sourceMediumLocalizedPairs_nonzeroEll_le_window_mul_divisorCap
    {m1Range ellRange : Finset ℤ} {M3 B xi W : ℝ} {D : ℕ}
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hW : ∀ m1 ∈ m1Range, (|(m1 : ℝ)| / M3) * B ≤ W)
    (hdiv : ∀ s : ℤ, s ≠ 0 →
      2 * s.natAbs.divisors.card ≤ D) :
    (sourceMediumLocalizedPairs m1Range (nonzeroEllRange ellRange)
        M3 B xi).card ≤
      (sourceIntegerWindow xi W).card * D := by
  have hwindow : ∀ p ∈ sourceMediumLocalizedPairs m1Range
      (nonzeroEllRange ellRange) M3 B xi,
      |xi - (((p.1 * p.2 : ℤ) : ℝ))| < W := by
    intro p hp
    have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
    simpa only [Int.cast_mul] using
      hpdata.2.2.trans_le (hW p.1 hpdata.1)
  apply card_sourceMediumLocalizedPairs_le_window_mul_fiber hwindow
  intro s hs
  have hs0 : s ≠ 0 := by
    unfold sourceMediumLocalizedProducts at hs
    rw [Finset.mem_image] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
    have hp1 : p.1 ≠ 0 := hm1 p.1 hpdata.1
    have hp2 : p.2 ≠ 0 := by
      exact (Finset.mem_filter.mp hpdata.2.1).2
    exact mul_ne_zero hp1 hp2
  have hfiber := card_sourceMediumProductFiber_le_two_mul_divisors
    (m1Range := m1Range) (ellRange := nonzeroEllRange ellRange)
    (M3 := M3) (B := B) (xi := xi) hs0
  exact hfiber.trans (hdiv s hs0)

/- Subpower pair count for the nonzero-ell slice.  This is the existing
   signed-divisor argument with its zero-product branch removed; consequently
   it does not assume the false global separation `W < a`. -/
theorem exists_sourceMediumLocalizedPairCard_nonzeroEll_subpower
    (m1Range ellRange : Finset ℤ)
    {M3 B a b W Nwindow eta : ℝ}
    (heta : 0 < eta) (hb : 0 ≤ b) (hW0 : 0 ≤ W)
    (hradius : ∀ m1 ∈ m1Range, (|(m1 : ℝ)| / M3) * B ≤ W)
    (hwindowCount : ∀ xi ∈ mediumFrequencyRegion a b,
      ((sourceIntegerWindow xi W).card : ℝ) ≤ Nwindow)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ xi ∈ mediumFrequencyRegion a b,
      ((sourceMediumLocalizedPairs m1Range (nonzeroEllRange ellRange)
        M3 B xi).card : ℝ) ≤
        Nwindow * C * Real.rpow (b + W) eta := by
  obtain ⟨C, hC, hdiv⟩ := card_signed_divisors_subpolynomial eta heta
  refine ⟨C, hC, ?_⟩
  intro xi hxi
  have hlocalWindow : ∀ p ∈
      sourceMediumLocalizedPairs m1Range (nonzeroEllRange ellRange)
        M3 B xi,
      |xi - (((p.1 * p.2 : ℤ) : ℝ))| < W := by
    intro p hp
    have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
    simpa only [Int.cast_mul] using
      hpdata.2.2.trans_le (hradius p.1 hpdata.1)
  have hproducts :
      ((sourceMediumLocalizedProducts m1Range (nonzeroEllRange ellRange)
        M3 B xi).card : ℝ) ≤ Nwindow := by
    have hnat := card_sourceMediumLocalizedProducts_le_integerWindow
      hlocalWindow
    have hreal :
        ((sourceMediumLocalizedProducts m1Range (nonzeroEllRange ellRange)
          M3 B xi).card : ℝ) ≤
          ((sourceIntegerWindow xi W).card : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans (hwindowCount xi hxi)
  have hfiber : ∀ s ∈ sourceMediumLocalizedProducts m1Range
      (nonzeroEllRange ellRange) M3 B xi,
      ((sourceMediumProductFiber m1Range (nonzeroEllRange ellRange)
        M3 B xi s).card : ℝ) ≤ C * Real.rpow s.natAbs eta := by
    intro s hs
    unfold sourceMediumLocalizedProducts at hs
    rw [Finset.mem_image] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
    have hp1 : p.1 ≠ 0 := hm1 p.1 hpdata.1
    have hp2 : p.2 ≠ 0 :=
      (Finset.mem_filter.mp hpdata.2.1).2
    have hprod0 : p.1 * p.2 ≠ 0 := mul_ne_zero hp1 hp2
    let D : Finset ℤ := m1Range.filter fun m1 => m1 ∣ p.1 * p.2
    have hcardFiberNat :
        (sourceMediumProductFiber m1Range (nonzeroEllRange ellRange)
          M3 B xi (p.1 * p.2)).card ≤ D.card :=
      card_sourceMediumProductFiber_le_signedDivisors hprod0
    have hcardFiber :
        ((sourceMediumProductFiber m1Range (nonzeroEllRange ellRange)
          M3 B xi (p.1 * p.2)).card : ℝ) ≤ (D.card : ℝ) := by
      exact_mod_cast hcardFiberNat
    have hD : (D.card : ℝ) ≤
        C * Real.rpow (p.1 * p.2).natAbs eta := hdiv
      (p.1 * p.2) D hprod0 (fun d hd =>
        (Finset.mem_filter.mp hd).2)
    calc
      ((sourceMediumProductFiber m1Range (nonzeroEllRange ellRange)
          M3 B xi (p.1 * p.2)).card : ℝ) ≤ (D.card : ℝ) := hcardFiber
      _ ≤ C * Real.rpow (p.1 * p.2).natAbs eta := hD
  rw [card_sourceMediumLocalizedPairs_eq_sum_fibers]
  push_cast
  calc
    (∑ s ∈ sourceMediumLocalizedProducts m1Range
        (nonzeroEllRange ellRange) M3 B xi,
        ((sourceMediumProductFiber m1Range (nonzeroEllRange ellRange)
          M3 B xi s).card : ℝ)) ≤
      ∑ s ∈ sourceMediumLocalizedProducts m1Range
        (nonzeroEllRange ellRange) M3 B xi,
        C * Real.rpow s.natAbs eta := by
          apply Finset.sum_le_sum
          intro s hs
          exact hfiber s hs
    _ ≤ ∑ _s ∈ sourceMediumLocalizedProducts m1Range
        (nonzeroEllRange ellRange) M3 B xi,
        C * Real.rpow (b + W) eta := by
          apply Finset.sum_le_sum
          intro s hs
          unfold sourceMediumLocalizedProducts at hs
          rw [Finset.mem_image] at hs
          obtain ⟨p, hp, rfl⟩ := hs
          have hlocal := hlocalWindow p hp
          have hprodabs : |(((p.1 * p.2 : ℤ) : ℝ))| ≤ b + W := by
            have htriangle : |(((p.1 * p.2 : ℤ) : ℝ))| ≤
                |xi| + |xi - (((p.1 * p.2 : ℤ) : ℝ))| := by
              calc
                |(((p.1 * p.2 : ℤ) : ℝ))| =
                    |xi - (xi - (((p.1 * p.2 : ℤ) : ℝ)))| := by ring_nf
                _ ≤ _ := abs_sub _ _
            exact htriangle.trans (add_le_add hxi.2 hlocal.le)
          have hrpow : Real.rpow (p.1 * p.2).natAbs eta ≤
              Real.rpow (b + W) eta := by
            apply Real.rpow_le_rpow
            · positivity
            · simpa only [Nat.cast_natAbs, Int.cast_abs] using hprodabs
            · exact heta.le
          exact mul_le_mul_of_nonneg_left hrpow hC.le
    _ = ((sourceMediumLocalizedProducts m1Range
        (nonzeroEllRange ellRange) M3 B xi).card : ℝ) *
        (C * Real.rpow (b + W) eta) := by simp
    _ ≤ Nwindow * (C * Real.rpow (b + W) eta) := by
      exact mul_le_mul_of_nonneg_right hproducts
        (mul_nonneg hC.le (Real.rpow_nonneg (add_nonneg hb hW0) _))
    _ = Nwindow * C * Real.rpow (b + W) eta := by ring

/-!
Uniform dyadic specialization with the divisor constant extracted before all
scale and range data.  The `ell = 0` slice is absent from the counted set.
-/
theorem exists_uniform_sourceMediumLocalizedPairCard_nonzeroEll
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ Ceta : ℝ, 0 < Ceta ∧
      ∀ {T : ℝ} {M1 M3 : ℕ},
        1 ≤ T → 1 ≤ M1 → 1 ≤ M3 →
        (M1 : ℝ) ≤ T → (M3 : ℝ) ≤ T →
        ∀ ellRange : Finset ℤ, ∀ xi ∈
          mediumFrequencyRegion
            (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
            (sourceHighFrequencyCutoff T),
          ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
            (nonzeroEllRange ellRange) (M3 : ℝ) (Real.rpow T eta) xi).card : ℝ) ≤
            Ceta * Real.rpow T (2 * eta) *
              (1 + (M1 : ℝ) / (M3 : ℝ)) := by
  have hetaDiv : 0 < eta / 6 := by linarith
  obtain ⟨Cdiv, hCdiv, hdiv⟩ :=
    card_signed_divisors_subpolynomial (eta / 6) hetaDiv
  let Ceta : ℝ := 4 * Cdiv * Real.rpow 3 (eta / 6)
  refine ⟨Ceta, ?_, ?_⟩
  · dsimp only [Ceta]
    exact mul_pos (mul_pos (by norm_num) hCdiv)
      (Real.rpow_pos_of_pos (by norm_num) _)
  · intro T M1 M3 hT hM1 hM3 hM1T hM3T ellRange xi hxi
    let M1R : ℝ := (M1 : ℝ)
    let M3R : ℝ := (M3 : ℝ)
    let B : ℝ := Real.rpow T eta
    let W : ℝ := 2 * M1R / M3R * B
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hT0 : 0 ≤ T := zero_le_one.trans hT
    have hB0 : 0 ≤ B := by
      dsimp only [B]
      exact Real.rpow_nonneg hT0 eta
    have hB1 : 1 ≤ B := by
      dsimp only [B]
      exact Real.one_le_rpow hT (le_of_lt heta)
    have hW0 : 0 ≤ W := by
      dsimp only [W]
      positivity
    have hM1R : 0 < M1R := by
      dsimp only [M1R]
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
    have hM3R : 0 < M3R := by
      dsimp only [M3R]
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM3)
    have hM1hi : ∀ m1 ∈ sourceSignedDyadicRange M1,
        |(m1 : ℝ)| ≤ 2 * M1R := by
      intro m1 hm1
      simpa only [M1R] using
        (sourceSignedDyadicRange_abs_bounds
          (lt_of_lt_of_le Nat.zero_lt_one hM1) hm1).2
    have hrad : ∀ m1 ∈ sourceSignedDyadicRange M1,
        (|(m1 : ℝ)| / M3R) * B ≤ W := by
      dsimp only [W]
      exact sourceMediumRadius_le_dyadicWindow hM3R hB0 hM1hi
    have hwindow : ∀ xi : ℝ, ∀ _hxi : xi ∈
        mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta M1R M3R)
          (sourceHighFrequencyCutoff T),
        ((sourceIntegerWindow xi W).card : ℝ) ≤
          4 * B * (1 + M1R / M3R) := by
      intro xi _
      have h := card_sourceIntegerWindow_le_sourceScale xi
        (M1 := M1R) (M3 := M3R) (B := B) (c1 := (2 : ℝ))
        (Lwindow := 4 * B)
        hM1R.le hM3R hB0 (by norm_num)
        (by nlinarith [hB1]) (by norm_num)
      convert h using 1 <;> ring
    have hm1 : ∀ m1 ∈ sourceSignedDyadicRange M1, m1 ≠ 0 :=
      fun m1 hm1 => sourceSignedDyadicRange_ne_zero
        (lt_of_lt_of_le Nat.zero_lt_one hM1) hm1
    have hlocalWindow : ∀ p ∈
        sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
          (nonzeroEllRange ellRange) M3R B xi,
        |xi - (((p.1 * p.2 : ℤ) : ℝ))| < W := by
      intro p hp
      have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
      simpa only [Int.cast_mul] using
        hpdata.2.2.trans_le (hrad p.1 hpdata.1)
    have hproducts :
        ((sourceMediumLocalizedProducts (sourceSignedDyadicRange M1)
          (nonzeroEllRange ellRange) M3R B xi).card : ℝ) ≤
          4 * B * (1 + M1R / M3R) := by
      have hnat := card_sourceMediumLocalizedProducts_le_integerWindow
        hlocalWindow
      have hreal :
          ((sourceMediumLocalizedProducts (sourceSignedDyadicRange M1)
            (nonzeroEllRange ellRange) M3R B xi).card : ℝ) ≤
            ((sourceIntegerWindow xi W).card : ℝ) := by
        exact_mod_cast hnat
      exact hreal.trans (hwindow xi hxi)
    have hfiber : ∀ s ∈ sourceMediumLocalizedProducts
        (sourceSignedDyadicRange M1) (nonzeroEllRange ellRange) M3R B xi,
        ((sourceMediumProductFiber (sourceSignedDyadicRange M1)
          (nonzeroEllRange ellRange) M3R B xi s).card : ℝ) ≤
          Cdiv * Real.rpow s.natAbs (eta / 6) := by
      intro s hs
      unfold sourceMediumLocalizedProducts at hs
      rw [Finset.mem_image] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
      have hp1 : p.1 ≠ 0 := hm1 p.1 hpdata.1
      have hp2 : p.2 ≠ 0 :=
        (Finset.mem_filter.mp hpdata.2.1).2
      have hprod0 : p.1 * p.2 ≠ 0 := mul_ne_zero hp1 hp2
      let D : Finset ℤ := (sourceSignedDyadicRange M1).filter
        fun m1 => m1 ∣ p.1 * p.2
      have hcardFiberNat :
          (sourceMediumProductFiber (sourceSignedDyadicRange M1)
            (nonzeroEllRange ellRange) M3R B xi
              (p.1 * p.2)).card ≤ D.card :=
        card_sourceMediumProductFiber_le_signedDivisors hprod0
      have hcardFiber :
          ((sourceMediumProductFiber (sourceSignedDyadicRange M1)
            (nonzeroEllRange ellRange) M3R B xi
              (p.1 * p.2)).card : ℝ) ≤ (D.card : ℝ) := by
        exact_mod_cast hcardFiberNat
      have hD : (D.card : ℝ) ≤
          Cdiv * Real.rpow (p.1 * p.2).natAbs (eta / 6) := hdiv
        (p.1 * p.2) D hprod0 (fun d hd =>
          (Finset.mem_filter.mp hd).2)
      calc
        ((sourceMediumProductFiber (sourceSignedDyadicRange M1)
            (nonzeroEllRange ellRange) M3R B xi
              (p.1 * p.2)).card : ℝ) ≤ (D.card : ℝ) := hcardFiber
        _ ≤ Cdiv * Real.rpow (p.1 * p.2).natAbs (eta / 6) := hD
    have hpairbound :
        ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
          (nonzeroEllRange ellRange) M3R B xi).card : ℝ) ≤
          (4 * B * (1 + M1R / M3R)) * Cdiv *
            Real.rpow (T ^ 6 + W) (eta / 6) := by
      rw [card_sourceMediumLocalizedPairs_eq_sum_fibers]
      push_cast
      calc
        (∑ s ∈ sourceMediumLocalizedProducts
            (sourceSignedDyadicRange M1) (nonzeroEllRange ellRange)
              M3R B xi,
            ((sourceMediumProductFiber (sourceSignedDyadicRange M1)
              (nonzeroEllRange ellRange) M3R B xi s).card : ℝ)) ≤
          ∑ s ∈ sourceMediumLocalizedProducts
            (sourceSignedDyadicRange M1) (nonzeroEllRange ellRange)
              M3R B xi,
            Cdiv * Real.rpow s.natAbs (eta / 6) := by
              apply Finset.sum_le_sum
              intro s hs
              exact hfiber s hs
        _ ≤ ∑ _s ∈ sourceMediumLocalizedProducts
            (sourceSignedDyadicRange M1) (nonzeroEllRange ellRange)
              M3R B xi,
            Cdiv * Real.rpow (T ^ 6 + W) (eta / 6) := by
              apply Finset.sum_le_sum
              intro s hs
              unfold sourceMediumLocalizedProducts at hs
              rw [Finset.mem_image] at hs
              obtain ⟨p, hp, rfl⟩ := hs
              have hlocal := hlocalWindow p hp
              have hxiHigh : |xi| ≤ T ^ 6 := by
                simpa only [sourceHighFrequencyCutoff] using hxi.2
              have hprodabs : |(((p.1 * p.2 : ℤ) : ℝ))| ≤
                  T ^ 6 + W := by
                have htriangle : |(((p.1 * p.2 : ℤ) : ℝ))| ≤
                    |xi| + |xi - (((p.1 * p.2 : ℤ) : ℝ))| := by
                  calc
                    |(((p.1 * p.2 : ℤ) : ℝ))| =
                        |xi - (xi - (((p.1 * p.2 : ℤ) : ℝ)))| := by ring_nf
                    _ ≤ _ := abs_sub _ _
                exact htriangle.trans (add_le_add hxiHigh hlocal.le)
              have hrpow : Real.rpow (p.1 * p.2).natAbs (eta / 6) ≤
                  Real.rpow (T ^ 6 + W) (eta / 6) := by
                apply Real.rpow_le_rpow
                · positivity
                · simpa only [Nat.cast_natAbs, Int.cast_abs] using hprodabs
                · exact hetaDiv.le
              exact mul_le_mul_of_nonneg_left hrpow hCdiv.le
        _ = ((sourceMediumLocalizedProducts (sourceSignedDyadicRange M1)
            (nonzeroEllRange ellRange) M3R B xi).card : ℝ) *
            (Cdiv * Real.rpow (T ^ 6 + W) (eta / 6)) := by simp
        _ ≤ (4 * B * (1 + M1R / M3R)) *
            (Cdiv * Real.rpow (T ^ 6 + W) (eta / 6)) := by
          exact mul_le_mul_of_nonneg_right hproducts
            (mul_nonneg hCdiv.le
              (Real.rpow_nonneg (add_nonneg (by positivity) hW0) _))
        _ = _ := by ring
    have hratioT : M1R / M3R ≤ T := by
      apply (div_le_iff₀ hM3R).2
      have hM3one : (1 : ℝ) ≤ M3R := by
        dsimp only [M3R]
        exact_mod_cast hM3
      have hTM3 : T ≤ T * M3R := by
        calc
          T = T * 1 := by ring
          _ ≤ T * M3R := mul_le_mul_of_nonneg_left
            hM3one hT0
      exact hM1T.trans hTM3
    have hBleT : B ≤ T := by
      dsimp only [B]
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hT heta1)
    have hWle : W ≤ 2 * T ^ 2 := by
      dsimp only [W]
      calc
        2 * M1R / M3R * B = 2 * (M1R / M3R) * B := by ring
        _ ≤ 2 * T * B := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratioT (by norm_num)) hB0
        _ ≤ 2 * T * T := by
          exact mul_le_mul_of_nonneg_left hBleT (by positivity)
        _ = 2 * T ^ 2 := by ring
    have hT26 : T ^ 2 ≤ T ^ 6 := by
      exact pow_le_pow_right₀ hT (by omega)
    have hBW : T ^ 6 + W ≤ 3 * T ^ 6 := by
      nlinarith
    have hrpowBound : Real.rpow (T ^ 6 + W) (eta / 6) ≤
        Real.rpow (3 * T ^ 6) (eta / 6) := by
      exact Real.rpow_le_rpow (by positivity) hBW (by positivity)
    have hTpowR : Real.rpow (T ^ 6) (eta / 6) =
        Real.rpow T eta := by
      have hpow := Real.rpow_mul hT0 (6 : ℝ) (eta / 6)
      norm_num [Real.rpow_natCast] at hpow ⊢
      calc
        Real.rpow (T ^ 6) (eta / 6) =
            Real.rpow T (6 * (eta / 6)) := hpow.symm
        _ = Real.rpow T eta := by congr 1 <;> ring
    have hthreeR : Real.rpow (3 * T ^ 6) (eta / 6) =
        Real.rpow 3 (eta / 6) * Real.rpow T eta := by
      have hmul := Real.mul_rpow (z := eta / 6)
        (by norm_num : 0 ≤ (3 : ℝ)) (by positivity : 0 ≤ T ^ 6)
      calc
        Real.rpow (3 * T ^ 6) (eta / 6) =
            Real.rpow 3 (eta / 6) * Real.rpow (T ^ 6) (eta / 6) := hmul
        _ = Real.rpow 3 (eta / 6) * Real.rpow T eta := by rw [hTpowR]
    have hfinalR : Real.rpow (T ^ 6 + W) (eta / 6) ≤
        Real.rpow 3 (eta / 6) * B := by
      calc
        Real.rpow (T ^ 6 + W) (eta / 6) ≤
            Real.rpow (3 * T ^ 6) (eta / 6) := hrpowBound
        _ = Real.rpow 3 (eta / 6) * Real.rpow T eta := hthreeR
        _ = Real.rpow 3 (eta / 6) * B := by rfl
    calc
      ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
          (nonzeroEllRange ellRange) M3R B xi).card : ℝ) ≤
          (4 * B * (1 + M1R / M3R)) * Cdiv *
            Real.rpow (T ^ 6 + W) (eta / 6) := hpairbound
      _ ≤ (4 * B * (1 + M1R / M3R)) * Cdiv *
            (Real.rpow 3 (eta / 6) * B) := by
          gcongr
      _ = Ceta * Real.rpow T (2 * eta) *
            (1 + (M1 : ℝ) / (M3 : ℝ)) := by
          dsimp only [Ceta, B, M1R, M3R]
          calc
            4 * Real.rpow T eta * (1 + (M1 : ℝ) / (M3 : ℝ)) * Cdiv *
                (Real.rpow 3 (eta / 6) * Real.rpow T eta) =
              4 * Cdiv * Real.rpow 3 (eta / 6) *
                (Real.rpow T eta * Real.rpow T eta) *
                (1 + (M1 : ℝ) / (M3 : ℝ)) := by ring
            _ = _ := by
              have hrpowAdd : Real.rpow T eta * Real.rpow T eta =
                  Real.rpow T (eta + eta) :=
                (Real.rpow_add hTpos eta eta).symm
              rw [hrpowAdd]
              congr 2 <;> ring

end GuthMaynardS3LiteralLemma92NonzeroMedium

#print axioms GuthMaynardS3LiteralLemma92NonzeroMedium.card_sourceMediumLocalizedPairs_le_zeroEll_add_nonzeroEll
#print axioms GuthMaynardS3LiteralLemma92NonzeroMedium.card_sourceMediumLocalizedPairs_nonzeroEll_le_window_mul_divisorCap
#print axioms GuthMaynardS3LiteralLemma92NonzeroMedium.exists_sourceMediumLocalizedPairCard_nonzeroEll_subpower
#print axioms GuthMaynardS3LiteralLemma92NonzeroMedium.exists_uniform_sourceMediumLocalizedPairCard_nonzeroEll
