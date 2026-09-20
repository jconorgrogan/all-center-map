import GuthMaynardEnergy115Actual
import GuthMaynardEnergy116UniformFourth
import GuthMaynardEnergy119ReducedHolder
import GuthMaynardEnergy119GCDCutoff
import GuthMaynardEnergy119ScaleAlgebra
import GuthMaynardEnergy119WeightedFloor

open scoped BigOperators Real
open CGLProofDAG GuthMaynardRatioKernelIdentity GuthMaynardLemma118
open GuthMaynardHeathBrownInterface GuthMaynardS3LiteralLemma83Energy
open GuthMaynardHeathBrownMajorant
open GuthMaynardEnergy115Actual GuthMaynardEnergy116UniformFourth
open GuthMaynardEnergy119ReducedHolder GuthMaynardEnergy119GCDCutoff
open GuthMaynardEnergy119ScaleAlgebra GuthMaynardEnergy119FloorCutoff
open GuthMaynardEnergy119WeightedFloor
open GuthMaynardEnergy118GCD
open GuthMaynardEnergy119RoundedRange

noncomputable section
set_option maxHeartbeats 1800000
namespace GuthMaynardEnergy119Factored

/-- Literal high-gcd cubic tail bound after exact gcd reindexing and a
second/fourth moment Holder step. -/
theorem high_gcd_factored_cubic {eta : ℝ} (heta : 0 < eta) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (N : ℕ) (W : Finset ℝ) (T : ℝ),
        1 ≤ N → T0 ≤ T → Real.rpow T (3/4 : ℝ) ≤ N →
        OneSeparated W → ContainedInIntervalOfLength W T →
        (∑ p ∈ (dyadicPairs N).filter
            (fun p => (N : ℝ)^2/T < (p.1.gcd p.2 : ℝ)),
          ratioMomentTermPow 3 W p) ≤
          C * Real.rpow T eta *
            (1 + Real.log (max 1 (2 * (N : ℝ)))) *
            Real.sqrt ((W.card : ℝ) * T + (W.card : ℝ)^2 * (N : ℝ) +
              Real.rpow (W.card : ℝ) (5/4 : ℝ) * Real.rpow T (1/2 : ℝ) * (N : ℝ)) *
            Real.sqrt ((N : ℝ) * (W.card : ℝ)^4 +
              (sourceApproximateAdditiveEnergy W : ℝ) * T +
              Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow T (1/2 : ℝ) * (N : ℝ)) := by
  obtain ⟨C2, T2, hC2, hT2, hsecond⟩ :=
    discrete_second_moment (eta := eta / 2) (by linarith)
  obtain ⟨C4, T4, hC4, hT4, hfourth⟩ :=
    GuthMaynardEnergy116UniformFourth.discrete_fourth_moment
      (eps := eta / 2) (by linarith)
  let Cbig : ℝ := C2 + C4 + 1
  let T0 : ℝ := max 2 (max T2 T4)
  have hCbig : 0 < Cbig := by
    dsimp [Cbig]
    positivity
  refine ⟨8 * Cbig, T0, ?_, ?_, ?_⟩
  · positivity
  · exact le_max_left _ _
  intro N W T hN hT0 hNT hsep hcontained
  have hT1 : 1 ≤ T := by
    have hh : (2 : ℝ) ≤ T := (le_max_left 2 (max T2 T4)).trans hT0
    linarith
  have hTnon : 0 ≤ T := by linarith
  have hNreal : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hscale : T ≤ (N : ℝ)^2 := by
    exact square_scale_of_three_quarters hT1 hNT
  have hT2le : T2 ≤ T := by
    exact (le_max_left T2 T4).trans ((le_max_right 2 (max T2 T4)).trans hT0)
  have hT4le : T4 ≤ T := by
    exact (le_max_right T2 T4).trans ((le_max_right 2 (max T2 T4)).trans hT0)
  let D : ℕ := Nat.floor ((N : ℝ)^2 / T)
  have hD := floor_cutoff_bounds (N := (N : ℝ)) (T := T)
    (by linarith) hscale
  have hsplit := dyadic_high_gcd_eq_sum_reduced 3 W N D
  have hper : ∀ d ∈ Finset.Icc (D+1) (2*N),
      (∑ p ∈ reducedPairs N d, ratioMomentTermPow 3 W p) ≤
        4 * Cbig * Real.rpow T eta *
          (Real.sqrt ((W.card : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
              ((W.card : ℝ)^2 + Real.rpow (W.card : ℝ) (5/4 : ℝ) *
                Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ)) *
            Real.sqrt ((sourceApproximateAdditiveEnergy W : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
              ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ))) := by
    intro d hd
    have hdl : 1 ≤ d := by
      have := (Finset.mem_Icc.mp hd).1
      dsimp [D] at this
      omega
    have hdu : d ≤ 2*N := (Finset.mem_Icc.mp hd).2
    obtain ⟨hMone, hMd, hcover⟩ :=
      ceil_dyadic_range_cover hN hdl hdu
    let M : ℕ := Nat.ceil ((N : ℝ)/(d : ℝ))
    have hMdef : M = Nat.ceil ((N : ℝ)/(d : ℝ)) := rfl
    have h2 := hsecond T M W hT2le hMone hsep hcontained
    have h4 := hfourth T M W hT4le hMone hsep hcontained
    have hshape2 := rounded_heathBrownShape_le T W hN hdl hdu hTnon
    let R : ℝ := (W.card : ℝ)
    let E : ℝ := (sourceApproximateAdditiveEnergy W : ℝ)
    have hshape4 :
        GuthMaynardEnergy116UniformFourth.fourthMomentShape T M W ≤
          4 * (E * (N : ℝ)^2/(d : ℝ)^2 +
            (R^4 + Real.rpow E (3/4 : ℝ) * R * Real.rpow T (1/2)) *
              (N : ℝ)/(d : ℝ)) := by
      have hh := quadratic_shape_scale
        (a := E)
        (b := R^4 + Real.rpow E (3/4 : ℝ) * R * Real.rpow T (1/2 : ℝ))
        (by dsimp [E]; positivity)
        (by dsimp [E, R]; positivity)
        (by positivity) hNreal
        (by exact_mod_cast (show 0 < d by omega)) hMd
      unfold GuthMaynardEnergy116UniformFourth.fourthMomentShape
      calc
        _ = E * (M : ℝ)^2 +
            (R^4 + Real.rpow E (3/4 : ℝ) * R * Real.rpow T (1/2 : ℝ)) * (M : ℝ) := by ring
        _ ≤ _ := hh
    have hpow : Real.rpow T (eta/2) ≤ Real.rpow T eta := by
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    let Xd : ℝ := (W.card : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
      ((W.card : ℝ)^2 + Real.rpow (W.card : ℝ) (5/4 : ℝ) *
        Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ)
    let Yd : ℝ := (sourceApproximateAdditiveEnergy W : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
      ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
        (W.card : ℝ) * Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ)
    have hXnon : 0 ≤ Xd := by
      dsimp [Xd]
      positivity
    have hYnon : 0 ≤ Yd := by
      dsimp [Yd]
      positivity
    have hC2bound : C2 * Real.rpow T (eta/2) *
        heathBrownShape T M W ≤ 4 * Cbig * Real.rpow T eta * Xd := by
      have hc2 : C2 ≤ Cbig := by dsimp [Cbig]; linarith
      have hs2 : heathBrownShape T M W ≤ 4 * Xd := by
        dsimp [Xd]
        exact hshape2
      have ht2 : C2 * Real.rpow T (eta/2) ≤ Cbig * Real.rpow T eta := by
        have hc := mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hTnon (eta/2))
        have hp := mul_le_mul_of_nonneg_left hpow hCbig.le
        exact hc.trans hp
      calc
        C2 * Real.rpow T (eta/2) * heathBrownShape T M W ≤
            C2 * Real.rpow T (eta/2) * (4 * Xd) :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg hC2.le (Real.rpow_nonneg hTnon _))
        _ ≤ Cbig * Real.rpow T eta * (4 * Xd) :=
          mul_le_mul_of_nonneg_right ht2 (by positivity)
        _ = 4 * Cbig * Real.rpow T eta * Xd := by ring
    have hC4bound : C4 * Real.rpow T (eta/2) *
        GuthMaynardEnergy116UniformFourth.fourthMomentShape T M W ≤
          4 * Cbig * Real.rpow T eta * Yd := by
      have hc4 : C4 ≤ Cbig := by dsimp [Cbig]; linarith
      have hs4 := hshape4
      have ht4 : C4 * Real.rpow T (eta/2) ≤ Cbig * Real.rpow T eta := by
        have hc := mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hTnon (eta/2))
        have hp := mul_le_mul_of_nonneg_left hpow hCbig.le
        exact hc.trans hp
      calc
        C4 * Real.rpow T (eta/2) * GuthMaynardEnergy116UniformFourth.fourthMomentShape T M W ≤
            C4 * Real.rpow T (eta/2) * (4 * Yd) :=
          mul_le_mul_of_nonneg_left hs4 (mul_nonneg hC4.le (Real.rpow_nonneg hTnon _))
        _ ≤ Cbig * Real.rpow T eta * (4 * Yd) :=
          mul_le_mul_of_nonneg_right ht4 (by positivity)
        _ = 4 * Cbig * Real.rpow T eta * Yd := by ring
    have h2bound : ratioKernelMoment 2 M W ≤ 4 * Cbig * Real.rpow T eta * Xd :=
      h2.trans hC2bound
    have h4bound : ratioKernelMoment 4 M W ≤ 4 * Cbig * Real.rpow T eta * Yd :=
      h4.trans hC4bound
    have hholder := reduced_cubic_le_rounded_geometricMean W hN hdl hdu
    have hprod := mul_le_mul (Real.sqrt_le_sqrt h2bound)
      (Real.sqrt_le_sqrt h4bound) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hQ : 0 ≤ 4 * Cbig * Real.rpow T eta := by
      exact mul_nonneg (mul_nonneg (by norm_num) hCbig.le)
        (Real.rpow_nonneg hTnon _)
    have hprod' :
        Real.sqrt (ratioKernelMoment 2 M W) *
            Real.sqrt (ratioKernelMoment 4 M W) ≤
          4 * Cbig * Real.rpow T eta * Real.sqrt Xd * Real.sqrt Yd := by
      calc
        _ ≤ Real.sqrt (4*Cbig*Real.rpow T eta*Xd) *
            Real.sqrt (4*Cbig*Real.rpow T eta*Yd) := hprod
        _ = _ := by
          rw [Real.sqrt_mul hQ, Real.sqrt_mul hQ]
          calc
            _ = (Real.sqrt (4*Cbig*Real.rpow T eta))^2 *
                Real.sqrt Xd * Real.sqrt Yd := by ring
            _ = _ := by rw [Real.sq_sqrt hQ]
    calc
      _ ≤ Real.sqrt (ratioKernelMoment 2 M W) *
          Real.sqrt (ratioKernelMoment 4 M W) := hholder
      _ ≤ _ := by simpa [Xd, Yd, mul_assoc] using hprod'
  have htail :
      (∑ d ∈ Finset.Icc (D+1) (2*N),
        ∑ p ∈ reducedPairs N d, ratioMomentTermPow 3 W p) ≤
        4 * Cbig * Real.rpow T eta *
          ∑ d ∈ Finset.Icc (D+1) (2*N),
            (Real.sqrt ((W.card : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
              ((W.card : ℝ)^2 + Real.rpow (W.card : ℝ) (5/4 : ℝ) *
                Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ)) *
            Real.sqrt ((sourceApproximateAdditiveEnergy W : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
              ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ))) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc (D+1) (2*N),
          4 * Cbig * Real.rpow T eta *
            (Real.sqrt ((W.card : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
              ((W.card : ℝ)^2 + Real.rpow (W.card : ℝ) (5/4 : ℝ) *
                Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ)) *
            Real.sqrt ((sourceApproximateAdditiveEnergy W : ℝ) * (N : ℝ)^2/(d : ℝ)^2 +
              ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow T (1/2 : ℝ)) * (N : ℝ)/(d : ℝ))) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hper d hd
      _ = _ := by simp only [Finset.mul_sum]
  have hweighted := weighted_floor_sum_le
    (N := (N : ℝ)) (T := T) (R := (W.card : ℝ))
    (E := (sourceApproximateAdditiveEnergy W : ℝ))
    (B := ((W.card : ℝ)^2 + Real.rpow (W.card : ℝ) (5/4 : ℝ) *
      Real.rpow T (1/2 : ℝ)) * (N : ℝ))
    (F := ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
      (W.card : ℝ) * Real.rpow T (1/2 : ℝ)) * (N : ℝ))
    (2*N) (by linarith) hscale
    (by positivity : 0 ≤ (W.card : ℝ))
    (by positivity : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ))
    (by
      have hR0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
      have hTpow : 0 ≤ Real.rpow T (1/2 : ℝ) := Real.rpow_nonneg hTnon _
      exact mul_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg
        (Real.rpow_nonneg hR0 _) hTpow)) (Nat.cast_nonneg _))
    (by
      have hE0 : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ) := by positivity
      have hR0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
      have hTpow : 0 ≤ Real.rpow T (1/2 : ℝ) := Real.rpow_nonneg hTnon _
      have hEpow : 0 ≤ Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) :=
        Real.rpow_nonneg hE0 _
      exact mul_nonneg (add_nonneg (pow_nonneg hR0 4)
        (mul_nonneg (mul_nonneg hEpow hR0) hTpow)) (Nat.cast_nonneg _))
  have htail2 := htail.trans (mul_le_mul_of_nonneg_left hweighted
    (mul_nonneg (mul_nonneg (by norm_num) hCbig.le) (Real.rpow_nonneg hTnon _)))
  have hfilter :
      (dyadicPairs N).filter (fun p => (N : ℝ)^2/T < (p.1.gcd p.2 : ℝ)) =
        (dyadicPairs N).filter (fun p => D < p.1.gcd p.2) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hx⟩
      have hDle : (D : ℝ) ≤ (N : ℝ)^2/T := by
        dsimp [D]
        exact Nat.floor_le (by positivity)
      have hlt : (D : ℝ) < (p.1.gcd p.2 : ℝ) := hDle.trans_lt hx
      exact ⟨hp, by exact_mod_cast hlt⟩
    · rintro ⟨hp, hdg⟩
      have hlt : (N : ℝ)^2/T < (D : ℝ) + 1 := by
        dsimp [D]
        exact Nat.lt_floor_add_one _
      have hdgR : (D : ℝ) + 1 ≤ (p.1.gcd p.2 : ℝ) := by
        have : D + 1 ≤ p.1.gcd p.2 := by omega
        exact_mod_cast this
      exact ⟨hp, hlt.trans_le hdgR⟩
  rw [hfilter, hsplit]
  calc
    _ ≤ 4 * Cbig * Real.rpow T eta *
        (2*(1+Real.log (max 1 ((2*N : ℕ) : ℝ))) *
          Real.sqrt ((W.card : ℝ) * T + ((W.card : ℝ)^2 +
            Real.rpow (W.card : ℝ) (5/4 : ℝ) * Real.rpow T (1/2)) * (N : ℝ)) *
          Real.sqrt ((sourceApproximateAdditiveEnergy W : ℝ) * T +
            ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4) *
              (W.card : ℝ) * Real.rpow T (1/2)) * (N : ℝ))) := htail2
    _ = 8 * Cbig * Real.rpow T eta *
        (1+Real.log (max 1 ((2*N : ℕ) : ℝ))) *
          Real.sqrt ((W.card : ℝ) * T + ((W.card : ℝ)^2 +
            Real.rpow (W.card : ℝ) (5/4) * Real.rpow T (1/2)) * (N : ℝ)) *
          Real.sqrt ((sourceApproximateAdditiveEnergy W : ℝ) * T +
            ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4) *
              (W.card : ℝ) * Real.rpow T (1/2)) * (N : ℝ)) := by ring
    _ = 8 * Cbig * Real.rpow T eta *
        (1+Real.log (max 1 (2*(N : ℝ)))) *
          Real.sqrt ((W.card : ℝ) * T + (W.card : ℝ)^2 * (N : ℝ) +
            Real.rpow (W.card : ℝ) (5/4) * Real.rpow T (1/2) * (N : ℝ)) *
          Real.sqrt ((N : ℝ) * (W.card : ℝ)^4 +
            (sourceApproximateAdditiveEnergy W : ℝ) * T +
            Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4) *
              (W.card : ℝ) * Real.rpow T (1/2) * (N : ℝ)) := by
      have hlog : (1+Real.log (max 1 ((2*N : ℕ) : ℝ))) =
          1+Real.log (max 1 (2*(N : ℝ))) := by norm_num
      rw [hlog]
      have hA : (W.card : ℝ) * T + ((W.card : ℝ)^2 +
          Real.rpow (W.card : ℝ) (5/4) * Real.rpow T (1/2)) * (N : ℝ) =
          (W.card : ℝ) * T + (W.card : ℝ)^2 * (N : ℝ) +
            Real.rpow (W.card : ℝ) (5/4) * Real.rpow T (1/2) * (N : ℝ) := by ring
      have hB : (sourceApproximateAdditiveEnergy W : ℝ) * T +
          ((W.card : ℝ)^4 + Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4) *
            (W.card : ℝ) * Real.rpow T (1/2)) * (N : ℝ) =
          (N : ℝ) * (W.card : ℝ)^4 +
            (sourceApproximateAdditiveEnergy W : ℝ) * T +
            Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4) *
              (W.card : ℝ) * Real.rpow T (1/2) * (N : ℝ) := by ring
      rw [hA, hB]
end GuthMaynardEnergy119Factored

#print axioms GuthMaynardEnergy119Factored.high_gcd_factored_cubic
