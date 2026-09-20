import GuthMaynardGMHalaszLiteralFront
import GuthMaynardGMKernelUniformShape

open scoped BigOperators ComplexConjugate
open CGLProofDAG
open GuthMaynardSectionFourTrace
open GuthMaynardGMHighValueComplement
open GuthMaynardGMKernelCorrelation
open GuthMaynardGMHalaszLiteralFront

noncomputable section
namespace GuthMaynardGMHalaszConcreteAbsorption

/-- The polynomial threshold and high-value scale imply the root-scale
inequality used by the local Halasz consumer. -/
theorem gmGrowth300
    {V : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hNlarge : (64 * (300 : ℝ)) ^ 10 ≤ (N : ℝ))
    (hV : 0 < V)
    (hVhigh : Real.rpow (N : ℝ) (4 / 5 : ℝ) ≤ V) :
    (64 * (300 : ℝ)) * (N : ℝ) * Real.sqrt (N : ℝ) ≤ V ^ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hA : 0 < (64 * (300 : ℝ)) := by norm_num
  have hAroot : (64 * (300 : ℝ)) ≤ Real.rpow (N : ℝ) (1 / 10 : ℝ) := by
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (64 * (300 : ℝ)) ^ 10) hNlarge
      (by norm_num : (0 : ℝ) ≤ 1 / 10)
    have hleft : ((64 * (300 : ℝ)) ^ 10) ^ (1 / 10 : ℝ) =
        64 * (300 : ℝ) := by
      calc
        ((64 * (300 : ℝ)) ^ 10) ^ (1 / 10 : ℝ) =
            (Real.rpow (64 * (300 : ℝ)) (10 : ℝ)) ^ (1 / 10 : ℝ) := by
              congr 2
              exact (Real.rpow_natCast (64 * (300 : ℝ)) 10).symm
        _ = Real.rpow (64 * (300 : ℝ)) ((10 : ℝ) * (1 / 10 : ℝ)) :=
              (Real.rpow_mul hA.le _ _).symm
        _ = 64 * (300 : ℝ) := by norm_num [Real.rpow_one]
    rw [hleft] at hpow
    exact hpow
  have hgrowth : (64 * (300 : ℝ)) * (N : ℝ) * Real.sqrt (N : ℝ) ≤
      (Real.rpow (N : ℝ) (4 / 5 : ℝ)) ^ 2 := by
    have hNhalf : (N : ℝ) * Real.rpow (N : ℝ) (1 / 2 : ℝ) =
        Real.rpow (N : ℝ) (1 + 1 / 2 : ℝ) := by
      calc
        (N : ℝ) * Real.rpow (N : ℝ) (1 / 2 : ℝ) =
            Real.rpow (N : ℝ) 1 * Real.rpow (N : ℝ) (1 / 2 : ℝ) := by
              congr 1
              exact (Real.rpow_one (N : ℝ)).symm
        _ = Real.rpow (N : ℝ) (1 + 1 / 2 : ℝ) :=
              (Real.rpow_add hNpos _ _).symm
    have hleft : (64 * (300 : ℝ)) * (N : ℝ) *
        Real.rpow (N : ℝ) (1 / 2 : ℝ) ≤
        Real.rpow (N : ℝ) (4 / 5 : ℝ) *
          Real.rpow (N : ℝ) (4 / 5 : ℝ) := by
      calc
        (64 * (300 : ℝ)) * (N : ℝ) * Real.rpow (N : ℝ) (1 / 2 : ℝ) =
            (64 * (300 : ℝ)) * ((N : ℝ) * Real.rpow (N : ℝ) (1 / 2 : ℝ)) := by ring
        _ ≤ Real.rpow (N : ℝ) (1 / 10) *
              ((N : ℝ) * Real.rpow (N : ℝ) (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hAroot
              (mul_nonneg hNpos.le (Real.rpow_nonneg hNpos.le _))
        _ = Real.rpow (N : ℝ) (1 / 10) *
              ((N : ℝ) * Real.rpow (N : ℝ) (1 / 2 : ℝ)) := by ring
        _ = Real.rpow (N : ℝ) (1 / 10) *
              Real.rpow (N : ℝ) (1 + 1 / 2 : ℝ) := by rw [hNhalf]
        _ = Real.rpow (N : ℝ) (1 / 10 + (1 + 1 / 2) : ℝ) :=
              (Real.rpow_add hNpos _ _).symm
        _ = Real.rpow (N : ℝ) (4 / 5 + 4 / 5 : ℝ) := by congr 1 <;> norm_num
        _ = Real.rpow (N : ℝ) (4 / 5 : ℝ) *
              Real.rpow (N : ℝ) (4 / 5 : ℝ) :=
                Real.rpow_add hNpos _ _
    simpa [Real.sqrt_eq_rpow, pow_two] using hleft
  have hsqV : (Real.rpow (N : ℝ) (4 / 5 : ℝ)) ^ 2 ≤ V ^ 2 := by
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hVhigh 2
  exact hgrowth.trans hsqV

/-- The source scale is at least `N` under the same explicit threshold. -/
theorem sourceScale_ge_N
    {V : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hNlarge : (64 * (300 : ℝ)) ^ 10 ≤ (N : ℝ))
    (hV : 0 < V)
    (hVhigh : Real.rpow (N : ℝ) (4 / 5 : ℝ) ≤ V) :
    (N : ℝ) ≤ ((19200 : ℝ)⁻¹) ^ 2 * V ^ 4 / (N : ℝ) ^ 2 := by
  have hcore := gmGrowth300 hN hNlarge hV hVhigh
  have hsquare :
      ((64 * (300 : ℝ)) * (N : ℝ) * Real.sqrt (N : ℝ)) ^ 2 ≤ (V ^ 2) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hcore 2
  have hsqrt : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hpoly : (19200 : ℝ) ^ 2 * (N : ℝ) ^ 3 ≤ V ^ 4 := by
    norm_num at hsquare ⊢
    nlinarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hden : 0 < (N : ℝ) ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  have hApos : (0 : ℝ) < 19200 := by norm_num
  field_simp [hApos.ne']
  nlinarith

/-- Concrete high-value local consumer at the contour-checked pointwise
constant `300`. The only analytic input is the literal finite Halasz front;
the coefficient cap and large values are explicit. -/
theorem gmHalaszLocalHighValues300
    {L V : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hNlarge : (64 * (300 : ℝ)) ^ 10 ≤ (N : ℝ))
    (hV : 0 < V)
    (hVhigh : Real.rpow (N : ℝ) (4 / 5 : ℝ) ≤ V)
    (hL : 1 ≤ L)
    (hLshape : L ≤ ((64 * (300 : ℝ))⁻¹) ^ 2 * V ^ 4 / (N : ℝ) ^ 2)
    (W : Finset ℝ) (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ L)
    (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W,
      V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * sourcePhase n t‖) :
    (W.card : ℝ) ≤
      9600 * (N : ℝ) ^ 2 * Real.log (2 * L) / V ^ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hA : 0 < (64 * (300 : ℝ)) := by norm_num
  have hA' : (64 * (300 : ℝ)) = 19200 := by norm_num
  have hcore := gmGrowth300 hN hNlarge hV hVhigh
  have hrootN : Real.sqrt (N : ℝ) ≤ V ^ 2 /
      ((64 * (300 : ℝ)) * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < (64 * (300 : ℝ)) * N)).2
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hqpos : 0 < V ^ 2 / ((64 * (300 : ℝ)) * (N : ℝ)) := by positivity
  have hrootL : Real.sqrt L ≤ V ^ 2 /
      ((64 * (300 : ℝ)) * (N : ℝ)) := by
    have hLsq : L ≤
        (V ^ 2 / ((64 * (300 : ℝ)) * (N : ℝ))) ^ 2 := by
      calc
        L ≤ ((64 * (300 : ℝ))⁻¹) ^ 2 * V ^ 4 / (N : ℝ) ^ 2 := hLshape
        _ = (V ^ 2 / ((64 * (300 : ℝ)) * (N : ℝ))) ^ 2 := by
          field_simp [ne_of_gt hA, ne_of_gt hNpos]
    nlinarith [Real.sq_sqrt hL0]
  obtain ⟨eta, heta, hfront⟩ :=
    exists_literal_halasz_front N W a hV.le ha hlarge
  let c' : ℝ := L * (N : ℝ) ^ 2 / V ^ 4
  have hc' : 0 < c' := by
    dsimp [c']
    positivity
  have hshape' : L = c' * V ^ 4 / (N : ℝ) ^ 2 := by
    dsimp [c']
    field_simp [ne_of_gt hV, ne_of_gt hNpos]
  have hbase := gmHalaszLocalHighValues uniformPointwiseKernelBound_300
    (c := c') (L := L) (V := V) (N := N)
    hc' hshape' hN (by
      have hA10 : (100 : ℝ) ≤ (64 * (300 : ℝ)) ^ 10 := by norm_num
      linarith) hV hVhigh hL
    (by simpa [hA'] using hrootL) (by simpa [hA'] using hrootN)
    W hsep hheight eta heta hfront
  norm_num at hbase ⊢
  exact hbase

end GuthMaynardGMHalaszConcreteAbsorption

#print axioms GuthMaynardGMHalaszConcreteAbsorption.gmHalaszLocalHighValues300
