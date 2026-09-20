import JutilaLemma6HorizontalDecay
import JutilaLemma6SieveCoefficientBridge
import JutilaCollarSourceParameters

/-! Literal conductor-one crossed pole for the principal Lemma-6 detector.
This module bounds the pole term only; it does not assert a contour identity. -/
namespace MAPJutilaPrincipalDetectorPole
open Complex Real Filter
open scoped BigOperators
open MAPJutilaMEntire MAPJutilaPseudocharacterMExact
open MAPJutilaMNonnegativeHalfPlaneBound MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaPseudocharacterHarmonicLower MAPJutilaGappedGrahamBypass
open MAPJutilaCollarSourceParameters MAPJutilaLemma6GenericTailAbsorption
noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

theorem principal_localEulerFactor_one {p : ℕ} (hp : p.Prime) :
    jutilaLocalEulerFactorComplex chiOne p 1 = 0 := by
  unfold jutilaLocalEulerFactorComplex jutilaNatPower
  rw [selbergPseudoCoeff_prime_sub_one hp]
  have hchi : chiOne p = 1 := by
    have he : (p:ZMod 1) = 1 := Subsingleton.elim _ _
    rw [he, map_one]
  rw [hchi]
  simp [Complex.cpow_neg_one, hp.ne_zero]

theorem norm_principal_localEulerProduct_one_le (r d : ℕ) :
    ‖jutilaLocalEulerProductComplex chiOne r d 1‖ ≤ 1 := by
  unfold jutilaLocalEulerProductComplex
  apply (Finset.norm_prod_le _ _).trans
  apply (Finset.prod_le_one (fun p hp => norm_nonneg _))
  intro p hp
  rw [principal_localEulerFactor_one (Nat.prime_of_mem_primeFactors hp)]
  norm_num

/-- At s=1 the literal principal local factors vanish, giving a sharper
finite bound than the imaginary-axis pseudocharacter envelope. -/
theorem norm_principal_M_one_le_card (xi : ℕ → ℂ) (Ds S : Finset ℕ)
    (hD : ∀ d ∈ Ds, 0 < d) (hS : ∀ r ∈ S, 0 < r)
    (hxi : ∀ d ∈ Ds, ‖xi d‖ ≤ 1) :
    ‖jutilaMWeightedSumComplex chiOne xi Ds S 1‖ ≤ (S.card:ℝ)*(Ds.card:ℝ) := by
  have hterm (r d : ℕ) (hr : 0<r) (hd : d∈Ds) :
      ‖jutilaMTermComplex chiOne xi r d 1‖ ≤ (r:ℝ) := by
    have hp := norm_selbergPseudoAt_le r d
    have hphi : (Nat.totient (r.gcd d):ℝ) ≤ r := by
      exact_mod_cast (Nat.totient_le (r.gcd d)).trans (Nat.gcd_le_left d hr)
    have hpR := hp.trans hphi
    have hchi := DirichletCharacter.norm_le_one chiOne d
    have hn := norm_jutilaNatPower_le_one (hD d hd) (s:=1) (by norm_num)
    have he := norm_principal_localEulerProduct_one_le r d
    unfold jutilaMTermComplex
    simp only [norm_mul]
    calc
      _ ≤ 1*1*(r:ℝ)*1*1 := by gcongr; exact hxi d hd
      _ = _ := by ring
  have hrow (r : ℕ) (hr : r∈S) :
      ‖(r:ℂ)⁻¹*jutilaMFiniteComplex chiOne xi Ds r 1‖ ≤ (Ds.card:ℝ) := by
    have hrp : (0:ℝ)<r := by exact_mod_cast hS r hr
    have hsum : ‖jutilaMFiniteComplex chiOne xi Ds r 1‖ ≤ (Ds.card:ℝ)*(r:ℝ) := by
      unfold jutilaMFiniteComplex
      apply (norm_sum_le _ _).trans
      have h := Finset.sum_le_sum (fun d hd => hterm r d (hS r hr) hd)
      simpa using h
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (r:ℝ)⁻¹*((Ds.card:ℝ)*(r:ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by field_simp
  unfold jutilaMWeightedSumComplex
  apply (norm_sum_le _ _).trans
  simpa using Finset.sum_le_sum hrow

theorem norm_canonical_principal_M_one_le {z1 z2 : ℝ} (hz1 : 1<z1) (hz12 : z1<z2) (R : ℕ) :
    ‖jutilaMWeightedSumComplex chiOne (jutilaLambdaComplex z1 z2)
      (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R) 1‖ ≤ (R:ℝ)*z2 := by
  have h := norm_principal_M_one_le_card (jutilaLambdaComplex z1 z2)
    (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R)
    (by intro d hd; exact (Finset.mem_Icc.mp hd).1)
    (by intro r hr; exact (Finset.mem_Icc.mp (jutilaPrimedRSet_subset_Icc 1 R hr)).1)
    (by intro d hd; simpa [jutilaLambdaComplex, Complex.norm_real, Real.norm_eq_abs]
      using abs_jutilaLambda_le_one hz1 hz12 d)
  have hcard : ((jutilaPrimedRSet 1 R).card:ℝ) ≤ R := by
    have h := Finset.card_le_card (jutilaPrimedRSet_subset_Icc 1 R)
    simpa using (show ((jutilaPrimedRSet 1 R).card:ℝ) ≤ ((Finset.Icc 1 R).card:ℝ) by exact_mod_cast h)
  have hDcard : ((jutilaLambdaSupport z2).card:ℝ) ≤ z2 := by
    simp only [jutilaLambdaSupport, Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le (by linarith)
  exact h.trans (mul_le_mul hcard hDcard (by positivity) (by positivity))

/-- The actual extra residue at w=1-rho for the conductor-one detector. -/
def principalDetectorPole (rho : ℂ) (X z1 z2 : ℝ) (R : ℕ) : ℂ :=
  Complex.Gamma (1-rho)*(X:ℂ)^(1-rho)*
    jutilaMWeightedSumComplex chiOne (jutilaLambdaComplex z1 z2)
      (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R) 1

theorem principalDetectorPole_norm_le {rho : ℂ} {X z1 z2 : ℝ} (R : ℕ)
    (hbeta0 : 0 ≤ rho.re) (hbeta1 : rho.re ≤ 1) (ht : 1 ≤ |rho.im|)
    (hX : 1 ≤ X) (hz1 : 1<z1) (hz12 : z1<z2) :
    ‖principalDetectorPole rho X z1 z2 R‖ ≤
      24*Real.exp (-|rho.im|/2)*X*(R:ℝ)*z2 := by
  have hGamma := MAPJutilaLemma6HorizontalDecay.norm_Gamma_detectorStrip_le
    (x:=1-rho.re) (t:= -rho.im) (by linarith) (by linarith) (by simpa using ht)
  have harg : ((1-rho.re:ℝ):ℂ)+(-rho.im:ℝ)*I = 1-rho := by apply Complex.ext <;> simp
  rw [harg] at hGamma
  simp only [abs_neg] at hGamma
  have hpower : ‖(X:ℂ)^(1-rho)‖ ≤ X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simpa using Real.rpow_le_self_of_one_le hX (show (1-rho).re≤1 by simp; linarith)
  have hM := norm_canonical_principal_M_one_le hz1 hz12 R
  have hsmooth : (1+|rho.im|)*Real.exp (-|rho.im|) ≤ 2*Real.exp (-|rho.im|/2) := by
    have hlinear : 1+|rho.im| ≤ 2*Real.exp (|rho.im|/2) := by
      have h := Real.add_one_le_exp (|rho.im|/2)
      linarith
    calc
      _ ≤ (2*Real.exp (|rho.im|/2))*Real.exp (-|rho.im|) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hz20 : 0 ≤ z2 := by linarith
  unfold principalDetectorPole
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (12*((1+|rho.im|)*Real.exp (-|rho.im|)))*X*((R:ℝ)*z2) := by
      apply mul_le_mul _ hM (norm_nonneg _) (by positivity)
      exact mul_le_mul (by nlinarith only [hGamma]) hpower (norm_nonneg _) (by positivity)
    _ ≤ (12*(2*Real.exp (-|rho.im|/2)))*X*((R:ℝ)*z2) := by
      gcongr
    _ = _ := by ring

/-- Explicit high-ordinate death test for the literal principal pole.
No contour displacement is asserted by this estimate. -/
theorem eventually_source_principalDetectorPole_lt_one {δ : ℝ}
    (hlo : 1/560 ≤ δ) (hhi : δ ≤ 1/280) :
    ∀ᶠ D : ℝ in atTop, ∀ rho : ℂ,
      1-δ ≤ rho.re → rho.re ≤ 1 → 12*Real.log D ≤ |rho.im| →
      ‖principalDetectorPole rho (lemmaSixSmoothScale δ D)
        (sourceZ1 δ D) (sourceZ2 δ D) (sourceR δ D)‖ < 1 := by
  filter_upwards [eventually_sourceGeometry hlo hhi,eventually_ge_atTop (25:ℝ),
    eventually_ge_atTop (Real.exp 1)] with D hgeo hD hDe
  intro rho hbeta hbeta1 ht
  have hDp : 0<D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hlog : 1 ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos 1) hDe
    simpa using h
  have hX : lemmaSixSmoothScale δ D ≤ D^2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hD1 (show 1+12*δ≤2 by linarith)
    simpa [lemmaSixSmoothScale] using h
  have hR : (sourceR δ D:ℝ) ≤ D := hgeo.R_upper.trans
    (Real.rpow_le_self_of_one_le hD1 (by linarith))
  have hz2 : sourceZ2 δ D ≤ D := Real.rpow_le_self_of_one_le hD1 (by linarith)
  have hExp : Real.exp (-|rho.im|/2) ≤ Real.rpow D (-6) := by
    have h := Real.exp_le_exp.mpr (show -|rho.im|/2 ≤ (-6)*Real.log D by linarith only [ht])
    simpa [Real.rpow_def_of_pos hDp, mul_comm] using h
  have hbound := principalDetectorPole_norm_le (X:=lemmaSixSmoothScale δ D)
    (z1:=sourceZ1 δ D) (z2:=sourceZ2 δ D) (sourceR δ D)
    (by linarith : 0≤rho.re) hbeta1 (by linarith) (by linarith [hgeo.X_two])
    hgeo.z1_one hgeo.z12
  have hDpow : Real.rpow D (-6)*D^2*D*D = (D^2)⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hDp.le]
    norm_num only [Real.rpow_ofNat]
    field_simp
  have hpow0 : 0 ≤ Real.rpow D (-6) := Real.rpow_nonneg hDp.le _
  have hX0 : 0 ≤ lemmaSixSmoothScale δ D := (lemmaSixSmoothScale_pos hDp).le
  have hz20 : 0 ≤ sourceZ2 δ D := (hgeo.z1_one.trans hgeo.z12).le.trans' zero_le_one
  calc
    _ ≤ 24*Real.exp (-|rho.im|/2)*lemmaSixSmoothScale δ D*(sourceR δ D:ℝ)*sourceZ2 δ D := hbound
    _ ≤ 24*Real.rpow D (-6)*D^2*D*D := by
      gcongr
    _ = 24/(D^2) := by rw [show 24*Real.rpow D (-6)*D^2*D*D =
        24*(Real.rpow D (-6)*D^2*D*D) by ring,hDpow]; rfl
    _ < 1 := (div_lt_one (sq_pos_of_pos hDp)).mpr (by nlinarith)

end
end MAPJutilaPrincipalDetectorPole
#print axioms MAPJutilaPrincipalDetectorPole.norm_canonical_principal_M_one_le
#print axioms MAPJutilaPrincipalDetectorPole.eventually_source_principalDetectorPole_lt_one
