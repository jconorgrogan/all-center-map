import MRTProposition61TypeIIFirstInequalityV3
import MRTLemma215DynamicTypeIICoefficientBoundsV3
import RamachandraShiftedCoefficientEnergy

/-!
# Premise-free Lemma 2.10 instantiation for dynamic Type-II packets

This file supplies the two exact character mean squares used on MRT pp. 59--60.
The coefficient presented to Lemma 2.10 is the literal critical-line
normalization `f(n) / sqrt n`.  No analytic hypothesis is introduced here:
both mean squares follow from `dyadic_twisted_character_mean_square_interval_le`.
-/

namespace MRTProposition61TypeIILemma210InstantiationV3

open scoped BigOperators
open scoped ArithmeticFunction
open MeasureTheory ArithmeticFunction
open MixedMellinCert
open MontgomeryVaughanFiniteReduction
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTLemma210DyadicMeanSquare
open MRTProposition61TypeIIFirstInequalityV3
open RamachandraShiftedCoefficientEnergy
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicCoefficientBoundsV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIICoefficientBoundsV3

noncomputable section

/-- The coefficient used by the source Type-II Dirichlet polynomials. -/
def criticalDyadicCoefficient (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f n / (Real.sqrt (n : ℝ) : ℂ)

/-- One source-normalized dyadic factor polynomial. -/
def typeIIDyadicPolynomial
    (q N : ℕ) (f : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  twistedFinitePolynomial q (dyadicSupport N)
    (criticalDyadicCoefficient f) chi t

/-- Its nonnegative norm field, in the exact real form consumed by the
Cauchy--Fubini layer. -/
def typeIIDyadicNormField
    (q N : ℕ) (f : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ‖typeIIDyadicPolynomial q N f chi t‖

theorem continuous_typeIIDyadicNormField
    (q N : ℕ) (f : ℕ → ℂ) (chi : DirichletCharacter ℂ q) :
    Continuous (typeIIDyadicNormField q N f chi) := by
  unfold typeIIDyadicNormField typeIIDyadicPolynomial
    twistedFinitePolynomial twistedPhase criticalDyadicCoefficient
  fun_prop

theorem typeIIDyadicNormField_nonneg
    (q N : ℕ) (f : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    0 ≤ typeIIDyadicNormField q N f chi t :=
  norm_nonneg _

theorem norm_criticalDyadicCoefficient_sq
    (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    ‖criticalDyadicCoefficient f n‖ ^ 2 =
      ‖f n‖ ^ 2 / (n : ℝ) := by
  unfold criticalDyadicCoefficient
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)), div_pow,
    Real.sq_sqrt (by positivity)]

/-- Exact polylog-energy adapter for a divisor-bounded Type-II cell.  This is
the finite coefficient summation following the two invocations of Lemma 2.10.
The common logarithm is left abstract so the caller can use the literal
source ambient logarithm. -/
theorem coefficientEnergy_critical_le_harmonic
    {N r a : ℕ} (L : ℝ) (hL : 0 ≤ L) (f : ℕ → ℂ)
    (hf : ∀ n ∈ dyadicSupport N,
      ‖f n‖ ≤ (tauAF r n : ℝ) * L ^ a) :
    coefficientEnergy (criticalDyadicCoefficient f) N ≤
      L ^ (2 * a) * (harmonic (2 * N) : ℝ) ^ (r * r) := by
  unfold coefficientEnergy
  calc
    (∑ n ∈ dyadicSupport N, ‖criticalDyadicCoefficient f n‖ ^ 2) ≤
        ∑ n ∈ dyadicSupport N,
          L ^ (2 * a) * ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
      rw [norm_criticalDyadicCoefficient_sq f hnpos]
      have hraw := hf n hn
      have hrawSq : ‖f n‖ ^ 2 ≤
          ((tauAF r n : ℝ) * L ^ a) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hraw 2
      have htau : (tauAF r n : ℝ) ^ 2 ≤ tauAF (r * r) n := by
        exact_mod_cast ShiuAnalyticLayer.tauAF_square_le_tauAF_mul r n
      have hnR : 0 ≤ (n : ℝ) := by positivity
      calc
        ‖f n‖ ^ 2 / (n : ℝ) ≤
            ((tauAF r n : ℝ) * L ^ a) ^ 2 / (n : ℝ) :=
          div_le_div_of_nonneg_right hrawSq hnR
        _ = L ^ (2 * a) * ((tauAF r n : ℝ) ^ 2 / (n : ℝ)) := by
          rw [show 2 * a = a * 2 by omega, pow_mul]
          ring
        _ ≤ L ^ (2 * a) * ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by
          gcongr
    _ ≤ ∑ n ∈ Finset.Ioc 0 (2 * N),
          L ^ (2 * a) * ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (RamachandraShiftedCoefficientEnergy.dyadicSupport_subset_Ioc_zero_two_mul N)
      intro n hn hnot
      exact mul_nonneg (pow_nonneg hL _)
        (div_nonneg (by positivity) (by positivity))
    _ = L ^ (2 * a) *
        ∑ n ∈ Finset.Ioc 0 (2 * N),
          ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ L ^ (2 * a) * (harmonic (2 * N) : ℝ) ^ (r * r) := by
      exact mul_le_mul_of_nonneg_left
        (sum_tauAF_div_cast_le_harmonic_pow (r * r) (2 * N))
        (pow_nonneg hL _)

/-- Source-facing polylog version.  A `tau_r log^a` coefficient envelope on
the literal dyadic block gives a completely explicit log-power energy bound.
The harmless `1 + log(4N)` base simultaneously dominates the coefficient
logs and the harmonic number. -/
theorem coefficientEnergy_critical_le_logPow
    {N r a : ℕ} (hN : 1 ≤ N) (f : ℕ → ℂ)
    (hf : ∀ n ∈ dyadicSupport N,
      ‖f n‖ ≤ (tauAF r n : ℝ) * Real.log (2 * (n : ℝ)) ^ a) :
    coefficientEnergy (criticalDyadicCoefficient f) N ≤
      (1 + Real.log (4 * (N : ℝ))) ^ (2 * a + r * r) := by
  let L : ℝ := 1 + Real.log (4 * (N : ℝ))
  have hlog4 : 0 ≤ Real.log (4 * (N : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 4 * N by omega)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hfL : ∀ n ∈ dyadicSupport N,
      ‖f n‖ ≤ (tauAF r n : ℝ) * L ^ a := by
    intro n hn
    have hnBounds := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := Nat.zero_lt_of_lt hnBounds.1
    have hlogNonneg : 0 ≤ Real.log (2 * (n : ℝ)) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * n by omega)
    have hlogLe4 : Real.log (2 * (n : ℝ)) ≤
        Real.log (4 * (N : ℝ)) := by
      apply Real.log_le_log (by positivity)
      have hnat : 2 * n ≤ 4 * N := by omega
      exact_mod_cast hnat
    have hlogLeL : Real.log (2 * (n : ℝ)) ≤ L := by
      dsimp [L]
      linarith
    exact (hf n hn).trans <| mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlogNonneg hlogLeL a) (by positivity)
  have henergy := coefficientEnergy_critical_le_harmonic L hL f hfL
  have hharm : (harmonic (2 * N) : ℝ) ≤ L := by
    have hbase := harmonic_le_one_add_log (2 * N)
    have hlog : Real.log (2 * (N : ℝ)) ≤
        Real.log (4 * (N : ℝ)) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast (show 2 * N ≤ 4 * N by omega)
    have hbase' : (harmonic (2 * N) : ℝ) ≤
        1 + Real.log (2 * (N : ℝ)) := by
      simpa [Nat.cast_mul] using hbase
    exact hbase'.trans (by dsimp [L]; linarith)
  have hharm0 : 0 ≤ (harmonic (2 * N) : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : 2 * N ≠ 0)).le
  calc
    coefficientEnergy (criticalDyadicCoefficient f) N ≤
        L ^ (2 * a) * (harmonic (2 * N) : ℝ) ^ (r * r) := henergy
    _ ≤ L ^ (2 * a) * L ^ (r * r) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hharm0 hharm (r * r))
        (pow_nonneg hL _)
    _ = L ^ (2 * a + r * r) := (pow_add L (2 * a) (r * r)).symm
    _ = (1 + Real.log (4 * (N : ℝ))) ^ (2 * a + r * r) := by rfl

/-- Literal specialization to an unscaled dyadic cell of either collected
Type-II factor list. -/
theorem factorListDyadicCell_energy_le_logPow
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub,
      f ∈ sortedComponentFactorList logIndex zbag mbag)
    (cell : Fin (sourceDyadicCount (factorUpperProduct sub))) :
    coefficientEnergy
        (criticalDyadicCoefficient (factorListDyadicCell sub cell))
        (2 ^ (cell : ℕ)) ≤
      (1 + Real.log (4 * ((2 ^ (cell : ℕ) : ℕ) : ℝ))) ^
        (4 * sub.length + sub.length * sub.length) := by
  let N : ℕ := 2 ^ (cell : ℕ)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact Nat.one_le_pow (cell : ℕ) 2 (by omega)
  have hf : ∀ n ∈ dyadicSupport N,
      ‖factorListDyadicCell sub cell n‖ ≤
        (tauAF sub.length n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ (2 * sub.length) := by
    intro n hn
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    exact factorListDyadicCell_norm_le
      logIndex zbag mbag sub hsub cell hn2
  have henergy := coefficientEnergy_critical_le_logPow
    (N := N) (r := sub.length) (a := 2 * sub.length) hN
    (factorListDyadicCell sub cell) hf
  simpa [N, show 2 * (2 * sub.length) = 4 * sub.length by omega]
    using henergy

/-- The scalar-absorbed prefix cell also has finite polylog energy, with the
scalar cost represented by an explicit natural log exponent. -/
theorem exists_scaledTypeIIPrefixCell_energy_logPow
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub,
      f ∈ sortedComponentFactorList logIndex zbag mbag)
    (cell : Fin (sourceDyadicCount (factorUpperProduct sub))) :
    ∃ B : ℕ,
      coefficientEnergy
          (criticalDyadicCoefficient
            (scaledTypeIIPrefixCell zbag mbag sub cell))
          (2 ^ (cell : ℕ)) ≤
        (1 + Real.log (4 * ((2 ^ (cell : ℕ) : ℕ) : ℝ))) ^ B := by
  obtain ⟨a, ha⟩ := exists_scaledTypeIIPrefixCell_bound
    logIndex zbag mbag sub hsub cell
  let N : ℕ := 2 ^ (cell : ℕ)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact Nat.one_le_pow (cell : ℕ) 2 (by omega)
  have hf : ∀ n ∈ dyadicSupport N,
      ‖scaledTypeIIPrefixCell zbag mbag sub cell n‖ ≤
        (tauAF sub.length n : ℝ) * Real.log (2 * (n : ℝ)) ^ a := by
    intro n hn
    apply ha n
    simpa [MontgomeryVaughanFiniteReduction.dyadicSupport,
      DeterminantCountWeld.dyadic, N] using hn
  refine ⟨2 * a + sub.length * sub.length, ?_⟩
  simpa [N] using coefficientEnergy_critical_le_logPow
    (N := N) (r := sub.length) (a := a) hN
      (scaledTypeIIPrefixCell zbag mbag sub cell) hf

/-- The first use of MRT Lemma 2.10 in Proposition 6.1: a moving interval of
length `2U`, uniformly in its center. -/
theorem typeIILocalSquareMass_le_lemma210
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (f : ℕ → ℂ)
    {U : ℝ} (hU : 0 ≤ U) (t : ℝ) :
    typeIILocalSquareMass (typeIIDyadicNormField q N f) U t ≤
      ((q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ)) *
        coefficientEnergy (criticalDyadicCoefficient f) N := by
  have h := dyadic_twisted_character_mean_square_interval_le
    (q := q) hN (criticalDyadicCoefficient f) (t - U)
    (T := 2 * U) (by positivity)
  unfold typeIILocalSquareMass
  rw [← intervalIntegral.integral_finsetSum]
  · change (∫ s in (t - U)..(t + U),
      ∑ chi : DirichletCharacter ℂ q,
        ‖typeIIDyadicPolynomial q N f chi s‖ ^ 2) ≤ _
    change (∫ s in (t - U)..(t + U),
      ∑ chi : DirichletCharacter ℂ q,
        ‖twistedFinitePolynomial q (dyadicSupport N)
          (criticalDyadicCoefficient f) chi s‖ ^ 2) ≤ _
    have hend : t - U + 2 * U = t + U := by ring
    rw [hend] at h
    exact h
  · intro chi hchi
    exact ((continuous_typeIIDyadicNormField q N f chi).pow 2).intervalIntegrable _ _

/-- The second use of MRT Lemma 2.10 in Proposition 6.1: the Fubini-enlarged
outer interval. -/
theorem typeIILongSquareMass_le_lemma210
    {q M : ℕ} [NeZero q] (hM : 1 ≤ M) (f : ℕ → ℂ)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    (∫ s in (a - U)..(b + U),
      ∑ chi : DirichletCharacter ℂ q,
        (typeIIDyadicNormField q M f chi s) ^ 2) ≤
      ((q : ℝ) * (b - a + 2 * U) + 8 * Real.pi * (M : ℝ)) *
        coefficientEnergy (criticalDyadicCoefficient f) M := by
  have hlength : 0 ≤ b - a + 2 * U := by linarith
  have h := dyadic_twisted_character_mean_square_interval_le
    (q := q) hM (criticalDyadicCoefficient f) (a - U)
    (T := b - a + 2 * U) hlength
  change (∫ s in (a - U)..(b + U),
    ∑ chi : DirichletCharacter ℂ q,
      ‖twistedFinitePolynomial q (dyadicSupport M)
        (criticalDyadicCoefficient f) chi s‖ ^ 2) ≤ _
  have hend : a - U + (b - a + 2 * U) = b + U := by ring
  rw [hend] at h
  exact h

/-- Exact premise-free Type-II source moment before coefficient-energy and
scale absorption.  This is Proposition 6.1 equation (99) through its two
applications of Lemma 2.10, with every constant still visible. -/
theorem typeII_outerMass_le_lemma210
    {q N M : ℕ} [NeZero q]
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (alphaCoeff betaCoeff : ℕ → ℂ)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    (∫ t in a..b,
      (factoredTypeIIMass
        (typeIIDyadicNormField q N alphaCoeff)
        (typeIIDyadicNormField q M betaCoeff) U t) ^ 2) ≤
      2 * U *
        (((q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ)) *
          coefficientEnergy (criticalDyadicCoefficient alphaCoeff) N) *
        (((q : ℝ) * (b - a + 2 * U) + 8 * Real.pi * (M : ℝ)) *
          coefficientEnergy (criticalDyadicCoefficient betaCoeff) M) := by
  apply typeII_outerMass_le_of_two_meanSquares
    (fun chi ↦ continuous_typeIIDyadicNormField q N alphaCoeff chi)
    (fun chi ↦ continuous_typeIIDyadicNormField q M betaCoeff chi)
    (fun chi t ↦ typeIIDyadicNormField_nonneg q N alphaCoeff chi t)
    (fun chi t ↦ typeIIDyadicNormField_nonneg q M betaCoeff chi t)
    hab hU
    (mul_nonneg (by positivity) (by
      unfold coefficientEnergy
      positivity))
    (mul_nonneg (by positivity) (by
      unfold coefficientEnergy
      positivity))
  · intro t ht
    exact typeIILocalSquareMass_le_lemma210 hN alphaCoeff hU t
  · exact typeIILongSquareMass_le_lemma210 hM betaCoeff hab hU

end
end MRTProposition61TypeIILemma210InstantiationV3

#print axioms MRTProposition61TypeIILemma210InstantiationV3.typeIILocalSquareMass_le_lemma210
#print axioms MRTProposition61TypeIILemma210InstantiationV3.typeIILongSquareMass_le_lemma210
#print axioms MRTProposition61TypeIILemma210InstantiationV3.coefficientEnergy_critical_le_logPow
#print axioms MRTProposition61TypeIILemma210InstantiationV3.factorListDyadicCell_energy_le_logPow
#print axioms MRTProposition61TypeIILemma210InstantiationV3.exists_scaledTypeIIPrefixCell_energy_logPow
#print axioms MRTProposition61TypeIILemma210InstantiationV3.typeII_outerMass_le_lemma210
