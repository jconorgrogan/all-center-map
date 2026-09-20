import KTwoPrimeArithmeticLogBudgetLargeScale
import Mathlib.NumberTheory.Chebyshev

/-!
# Vol. 3 (29.32) from the weakest dyadic Chebyshev input

Mathlib currently contains Chebyshev's upper bound but explicitly lists the
lower bound as a TODO.  This module therefore isolates the exact missing
prime-distribution theorem as a logarithmically weighted dyadic lower bound,
then proves all deterministic steps from that theorem to the reciprocal-prime
statement used after Lemma 29.7.

The source input below is not a renaming of (29.32): its summand is `log p`,
not `1/p`.  It is the direct dyadic consequence of either the prime number
theorem or a Chebyshev lower bound strong enough to give positive mass after
subtracting the certified upper bound at the left endpoint.
-/

namespace GuthMaynardJutilaLemma29NineKTwo

open GuthMaynardJutilaTransference

noncomputable section

def dyadicPrimeLogMass (J : ℝ) : ℝ :=
  ∑ p ∈ primeRealIcc J (2*J), Real.log (p:ℝ)

/-- Weakest honest imported prime-distribution leaf needed for (29.32): every
sufficiently large dyadic interval has positive Chebyshev mass proportional
to its length. -/
def DyadicChebyshevLogPrimeLower : Prop :=
  ∃ a J₀ : ℝ, 0 < a ∧ 2 ≤ J₀ ∧
    ∀ J : ℝ, J₀ ≤ J → a*J ≤ dyadicPrimeLogMass J

/-- Native `Chebyshev.theta` formulation of the one missing imported theorem.
This is the most convenient statement for an eventual upstream mathlib lower
Chebyshev bound. -/
def DyadicChebyshevThetaIncrementLower : Prop :=
  ∃ a J₀ : ℝ, 0 < a ∧ 2 ≤ J₀ ∧
    ∀ J : ℝ, J₀ ≤ J → a*J ≤ Chebyshev.theta (2*J) - Chebyshev.theta J

/-- Standard global Chebyshev lower bound, with only the constant strength
needed to survive subtraction of mathlib's certified upper bound
`theta J ≤ log 4 * J`.  Mathlib's `NumberTheory.Chebyshev` currently lists
this lower bound as a TODO. -/
def ChebyshevThetaLinearLowerAboveLogTwo : Prop :=
  ∃ a J₀ : ℝ, Real.log 2 < a ∧ 2 ≤ J₀ ∧
    ∀ x : ℝ, J₀ ≤ x → a*x ≤ Chebyshev.theta x

theorem dyadicChebyshevThetaIncrementLower_of_linearLower
    (hlinear : ChebyshevThetaLinearLowerAboveLogTwo) :
    DyadicChebyshevThetaIncrementLower := by
  obtain ⟨a, J₀, ha, hJ₀, hlower⟩ := hlinear
  let b := 2*a-Real.log 4
  have hlogFour : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hb : 0 < b := by dsimp [b]; rw [hlogFour]; linarith
  refine ⟨b, J₀, hb, hJ₀, ?_⟩
  intro J hJJ₀
  have hJ0 : 0 ≤ J := by linarith
  have h2JJ₀ : J₀ ≤ 2*J := by linarith
  have hlower2 := hlower (2*J) h2JJ₀
  have hupperJ := Chebyshev.theta_le_log4_mul_x hJ0
  dsimp [b]
  linarith

theorem theta_increment_le_dyadicPrimeLogMass
    {J : ℝ} (hJ : 0 ≤ J) :
    Chebyshev.theta (2*J) - Chebyshev.theta J ≤ dyadicPrimeLogMass J := by
  classical
  let A : Finset ℕ := (Finset.Icc 0 ⌊2*J⌋₊).filter Nat.Prime
  let B : Finset ℕ := (Finset.Icc 0 ⌊J⌋₊).filter Nat.Prime
  have hJ2 : J ≤ 2*J := by linarith
  have hBA : B ⊆ A := by
    intro p hp
    have hpB := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hpB.2⟩
    have hpI := Finset.mem_Icc.mp hpB.1
    exact Finset.mem_Icc.mpr ⟨hpI.1,
      hpI.2.trans (Nat.floor_mono hJ2)⟩
  have hdiff : Chebyshev.theta (2*J) - Chebyshev.theta J =
      ∑ p ∈ A \ B, Real.log (p:ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
    change (∑ p ∈ A, Real.log (p:ℝ)) -
        (∑ p ∈ B, Real.log (p:ℝ)) = _
    have hsplit := Finset.sum_sdiff hBA (f := fun p : ℕ => Real.log (p:ℝ))
    linarith
  have hsubset : A \ B ⊆ primeRealIcc J (2*J) := by
    intro p hp
    have hpAB := Finset.mem_sdiff.mp hp
    have hpA := Finset.mem_filter.mp hpAB.1
    have hpAI := Finset.mem_Icc.mp hpA.1
    have hpNotB : ⌊J⌋₊ < p := by
      by_contra hnot
      have hple : p ≤ ⌊J⌋₊ := Nat.le_of_not_gt hnot
      apply hpAB.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpAI.1, hple⟩, hpA.2⟩
    have hpLower : J ≤ (p:ℝ) := by
      exact (Nat.floor_lt hJ).mp hpNotB |>.le
    have hpUpper : (p:ℝ) ≤ 2*J := by
      have hpCast : (p:ℝ) ≤ (⌊2*J⌋₊:ℝ) := by exact_mod_cast hpAI.2
      exact hpCast.trans (Nat.floor_le (by positivity : 0 ≤ 2*J))
    exact (mem_primeRealIcc_iff (by positivity : 0 ≤ 2*J)).mpr
      ⟨hpLower, hpUpper, hpA.2⟩
  rw [hdiff]
  unfold dyadicPrimeLogMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro p hp hpnot
    have hpData := (mem_primeRealIcc_iff (by positivity : 0 ≤ 2*J)).mp hp
    exact Real.log_nonneg (by exact_mod_cast hpData.2.2.one_le))

theorem dyadicChebyshevLogPrimeLower_of_thetaIncrement
    (htheta : DyadicChebyshevThetaIncrementLower) :
    DyadicChebyshevLogPrimeLower := by
  obtain ⟨a, J₀, ha, hJ₀, hlarge⟩ := htheta
  refine ⟨a, J₀, ha, hJ₀, ?_⟩
  intro J hJJ₀
  exact (hlarge J hJJ₀).trans
    (theta_increment_le_dyadicPrimeLogMass (by linarith))

theorem dyadicPrimeLogMass_le_reciprocal
    {J : ℝ} (hJ : 2 ≤ J) :
    dyadicPrimeLogMass J ≤
      (2*J*Real.log (2*J)) * primeReciprocalSum J (2*J) (1/2) := by
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have h2Jpos : 0 < 2*J := by positivity
  unfold dyadicPrimeLogMass primeReciprocalSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpData := (mem_primeRealIcc_iff h2Jpos.le).mp hp
  have hpPos : (0:ℝ) < p := by exact_mod_cast hpData.2.2.pos
  have hpUpper : (p:ℝ) ≤ 2*J := hpData.2.1
  have hpOne : (1:ℝ) ≤ p := by exact_mod_cast hpData.2.2.one_le
  have hlogp0 : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg hpOne
  have hlogMono : Real.log (p:ℝ) ≤ Real.log (2*J) :=
    Real.log_le_log hpPos hpUpper
  have hratio : 1 ≤ (2*J)/(p:ℝ) := by
    apply (le_div_iff₀ hpPos).2
    simpa using hpUpper
  have hratio0 : 0 ≤ (2*J)/(p:ℝ) := by positivity
  have hterm : Real.rpow (p:ℝ) (-2*(1/2:ℝ)) = (p:ℝ)⁻¹ := by
    norm_num [Real.rpow_neg_one]
  rw [hterm]
  calc
    Real.log (p:ℝ) = Real.log (p:ℝ)*1 := by ring
    _ ≤ Real.log (p:ℝ)*((2*J)/(p:ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hlogp0
    _ ≤ Real.log (2*J)*((2*J)/(p:ℝ)) :=
      mul_le_mul_of_nonneg_right hlogMono hratio0
    _ = (2*J*Real.log (2*J))*(p:ℝ)⁻¹ := by
      field_simp

/-- The weighted Chebyshev lower bound implies the exact reciprocal-prime
lower bound in note (29.32), with the real-log normalization unchanged. -/
theorem dyadicPrimeReciprocalLower29_32_of_chebyshev
    (hcheb : DyadicChebyshevLogPrimeLower) :
    DyadicPrimeReciprocalLower29_32 := by
  obtain ⟨a, J₀, ha, hJ₀, hlarge⟩ := hcheb
  let c := a/4
  refine ⟨c, J₀, by dsimp [c]; positivity, hJ₀, ?_⟩
  intro J hJJ₀
  have hJ : 2 ≤ J := hJ₀.trans hJJ₀
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have hlogJ : 0 < Real.log J := Real.log_pos (by linarith)
  have h2Jpos : 0 < 2*J := by positivity
  have hlog2J : 0 < Real.log (2*J) := Real.log_pos (by nlinarith)
  have hlog2 : Real.log 2 ≤ Real.log J :=
    Real.log_le_log (by norm_num) hJ
  have hlogSplit : Real.log (2*J) = Real.log 2 + Real.log J := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hJpos.ne']
  have hlog2Jle : Real.log (2*J) ≤ 2*Real.log J := by
    rw [hlogSplit]
    linarith
  have hmass := hlarge J hJJ₀
  have hupper := dyadicPrimeLogMass_le_reciprocal hJ
  have hcombined : a*J ≤
      (2*J*Real.log (2*J))*primeReciprocalSum J (2*J) (1/2) :=
    hmass.trans hupper
  have hrecip : a/(2*Real.log (2*J)) ≤
      primeReciprocalSum J (2*J) (1/2) := by
    have hden : 0 < 2*J*Real.log (2*J) := by positivity
    have hquot : (a*J)/(2*J*Real.log (2*J)) ≤
        primeReciprocalSum J (2*J) (1/2) := by
      apply (div_le_iff₀ hden).2
      nlinarith
    convert hquot using 1
    field_simp
  have hdenCompare : 2*Real.log (2*J) ≤ 4*Real.log J := by linarith
  have hleft : c/Real.log J ≤ a/(2*Real.log (2*J)) := by
    dsimp [c]
    rw [div_div]
    exact (div_le_div_iff₀ (by positivity : 0 < 4*Real.log J)
      (by positivity : 0 < 2*Real.log (2*J))).2 (by
        nlinarith)
  exact hleft.trans hrecip

theorem dyadicPrimeReciprocalLower29_32_of_thetaIncrement
    (htheta : DyadicChebyshevThetaIncrementLower) :
    DyadicPrimeReciprocalLower29_32 :=
  dyadicPrimeReciprocalLower29_32_of_chebyshev
    (dyadicChebyshevLogPrimeLower_of_thetaIncrement htheta)

theorem dyadicPrimeReciprocalLower29_32_of_linearChebyshev
    (hlinear : ChebyshevThetaLinearLowerAboveLogTwo) :
    DyadicPrimeReciprocalLower29_32 :=
  dyadicPrimeReciprocalLower29_32_of_thetaIncrement
    (dyadicChebyshevThetaIncrementLower_of_linearLower hlinear)

end

end GuthMaynardJutilaLemma29NineKTwo

#print axioms GuthMaynardJutilaLemma29NineKTwo.dyadicPrimeLogMass_le_reciprocal
#print axioms GuthMaynardJutilaLemma29NineKTwo.dyadicPrimeReciprocalLower29_32_of_chebyshev
#print axioms GuthMaynardJutilaLemma29NineKTwo.dyadicPrimeReciprocalLower29_32_of_thetaIncrement
#print axioms GuthMaynardJutilaLemma29NineKTwo.dyadicPrimeReciprocalLower29_32_of_linearChebyshev
