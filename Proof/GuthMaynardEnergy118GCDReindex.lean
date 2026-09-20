import GuthMaynardLengthComparison
import GuthMaynardHeathBrownIccIocEndpointAdapter

open scoped BigOperators

namespace GuthMaynardEnergy118GCD

open GuthMaynardLengthComparison
open GuthMaynardHeathBrownIccIocEndpointAdapter
open GuthMaynardRatioKernelIdentity

noncomputable section

abbrev Pair := ℕ × ℕ

def dyadicPairs (N : ℕ) : Finset Pair :=
  (Finset.Ioc N (2 * N)).product (Finset.Ioc N (2 * N))

def gcdClass (N d : ℕ) : Finset Pair :=
  (dyadicPairs N).filter (fun p => p.1.gcd p.2 = d)

/-- Primitive coordinates whose scaled pair lies in the original open-left
dyadic rectangle.  The endpoint inequalities are retained literally. -/
def reducedPairs (N d : ℕ) : Finset Pair :=
  ((Finset.Icc 1 (2 * N)).product (Finset.Icc 1 (2 * N))).filter
    (fun p => N < d * p.1 ∧ d * p.1 ≤ 2 * N ∧
      N < d * p.2 ∧ d * p.2 ≤ 2 * N ∧ p.1.Coprime p.2)

def scalePair (d : ℕ) (p : Pair) : Pair := (d * p.1, d * p.2)

private lemma scalePair_mem_gcdClass
    {N d : ℕ} (hd : 1 ≤ d) {p : Pair}
    (hp : p ∈ reducedPairs N d) :
    scalePair d p ∈ gcdClass N d := by
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hbounds⟩
  rcases hbounds with ⟨haL, haU, hbL, hbU, hab⟩
  rw [gcdClass, Finset.mem_filter]
  constructor
  · apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Ioc.mpr ⟨haL, haU⟩,
      Finset.mem_Ioc.mpr ⟨hbL, hbU⟩⟩
  · dsimp [scalePair]
    rw [Nat.gcd_mul_left, hab.gcd_eq_one, mul_one]

private lemma gcdClass_mem_scaled_preimage
    {N d : ℕ} (hd : 1 ≤ d) {p : Pair}
    (hp : p ∈ gcdClass N d) :
    ∃ q ∈ reducedPairs N d, scalePair d q = p := by
  rcases p with ⟨m, n⟩
  rw [gcdClass, Finset.mem_filter] at hp
  rcases Finset.mem_product.mp hp.1 with ⟨hm, hn⟩
  have hmI := Finset.mem_Ioc.mp hm
  have hnI := Finset.mem_Ioc.mp hn
  have hmpos : 0 < m := by omega
  have hnpos : 0 < n := by omega
  have hdm : d ∣ m := by
    rw [← hp.2]
    exact Nat.gcd_dvd_left m n
  have hdn : d ∣ n := by
    rw [← hp.2]
    exact Nat.gcd_dvd_right m n
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hmqpos : 0 < m / d := Nat.div_pos
    (Nat.le_of_dvd (by omega) hdm) hdpos
  have hnqpos : 0 < n / d := Nat.div_pos
    (Nat.le_of_dvd (by omega) hdn) hdpos
  have hcop : (m / d).Coprime (n / d) := by
    have h := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left n hmpos)
    rw [hp.2] at h
    exact h
  have hmqle : m / d ≤ 2 * N := (Nat.div_le_self m d).trans hmI.2
  have hnqle : n / d ≤ 2 * N := (Nat.div_le_self n d).trans hnI.2
  have hscaleM : d * (m / d) = m := Nat.mul_div_cancel' hdm
  have hscaleN : d * (n / d) = n := Nat.mul_div_cancel' hdn
  refine ⟨(m / d, n / d), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hmqpos.ne', hmqle⟩,
        Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hnqpos.ne', hnqle⟩⟩
    · exact ⟨by simpa [hscaleM] using hmI.1,
        by simpa [hscaleM] using hmI.2,
        by simpa [hscaleN] using hnI.1,
        by simpa [hscaleN] using hnI.2, hcop⟩
  · simp [scalePair, hscaleM, hscaleN]

private lemma scalePair_injective
    {d : ℕ} (hd : 1 ≤ d) : Function.Injective (scalePair d) := by
  intro p q hpq
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, e⟩
  have hfst := congrArg Prod.fst hpq
  have hsnd := congrArg Prod.snd hpq
  dsimp [scalePair] at hfst hsnd
  exact Prod.ext (Nat.mul_left_cancel hd hfst) (Nat.mul_left_cancel hd hsnd)

/-- Scaling by `d` is a bijection from the literal reduced pairs onto the
original dyadic pairs with exact gcd `d`. -/
theorem scalePair_bijective_gcdClass
    {N d : ℕ} (hd : 1 ≤ d) :
    (∀ p ∈ reducedPairs N d, scalePair d p ∈ gcdClass N d) ∧
    (Function.Injective (scalePair d)) ∧
    (∀ p ∈ gcdClass N d, ∃ q ∈ reducedPairs N d, scalePair d q = p) := by
  exact ⟨fun p hp => scalePair_mem_gcdClass hd hp,
    scalePair_injective hd,
    fun p hp => gcdClass_mem_scaled_preimage hd hp⟩

/-! The following identity is the finite sum form of the preceding bijection.
It is deliberately generic, so later bounds can choose the exact ratio kernel
or another nonnegative moment without changing the endpoint bookkeeping. -/
theorem sum_gcdClass_eq_sum_reduced
    {N d : ℕ} (hd : 1 ≤ d) {α : Type*} [AddCommMonoid α]
    (F : Pair → α) :
    (∑ p ∈ reducedPairs N d, F (scalePair d p)) =
      ∑ p ∈ gcdClass N d, F p := by
  apply Finset.sum_bij (fun p _ => scalePair d p)
  · intro p hp
    exact scalePair_mem_gcdClass hd hp
  · intro p hp q hq heq
    exact scalePair_injective hd heq
  · intro p hp
    rcases gcdClass_mem_scaled_preimage hd hp with ⟨q, hq, hscale⟩
    exact ⟨q, hq, hscale⟩
  · intro p hp
    rfl

def ratioMomentTermPow (e : ℕ) (W : Finset ℝ) (p : Pair) : ℝ :=
  ‖ratioDirichletKernel W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ e

def ratioMomentTerm (W : Finset ℝ) (p : Pair) : ℝ :=
  ratioMomentTermPow 2 W p

/-- Exact ratio-kernel second-moment reindexing.  The ratio is literally
`a/b = (d*a)/(d*b)`; no floor or surrogate interval occurs. -/
private lemma ratioMomentTermPow_scale_eq
    (e : ℕ) (W : Finset ℝ) {d : ℕ} (hd : 1 ≤ d) (p : Pair) :
    ratioMomentTermPow e W (scalePair d p) = ratioMomentTermPow e W p := by
  dsimp [ratioMomentTermPow, scalePair]
  rw [ratioDirichletKernel_scale W d p.1 p.2 (by omega)]

theorem ratioKernelMomentPow_gcdClass_eq_reduced
    (e : ℕ) (W : Finset ℝ) {N d : ℕ} (hd : 1 ≤ d) :
    (∑ p ∈ gcdClass N d, ratioMomentTermPow e W p) =
      ∑ p ∈ reducedPairs N d, ratioMomentTermPow e W p := by
  calc
    (∑ p ∈ gcdClass N d, ratioMomentTermPow e W p) =
        ∑ p ∈ reducedPairs N d, ratioMomentTermPow e W (scalePair d p) :=
      (sum_gcdClass_eq_sum_reduced hd (ratioMomentTermPow e W)).symm
    _ = ∑ p ∈ reducedPairs N d, ratioMomentTermPow e W p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact ratioMomentTermPow_scale_eq e W hd p

theorem ratioKernelMoment_gcdClass_eq_reduced
    (W : Finset ℝ) {N d : ℕ} (hd : 1 ≤ d) :
    (∑ p ∈ gcdClass N d, ratioMomentTerm W p) =
      ∑ p ∈ reducedPairs N d, ratioMomentTerm W p := by
  simpa only [ratioMomentTerm] using
    ratioKernelMomentPow_gcdClass_eq_reduced 2 W hd

private def taggedGcdPairs (N : ℕ) : Finset (ℕ × Pair) :=
  ((Finset.Icc 1 (2 * N)).product (dyadicPairs N)).filter
    (fun q => q.2.1.gcd q.2.2 = q.1)

private lemma sum_taggedGcdPairs_eq_sum_classes
    {N : ℕ} {α : Type*} [AddCommMonoid α] (F : Pair → α) :
    (∑ q ∈ taggedGcdPairs N, F q.2) =
      ∑ d ∈ Finset.Icc 1 (2 * N), ∑ p ∈ gcdClass N d, F p := by
  simp [taggedGcdPairs, gcdClass, Finset.sum_product, Finset.sum_filter]

private lemma dyadicPair_mem_taggedGcdPairs
    {N : ℕ} (hN : 1 ≤ N) {p : Pair} (hp : p ∈ dyadicPairs N) :
    (p.1.gcd p.2, p) ∈ taggedGcdPairs N := by
  rcases Finset.mem_product.mp hp with ⟨hm, hn⟩
  have hmI := Finset.mem_Ioc.mp hm
  have hnI := Finset.mem_Ioc.mp hn
  have hgpos : 0 < p.1.gcd p.2 :=
    Nat.gcd_pos_of_pos_left p.2 (by omega)
  have hgle : p.1.gcd p.2 ≤ 2 * N :=
    (Nat.gcd_le_left p.2 (by omega)).trans hmI.2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hgpos.ne', hgle⟩, hp⟩, rfl⟩

/-- Exact partition of the original dyadic rectangle by the integer gcd. -/
theorem dyadicPairs_sum_eq_sum_gcdClasses
    {N : ℕ} (hN : 1 ≤ N) {α : Type*} [AddCommMonoid α]
    (F : Pair → α) :
    (∑ p ∈ dyadicPairs N, F p) =
      ∑ d ∈ Finset.Icc 1 (2 * N), ∑ p ∈ gcdClass N d, F p := by
  calc
    (∑ p ∈ dyadicPairs N, F p) =
        ∑ q ∈ taggedGcdPairs N, F q.2 := by
      apply Finset.sum_bij (fun p _ => (p.1.gcd p.2, p))
      · intro p hp
        exact dyadicPair_mem_taggedGcdPairs hN hp
      · intro p hp q hq heq
        exact congrArg Prod.snd heq
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqprod, hqgcd⟩
        rcases Finset.mem_product.mp hqprod with ⟨hdq, hpq⟩
        exact ⟨q.2, hpq, by
          exact Prod.ext hqgcd rfl⟩
      · intro p hp
        rfl
    _ = ∑ d ∈ Finset.Icc 1 (2 * N), ∑ p ∈ gcdClass N d, F p :=
      sum_taggedGcdPairs_eq_sum_classes F

/-- Total ratio-kernel second moment decomposes exactly into reduced gcd
classes, with no rounded `N/d` interval. -/
theorem dyadicRatioKernelMoment_eq_sum_reducedGcdClasses
    (W : Finset ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ dyadicPairs N, ratioMomentTerm W p) =
      ∑ d ∈ Finset.Icc 1 (2 * N),
        ∑ p ∈ reducedPairs N d, ratioMomentTerm W p := by
  rw [dyadicPairs_sum_eq_sum_gcdClasses hN (ratioMomentTerm W)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ratioKernelMoment_gcdClass_eq_reduced W (by
    exact Finset.mem_Icc.mp hd |>.1)]

theorem dyadicRatioKernelMomentPow_eq_sum_reducedGcdClasses
    (e : ℕ) (W : Finset ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ dyadicPairs N, ratioMomentTermPow e W p) =
      ∑ d ∈ Finset.Icc 1 (2 * N),
        ∑ p ∈ reducedPairs N d, ratioMomentTermPow e W p := by
  rw [dyadicPairs_sum_eq_sum_gcdClasses hN (ratioMomentTermPow e W)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ratioKernelMomentPow_gcdClass_eq_reduced e W
    (Finset.mem_Icc.mp hd |>.1)]

end
end GuthMaynardEnergy118GCD

#print axioms GuthMaynardEnergy118GCD.scalePair_bijective_gcdClass
#print axioms GuthMaynardEnergy118GCD.sum_gcdClass_eq_sum_reduced
#print axioms GuthMaynardEnergy118GCD.ratioKernelMoment_gcdClass_eq_reduced
#print axioms GuthMaynardEnergy118GCD.ratioKernelMomentPow_gcdClass_eq_reduced
#print axioms GuthMaynardEnergy118GCD.dyadicPairs_sum_eq_sum_gcdClasses
#print axioms GuthMaynardEnergy118GCD.dyadicRatioKernelMoment_eq_sum_reducedGcdClasses
#print axioms GuthMaynardEnergy118GCD.dyadicRatioKernelMomentPow_eq_sum_reducedGcdClasses
