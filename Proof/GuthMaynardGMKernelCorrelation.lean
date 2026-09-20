import CGLProofDAG
import GoldfeldPolyaVinogradovKernel
import GuthMaynardGMClassicalKernel
import HuxleyHalaszFront

open scoped BigOperators
open CGLProofDAG

noncomputable section
namespace TrueShell

def GMFiniteShell : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℝ) (N : ℕ) (W : Finset ℝ),
      1 ≤ N → 1 ≤ L → OneSeparated W →
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ L) →
      ∀ t ∈ W,
        (∑ u ∈ W,
          ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
            Real.sqrt (N : ℝ))) ≤
          C * ((N : ℝ) * Real.log (2 * L) +
            (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))

private theorem right_floor_inj {W : Finset ℝ} (hsep : OneSeparated W)
    {a : ℝ} : Set.InjOn (fun b : ℝ => Nat.floor (b - a))
      {b | b ∈ W ∧ a < b} := by
  intro b hb c hc heq
  change Nat.floor (b - a) = Nat.floor (c - a) at heq
  have hbu := Nat.lt_floor_add_one (b - a)
  have hcu := Nat.lt_floor_add_one (c - a)
  have hbl : (Nat.floor (b - a) : ℝ) ≤ b - a :=
    Nat.floor_le (sub_nonneg.mpr hb.2.le)
  have hcl : (Nat.floor (c - a) : ℝ) ≤ c - a :=
    Nat.floor_le (sub_nonneg.mpr hc.2.le)
  have hbu' : b - a < (Nat.floor (c - a) : ℝ) + 1 := by simpa [heq] using hbu
  have hcu' : c - a < (Nat.floor (b - a) : ℝ) + 1 := by simpa [heq] using hcu
  have hbc : |b - c| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  by_contra hne
  exact (not_lt_of_ge (hsep b hb.1 c hc.1 hne)) hbc

private theorem left_floor_inj {W : Finset ℝ} (hsep : OneSeparated W)
    {a : ℝ} : Set.InjOn (fun b : ℝ => Nat.floor (a - b))
      {b | b ∈ W ∧ b < a} := by
  intro b hb c hc heq
  change Nat.floor (a - b) = Nat.floor (a - c) at heq
  have hbu := Nat.lt_floor_add_one (a - b)
  have hcu := Nat.lt_floor_add_one (a - c)
  have hbl : (Nat.floor (a - b) : ℝ) ≤ a - b :=
    Nat.floor_le (sub_nonneg.mpr hb.2.le)
  have hcl : (Nat.floor (a - c) : ℝ) ≤ a - c :=
    Nat.floor_le (sub_nonneg.mpr hc.2.le)
  have hbu' : a - b < (Nat.floor (a - c) : ℝ) + 1 := by simpa [heq] using hbu
  have hcu' : a - c < (Nat.floor (a - b) : ℝ) + 1 := by simpa [heq] using hcu
  have hbc : |b - c| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  by_contra hne
  exact (not_lt_of_ge (hsep b hb.1 c hc.1 hne)) hbc

private theorem recip_side
    {L : ℝ} {W : Finset ℝ} (hL : 1 ≤ L)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ L) {t : ℝ} (ht : t ∈ W)
    (hright : ∀ u ∈ W, t < u →
      (∑ v ∈ W.filter (fun v => t < v),
        (1 : ℝ) / (1 + |v - t|)) ≤ 4 * Real.log (2 * L)) :
    True := by trivial

private theorem reciprocal_bound
    {L : ℝ} {W : Finset ℝ} (hL : 1 ≤ L)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ L) {t : ℝ} (ht : t ∈ W) :
    (∑ u ∈ W, (1 : ℝ) / (1 + |u - t|)) ≤ 10 * Real.log (2 * L) := by
  classical
  let sR := W.filter (fun u => t < u)
  let sL := W.filter (fun u => u < t)
  let K : ℕ := Nat.floor L
  have hL0 : 0 ≤ L := by linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hRmem : ∀ u ∈ sR, Nat.floor (u - t) ∈ Finset.Icc 1 (K + 1) := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    have htu : 0 ≤ u - t := by linarith
    have hfloorpos : 1 ≤ Nat.floor (u - t) := by
      apply Nat.le_floor
      have hs := hsep t ht u hu'.1 (Ne.symm (ne_of_gt hu'.2))
      rw [abs_sub_comm, abs_of_nonneg htu] at hs
      norm_num at hs ⊢
      exact hs
    have hut : u - t ≤ L := by linarith [(hheight t ht).1, (hheight u hu'.1).2]
    exact Finset.mem_Icc.mpr ⟨hfloorpos,
      (Nat.floor_mono hut).trans (Nat.le_succ _)
      ⟩
  have hLmem : ∀ u ∈ sL, Nat.floor (t - u) ∈ Finset.Icc 1 (K + 1) := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    have htu : 0 ≤ t - u := by linarith
    have hfloorpos : 1 ≤ Nat.floor (t - u) := by
      apply Nat.le_floor
      have hs := hsep t ht u hu'.1 (Ne.symm (ne_of_lt hu'.2))
      rw [abs_of_nonneg (sub_nonneg.mpr hu'.2.le)] at hs
      norm_num at hs ⊢
      exact hs
    have hut : t - u ≤ L := by linarith [(hheight t ht).2, (hheight u hu'.1).1]
    exact Finset.mem_Icc.mpr ⟨hfloorpos,
      (Nat.floor_mono hut).trans (Nat.le_succ _)
      ⟩
  have hRinj : Set.InjOn (fun u : ℝ => Nat.floor (u - t)) (sR : Set ℝ) := by
    intro u hu v hv heq
    exact right_floor_inj hsep
      ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
      ⟨(Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩ heq
  have hLinj : Set.InjOn (fun u : ℝ => Nat.floor (t - u)) (sL : Set ℝ) := by
    intro u hu v hv heq
    exact left_floor_inj hsep
      ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
      ⟨(Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩ heq
  have hsideR : (∑ u ∈ sR, (1 : ℝ) / (1 + |u - t|)) ≤
      4 * Real.log (2 * L) := by
    have hterm : ∀ u ∈ sR,
        (1 : ℝ) / (1 + |u - t|) ≤ 1 / (Nat.floor (u - t) : ℝ) := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have hfl := Nat.floor_le (show 0 ≤ u - t by linarith)
      have hp : 0 < (Nat.floor (u - t) : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp (hRmem u hu)).1
      apply (div_le_div_iff₀ (by positivity) hp).2
      rw [abs_of_nonneg (sub_nonneg.mpr hu'.2.le)]
      linarith [hfl]
    calc
      (∑ u ∈ sR, (1 : ℝ) / (1 + |u - t|)) ≤
          ∑ u ∈ sR, 1 / (Nat.floor (u - t) : ℝ) := by
            apply Finset.sum_le_sum; intro u hu; exact hterm u hu
      _ = ∑ n ∈ sR.image (fun u : ℝ => Nat.floor (u - t)),
          1 / (n : ℝ) := by
            exact (Finset.sum_image (f := fun n : ℕ => 1 / (n : ℝ)) hRinj).symm
      _ ≤ ∑ n ∈ Finset.Icc 1 (K + 1), 1 / (n : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              rw [Finset.mem_image] at hn
              obtain ⟨u, hu, rfl⟩ := hn
              exact hRmem u hu
            · intro n _ _; positivity
      _ ≤ 1 + Real.log (K + 1) := by
            have hh := harmonic_le_one_add_log (K + 1)
            simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
              Rat.cast_natCast, Nat.cast_add, Nat.cast_one, one_div] using hh
      _ ≤ 4 * Real.log (2 * L) := by
            have hK : (K : ℝ) ≤ L := Nat.floor_le hL0
            have hKL : (K + 1 : ℝ) ≤ 2 * L := by norm_num; nlinarith
            have hlog := Real.log_le_log (by positivity : (0 : ℝ) < K + 1) hKL
            have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
            have hlogmul : Real.log (2 * L) = Real.log 2 + Real.log L := by
              rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : L ≠ 0)]
            rw [hlogmul]
            nlinarith
  have hsideL : (∑ u ∈ sL, (1 : ℝ) / (1 + |u - t|)) ≤
      4 * Real.log (2 * L) := by
    have hterm : ∀ u ∈ sL,
        (1 : ℝ) / (1 + |u - t|) ≤ 1 / (Nat.floor (t - u) : ℝ) := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have hfl := Nat.floor_le (show 0 ≤ t - u by linarith)
      have hp : 0 < (Nat.floor (t - u) : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp (hLmem u hu)).1
      apply (div_le_div_iff₀ (by positivity) hp).2
      rw [abs_of_nonpos (sub_nonpos.mpr hu'.2.le)]
      linarith [hfl]
    calc
      (∑ u ∈ sL, (1 : ℝ) / (1 + |u - t|)) ≤
          ∑ u ∈ sL, 1 / (Nat.floor (t - u) : ℝ) := by
            apply Finset.sum_le_sum; intro u hu; exact hterm u hu
      _ = ∑ n ∈ sL.image (fun u : ℝ => Nat.floor (t - u)),
          1 / (n : ℝ) := by
            exact (Finset.sum_image (f := fun n : ℕ => 1 / (n : ℝ)) hLinj).symm
      _ ≤ ∑ n ∈ Finset.Icc 1 (K + 1), 1 / (n : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              rw [Finset.mem_image] at hn
              obtain ⟨u, hu, rfl⟩ := hn
              exact hLmem u hu
            · intro n _ _; positivity
      _ ≤ 1 + Real.log (K + 1) := by
            have hh := harmonic_le_one_add_log (K + 1)
            simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
              Rat.cast_natCast, Nat.cast_add, Nat.cast_one, one_div] using hh
      _ ≤ 4 * Real.log (2 * L) := by
            have hK : (K : ℝ) ≤ L := Nat.floor_le hL0
            have hKL : (K + 1 : ℝ) ≤ 2 * L := by norm_num; nlinarith
            have hlog := Real.log_le_log (by positivity : (0 : ℝ) < K + 1) hKL
            have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
            have hlogmul : Real.log (2 * L) = Real.log 2 + Real.log L := by
              rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : L ≠ 0)]
            rw [hlogmul]
            nlinarith
  have hzero : (1 : ℝ) / (1 + |t - t|) ≤ 2 * Real.log (2 * L) := by
    rw [sub_self, abs_zero]
    have hlogmono : Real.log 2 ≤ Real.log (2 * L) := by
      apply Real.log_le_log (by norm_num); nlinarith
    nlinarith [hlog2]
  have hpart : W = insert t sR ∪ sL := by
    ext u
    constructor
    · intro hu
      by_cases hut : u = t
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr (Or.inl hut)))
      · by_cases htu : t < u
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_filter.mpr ⟨hu, htu⟩))))
        · exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hu,
              lt_of_le_of_ne (le_of_not_gt htu) hut⟩))
    · intro hu
      rcases Finset.mem_union.mp hu with hu | hu
      · rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ht
        · exact (Finset.mem_filter.mp hu).1
      · exact (Finset.mem_filter.mp hu).1
  have hdisj : Disjoint (insert t sR) sL := by
    rw [Finset.disjoint_left]
    intro u hu hv
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact (lt_irrefl _ (Finset.mem_filter.mp hv).2)
    · exact (lt_irrefl _ (lt_trans (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hv).2))
  rw [hpart, Finset.sum_union hdisj, Finset.sum_insert]
  · simp only [sub_self, abs_zero]
    have hzero' := hzero
    simp only [sub_self, abs_zero] at hzero'
    nlinarith [hsideR, hsideL, hzero']
  · intro hu
    exact (lt_irrefl _ (Finset.mem_filter.mp hu).2)

def GMFiniteShell16 : Prop :=
  ∀ (L : ℝ) (N : ℕ) (W : Finset ℝ),
    1 ≤ N → 1 ≤ L → OneSeparated W →
    (∀ t ∈ W, 0 ≤ t ∧ t ≤ L) →
    ∀ t ∈ W,
      (∑ u ∈ W,
        ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
          Real.sqrt (N : ℝ))) ≤
        16 * ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))

theorem gmFiniteShell16 : GMFiniteShell16 := by
  intro L N W hN hL hsep hheight t ht
  have hrec := reciprocal_bound hL hsep hheight ht
  have hsqrt : ∀ u ∈ W, Real.sqrt |u - t| ≤ Real.sqrt L := by
    intro u hu
    apply Real.sqrt_le_sqrt
    rw [abs_le]
    constructor <;> linarith [(hheight u hu).1, (hheight u hu).2,
      (hheight t ht).1, (hheight t ht).2]
  calc
    (∑ u ∈ W,
      ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
        Real.sqrt (N : ℝ))) ≤
      (N : ℝ) * (∑ u ∈ W, (1 : ℝ) / (1 + |u - t|)) +
        ∑ u ∈ W, Real.sqrt L + ∑ u ∈ W, Real.sqrt (N : ℝ) := by
      simp only [Finset.sum_add_distrib]
      have hfirst : (∑ u ∈ W, (N : ℝ) / (1 + |u - t|)) =
          (N : ℝ) * ∑ u ∈ W, (1 : ℝ) / (1 + |u - t|) := by
        simp [div_eq_mul_inv, Finset.mul_sum]
      rw [hfirst]
      have hN0 : 0 ≤ (N : ℝ) := by positivity
      apply add_le_add
      · exact add_le_add (le_rfl) (by
          apply Finset.sum_le_sum; intro u hu; exact hsqrt u hu)
      · exact le_rfl
    _ ≤ 16 * ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
      simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      have hlog : 0 ≤ Real.log (2 * L) := (Real.log_pos (by nlinarith)).le
      have hcard : 0 ≤ (W.card : ℝ) := by positivity
      have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
      have hsN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith [hrec]

theorem gmFiniteShell : GMFiniteShell := by
  exact ⟨16, by norm_num, gmFiniteShell16⟩

end TrueShell

#print axioms TrueShell.gmFiniteShell

open scoped BigOperators ComplexConjugate
open CGLProofDAG
open GuthMaynardSectionFourTrace
open GuthMaynardGMHighValueComplement
open MAPJutilaDeterministicCore
open MAPHuxleyHalaszFront

namespace GuthMaynardGMKernelCorrelation

/-- A literal pointwise kernel majorant whose constant is fixed before all
geometric and large-value variables are introduced.  In particular, it has no
hidden dependence on `L`, `W`, or a large-value level `V`. -/
def UniformPointwiseKernelBound (Ck : ℝ) : Prop :=
  0 < Ck ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (L : ℝ), 1 ≤ L →
      ∀ (W : Finset ℝ), OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ L) →
          ∀ (t : ℝ), t ∈ W → ∀ (u : ℝ), u ∈ W →
            ‖gmDyadicKernel N (u - t)‖ ≤
              Ck * ((N : ℝ) / (1 + |u - t|) +
                Real.sqrt |u - t| + Real.sqrt (N : ℝ))

/-- The actual shell estimate, with its constant exposed as `16`. -/
def ActualGMShell16 : Prop :=
    ∀ (L : ℝ) (N : ℕ) (W : Finset ℝ),
      1 ≤ N → 1 ≤ L → OneSeparated W →
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ L) →
      ∀ t ∈ W,
        (∑ u ∈ W,
          ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
            Real.sqrt (N : ℝ))) ≤
          16 * ((N : ℝ) * Real.log (2 * L) +
            (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))

theorem actualgmFiniteShell16 : ActualGMShell16 := by
  exact TrueShell.gmFiniteShell16

/-- Literal double correlation from the pointwise kernel leaf and the actual
finite shell leaf.  The phase weights are norm one and the constant is fixed
before `N,L,W,V`. -/
theorem doubleCorrelation_le_of_uniformPointwise
    {Ck : ℝ} (hK : UniformPointwiseKernelBound Ck)
    {L : ℝ} {N : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (W : Finset ℝ) (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ L)
    (eta : ℝ → ℂ) (heta : ∀ t ∈ W, ‖eta t‖ = 1) :
    ‖∑ t ∈ W, ∑ u ∈ W,
          conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ ≤
        16 * Ck * (W.card : ℝ) *
          ((N : ℝ) * Real.log (2 * L) +
            (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
  obtain ⟨hCk, hpoint⟩ := hK
  have hshell := actualgmFiniteShell16 L N W hN hL hsep hheight
  have hpoint' : ∀ t ∈ W, ∀ u ∈ W,
      ‖gmDyadicKernel N (u - t)‖ ≤
        Ck * ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
          Real.sqrt (N : ℝ)) := by
    intro t ht u hu
    exact hpoint N hN L hL W hsep hheight t ht u hu
  have hsum : ∀ t ∈ W,
      ∑ u ∈ W, ‖gmDyadicKernel N (u - t)‖ ≤
        Ck * (16 * ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))) := by
    intro t ht
    calc
      ∑ u ∈ W, ‖gmDyadicKernel N (u - t)‖ ≤
          ∑ u ∈ W, Ck *
            ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
              Real.sqrt (N : ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hpoint' t ht u hu
      _ = Ck * ∑ u ∈ W,
            ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
              Real.sqrt (N : ℝ)) := by
        simp_rw [Finset.mul_sum]
      _ ≤ Ck * (16 * ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left (hshell t ht) hCk.le
  calc
    ‖∑ t ∈ W, ∑ u ∈ W,
        conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ ≤
      ∑ t ∈ W, ‖∑ u ∈ W,
        conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_sum_le _ _
    _ = ∑ t ∈ W, ∑ u ∈ W, ‖gmDyadicKernel N (u - t)‖ := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      have hstar : ‖(starRingEnd ℂ) (eta t)‖ = 1 := by
        calc
          ‖(starRingEnd ℂ) (eta t)‖ = ‖eta t‖ := norm_star _
          _ = 1 := heta t ht
      rw [norm_mul, norm_mul, hstar, heta u hu]
      norm_num
    _ ≤ ∑ t ∈ W, Ck *
        (16 * ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hsum t ht
    _ = 16 * Ck * (W.card : ℝ) *
        ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/- The next leaf isolates the numerical absorption after the finite Halasz
front.  The root relation `L = c V^4/N^2`, the threshold `V ≥ N^(4/5)`, and
the large-`N` hypothesis remain explicit; the two displayed square-root
inequalities are the elementary root-scale contract a later range lemma may
discharge from those hypotheses. -/
theorem gmHalaszLocalHighValues
    {Ck : ℝ} (hK : UniformPointwiseKernelBound Ck)
    {c L V : ℝ} {N : ℕ}
    (hc : 0 < c) (hLshape : L = c * V ^ 4 / (N : ℝ) ^ 2)
    (hN : 1 ≤ N) (hNlarge : (100 : ℝ) ≤ (N : ℝ))
    (hV : 0 < V)
    (hVhigh : Real.rpow (N : ℝ) (4 / 5 : ℝ) ≤ V)
    (hL : 1 ≤ L)
    (hrootL : Real.sqrt L ≤ V ^ 2 / (64 * Ck * (N : ℝ)))
    (hrootN : Real.sqrt (N : ℝ) ≤ V ^ 2 / (64 * Ck * (N : ℝ)))
    (W : Finset ℝ) (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ L)
    (eta : ℝ → ℂ) (heta : ∀ t ∈ W, ‖eta t‖ = 1)
    (hfront : ((W.card : ℝ) * V) ^ 2 ≤
      (N : ℝ) *
        ‖∑ t ∈ W, ∑ u ∈ W,
          conj (eta t) * eta u * gmDyadicKernel N (u - t)‖) :
    (W.card : ℝ) ≤
      32 * Ck * (N : ℝ) ^ 2 * Real.log (2 * L) / V ^ 2 := by
  have hCk : 0 < Ck := hK.1
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
  have hR0 : 0 ≤ (W.card : ℝ) := by positivity
  have hdouble := doubleCorrelation_le_of_uniformPointwise hK hN hL W
    hsep hheight eta heta
  by_cases hR : W.card = 0
  · have hlog : 0 ≤ Real.log (2 * L) := by
      apply (Real.log_pos (by nlinarith)).le
    simp only [hR, Nat.cast_zero, zero_mul]
    positivity
  · have hRpos : 0 < (W.card : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hR)
    have hquad : ((W.card : ℝ) * V) ^ 2 ≤
        (N : ℝ) *
          (16 * Ck * (W.card : ℝ) *
            ((N : ℝ) * Real.log (2 * L) +
              (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))) := by
      exact hfront.trans
        (mul_le_mul_of_nonneg_left hdouble hN0)
    have hquad' : (W.card : ℝ) * V ^ 2 ≤
        16 * Ck * (N : ℝ) *
          ((N : ℝ) * Real.log (2 * L) +
            (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
      apply (le_of_mul_le_mul_left ?_ hRpos)
      calc
        (W.card : ℝ) * ((W.card : ℝ) * V ^ 2) =
            ((W.card : ℝ) * V) ^ 2 := by ring
        _ ≤ _ := hquad
        _ = (W.card : ℝ) *
            (16 * Ck * (N : ℝ) *
              ((N : ℝ) * Real.log (2 * L) +
                (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))) := by ring
    have hroot : 16 * Ck * (N : ℝ) *
          (Real.sqrt L + Real.sqrt (N : ℝ)) ≤ V ^ 2 / 2 := by
      have hfac : 0 < 64 * Ck * (N : ℝ) := by positivity
      have hrootL' := (le_div_iff₀ hfac).mp hrootL
      have hrootN' := (le_div_iff₀ hfac).mp hrootN
      nlinarith [add_le_add hrootL' hrootN']
    have hroot' : (W.card : ℝ) *
          (16 * Ck * (N : ℝ) *
            (Real.sqrt L + Real.sqrt (N : ℝ))) ≤
        (W.card : ℝ) * (V ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hroot hR0
    apply (le_div_iff₀ hV2).2
    nlinarith [hquad', hroot']

end GuthMaynardGMKernelCorrelation

#print axioms GuthMaynardGMKernelCorrelation.doubleCorrelation_le_of_uniformPointwise
#print axioms GuthMaynardGMKernelCorrelation.gmHalaszLocalHighValues
