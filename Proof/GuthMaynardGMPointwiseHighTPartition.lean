import GuthMaynardGMPointwiseKernel
import GuthMaynardDiscreteBandCount

open scoped BigOperators ComplexConjugate
open GuthMaynardSectionFourTrace
open GuthMaynardGMPointwiseKernel

noncomputable section
namespace GuthMaynardGMPointwiseHighTPartition

/-- The literal increment of the phase from `n` to `n+1`. -/
def gmIncrement (t : ℝ) (n : ℕ) : ℝ :=
  t * Real.log (1 + 1 / (n : ℝ))

def gmStepPhase (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * gmIncrement t n)

private theorem log_succ_sub_log
    {n : ℕ} (hn : 0 < n) :
  Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) =
      Real.log (1 + 1 / (n : ℝ)) := by
  rw [← Real.log_div (by positivity : ((n : ℝ) + 1) ≠ 0)
    (ne_of_gt (by exact_mod_cast hn : (0 : ℝ) < n))]
  congr 1
  field_simp

/-- Exact multiplicative phase recurrence, with no continuous surrogate. -/
theorem sourcePhase_succ_eq_mul_gmStepPhase
    {t : ℝ} {n : ℕ} (hn : 0 < n) :
    sourcePhase (n + 1) t = sourcePhase n t * gmStepPhase t n := by
  unfold GuthMaynardSectionFourTrace.sourcePhase gmStepPhase gmIncrement
  rw [← Complex.exp_add]
  congr 1
  have hlog := log_succ_sub_log hn
  norm_num [Nat.cast_add, Nat.cast_one]
  have hlogn : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)).symm
  rw [hlogn]
  have hlog' : Real.log ((n : ℝ) + 1) =
      Real.log (n : ℝ) + Real.log (1 + 1 / (n : ℝ)) := by
    linarith [hlog]
  rw [hlog']
  push_cast
  ring

theorem gmIncrement_succ_lt
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) :
    gmIncrement t (n + 1) < gmIncrement t n := by
  unfold gmIncrement
  norm_num [Nat.cast_add, Nat.cast_one]
  apply mul_lt_mul_of_pos_left _ ht
  apply Real.strictMonoOn_log
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact Set.mem_Ioi.mpr (by positivity)
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hnp : (n : ℝ) < n + 1 := by norm_num
    apply (add_lt_add_iff_left (1 : ℝ)).2
    simpa [one_div] using (one_div_lt_one_div_of_lt hnR hnp)

/- The literal adjacent increment gap.  This is the finite difference input
used by the resonance count, and is proved before any kernel estimate. -/
theorem gmIncrement_gap_lower
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) :
    t / ((n : ℝ) + 1) ^ 2 ≤
      gmIncrement t n - gmIncrement t (n + 1) := by
  unfold gmIncrement
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 0 < 1 + 1 / ((n : ℝ) * (n + 2)) := by positivity
  have hloglower : 1 / ((n : ℝ) + 1) ^ 2 ≤
      Real.log (1 + 1 / ((n : ℝ) * (n + 2))) := by
    have hlog := Real.one_sub_inv_le_log_of_pos hratio
    have halg : 1 / ((n : ℝ) + 1) ^ 2 ≤
        1 - (1 + 1 / ((n : ℝ) * (n + 2)))⁻¹ := by
      field_simp
      ring_nf
      nlinarith [sq_nonneg (n : ℝ)]
    exact halg.trans hlog
  have hlogid :
      Real.log (1 + 1 / (n : ℝ)) -
        Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) =
      Real.log (1 + 1 / ((n : ℝ) * (n + 2))) := by
    rw [← Real.log_div]
    · congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    · positivity
    · positivity
  have hmul := mul_le_mul_of_nonneg_left hloglower ht.le
  calc
    t / ((n : ℝ) + 1) ^ 2 ≤
        t * Real.log (1 + 1 / ((n : ℝ) * (n + 2))) := by
      simpa [div_eq_mul_inv] using hmul
    _ = t * (Real.log (1 + 1 / (n : ℝ)) -
          Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ))) := by
      rw [hlogid]
    _ = t * Real.log (1 + 1 / (n : ℝ)) -
          t * Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) := by ring

theorem gmIncrement_pairwise_gap
    {N : ℕ} {t : ℝ} (ht : 0 < t) (hN : 1 ≤ N)
    {a b : ℕ} (ha : N < a) (hb : b ≤ 2 * N) (hab : a ≤ b) :
    (t / (9 * (N : ℝ) ^ 2)) * ((b : ℝ) - a) ≤
      gmIncrement t a - gmIncrement t b := by
  let g : ℝ := t / (9 * (N : ℝ) ^ 2)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hg : 0 < g := by
    dsimp [g]
    positivity
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have hbN : N < b := lt_of_lt_of_le ha hab
      have hbmem : b ∈ Finset.Ioc N (2 * N) :=
        Finset.mem_Ioc.mpr ⟨hbN, le_trans (Nat.le_succ b) hb⟩
      have hstep := gmIncrement_gap_lower ht (Nat.zero_lt_of_lt hbN)
      have hstep' : g ≤ gmIncrement t b - gmIncrement t (b + 1) := by
        dsimp [g]
        have hden : (b : ℝ) + 1 ≤ (2 * (N : ℝ)) + 1 := by
          exact_mod_cast (Nat.succ_le_succ (le_trans (Nat.le_succ b) hb))
        have hsq : ((b : ℝ) + 1) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 := by
          have hNb : (b : ℝ) ≤ 2 * N := by exact_mod_cast (le_trans (Nat.le_succ b) hb)
          have hlin : (b : ℝ) + 1 ≤ 3 * (N : ℝ) := by
            calc
              (b : ℝ) + 1 ≤ 2 * (N : ℝ) + 1 := by linarith
              _ ≤ 3 * (N : ℝ) := by linarith [hNone]
          nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ (b : ℝ) + 1) hlin]
        have hpos : 0 ≤ t / ((3 * (N : ℝ)) ^ 2) := by positivity
        have hsmall : t / ((3 * (N : ℝ)) ^ 2) ≤ t / ((b : ℝ) + 1) ^ 2 := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          nlinarith
        have heq : (3 * (N : ℝ)) ^ 2 = 9 * (N : ℝ) ^ 2 := by ring
        calc
          t / (9 * (N : ℝ) ^ 2) = t / ((3 * (N : ℝ)) ^ 2) := by rw [heq]
          _ ≤ t / ((b : ℝ) + 1) ^ 2 := hsmall
          _ ≤ gmIncrement t b - gmIncrement t (b + 1) := hstep
      have hbprev : b ≤ 2 * N := le_trans (Nat.le_succ b) hb
      calc
        t / (9 * (N : ℝ) ^ 2) * ((↑(b + 1) : ℝ) - a) =
            t / (9 * (N : ℝ) ^ 2) * ((b : ℝ) - a) +
              t / (9 * (N : ℝ) ^ 2) := by push_cast; ring
        _ ≤ (gmIncrement t a - gmIncrement t b) +
              (gmIncrement t b - gmIncrement t (b + 1)) :=
          add_le_add (ih hbprev) hstep'
        _ = gmIncrement t a - gmIncrement t (b + 1) := by ring

/-- The exact finite resonant set for the increment partition.  A point is
resonant when its increment lies within `δ` of an integer multiple of `2π`.
The complement is the set on which the finite Kusmin bound is applied. -/
noncomputable def gmResonant (N : ℕ) (t δ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (2 * N)).filter
    (fun n => ∃ k : ℤ, |gmIncrement t n - 2 * Real.pi * k| ≤ δ)

noncomputable def gmOffResonant (N : ℕ) (t δ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (2 * N)).filter
    (fun n => ¬ ∃ k : ℤ, |gmIncrement t n - 2 * Real.pi * k| ≤ δ)

noncomputable def gmResonantBand (N : ℕ) (t δ : ℝ) (k : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (2 * N)).filter
    (fun n => |gmIncrement t n - 2 * Real.pi * k| ≤ δ)

/-- The resonance/off-resonance split is an exact partition of the literal
integer range. -/
theorem gm_resonant_union_offResonant
    (N : ℕ) (t δ : ℝ) :
    gmResonant N t δ ∪ gmOffResonant N t δ = Finset.Ioc N (2 * N) := by
  classical
  ext n
  simp only [gmResonant, gmOffResonant, Finset.mem_union,
    Finset.mem_filter]
  tauto

theorem gmResonantBand_card_le
    {N : ℕ} {t δ : ℝ} (hN : 1 ≤ N) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℤ) :
    (gmResonantBand N t δ k).card ≤
      1 + 2 * δ / (t / (9 * (N : ℝ) ^ 2)) := by
  classical
  exact GuthMaynardDiscreteBandCount.card_le_one_add_two_width_div_gap
    (s := gmResonantBand N t δ k) (f := gmIncrement t)
    (c := 2 * Real.pi * k) (δ := δ)
    (g := t / (9 * (N : ℝ) ^ 2))
    (by positivity) hδ.le
    (by intro n hn; exact Finset.mem_filter.mp hn |>.2)
    (by
      intro a ha b hb hab
      have haI := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
      have hbI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
      exact gmIncrement_pairwise_gap ht hN haI.1 hbI.2 hab)

/-- A reusable finite partition/count helper for the discrete second
 derivative argument.  The hypotheses are only the monotone increment and
 adjacent-gap facts; no kernel estimate is assumed. -/
def GMResonanceCountContract : Prop :=
  ∀ (N : ℕ) (t δ : ℝ),
    1 ≤ N → N ≤ t → t ≤ (N : ℝ) ^ 2 →
    0 < δ →
    (∀ n ∈ Finset.Ioc N (2 * N),
      gmIncrement t (n + 1) < gmIncrement t n) →
    (∀ n ∈ Finset.Ioc N (2 * N),
      t / (9 * (N : ℝ) ^ 2) ≤
        gmIncrement t n - gmIncrement t (n + 1)) →
    (gmResonant N t δ).card ≤
      4 * ((t / (N : ℝ)) + 1) * (1 + 2 * δ * (9 * (N : ℝ) ^ 2 / t))

/-- The concrete scale selected by the high-t proof. -/
def gmResonanceWidth (N : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt t / N

def gmBandLabels (N : ℕ) (t : ℝ) : Finset ℤ :=
  Finset.Icc (-(Nat.ceil (t / N + 1) : ℤ)) (Nat.ceil (t / N + 1) : ℤ)

theorem gmBandLabels_card_le
    {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 0 ≤ t) :
    (gmBandLabels N t).card ≤ 2 * Nat.ceil (t / N + 1) + 1 := by
  unfold gmBandLabels
  rw [Int.card_Icc]
  omega

theorem gmIncrement_pos
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) :
    0 < gmIncrement t n := by
  unfold gmIncrement
  apply mul_pos ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply Real.log_pos
  have : 0 < 1 / (n : ℝ) := by positivity
  linarith

theorem gmIncrement_le_t_div_N
    {t : ℝ} {N n : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n) (ht : 0 ≤ t) :
    gmIncrement t n ≤ t / (N : ℝ) := by
  unfold gmIncrement
  have hNR : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le hNR (by exact_mod_cast hNn)
  have hlog : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (n : ℝ))
    nlinarith
  have hfrac : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := by
    exact one_div_le_one_div_of_le hNR (by exact_mod_cast hNn)
  exact (mul_le_mul_of_nonneg_left (hlog.trans hfrac) ht).trans_eq (by ring)

theorem gmResonant_mem_bandLabels
    {N : ℕ} {t δ : ℝ} (hN : 1 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} (hn : n ∈ gmResonant N t δ)
    {k : ℤ} (hk : |gmIncrement t n - 2 * Real.pi * k| ≤ δ)
    : k ∈ gmBandLabels N t := by
  classical
  have hn' := Finset.mem_filter.mp hn
  have hnIoc : n ∈ Finset.Ioc N (2 * N) := hn'.1
  have hnN : N ≤ n := (Finset.mem_Ioc.mp hnIoc).1.le
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_of_lt hN) hnN
  have htpos : 0 < t := lt_of_lt_of_le
    (by exact_mod_cast (Nat.zero_lt_of_lt hN)) hNt
  have hdpos := gmIncrement_pos htpos hnpos
  have ht0 : 0 ≤ t := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    linarith
  have hdle := gmIncrement_le_t_div_N hN hnN ht0
  have habs := abs_le.mp hk
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hkupper : (k : ℝ) ≤ t / (N : ℝ) + 1 := by
    have hku : 2 * Real.pi * (k : ℝ) ≤ t / (N : ℝ) + 1 := by linarith
    nlinarith [hpi]
  have hklower : -(t / (N : ℝ) + 1) ≤ (k : ℝ) := by
    have hkl : -(t / (N : ℝ) + 1) ≤ 2 * Real.pi * (k : ℝ) := by linarith
    nlinarith [hpi]
  rw [gmBandLabels, Finset.mem_Icc]
  constructor
  · have hceil : t / (N : ℝ) + 1 ≤ (Nat.ceil (t / (N : ℝ) + 1) : ℝ) := Nat.le_ceil _
    have : ((-(Nat.ceil (t / (N : ℝ) + 1) : ℤ) : ℤ) : ℝ) ≤ (k : ℝ) := by
      norm_num
      linarith
    exact_mod_cast this
  · have hceil : t / (N : ℝ) + 1 ≤ (Nat.ceil (t / (N : ℝ) + 1) : ℝ) := Nat.le_ceil _
    have : (k : ℝ) ≤ ((Nat.ceil (t / (N : ℝ) + 1) : ℤ) : ℝ) := by
      norm_num
      linarith
    exact_mod_cast this

theorem gmResonant_card_le_bandLabels
    {N : ℕ} {t δ : ℝ} (hN : 1 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (gmResonant N t δ).card ≤
      (gmBandLabels N t).card *
        (1 + 2 * δ / (t / (9 * (N : ℝ) ^ 2))) := by
  classical
  let labels := gmBandLabels N t
  let U : Finset ℕ := labels.biUnion (fun k => gmResonantBand N t δ k)
  have hsub : gmResonant N t δ ⊆ U := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    obtain ⟨k, hk⟩ := hn'.2
    have hkmem : k ∈ labels := by
      exact gmResonant_mem_bandLabels hN hNt htN hδ hδ1 hn hk
    exact Finset.mem_biUnion.mpr ⟨k, hkmem,
      Finset.mem_filter.mpr ⟨hn'.1, hk⟩⟩
  have hU : U.card ≤
      ∑ k ∈ labels, (gmResonantBand N t δ k).card := by
    exact Finset.card_biUnion_le
  have ht : 0 < t := lt_of_lt_of_le
    (by exact_mod_cast (Nat.zero_lt_of_lt hN)) hNt
  have hband : ∀ k ∈ labels,
      ((gmResonantBand N t δ k).card : ℝ) ≤
        1 + 2 * δ / (t / (9 * (N : ℝ) ^ 2)) := by
    intro k hk
    exact gmResonantBand_card_le hN ht hδ hδ1 k
  calc
    ((gmResonant N t δ).card : ℝ) ≤ U.card := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ k ∈ labels, (gmResonantBand N t δ k).card : ℕ) : ℝ) := by
      exact_mod_cast hU
    _ = ∑ k ∈ labels, ((gmResonantBand N t δ k).card : ℝ) := by simp
    _ ≤ ∑ _k ∈ labels,
        (1 + 2 * δ / (t / (9 * (N : ℝ) ^ 2))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hband k hk
    _ = (labels.card : ℝ) * (1 + 2 * δ / (t / (9 * (N : ℝ) ^ 2))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

theorem gmResonant_card_le_sqrtScale
    {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2) :
    (gmResonant N t (Real.sqrt t / N)).card ≤
      (gmBandLabels N t).card * (1 + 18 * (N : ℝ) / Real.sqrt t) := by
  have ht : 0 < t := lt_of_lt_of_le
    (by exact_mod_cast (Nat.zero_lt_of_lt hN)) hNt
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrtle : Real.sqrt t ≤ (N : ℝ) := by
    nlinarith [Real.sq_sqrt ht.le]
  have hδ : 0 < Real.sqrt t / N := by positivity
  have hδ1 : Real.sqrt t / N ≤ 1 := by
    apply (div_le_iff₀ hNpos).2
    simpa using hsqrtle
  have hraw := gmResonant_card_le_bandLabels hN hNt htN hδ hδ1
  have hratio : 2 * (Real.sqrt t / (N : ℝ)) /
      (t / (9 * (N : ℝ) ^ 2)) = 18 * (N : ℝ) / Real.sqrt t := by
    field_simp [ne_of_gt ht, ne_of_gt hNpos, ne_of_gt hsqrtpos]
    nlinarith [Real.sq_sqrt ht.le]
  rw [hratio] at hraw
  exact hraw

theorem gmResonanceWidth_pos
    {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 0 < t) :
    0 < gmResonanceWidth N t := by
  unfold gmResonanceWidth
  positivity

end GuthMaynardGMPointwiseHighTPartition

#print axioms GuthMaynardGMPointwiseHighTPartition.sourcePhase_succ_eq_mul_gmStepPhase
#print axioms GuthMaynardGMPointwiseHighTPartition.gmIncrement_succ_lt
#print axioms GuthMaynardGMPointwiseHighTPartition.gmIncrement_gap_lower
#print axioms GuthMaynardGMPointwiseHighTPartition.gmIncrement_pairwise_gap
#print axioms GuthMaynardGMPointwiseHighTPartition.gmIncrement_pos
#print axioms GuthMaynardGMPointwiseHighTPartition.gmIncrement_le_t_div_N
#print axioms GuthMaynardGMPointwiseHighTPartition.gmResonant_mem_bandLabels
#print axioms GuthMaynardGMPointwiseHighTPartition.gmBandLabels_card_le
#print axioms GuthMaynardGMPointwiseHighTPartition.gmResonantBand_card_le
#print axioms GuthMaynardGMPointwiseHighTPartition.gmResonant_card_le_bandLabels
#print axioms GuthMaynardGMPointwiseHighTPartition.gmResonant_card_le_sqrtScale
#print axioms GuthMaynardGMPointwiseHighTPartition.gm_resonant_union_offResonant
