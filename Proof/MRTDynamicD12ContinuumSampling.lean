import MAPPolylogCor212SplitSampled

/-! Actual compact-interval sampling: clipped unit bins, attained maxima,
parity spacing, and pointwise coverage. No analytic moment input is used. -/
namespace MRTDynamicD12ContinuumSampling
noncomputable section
open scoped BigOperators

abbrev Bin (a b : ℝ) := Fin ⌈b - a⌉₊
def left (a : ℝ) (i : ℕ) : ℝ := a + i
def right (a b : ℝ) (i : ℕ) : ℝ := min b (a + i + 1)

theorem left_lt_end {a b : ℝ} (i : Bin a b) : left a i < b := by
  have hi : (i.val : ℝ) < b - a := Nat.lt_ceil.mp i.isLt
  unfold left
  linarith

theorem bin_length {a b : ℝ} (i : Bin a b) :
    0 ≤ right a b i - left a i ∧ right a b i - left a i ≤ 1 := by
  have hi := left_lt_end i
  unfold left right at *
  constructor
  · exact sub_nonneg.mpr (le_min hi.le (by linarith))
  · have := min_le_right b (a + (i.val : ℝ) + 1)
    linarith

theorem exists_maximum {a b : ℝ} (f : ℝ → ℝ) (hf : Continuous f)
    (i : Bin a b) :
    ∃ t ∈ Set.Icc (left a i) (right a b i),
      ∀ u ∈ Set.Icc (left a i) (right a b i), f u ≤ f t := by
  exact isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (sub_nonneg.mp (bin_length i).1)) hf.continuousOn

def sample {a b : ℝ} (f : ℝ → ℝ) (hf : Continuous f) (i : Bin a b) : ℝ :=
  Classical.choose (exists_maximum f hf i)

theorem sample_mem {a b : ℝ} (f : ℝ → ℝ) (hf : Continuous f) (i : Bin a b) :
    sample f hf i ∈ Set.Icc (left a i) (right a b i) :=
  (Classical.choose_spec (exists_maximum f hf i)).1

theorem sample_max {a b : ℝ} (f : ℝ → ℝ) (hf : Continuous f) (i : Bin a b)
    {t : ℝ} (ht : t ∈ Set.Icc (left a i) (right a b i)) :
    f t ≤ f (sample f hf i) :=
  (Classical.choose_spec (exists_maximum f hf i)).2 t ht

theorem sample_range {a b : ℝ} (f : ℝ → ℝ) (hf : Continuous f) (i : Bin a b) :
    sample f hf i ∈ Set.Icc a b := by
  have h := sample_mem f hf i
  constructor
  · exact (by unfold left; exact le_add_of_nonneg_right (Nat.cast_nonneg _) : a ≤ left a i).trans h.1
  · exact h.2.trans (min_le_left _ _)

theorem parity_spacing {a b : ℝ} (f : ℝ → ℝ) (hf : Continuous f)
    (i j : Bin a b) (hne : i ≠ j) (hpar : i.val % 2 = j.val % 2) :
    1 ≤ |sample f hf i - sample f hf j| := by
  have hi := sample_mem f hf i
  have hj := sample_mem f hf j
  have hir := hi.2.trans (min_le_right _ _)
  have hjr := hj.2.trans (min_le_right _ _)
  have hij : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hn : i.val + 2 ≤ j.val := by omega
    have hn' : (i.val : ℝ) + 2 ≤ j.val := by exact_mod_cast hn
    have hd : 1 ≤ sample f hf j - sample f hf i := by
      unfold left at hj
      linarith [hj.1]
    exact hd.trans (by simpa only [neg_sub] using neg_le_abs (sample f hf i - sample f hf j))
  · have hn : j.val + 2 ≤ i.val := by omega
    have hn' : (j.val : ℝ) + 2 ≤ i.val := by exact_mod_cast hn
    have hd : 1 ≤ sample f hf i - sample f hf j := by
      unfold left at hi
      linarith [hi.1]
    exact hd.trans (le_abs_self _)

/-- Every point except the right endpoint belongs to a literal finite bin. -/
theorem coverage {a b t : ℝ} (ht : t ∈ Set.Ico a b) :
    ∃ i : Bin a b, t ∈ Set.Icc (left a i) (right a b i) := by
  have h0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
  have hn : ⌊t - a⌋₊ < ⌈b - a⌉₊ :=
    Nat.floor_lt_ceil_of_lt_of_pos (by linarith [ht.2]) (by linarith [ht.1, ht.2])
  refine ⟨⟨⌊t - a⌋₊, hn⟩, ?_, ?_⟩
  · have := Nat.floor_le h0
    dsimp [left]
    linarith
  · have := Nat.lt_floor_add_one (t - a)
    dsimp [right]
    exact le_min ht.2.le (by linarith)

theorem bin_card_bound {a b : ℝ} (hab : a ≤ b) :
    (Fintype.card (Bin a b) : ℝ) < b - a + 1 := by
  simpa using Nat.ceil_lt_add_one (sub_nonneg.mpr hab)

/-- Exact telescoping of the clipped partition, including its final short bin. -/
theorem integral_eq_sum {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : Continuous f) :
    (∫ t in a..b, f t) =
      ∑ i : Bin a b, ∫ t in left a i..right a b i, f t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
    (a := fun k : ℕ => min b (a + k)) (n := ⌈b-a⌉₊)
    (fun k hk => hf.intervalIntegrable _ _)
  have hend : min b (a + (⌈b-a⌉₊ : ℝ)) = b :=
    min_eq_left (by linarith [Nat.le_ceil (b-a)])
  have hstart : min b (a + (0 : ℕ)) = a := by simp [min_eq_right hab]
  dsimp only at h
  rw [hstart, hend] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hleft : min b (a + (i.val : ℝ)) = left a i :=
    min_eq_right (left_lt_end i).le
  simp only [hleft, right, Nat.cast_add, Nat.cast_one, add_assoc]

theorem integral_le_samples {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ t, 0 ≤ f t) :
    (∫ t in a..b, f t) ≤ ∑ i : Bin a b, f (sample f hf i) := by
  rw [integral_eq_sum hab f hf]
  apply Finset.sum_le_sum
  intro i hi
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (sub_nonneg.mp (bin_length i).1) (hf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)
    (fun t ht => sample_max f hf i ht)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h.trans (mul_le_of_le_one_left (hpos _) (bin_length i).2)

/-- The two actual finite color classes, with all characters included. -/
def coloredSamples {q : ℕ} [NeZero q] {a b : ℝ}
    (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))
    (color : ℕ) : Finset (DirichletCharacter ℂ q × ℝ) := by
  classical
  exact (Finset.univ.filter (fun z : DirichletCharacter ℂ q × Bin a b =>
    z.2.val % 2 = color)).image (fun z => (z.1, sample (F z.1) (hF z.1) z.2))

theorem coloredSamples_spacing {q : ℕ} [NeZero q] {a b : ℝ}
    (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))
    (color : ℕ) :
    MAPMRTLemma211AllCharacterSource.SameCharacterOneSeparated
      (coloredSamples (a := a) (b := b) F hF color) := by
  classical
  intro z hz w hw hne hchar
  obtain ⟨⟨χ,i⟩, hi, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨⟨ψ,j⟩, hj, rfl⟩ := Finset.mem_image.mp hw
  dsimp at hchar
  subst ψ
  have hij : i ≠ j := by intro h; subst j; exact hne rfl
  exact parity_spacing (F χ) (hF χ) i j hij
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

theorem coloredSamples_range {q : ℕ} [NeZero q] {a b : ℝ}
    (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))
    (color : ℕ) {z : DirichletCharacter ℂ q × ℝ}
    (hz : z ∈ coloredSamples (a := a) (b := b) F hF color) :
    z.2 ∈ Set.Icc a b := by
  classical
  obtain ⟨⟨χ,i⟩, hi, rfl⟩ := Finset.mem_image.mp hz
  exact sample_range (F χ) (hF χ) i

theorem coloredSamples_card {q : ℕ} [NeZero q] {a b : ℝ}
    (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))
    (color : ℕ) :
    (coloredSamples (a := a) (b := b) F hF color).card ≤
      Fintype.card (DirichletCharacter ℂ q) * ⌈b-a⌉₊ := by
  classical
  exact (Finset.card_image_le).trans
    ((Finset.card_filter_le _ _).trans_eq (by simp [Fintype.card_prod]))

/-- Uniform `A = 1` cardinal budget whenever interval length plus one is at most `T`. -/
theorem coloredSamples_card_le_qT {q : ℕ} [NeZero q] {a b T : ℝ}
    (hab : a ≤ b) (hlen : b - a + 1 ≤ T)
    (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))
    (color : ℕ) :
    ((coloredSamples (a := a) (b := b) F hF color).card : ℝ) ≤ (q : ℝ) * T := by
  have hc := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at hc
  have hc' : (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ q := by
    exact_mod_cast hc.le.trans (Nat.totient_le q)
  have hn : (⌈b-a⌉₊ : ℝ) ≤ T :=
    (Nat.ceil_lt_add_one (sub_nonneg.mpr hab)).le.trans hlen
  have hs : ((coloredSamples (a := a) (b := b) F hF color).card : ℝ) ≤
      (Fintype.card (DirichletCharacter ℂ q) : ℝ) * (⌈b-a⌉₊ : ℝ) := by
    exact_mod_cast coloredSamples_card (a := a) (b := b) F hF color
  exact hs.trans (mul_le_mul hc' hn (by positivity) (by positivity))

/-- Positive annular samples lie literally in the moment source's absolute-value range. -/
theorem positive_annular_range {q : ℕ} [NeZero q] {T : ℝ} (hT : 0 ≤ T)
    (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))
    (color : ℕ) {z : DirichletCharacter ℂ q × ℝ}
    (hz : z ∈ coloredSamples (a := T/2) (b := T) F hF color) :
    T/2 ≤ |z.2| ∧ |z.2| ≤ T := by
  have hr := coloredSamples_range F hF color hz
  rw [abs_of_nonneg (by linarith [hr.1] : 0 ≤ z.2)]
  exact hr

/-- The same construction directly handles the negative annular half. -/
theorem negative_annular_range {q : ℕ} [NeZero q] {T : ℝ} (hT : 0 ≤ T)
    (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))
    (color : ℕ) {z : DirichletCharacter ℂ q × ℝ}
    (hz : z ∈ coloredSamples (a := -T) (b := -T/2) F hF color) :
    T/2 ≤ |z.2| ∧ |z.2| ≤ T := by
  have hr := coloredSamples_range F hF color hz
  rw [abs_of_nonpos (by linarith [hr.2] : z.2 ≤ 0)]
  constructor <;> linarith [hr.1, hr.2]

end
end MRTDynamicD12ContinuumSampling

#print axioms MRTDynamicD12ContinuumSampling.integral_le_samples
#print axioms MRTDynamicD12ContinuumSampling.coloredSamples_spacing
#print axioms MRTDynamicD12ContinuumSampling.coloredSamples_card_le_qT
