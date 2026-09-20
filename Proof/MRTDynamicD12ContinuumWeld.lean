import MRTDynamicD12ContinuumSampling

namespace MRTDynamicD12ContinuumSampling
noncomputable section
open scoped BigOperators
open MAPMRTProposition61TypeD1FirstInequality

variable {q : ℕ} [NeZero q] {a b : ℝ}
variable (F : DirichletCharacter ℂ q → ℝ → ℝ) (hF : ∀ χ, Continuous (F χ))

abbrev Indices (a b : ℝ) (q : ℕ) := DirichletCharacter ℂ q × Bin a b

def colorIndices (color : ℕ) : Finset (Indices a b q) := by
  classical
  exact Finset.univ.filter (fun z => z.2.val % 2 = color)

def samplePair (z : Indices a b q) : DirichletCharacter ℂ q × ℝ :=
  (z.1, sample (F z.1) (hF z.1) z.2)

theorem samplePair_injOn (color : ℕ) :
    Set.InjOn (samplePair F hF) (↑(colorIndices (a := a) (b := b) (q := q) color) : Set (Indices a b q)) := by
  classical
  intro x hx y hy heq
  rcases x with ⟨χ,i⟩
  rcases y with ⟨ψ,j⟩
  have hc : χ = ψ := congrArg Prod.fst heq
  subst ψ
  have ht : sample (F χ) (hF χ) i = sample (F χ) (hF χ) j := congrArg Prod.snd heq
  have hij : i = j := by
    by_contra hn
    have hp := parity_spacing (F χ) (hF χ) i j hn
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
    rw [ht, sub_self, abs_zero] at hp
    norm_num at hp
  subst j
  rfl

def assignedLeft (color : ℕ) (z : DirichletCharacter ℂ q × ℝ) : ℝ := by
  classical
  exact if hz : z ∈ coloredSamples (a := a) (b := b) F hF color then
    left a (Classical.choose (Finset.mem_image.mp hz)).2 else a

def assignedRight (color : ℕ) (z : DirichletCharacter ℂ q × ℝ) : ℝ := by
  classical
  exact if hz : z ∈ coloredSamples (a := a) (b := b) F hF color then
    right a b (Classical.choose (Finset.mem_image.mp hz)).2 else a

theorem assigned_endpoints (color : ℕ) (x : Indices a b q)
    (hx : x ∈ colorIndices (a := a) (b := b) (q := q) color) :
    assignedLeft (a := a) (b := b) F hF color (samplePair F hF x) = left a x.2 ∧
    assignedRight (a := a) (b := b) F hF color (samplePair F hF x) = right a b x.2 := by
  classical
  have hz : samplePair F hF x ∈ coloredSamples (a := a) (b := b) F hF color :=
    Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hchoice := Classical.choose_spec (Finset.mem_image.mp hz)
  have hc : Classical.choose (Finset.mem_image.mp hz) = x :=
    samplePair_injOn F hF color hchoice.1 hx hchoice.2
  simp only [assignedLeft, assignedRight, dif_pos hz, hc, and_self]

theorem assigned_length (color : ℕ) {z : DirichletCharacter ℂ q × ℝ}
    (hz : z ∈ coloredSamples (a := a) (b := b) F hF color) :
    0 ≤ assignedRight (a := a) (b := b) F hF color z - assignedLeft (a := a) (b := b) F hF color z ∧
      assignedRight (a := a) (b := b) F hF color z - assignedLeft (a := a) (b := b) F hF color z ≤ 1 := by
  classical
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have he := assigned_endpoints F hF color x hx
  change 0 ≤ assignedRight (a := a) (b := b) F hF color (samplePair F hF x) -
    assignedLeft (a := a) (b := b) F hF color (samplePair F hF x) ∧
    assignedRight (a := a) (b := b) F hF color (samplePair F hF x) -
    assignedLeft (a := a) (b := b) F hF color (samplePair F hF x) ≤ 1
  rw [he.1,he.2]
  exact bin_length x.2

theorem assigned_max (color : ℕ) {z : DirichletCharacter ℂ q × ℝ}
    (hz : z ∈ coloredSamples (a := a) (b := b) F hF color)
    {t : ℝ} (ht : t ∈ Set.Icc (assignedLeft (a := a) (b := b) F hF color z) (assignedRight (a := a) (b := b) F hF color z)) :
    F z.1 t ≤ F z.1 z.2 := by
  classical
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have he := assigned_endpoints F hF color x hx
  change t ∈ Set.Icc (assignedLeft (a := a) (b := b) F hF color (samplePair F hF x))
    (assignedRight (a := a) (b := b) F hF color (samplePair F hF x)) at ht
  rw [he.1,he.2] at ht
  exact sample_max (F x.1) (hF x.1) x.2 ht

/-- The callbacks recover every indexed interval exactly, with no loss or duplicate removal. -/
theorem colored_integral_eq (color : ℕ)
    (G : DirichletCharacter ℂ q → ℝ → ℝ) :
    (∑ z ∈ coloredSamples (a := a) (b := b) F hF color,
      ∫ t in assignedLeft (a := a) (b := b) F hF color z..assignedRight (a := a) (b := b) F hF color z, G z.1 t) =
    ∑ x ∈ colorIndices (a := a) (b := b) (q := q) color,
      ∫ t in left a x.2..right a b x.2, G x.1 t := by
  classical
  change (∑ z ∈ (colorIndices (a := a) (b := b) (q := q) color).image (samplePair F hF), _) = _
  rw [Finset.sum_image (samplePair_injOn F hF color)]
  apply Finset.sum_congr rfl
  intro x hx
  have he := assigned_endpoints F hF color x hx
  rw [he.1,he.2]
  rfl

theorem sum_colorIndices (g : Indices a b q → ℝ) :
    (∑ x ∈ colorIndices (a := a) (b := b) (q := q) 0, g x) +
    (∑ x ∈ colorIndices (a := a) (b := b) (q := q) 1, g x) = ∑ x, g x := by
  classical
  have hp : (fun x : Indices a b q => ¬ x.2.val % 2 = 0) =
      (fun x : Indices a b q => x.2.val % 2 = 1) := by
    funext x
    apply propext
    omega
  simpa only [colorIndices, hp] using
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Indices a b q => x.2.val % 2 = 0) g

/-- Exact continuum mass equals the masses of the two actually constructed colors. -/
theorem continuum_eq_colored_integrals (hab : a ≤ b)
    (G : DirichletCharacter ℂ q → ℝ → ℝ) (hG : ∀ χ, Continuous (G χ)) :
    (∑ χ, ∫ t in a..b, G χ t) =
    (∑ z ∈ coloredSamples (a := a) (b := b) F hF 0,
      ∫ t in assignedLeft (a := a) (b := b) F hF 0 z..assignedRight (a := a) (b := b) F hF 0 z, G z.1 t) +
    (∑ z ∈ coloredSamples (a := a) (b := b) F hF 1,
      ∫ t in assignedLeft (a := a) (b := b) F hF 1 z..assignedRight (a := a) (b := b) F hF 1 z, G z.1 t) := by
  classical
  rw [colored_integral_eq, colored_integral_eq, sum_colorIndices]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact integral_eq_sum hab (G χ) (hG χ)

abbrev fourthContinuous : ∀ χ, Continuous (fun t => F χ t ^ 4) :=
  fun χ => (hF χ).pow 4

abbrev fourthSamples (color : ℕ) :=
  coloredSamples (a := a) (b := b) (fun χ t => F χ t ^ 4) (fourthContinuous F hF) color

abbrev fourthLeft (color : ℕ) :=
  assignedLeft (a := a) (b := b) (fun χ t => F χ t ^ 4) (fourthContinuous F hF) color

abbrev fourthRight (color : ℕ) :=
  assignedRight (a := a) (b := b) (fun χ t => F χ t ^ 4) (fourthContinuous F hF) color

/-- Literal fourth-moment continuum-to-source identity, with constructed sample data. -/
theorem continuum_fourth_eq_sampled (hab : a ≤ b) :
    (∑ χ, ∫ t in a..b, F χ t ^ 4) =
      bhpSampledPieceMass F (fourthSamples (a := a) (b := b) F hF 0)
        (fourthLeft (a := a) (b := b) F hF 0) (fourthRight (a := a) (b := b) F hF 0) +
      bhpSampledPieceMass F (fourthSamples (a := a) (b := b) F hF 1)
        (fourthLeft (a := a) (b := b) F hF 1) (fourthRight (a := a) (b := b) F hF 1) :=
  continuum_eq_colored_integrals (fun χ t => F χ t ^ 4) (fourthContinuous F hF)
    hab (fun χ t => F χ t ^ 4) (fourthContinuous F hF)

theorem fourthSamples_length (color : ℕ) {z : DirichletCharacter ℂ q × ℝ}
    (hz : z ∈ fourthSamples (a := a) (b := b) F hF color) :
    0 ≤ fourthRight (a := a) (b := b) F hF color z - fourthLeft (a := a) (b := b) F hF color z ∧
    fourthRight (a := a) (b := b) F hF color z - fourthLeft (a := a) (b := b) F hF color z ≤ 1 :=
  assigned_length _ _ color hz

theorem fourthSamples_max (color : ℕ) {z : DirichletCharacter ℂ q × ℝ}
    (hz : z ∈ fourthSamples (a := a) (b := b) F hF color)
    {t : ℝ} (ht : t ∈ Set.Icc (fourthLeft (a := a) (b := b) F hF color z) (fourthRight (a := a) (b := b) F hF color z)) :
    F z.1 t ^ 4 ≤ F z.1 z.2 ^ 4 :=
  assigned_max _ _ color hz ht

end
end MRTDynamicD12ContinuumSampling

#print axioms MRTDynamicD12ContinuumSampling.continuum_fourth_eq_sampled
#print axioms MRTDynamicD12ContinuumSampling.fourthSamples_max
