import PrimitiveRectangleSpecialization
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Simultaneous removal of finitely many simple poles
-/

namespace FiniteRemovableExtension

open Set Filter Topology Asymptotics Function Complex
open scoped BigOperators

noncomputable section

variable {S : Finset ℂ} (residue : ℂ → ℂ)

/-- The finite sum of prescribed simple principal parts. -/
def principalPartSum (S : Finset ℂ) (residue : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ S, residue ρ * (z - ρ)⁻¹

/-- Subtract all prescribed finite principal parts. -/
def principalPartsRemoved (S : Finset ℂ) (residue : ℂ → ℂ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z - principalPartSum S residue z

/-- Patch every point of a finite pole set by the punctured-neighborhood limit
of the common principal-part-removed function. -/
def finiteRemovableExtension (S : Finset ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z ∈ S then limUnder (𝓝[≠] z) g else g z

/-- Multiplication by `z-p` extracts exactly the `p` principal part from the
finite sum. -/
theorem tendsto_mul_principalPartSum_at
    {p : ℂ} (hp : p ∈ S) :
    Tendsto (fun z => (z - p) * principalPartSum S residue z)
      (𝓝[≠] p) (𝓝 (residue p)) := by
  have hterm : ∀ ρ ∈ S,
      Tendsto (fun z => (z - p) * (residue ρ * (z - ρ)⁻¹))
        (𝓝[≠] p) (𝓝 (if ρ = p then residue p else 0)) := by
    intro ρ hρ
    by_cases hρp : ρ = p
    · subst ρ
      have hmain : Tendsto
          (fun z => (z - p) * (residue p * (z - p)⁻¹))
          (nhdsWithin p {p}ᶜ) (nhds (residue p)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hne : z - p ≠ 0 := sub_ne_zero.mpr hz
        field_simp [hne]
      simpa using hmain
    · have hsub : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
        have hid : Tendsto (fun z : ℂ => z)
            (nhdsWithin p {p}ᶜ) (nhds p) :=
          continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
        have hc : Tendsto (fun _z : ℂ => p)
            (nhdsWithin p {p}ᶜ) (nhds p) := tendsto_const_nhds
        simpa using hid.sub hc
      have hden : Tendsto (fun z : ℂ => z - ρ) (𝓝[≠] p) (𝓝 (p - ρ)) := by
        exact (continuousAt_id.sub continuousAt_const).tendsto.mono_left
          nhdsWithin_le_nhds
      have hne : p - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρp)
      have hinv := hden.inv₀ hne
      simpa [hρp] using hsub.mul (tendsto_const_nhds.mul hinv)
  have hsum := tendsto_finsetSum S hterm
  convert hsum using 1
  · ext z
    simp only [principalPartSum]
    rw [Finset.mul_sum]
  · simp [hp]

/-- A matching local residue makes the common principal-part-removed function
little-oh of the reciprocal singularity, exactly the hypothesis consumed by
Mathlib's removable-singularity theorem. -/
theorem principalPartsRemoved_isLittleO
    (f : ℂ → ℂ) {p : ℂ} (hp : p ∈ S)
    (hres : Tendsto (fun z => (z - p) * f z)
      (𝓝[≠] p) (𝓝 (residue p))) :
    (fun z => principalPartsRemoved S residue f z -
        principalPartsRemoved S residue f p) =o[𝓝[≠] p]
      fun z => (z - p)⁻¹ := by
  have hprincipal := tendsto_mul_principalPartSum_at (S := S) residue hp
  have hremovedMul : Tendsto
      (fun z => (z - p) * principalPartsRemoved S residue f z)
      (𝓝[≠] p) (𝓝 0) := by
    have hsub := hres.sub hprincipal
    convert hsub using 1
    · ext z
      simp only [principalPartsRemoved]
      ring
    · ring
  have hsubzero : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    have hid : Tendsto (fun z : ℂ => z)
        (nhdsWithin p {p}ᶜ) (nhds p) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun _z : ℂ => p)
        (nhdsWithin p {p}ᶜ) (nhds p) := tendsto_const_nhds
    simpa using hid.sub hc
  have hvalueMul : Tendsto
      (fun z => (z - p) * principalPartsRemoved S residue f p)
      (𝓝[≠] p) (𝓝 0) := by
    simpa using hsubzero.mul_const (principalPartsRemoved S residue f p)
  rw [isLittleO_iff_tendsto]
  · have heq :
        (fun z => (z - p) * principalPartsRemoved S residue f z -
          (z - p) * principalPartsRemoved S residue f p) =ᶠ[𝓝[≠] p]
        (fun z => (principalPartsRemoved S residue f z -
          principalPartsRemoved S residue f p) / (z - p)⁻¹) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hne : z - p ≠ 0 := sub_ne_zero.mpr hz
      field_simp [hne]
    simpa using (hremovedMul.sub hvalueMul).congr' heq
  · intro z hz
    have hzp : z = p := by
      exact sub_eq_zero.mp (inv_eq_zero.mp hz)
    subst z
    simp

/-- Simultaneous finite removable-singularity theorem.  The pole set lies in
the interior of `U`; away from it `g` is holomorphic, and at each pole it
satisfies Mathlib's one-point little-oh compatibility.  The direct finite
patch is therefore holomorphic throughout `U`. -/
theorem differentiableOn_finiteRemovableExtension
    (U : Set ℂ) (g : ℂ → ℂ)
    (hInterior : ∀ p ∈ S, U ∈ nhds p)
    (hDiff : DifferentiableOn ℂ g (U \ (↑S : Set ℂ)))
    (hLittle : ∀ p ∈ S,
      (fun z => g z - g p) =o[𝓝[≠] p] fun z => (z - p)⁻¹) :
    DifferentiableOn ℂ (finiteRemovableExtension S g) U := by
  classical
  intro p hpU
  by_cases hpS : p ∈ S
  · let others : Set ℂ := (↑S : Set ℂ) \ {p}
    have hOthersFinite : others.Finite := by
      exact S.finite_toSet.diff (t := {p})
    have hpOthers : p ∉ others := by
      simp [others]
    have hOthersCompl : othersᶜ ∈ nhds p :=
      hOthersFinite.isClosed.isOpen_compl.mem_nhds hpOthers
    have hV : U \ others ∈ nhds p := by
      rw [diff_eq]
      exact inter_mem (hInterior p hpS) hOthersCompl
    have hsmall : (U \ others) \ {p} ⊆ U \ (↑S : Set ℂ) := by
      intro z hz
      refine ⟨hz.1.1, ?_⟩
      intro hzS
      by_cases hzp : z = p
      · exact hz.2 hzp
      · exact hz.1.2 ⟨hzS, hzp⟩
    have hDiffV : DifferentiableOn ℂ g ((U \ others) \ {p}) :=
      hDiff.mono hsmall
    have hUpdate : DifferentiableOn ℂ
        (Function.update g p (limUnder (𝓝[≠] p) g)) (U \ others) :=
      Complex.differentiableOn_update_limUnder_of_isLittleO
        hV hDiffV (hLittle p hpS)
    have hUpdateAt : DifferentiableAt ℂ
        (Function.update g p (limUnder (𝓝[≠] p) g)) p :=
      hUpdate.differentiableAt hV
    have hLocalEq : finiteRemovableExtension S g =ᶠ[nhds p]
        Function.update g p (limUnder (𝓝[≠] p) g) := by
      filter_upwards [hOthersCompl] with z hz
      by_cases hzp : z = p
      · subst z
        simp [finiteRemovableExtension, hpS]
      · have hzS : z ∉ S := by
          intro hzMem
          exact hz ⟨hzMem, hzp⟩
        simp [finiteRemovableExtension, hzS, hzp]
    exact (hUpdateAt.congr_of_eventuallyEq hLocalEq).differentiableWithinAt
  · have hSCompl : (↑S : Set ℂ)ᶜ ∈ nhds p :=
      S.finite_toSet.isClosed.isOpen_compl.mem_nhds hpS
    have hfilter : nhdsWithin p (U \ (↑S : Set ℂ)) = nhdsWithin p U := by
      rw [diff_eq, inter_comm]
      exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hSCompl)
    have hBase : DifferentiableWithinAt ℂ g U p := by
      rcases hDiff p ⟨hpU, hpS⟩ with ⟨g', hg'⟩
      refine ⟨g', ?_⟩
      unfold HasFDerivWithinAt at hg' ⊢
      rw [hfilter] at hg'
      exact hg'
    have hLocalEq : finiteRemovableExtension S g =ᶠ[nhds p] g := by
      filter_upwards [hSCompl] with z hz
      have hzS : z ∉ S := by simpa using hz
      simp [finiteRemovableExtension, hzS]
    exact hBase.congr_of_eventuallyEq
      (hLocalEq.filter_mono nhdsWithin_le_nhds)
      (by simp [finiteRemovableExtension, hpS])

end

end FiniteRemovableExtension
