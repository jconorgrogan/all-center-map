import MontgomeryMixedMomentFamily
namespace MAPMontgomeryMixedMomentPacking
open scoped BigOperators
open Complex MeasureTheory
open MAPMontgomeryMixedMomentIntegral MAPMRTCorollary25Minkowski
open MAPMontgomeryLowStripContinuousTypeII MAPMRTLemma211AllCharacterSource
noncomputable section
theorem sum_localIntegral_le_enlargedIntegral
    (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ s, 0 ≤ G s) (W : Finset ℝ)
    {B T : ℝ} (hB : 0 < B) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 3 * B ≤ |t - u|) :
    (∑ t ∈ W, ∫ s in (t - B)..(t + B), G s) ≤
      ∫ s in (-(T + B))..(T + B), G s := by
  classical
  let I : ℝ → Set ℝ := fun t => Set.Ioc (t - B) (t + B)
  let J : Set ℝ := Set.Ioc (-(T + B)) (T + B)
  have hpair : Set.Pairwise (↑W) (Function.onFun Disjoint I) := by
    intro t ht u hu hne
    exact disjoint_recenteredIoc_of_threeBSeparated hB
      (hsep t ht u hu hne)
  have hmeas : ∀ t ∈ W, MeasurableSet (I t) := by
    intro t ht
    exact measurableSet_Ioc
  have hintLocal : ∀ t ∈ W,
      IntegrableOn G (I t) := by
    intro t ht
    exact (hG).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hunion :
      (∫ s in ⋃ t ∈ W, I t, G s) =
        ∑ t ∈ W, ∫ s in I t, G s :=
    MeasureTheory.integral_biUnion_finset W hmeas hpair hintLocal
  have hsub : (⋃ t ∈ W, I t) ⊆ J := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨htW, hxI⟩ := ht
    have htbound := abs_le.mp (hheight t htW)
    dsimp [I, J] at hxI ⊢
    constructor <;> linarith [hxI.1, hxI.2, htbound.1, htbound.2]
  have hglobal : IntegrableOn G J :=
    (hG).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hmono :
      (∫ s in ⋃ t ∈ W, I t, G s) ≤
        ∫ s in J, G s := by
    apply MeasureTheory.setIntegral_mono_set hglobal
    · exact Filter.Eventually.of_forall fun s => by
        exact hG0 s
    · exact Filter.Eventually.of_forall fun s hs => hsub hs
  calc
    (∑ t ∈ W, ∫ s in (t - B)..(t + B), G s) =
        ∑ t ∈ W, ∫ s in I t, G s := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [intervalIntegral.integral_of_le (by linarith)]
    _ = ∫ s in ⋃ t ∈ W, I t, G s := hunion.symm
    _ ≤ ∫ s in J, G s := hmono
    _ = ∫ s in (-(T + B))..(T + B), G s := by
      rw [intervalIntegral.integral_of_le (by linarith)]


theorem perronConvolution_le_localIntegral
    (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ s, 0 ≤ G s) {B t : ℝ} (hB : 0 ≤ B) :
    perronConvolution G B t ≤
      ∫ s in (t - B)..(t + B), G s := by
  rw [perronConvolution_eq_translatedIntegral]
  have hcont : Continuous G :=
    hG
  have hmono :
      (∫ s in (-B + t)..(B + t),
        perronWeight (s - t) * G s) ≤
      ∫ s in (-B + t)..(B + t), G s := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact ((continuous_perronWeight.comp
        (continuous_id.sub continuous_const)).mul hcont).intervalIntegrable _ _
    · exact hcont.intervalIntegrable _ _
    · intro s hs
      have hw : perronWeight (s - t) ≤ 1 := by
        unfold perronWeight
        have hd : 1 ≤ 1 + |s - t| := by linarith [abs_nonneg (s - t)]
        exact (div_le_one (by positivity : 0 < 1 + |s - t|)).2 hd
      exact mul_le_of_le_one_left (hG0 s) hw
  simpa [sub_eq_add_neg, add_comm] using hmono


/-- Packs any nonnegative continuous moment over the exact complex-zero
family; imaginary-part injectivity follows from the retained spacing. -/
theorem sum_zeroFamily_perronConvolution_le
    {q : ℕ} [NeZero q] (W : DirichletCharacter ℂ q → Finset ℂ)
    (G : DirichletCharacter ℂ q → ℝ → ℝ)
    (hG : ∀ chi, Continuous (G chi)) (hG0 : ∀ chi t, 0 ≤ G chi t)
    {B T : ℝ} (hB : 0 < B) (hT : 0 ≤ T)
    (hheight : ∀ chi rho, rho ∈ W chi → |rho.im| ≤ T)
    (hsep : ∀ chi rho, rho ∈ W chi → ∀ rho', rho' ∈ W chi →
      rho ≠ rho' → 3 * B ≤ |rho.im-rho'.im|) :
    (∑ chi : DirichletCharacter ℂ q, ∑ rho ∈ W chi,
      perronConvolution (G chi) B rho.im) ≤
      ∑ chi : DirichletCharacter ℂ q, ∫ s in (-(T+B))..(T+B), G chi s := by
  classical
  apply Finset.sum_le_sum
  intro chi hchi
  have hlocal : (∑ rho ∈ W chi, perronConvolution (G chi) B rho.im) ≤
      ∑ rho ∈ W chi, ∫ s in (rho.im-B)..(rho.im+B), G chi s := by
    exact Finset.sum_le_sum fun rho hrho =>
      perronConvolution_le_localIntegral (G chi) (hG chi) (hG0 chi) hB.le
  apply hlocal.trans
  let WI := (W chi).image Complex.im
  have himinj := im_injOn_of_threeBSeparated (W chi) hB
    (fun rho hrho rho' hrho' hne => hsep chi rho hrho rho' hrho' hne)
  have hsumImage :
      (∑ rho ∈ W chi, ∫ s in (rho.im-B)..(rho.im+B), G chi s) =
      ∑ t ∈ WI, ∫ s in (t-B)..(t+B), G chi s := by
    dsimp [WI]
    rw [Finset.sum_image]
    intro rho hrho rho' hrho' him
    exact himinj hrho hrho' him
  rw [hsumImage]
  apply sum_localIntegral_le_enlargedIntegral (G chi) (hG chi) (hG0 chi) WI hB hT
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨rho,hrho,rfl⟩
    exact hheight chi rho hrho
  · intro t ht u hu hne
    rcases Finset.mem_image.mp ht with ⟨rho,hrho,rfl⟩
    rcases Finset.mem_image.mp hu with ⟨rho',hrho',heq⟩
    subst u
    exact hsep chi rho hrho rho' hrho' (fun h => hne (congrArg Complex.im h))

end
end MAPMontgomeryMixedMomentPacking

#print axioms MAPMontgomeryMixedMomentPacking.sum_zeroFamily_perronConvolution_le
