import FiniteBlaschkeAlgebra
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.NormalForm

open scoped BigOperators
open Complex Set Metric
noncomputable section

namespace FordScaledBlaschkeFill

open FiniteBlaschkeAlgebra

/-- The normal-form filling of a finite Blaschke product times an analytic
function.  The explicit meromorphic normal form removes the poles of the
canonical factors at the selected zeros. -/
def scaledBlaschkeFill
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => f z * finiteBlaschkeProduct c R S m z)
    (Metric.closedBall c R)

private theorem meromorphicOn_shiftedCanonicalFactor
    (c : ℂ) (R : ℝ) (ρ : ℂ) :
    MeromorphicOn (shiftedCanonicalFactor c R ρ) Set.univ := by
  intro z hz
  unfold shiftedCanonicalFactor Complex.canonicalFactor
  fun_prop

private theorem meromorphicOrderAt_shiftedCanonicalFactor_self
    {c ρ : ℂ} {R : ℝ} (hρ : ρ ∈ Metric.ball c R) :
    meromorphicOrderAt (shiftedCanonicalFactor c R ρ) ρ = -1 := by
  have hρ' : ρ - c ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hρ
  have hcomp : shiftedCanonicalFactor c R ρ =
      Complex.canonicalFactor R (ρ - c) ∘ (fun z : ℂ => z - c) := rfl
  rw [hcomp, meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  simpa using Complex.meromorphicOrderAt_canonicalFactor hρ'

private theorem analyticAt_shiftedCanonicalFactor_of_ne
    {c ρ z : ℂ} {R : ℝ} (hzρ : z ≠ ρ) :
    AnalyticAt ℂ (shiftedCanonicalFactor c R ρ) z := by
  have hne : z - c ≠ ρ - c := fun h => hzρ (sub_left_inj.mp h)
  have houter : z - c ∈ ({ρ - c} : Set ℂ)ᶜ := hne
  have hcan := Complex.analyticOnNhd_canonicalFactor R (ρ - c)
    (z - c) houter
  change AnalyticAt ℂ
    (Complex.canonicalFactor R (ρ - c) ∘ (fun w : ℂ => w - c)) z
  have hsub : AnalyticAt ℂ (fun w : ℂ => w - c) z := by fun_prop
  exact AnalyticAt.comp (f := fun w : ℂ => w - c) (x := z) hcan hsub

private theorem shiftedCanonicalFactor_ne_zero_in_closedBall
    {c ρ z : ℂ} {R : ℝ}
    (hρ : ρ ∈ Metric.ball c R) (hz : z ∈ Metric.closedBall c R)
    (hzρ : z ≠ ρ) :
    shiftedCanonicalFactor c R ρ z ≠ 0 := by
  apply Complex.canonicalFactor_ne_zero
  · simpa [Metric.mem_ball, dist_eq_norm] using hρ
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  · intro h
    exact hzρ (sub_left_inj.mp h)

private theorem meromorphicOn_finiteBlaschkeProduct
    {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R) :
    MeromorphicOn (finiteBlaschkeProduct c R S m) Set.univ := by
  change MeromorphicOn
    (fun z : ℂ => ∏ ρ ∈ S,
      (shiftedCanonicalFactor c R ρ z) ^ m ρ) Set.univ
  exact MeromorphicOn.fun_prod
    (s := S) fun ρ hρ =>
      (meromorphicOn_shiftedCanonicalFactor c R ρ).pow (m ρ)

private theorem meromorphicOrderAt_finiteBlaschkeProduct_at_mem
    {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R)
    {z : ℂ} (hz : z ∈ S) :
    meromorphicOrderAt (finiteBlaschkeProduct c R S m) z =
      -(m z : ℤ) := by
  change meromorphicOrderAt
    (fun w : ℂ => ∏ ρ ∈ S,
      (shiftedCanonicalFactor c R ρ w) ^ m ρ) z = _
  rw [meromorphicOrderAt_fun_prod]
  · rw [Finset.sum_eq_single z]
    · rw [show (fun w =>
          shiftedCanonicalFactor c R z w ^ m z) =
          (shiftedCanonicalFactor c R z) ^ m z by rfl,
        meromorphicOrderAt_pow]
      · rw [meromorphicOrderAt_shiftedCanonicalFactor_self (hS z hz)]
        change (((m z : ℤ) : WithTop ℤ) * ((-1 : ℤ) : WithTop ℤ)) =
          ((-(m z : ℤ) : ℤ) : WithTop ℤ)
        rw [← WithTop.coe_mul]
        congr 1
        exact mul_neg_one _
      · exact (meromorphicOn_shiftedCanonicalFactor c R z) z (Set.mem_univ z)
    · intro ρ hρ hρz
      have han := analyticAt_shiftedCanonicalFactor_of_ne
        (c := c) (R := R) hρz.symm
      have hzclosed : z ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall]
        exact (Metric.mem_ball.mp (hS z hz)).le
      have hne := shiftedCanonicalFactor_ne_zero_in_closedBall
        (hS ρ hρ) hzclosed hρz.symm
      have hanPow := han.pow (m ρ)
      change meromorphicOrderAt
        ((shiftedCanonicalFactor c R ρ) ^ m ρ) z = 0
      rw [hanPow.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (pow_ne_zero _ hne)]
    · exact fun h => (h hz).elim
  · intro ρ hρ
    exact ((meromorphicOn_shiftedCanonicalFactor c R ρ).pow _) z (Set.mem_univ z)

private theorem analyticAt_finiteBlaschkeProduct_of_not_mem
    {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    {z : ℂ} (hz : z ∉ S) :
    AnalyticAt ℂ (finiteBlaschkeProduct c R S m) z := by
  change AnalyticAt ℂ
    (fun w : ℂ => ∏ ρ ∈ S,
      (shiftedCanonicalFactor c R ρ w) ^ m ρ) z
  apply Finset.analyticAt_fun_prod
  intro ρ hρ
  have hzρ : z ≠ ρ := by
    intro h
    exact hz (h ▸ hρ)
  exact (analyticAt_shiftedCanonicalFactor_of_ne hzρ).pow _

private theorem finiteBlaschkeProduct_ne_zero_of_not_mem
    {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R)
    {z : ℂ} (hz : z ∈ Metric.closedBall c R) (hzS : z ∉ S) :
    finiteBlaschkeProduct c R S m z ≠ 0 := by
  simp only [finiteBlaschkeProduct, Finset.prod_ne_zero_iff]
  intro ρ hρ
  exact pow_ne_zero _ (shiftedCanonicalFactor_ne_zero_in_closedBall
    (hS ρ hρ) hz (fun h => hzS (h ▸ hρ)))

private theorem analyticAt_finiteBlaschkeProduct_of_center_zero
    {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hcS : c ∉ S ∨ m c = 0) :
    AnalyticAt ℂ (finiteBlaschkeProduct c R S m) c := by
  change AnalyticAt ℂ
    (fun w : ℂ => ∏ ρ ∈ S,
      (shiftedCanonicalFactor c R ρ w) ^ m ρ) c
  apply Finset.analyticAt_fun_prod
  intro ρ hρ
  by_cases hρc : ρ = c
  · subst ρ
    have hm0 : m c = 0 := hcS.resolve_left (fun h => h hρ)
    have hfun : (fun w : ℂ =>
        (shiftedCanonicalFactor c R c w) ^ m c) = (fun _ : ℂ => (1 : ℂ)) := by
      simp [hm0]
    rw [hfun]
    exact analyticAt_const
  · exact (analyticAt_shiftedCanonicalFactor_of_ne (fun h => hρc h.symm)).pow _

private theorem one_le_norm_finiteBlaschkeProduct_center
    {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R) (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R)
    (hcS : c ∉ S ∨ m c = 0) :
    1 ≤ ‖finiteBlaschkeProduct c R S m c‖ := by
  simp only [finiteBlaschkeProduct, norm_prod, norm_pow]
  apply Finset.one_le_prod₀
  intro ρ hρ
  by_cases hρc : ρ = c
  · subst ρ
    have hm0 : m c = 0 := hcS.resolve_left (fun h => h hρ)
    simp [hm0]
  · exact one_le_pow₀ (one_le_norm_shiftedCanonicalFactor_center hR
      (hS ρ hρ) hρc)

private theorem meromorphicOn_raw
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R) :
    MeromorphicOn (fun z => f z * finiteBlaschkeProduct c R S m z)
      (Metric.closedBall c R) := by
  apply MeromorphicOn.mul hf.meromorphicOn
  intro z hz
  exact (meromorphicOn_finiteBlaschkeProduct hS) z (Set.mem_univ z)

private theorem analyticAt_raw_of_not_mem
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    {z : ℂ} (hf : AnalyticAt ℂ f z) (hz : z ∉ S) :
    AnalyticAt ℂ (fun w => f w * finiteBlaschkeProduct c R S m w) z :=
  hf.mul (analyticAt_finiteBlaschkeProduct_of_not_mem hz)

theorem analyticOnNhd_scaledBlaschkeFill
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R)
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ)
    (hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤)
    (hcover : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ S) :
    AnalyticOnNhd ℂ (scaledBlaschkeFill f c R S m)
      (Metric.closedBall c R) := by
  let raw : ℂ → ℂ := fun z => f z * finiteBlaschkeProduct c R S m z
  have hraw : MeromorphicOn raw (Metric.closedBall c R) := meromorphicOn_raw hf hS
  have hnf : MeromorphicNFOn (toMeromorphicNFOn raw (Metric.closedBall c R))
      (Metric.closedBall c R) :=
    meromorphicNFOn_toMeromorphicNFOn raw (Metric.closedBall c R)
  intro z hz
  apply (hnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hraw hz]
  change 0 ≤ meromorphicOrderAt (f * finiteBlaschkeProduct c R S m) z
  rw [meromorphicOrderAt_mul (hf z hz).meromorphicAt
    ((meromorphicOn_finiteBlaschkeProduct hS) z (Set.mem_univ z))]
  by_cases hzS : z ∈ S
  · rw [show meromorphicOrderAt f z = (m z : ℤ) by
      rw [(hf z hz).meromorphicOrderAt_eq]
      rw [← Nat.cast_analyticOrderNatAt (hfinite z hzS), hm z hzS]
      simp,
      meromorphicOrderAt_finiteBlaschkeProduct_at_mem hS hzS]
    simp
  · have hzclosed : z ∈ Metric.closedBall c R := hz
    have hprod := analyticAt_finiteBlaschkeProduct_of_not_mem
      (c := c) (R := R) (m := m) hzS
    have hprod0 := finiteBlaschkeProduct_ne_zero_of_not_mem
      (c := c) (R := R) (m := m) hS hzclosed hzS
    rw [hprod.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hprod0]
    simpa using (hf z hz).meromorphicOrderAt_nonneg

theorem scaledBlaschkeFill_ne_zero_of_zero_covered
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R)
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ)
    (hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤)
    (hcover : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ S)
    {z : ℂ} (hz : z ∈ Metric.ball c R) :
    scaledBlaschkeFill f c R S m z ≠ 0 := by
  have hzclosed : z ∈ Metric.closedBall c R :=
    Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le
  have han := analyticOnNhd_scaledBlaschkeFill hR hf hS hm hfinite hcover
    z hzclosed
  apply han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  let raw : ℂ → ℂ := fun w => f w * finiteBlaschkeProduct c R S m w
  have hraw : MeromorphicOn raw (Metric.closedBall c R) := meromorphicOn_raw hf hS
  unfold scaledBlaschkeFill
  rw [meromorphicOrderAt_toMeromorphicNFOn hraw hzclosed]
  change meromorphicOrderAt (f * finiteBlaschkeProduct c R S m) z = 0
  rw [meromorphicOrderAt_mul (hf z hzclosed).meromorphicAt
    ((meromorphicOn_finiteBlaschkeProduct hS) z (Set.mem_univ z))]
  by_cases hzS : z ∈ S
  · rw [show meromorphicOrderAt f z = (m z : ℤ) by
      rw [(hf z hzclosed).meromorphicOrderAt_eq]
      rw [← Nat.cast_analyticOrderNatAt (hfinite z hzS), hm z hzS]
      simp,
      meromorphicOrderAt_finiteBlaschkeProduct_at_mem hS hzS]
    simp
  · have hf0 : f z ≠ 0 := by
      intro hzero
      exact hzS (hcover z hz hzero)
    have hprod0 := finiteBlaschkeProduct_ne_zero_of_not_mem
      (c := c) (R := R) (m := m) hS hzclosed hzS
    have hprodAn := analyticAt_finiteBlaschkeProduct_of_not_mem
      (c := c) (R := R) (m := m) hzS
    rw [(hf z hzclosed).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0,
      hprodAn.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hprod0]
    simp

theorem norm_scaledBlaschkeFill_eq_on_sphere
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R)
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ)
    (hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤)
    (hcover : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ S)
    {z : ℂ} (hz : z ∈ Metric.sphere c R) :
    ‖scaledBlaschkeFill f c R S m z‖ = ‖f z‖ := by
  have hzclosed : z ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz
  have hzS : z ∉ S := by
    intro hzmem
    have hzball := hS z hzmem
    rw [Metric.mem_ball] at hzball
    rw [Metric.mem_sphere] at hz
    linarith
  have hrawAn : AnalyticAt ℂ (fun w =>
      f w * finiteBlaschkeProduct c R S m w) z :=
    analyticAt_raw_of_not_mem (hf z hzclosed) hzS
  have hraw : MeromorphicOn (fun w =>
      f w * finiteBlaschkeProduct c R S m w) (Metric.closedBall c R) :=
    meromorphicOn_raw hf hS
  have heq : scaledBlaschkeFill f c R S m z =
      f z * finiteBlaschkeProduct c R S m z := by
    unfold scaledBlaschkeFill
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hraw hzclosed,
      toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt]
  rw [heq]
  exact norm_mul_finiteBlaschkeProduct_eq_on_sphere f hS hz

theorem norm_f_center_le_scaledBlaschkeFill_center
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c R)
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ)
    (hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤)
    (hcover : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ S)
    (hfc : f c ≠ 0) :
    ‖f c‖ ≤ ‖scaledBlaschkeFill f c R S m c‖ := by
  have hcclosed : c ∈ Metric.closedBall c R := by
    simp [Metric.mem_closedBall, hR.le]
  have hcS : c ∉ S ∨ m c = 0 := by
    by_cases hc : c ∈ S
    · right
      have horder : analyticOrderAt f c = 0 :=
        (hf c hcclosed).analyticOrderAt_eq_zero.mpr hfc
      have hnat : analyticOrderNatAt f c = 0 := by
        simp [analyticOrderNatAt, horder]
      rw [hm c hc, hnat]
    · exact Or.inl hc
  have hprodAn := analyticAt_finiteBlaschkeProduct_of_center_zero
    (R := R) (m := m) hcS
  have hrawAn : AnalyticAt ℂ (fun w =>
      f w * finiteBlaschkeProduct c R S m w) c :=
    (hf c hcclosed).mul hprodAn
  have hraw : MeromorphicOn (fun w =>
      f w * finiteBlaschkeProduct c R S m w) (Metric.closedBall c R) :=
    meromorphicOn_raw hf hS
  have heq : scaledBlaschkeFill f c R S m c =
      f c * finiteBlaschkeProduct c R S m c := by
    unfold scaledBlaschkeFill
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hraw hcclosed,
      toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt]
  rw [heq, norm_mul]
  exact le_mul_of_one_le_right (norm_nonneg _) <|
    one_le_norm_finiteBlaschkeProduct_center hR hS hcS

end FordScaledBlaschkeFill

#print axioms FordScaledBlaschkeFill.analyticOnNhd_scaledBlaschkeFill
#print axioms FordScaledBlaschkeFill.scaledBlaschkeFill_ne_zero_of_zero_covered
#print axioms FordScaledBlaschkeFill.norm_scaledBlaschkeFill_eq_on_sphere
#print axioms FordScaledBlaschkeFill.norm_f_center_le_scaledBlaschkeFill_center
