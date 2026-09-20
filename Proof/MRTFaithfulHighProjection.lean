import MRTFaithfulEquation79Duality
import MRTFaithfulLowWindowCauchy
import MRTProposition51ProjectionHighDifferentiation
import MRTEquation77

/-! The faithful high projection at the raw critical-sum normalization. -/
namespace MAPMRTFaithfulHighProjection
open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTFaithfulSmoothCutoff MAPMRTFaithfulSmoothCutoffBudgets
open MAPMRTProposition51ProjectionHighDerivative
open MAPMRTProposition51ProjectionHighDifferentiation
open MAPMRTProposition51ProjectionHighGeometry
open MAPMRTFaithfulLowWindowCauchy MAPMRTFaithfulEquation79Duality
open MAPMRTVanDerCorputProof
noncomputable section
open scoped FourierTransform
set_option maxHeartbeats 1000000

def faithfulHighDerivativeBudget : ℝ :=
  3 * (1 + faithfulCutoffDerivBudget) * (6 + 10 * Real.pi)

theorem faithfulHighDerivativeBudget_nonneg : 0 ≤ faithfulHighDerivativeBudget := by
  unfold faithfulHighDerivativeBudget
  have := faithfulCutoffDerivBudget_nonneg
  positivity

theorem faithful_sourceDualIntegrandDerivative_eq_zero_outside
    {X H beta u x : ℝ} {g : ℝ → ℂ}
    (hH : 0 < H) (hx : H / 8 < |X * Real.exp u - x|) :
    sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g u x = 0 := by
  have ha : 1 / 8 < |(X * Real.exp u - x) / H| := by
    rw [abs_div, abs_of_pos hH]
    exact (lt_div_iff₀ hH).2 (by linarith)
  have hc := faithfulCutoff_zero ha.le
  have hd : faithfulCutoffDeriv ((X * Real.exp u - x) / H) = 0 := by
    by_contra hn
    exact (not_le_of_gt ha) (abs_le_eighth_of_faithfulCutoffDeriv_ne_zero hn)
  simp [sourceDualIntegrandDerivative, hc, hd]

theorem faithful_derivative_physical_exp_bounds
    {X H u x : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∈ Icc (X / 2) (4 * X))
    (hp : |X * Real.exp u - x| ≤ H / 8) :
    7 / 16 ≤ Real.exp u ∧ Real.exp u ≤ 65 / 16 := by
  rw [abs_le] at hp
  constructor <;> nlinarith [hx.1, hx.2]

theorem exp_log_shift_physical
    {X : ℝ} {n : ℕ} (hX : 0 < X) (hn : 0 < n) (z : ℝ) :
    X * Real.exp (Real.log n - Real.log X - z) = Real.exp (-z) * n := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by exact_mod_cast hn), Real.exp_log hX,
    Real.exp_neg]
  field_simp

theorem faithful_sourceDualIntegrandDerivative_le_physical
    {X H beta u x : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hx : x ∈ Icc (X / 2) (4 * X)) :
    ‖sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g u x‖ ≤
      faithfulHighDerivativeBudget * (|beta| * X) * Real.sqrt X * ‖g x‖ := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  by_cases hp : |X * Real.exp u - x| ≤ H / 8
  · have he := faithful_derivative_physical_exp_bounds hX hHpos hHalf hx hp
    have he5 : Real.exp u ≤ 5 := by linarith [he.2]
    have heHalf : Real.exp (u / 2) ≤ 3 := by
      have hs : Real.exp (u / 2) ^ 2 = Real.exp u := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      nlinarith [Real.exp_pos (u / 2)]
    let B := 1 + faithfulCutoffDerivBudget
    have hB : 0 ≤ B := by dsimp [B]; linarith [faithfulCutoffDerivBudget_nonneg]
    have hbetaX : 1 ≤ |beta| * X := by
      have hb := mul_le_mul_of_nonneg_left hHalf (abs_nonneg beta)
      nlinarith
    have hdiv : X / H ≤ |beta| * X := by
      apply (div_le_iff₀ hHpos).2
      nlinarith
    have hraw := norm_sourceDualIntegrandDerivative_le
      (X := X) (beta := beta) (u := u) (x := x) (g := g)
      hHpos hB
      (fun y ↦ (abs_faithfulCutoff_le_one y).trans (by dsimp [B]; linarith [faithfulCutoffDerivBudget_nonneg]))
      (fun y ↦ (abs_faithfulCutoffDeriv_le y).trans (by dsimp [B]; linarith))
    rw [abs_of_pos hX] at hraw
    have hinner : B / 2 + 2 * Real.pi * |beta| * X * Real.exp u * B +
        B * (X * Real.exp u / H) ≤ B * (6 + 10 * Real.pi) * (|beta| * X) := by
      have h1 : B / 2 ≤ B * (|beta| * X) := by nlinarith
      have h2 : 2 * Real.pi * |beta| * X * Real.exp u * B ≤
          10 * Real.pi * B * (|beta| * X) := by
        calc
          _ ≤ 2 * Real.pi * |beta| * X * 5 * B := by gcongr
          _ = _ := by ring
      have h3 : B * (X * Real.exp u / H) ≤ 5 * B * (|beta| * X) := by
        calc
          _ ≤ B * (X * 5 / H) := by gcongr
          _ = 5 * B * (X / H) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by positivity)
      linarith
    calc
      _ ≤ Real.sqrt X * Real.exp (u / 2) *
          (B / 2 + 2 * Real.pi * |beta| * X * Real.exp u * B +
            B * (X * Real.exp u / H)) * ‖g x‖ := hraw
      _ ≤ Real.sqrt X * 3 * (B * (6 + 10 * Real.pi) * (|beta| * X)) * ‖g x‖ := by
        gcongr
      _ = _ := by unfold faithfulHighDerivativeBudget B; ring
  · rw [faithful_sourceDualIntegrandDerivative_eq_zero_outside hHpos (lt_of_not_ge hp), norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg faithfulHighDerivativeBudget_nonneg
      (mul_nonneg (abs_nonneg _) hX.le)) (Real.sqrt_nonneg _)) (norm_nonneg _)

theorem faithful_sourceDualIntegrandDerivative_integrable
    {X H beta u : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    Integrable (sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g u) := by
  have hc : Continuous (fun x : ℝ ↦
      sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv (fun _ ↦ 1) u x) := by
    unfold sourceDualIntegrandDerivative
    have hc : Continuous (fun x : ℝ ↦ faithfulCutoff ((X * Real.exp u - x) / H)) :=
      faithfulCutoff_continuous.comp (by fun_prop)
    have hd : Continuous (fun x : ℝ ↦ faithfulCutoffDeriv ((X * Real.exp u - x) / H)) :=
      faithfulCutoffDeriv_continuous.comp (by fun_prop)
    fun_prop
  have hm : AEStronglyMeasurable
      (sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g u) := by
    have heq : sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g u =
        fun x ↦ sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv (fun _ ↦ 1) u x * g x := by
      funext x
      exact sourceDualIntegrandDerivative_factor _ _ _ _ _ _ _ _
    rw [heq]
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  apply (hg.norm.const_mul (faithfulHighDerivativeBudget * (|beta| * X) * Real.sqrt X)).mono' hm
  filter_upwards with x
  by_cases hx : x ∈ Icc (X / 2) (4 * X)
  · exact faithful_sourceDualIntegrandDerivative_le_physical hX hH hHalf hhard hx
  · simp [sourceDualIntegrandDerivative, hgSupport x hx]

theorem faithful_derivative_coefficient_le_window
    {X H beta z x : ℝ} {n : ℕ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖f n * (Real.sqrt n : ℂ)⁻¹ *
      sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g
        (Real.log n - Real.log X - z) x‖ ≤
      faithfulHighDerivativeBudget * (|beta| * X) * ‖g x‖ *
        (if |x - Real.exp (-z) * n| ≤ H then ‖f n‖ else 0) := by
  have hnX : X < (n : ℝ) := (Nat.floor_lt hX.le).mp (Finset.mem_Ioc.mp hn).1
  have hnpos : 0 < n := by exact_mod_cast (hX.trans hnX)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  by_cases hx : x ∈ Icc (X / 2) (4 * X)
  · by_cases hw : |x - Real.exp (-z) * n| ≤ H
    · rw [if_pos hw]
      have hraw := faithful_sourceDualIntegrandDerivative_le_physical
        (u := Real.log n - Real.log X - z) (g := g) hX hH hHalf hhard hx
      have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
      have hratio : (Real.sqrt (n : ℝ))⁻¹ * Real.sqrt X ≤ 1 := by
        have hd : Real.sqrt X / Real.sqrt n ≤ 1 :=
          (div_le_one hs).2 (Real.sqrt_le_sqrt hnX.le)
        simpa [div_eq_mul_inv, mul_comm] using hd
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      calc
        _ ≤ ‖f n‖ * (Real.sqrt (n : ℝ))⁻¹ *
            (faithfulHighDerivativeBudget * (|beta| * X) * Real.sqrt X * ‖g x‖) := by
          gcongr
        _ = (faithfulHighDerivativeBudget * (|beta| * X) * ‖g x‖ * ‖f n‖) *
            ((Real.sqrt (n : ℝ))⁻¹ * Real.sqrt X) := by ring
        _ ≤ (faithfulHighDerivativeBudget * (|beta| * X) * ‖g x‖ * ‖f n‖) * 1 :=
          mul_le_mul_of_nonneg_left hratio (by
            have := faithfulHighDerivativeBudget_nonneg
            positivity)
        _ = _ := mul_one _
    · rw [if_neg hw]
      have hp : H / 8 < |X * Real.exp (Real.log n - Real.log X - z) - x| := by
        rw [exp_log_shift_physical hX hnpos, abs_sub_comm]
        linarith [lt_of_not_ge hw]
      rw [faithful_sourceDualIntegrandDerivative_eq_zero_outside hHpos hp]
      simp
  · simp [sourceDualIntegrandDerivative, hgSupport x hx]

def faithfulTranslatedCriticalDerivative
    (X H beta : ℝ) (f : ℕ → ℂ) (g : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
    ∫ x : ℝ, sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g
      (Real.log n - Real.log X - z) x

theorem faithfulTranslatedCriticalDerivative_eq_zero_off
    {X H beta z : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0)
    (hz : Real.exp (-z) ∉ Icc (1 / 8) (17 / 4)) :
    faithfulTranslatedCriticalDerivative X H beta f g z = 0 := by
  unfold faithfulTranslatedCriticalDerivative
  apply Finset.sum_eq_zero
  intro n hn
  have hnX : X < (n : ℝ) := (Nat.floor_lt hX.le).mp (Finset.mem_Ioc.mp hn).1
  have hnFloor : (n : ℝ) ≤ ⌊2 * X⌋₊ := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hnTop : (n : ℝ) ≤ 2 * X := hnFloor.trans (Nat.floor_le (by positivity))
  have hnpos : 0 < n := by exact_mod_cast (hX.trans hnX)
  have hz0 := Real.exp_pos (-z)
  have hd (x : ℝ) : sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g
      (Real.log n - Real.log X - z) x = 0 := by
    by_cases hx : x ∈ Icc (X / 2) (4 * X)
    · apply faithful_sourceDualIntegrandDerivative_eq_zero_outside hH
      rw [exp_log_shift_physical hX hnpos]
      by_cases hlow : Real.exp (-z) < 1 / 8
      · have hm := mul_le_mul_of_nonneg_left hnTop hz0.le
        have hl := mul_lt_mul_of_pos_right hlow hX
        have hneg : Real.exp (-z) * n - x < 0 := by nlinarith [hx.1]
        rw [abs_of_neg hneg]
        nlinarith [hx.1]
      · have hhigh : 17 / 4 < Real.exp (-z) := by
          by_contra hh
          exact hz ⟨le_of_not_gt hlow, le_of_not_gt hh⟩
        have hm := mul_le_mul_of_nonneg_left hnX.le hz0.le
        have hl := mul_lt_mul_of_pos_right hhigh hX
        have hpos : 0 < Real.exp (-z) * n - x := by nlinarith [hx.2]
        rw [abs_of_pos hpos]
        nlinarith [hx.2]
    · simp [sourceDualIntegrandDerivative, hgSupport x hx]
  simp_rw [hd]
  simp

theorem faithfulTranslatedCriticalDerivative_le_window
    {X H beta z : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H) (hg : Integrable g) (hgL2 : MemLp g 2)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖faithfulTranslatedCriticalDerivative X H beta f g z‖ ≤
      faithfulHighDerivativeBudget * (|beta| * X) *
        ∫ x : ℝ, ‖g x‖ * scaledCenteredWindowSum X H (Real.exp (-z)) f x := by
  let C := faithfulHighDerivativeBudget * (|beta| * X)
  have hD : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      Integrable (fun x : ℝ ↦ f n * (Real.sqrt n : ℂ)⁻¹ *
        sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g
          (Real.log n - Real.log X - z) x) := by
    intro n hn
    exact (faithful_sourceDualIntegrandDerivative_integrable
      hX hH hHalf hhard hg hgSupport).const_mul _
  have heq : faithfulTranslatedCriticalDerivative X H beta f g z =
      ∫ x : ℝ, ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        f n * (Real.sqrt n : ℂ)⁻¹ * sourceDualIntegrandDerivative X H beta
          faithfulCutoff faithfulCutoffDeriv g (Real.log n - Real.log X - z) x := by
    rw [integral_finset_sum _ hD]
    simp only [integral_const_mul, faithfulTranslatedCriticalDerivative]
  have hW := hgL2.norm.integrable_mul
    (memLp_two_scaledCenteredWindowSum X H (Real.exp (-z)) f)
  rw [heq, ← integral_const_mul]
  calc
    _ ≤ ∫ x : ℝ, ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        f n * (Real.sqrt n : ℂ)⁻¹ * sourceDualIntegrandDerivative X H beta
          faithfulCutoff faithfulCutoffDeriv g (Real.log n - Real.log X - z) x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ norm_nonneg _) (hW.const_mul _)
      filter_upwards with x
      calc
        _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          ‖f n * (Real.sqrt n : ℂ)⁻¹ * sourceDualIntegrandDerivative X H beta
            faithfulCutoff faithfulCutoffDeriv g (Real.log n - Real.log X - z) x‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
            C * ‖g x‖ * (if |x - Real.exp (-z) * n| ≤ H then ‖f n‖ else 0) := by
          apply Finset.sum_le_sum
          intro n hn
          exact faithful_derivative_coefficient_le_window hX hH hHalf hhard hn hgSupport
        _ = _ := by
          unfold scaledCenteredWindowSum C
          rw [← Finset.mul_sum]
          simp only [Pi.mul_apply]
          ring

/-- Uniform derivative bound for the entire translated critical sum. -/
theorem faithfulTranslatedCriticalDerivative_norm_le
    {X H beta z : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H) (hg : Integrable g) (hgL2 : MemLp g 2)
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖faithfulTranslatedCriticalDerivative X H beta f g z‖ ≤
      faithfulHighDerivativeBudget * (|beta| * X) *
        Real.sqrt (1088 * ordinarySlidingMass X H f) := by
  by_cases hz : Real.exp (-z) ∈ Icc (1 / 8) (17 / 4)
  · have hw := integral_norm_mul_scaledWindow_sq_le
      (X := X) (H := H) (lambda := Real.exp (-z)) (f := f)
      hgL2 hgOne (le_trans zero_le_one hH) hz.1 hz.2
    have hs : (∫ x : ℝ, ‖g x‖ * scaledCenteredWindowSum X H (Real.exp (-z)) f x) ≤
        Real.sqrt (1088 * ordinarySlidingMass X H f) := Real.le_sqrt_of_sq_le hw
    exact (faithfulTranslatedCriticalDerivative_le_window hX hH hHalf hhard hg hgL2 hgSupport).trans
      (mul_le_mul_of_nonneg_left hs (mul_nonneg faithfulHighDerivativeBudget_nonneg
        (mul_nonneg (abs_nonneg _) hX.le)))
  · rw [faithfulTranslatedCriticalDerivative_eq_zero_off hX
      (lt_of_lt_of_le zero_lt_one hH) hHalf hgSupport hz, norm_zero]
    exact mul_nonneg (mul_nonneg faithfulHighDerivativeBudget_nonneg
      (mul_nonneg (abs_nonneg _) hX.le)) (Real.sqrt_nonneg _)

def faithfulTranslatedCriticalSum
    (X H beta : ℝ) (f : ℕ → ℂ) (g : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
    logarithmicDualFunction X H beta faithfulCutoff g (Real.log n - Real.log X - z)

theorem faithfulTranslatedCriticalSum_hasDerivAt
    {X H beta z : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hH : 0 < H) (hg : Integrable g) :
    HasDerivAt (faithfulTranslatedCriticalSum X H beta f g)
      (-faithfulTranslatedCriticalDerivative X H beta f g z) z := by
  have hG (u : ℝ) := hasDerivAt_logarithmicDualFunction
    (X := X) (beta := beta) (u := u) (B := 1 + faithfulCutoffDerivBudget)
    hH (by linarith [faithfulCutoffDerivBudget_nonneg])
    faithfulCutoff_continuous faithfulCutoffDeriv_continuous faithfulCutoff_hasDerivAt
    (fun y ↦ (abs_faithfulCutoff_le_one y).trans (by linarith [faithfulCutoffDerivBudget_nonneg]))
    (fun y ↦ (abs_faithfulCutoffDeriv_le y).trans (by linarith)) hg
  have ht (n : ℕ) : HasDerivAt
      (fun z : ℝ ↦ f n * (Real.sqrt n : ℂ)⁻¹ *
        logarithmicDualFunction X H beta faithfulCutoff g (Real.log n - Real.log X - z))
      (-(f n * (Real.sqrt n : ℂ)⁻¹ * ∫ x : ℝ,
        sourceDualIntegrandDerivative X H beta faithfulCutoff faithfulCutoffDeriv g
          (Real.log n - Real.log X - z) x)) z := by
    have hi : HasDerivAt (fun y : ℝ ↦ Real.log n - Real.log X - y) (-1) z := by
      simpa using (hasDerivAt_const z (Real.log n - Real.log X)).sub (hasDerivAt_id z)
    have hcomp := (hG (Real.log n - Real.log X - z)).scomp z hi
    simpa [Function.comp_def] using hcomp.const_mul (f n * (Real.sqrt n : ℂ)⁻¹)
  simpa [faithfulTranslatedCriticalSum, faithfulTranslatedCriticalDerivative] using
    (HasDerivAt.fun_sum (u := Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) (fun n hn ↦ ht n))

theorem faithfulTranslatedCriticalSum_sub_le
    {X H beta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H) (hg : Integrable g) (hgL2 : MemLp g 2)
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) (z : ℝ) :
    ‖faithfulTranslatedCriticalSum X H beta f g 0 - faithfulTranslatedCriticalSum X H beta f g z‖ ≤
      (faithfulHighDerivativeBudget * (|beta| * X) * Real.sqrt (1088 * ordinarySlidingMass X H f)) * |z| := by
  have hd (u : ℝ) := faithfulTranslatedCriticalSum_hasDerivAt
    (X := X) (beta := beta) (z := u) (f := f) (lt_of_lt_of_le zero_lt_one hH) hg
  have hb (u : ℝ) : ‖deriv (faithfulTranslatedCriticalSum X H beta f g) u‖ ≤
      faithfulHighDerivativeBudget * (|beta| * X) * Real.sqrt (1088 * ordinarySlidingMass X H f) := by
    rw [(hd u).deriv, norm_neg]
    exact faithfulTranslatedCriticalDerivative_norm_le hX hH hHalf hhard hg hgL2 hgOne hgSupport
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (Set.univ : Set ℝ)) (fun u _ ↦ (hd u).differentiableAt)
    (fun u _ ↦ hb u) convex_univ (Set.mem_univ z) (Set.mem_univ (0 : ℝ))
  simpa [Real.norm_eq_abs] using hm

def faithfulHighKernelMoment : ℝ :=
  ∫ v : ℝ, |v| * ‖cutoffFourierKernel faithfulCutoff v‖

theorem faithfulHighKernelMoment_nonneg : 0 ≤ faithfulHighKernelMoment := by
  unfold faithfulHighKernelMoment
  exact integral_nonneg fun v ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem faithfulHighKernelMoment_integrable :
    Integrable (fun v : ℝ ↦ |v| * ‖cutoffFourierKernel faithfulCutoff v‖) := by
  simpa [faithfulCutoffFourierKernel_eq_schwartz, Real.norm_eq_abs] using
    faithfulCutoffFourierSchwartz.integrable_pow_mul volume 1

theorem faithfulCutoffFourierKernel_mass : ∫ v : ℝ, cutoffFourierKernel faithfulCutoff v = 1 := by
  have hi : Integrable (fun y : ℝ ↦ (faithfulCutoff y : ℂ)) := faithfulCutoffSchwartz.integrable
  have hF : Integrable (𝓕 (fun y : ℝ ↦ (faithfulCutoff y : ℂ))) := faithfulCutoffFourierKernel_integrable
  have hc : Continuous (fun y : ℝ ↦ (faithfulCutoff y : ℂ)) :=
    Complex.continuous_ofReal.comp faithfulCutoff_continuous
  have hinv := hi.fourierInv_fourier_eq hF (hc.continuousAt (x := 0))
  simpa [Real.fourierInv_eq', cutoffFourierKernel, faithfulCutoff_one (by norm_num : |(0 : ℝ)| ≤ 1 / 10)] using hinv

theorem faithful_translated_kernel_integrable
    {G : ℝ → ℂ} {s u : ℝ} (hs : s ≠ 0) (hG : Integrable G) :
    Integrable (fun v : ℝ ↦ G (u - s * v) * cutoffFourierKernel faithfulCutoff v) := by
  have hi := (hG.comp_sub_left u).comp_mul_left' hs
  have hb (v : ℝ) : ‖cutoffFourierKernel faithfulCutoff v‖ ≤ faithfulCutoffFourierDecayConstant 0 := by
    simpa using norm_faithfulCutoffFourierKernel_le_decay 0 v
  have hm := hi.bdd_mul faithfulCutoffFourierKernel_continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  simpa [mul_comm] using hm

theorem faithful_highProjectedSum_eq_translated
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
      highFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g) (Real.log n - Real.log X)) =
      faithfulTranslatedCriticalSum X H beta f g 0 -
        ∫ v : ℝ, faithfulTranslatedCriticalSum X H beta f g
          ((2 * Real.pi * eta / (|beta| * X)) * v) * cutoffFourierKernel faithfulCutoff v := by
  have hG := faithful_logarithmicDual_integrable_half_range (beta := beta) hX hH hHalf hg hgSupport
  have hs : 2 * Real.pi * eta / (|beta| * X) ≠ 0 := by positivity
  have hsum : (∫ v : ℝ, faithfulTranslatedCriticalSum X H beta f g
        ((2 * Real.pi * eta / (|beta| * X)) * v) * cutoffFourierKernel faithfulCutoff v) =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
        ∫ v : ℝ, logarithmicDualFunction X H beta faithfulCutoff g
          (Real.log n - Real.log X - (2 * Real.pi * eta / (|beta| * X)) * v) *
            cutoffFourierKernel faithfulCutoff v := by
    unfold faithfulTranslatedCriticalSum
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro n hn
      simpa only [mul_assoc] using ((faithful_translated_kernel_integrable (u := Real.log n - Real.log X) hs hG).const_mul
        ((Real.sqrt n : ℂ)⁻¹)).const_mul (f n)
  rw [hsum]
  unfold highFrequencyProjection mediumOrLowProjection rescaledProjection
  have hshift (v : ℝ) : 2 * Real.pi * v / (|beta| * X / eta) =
      (2 * Real.pi * eta / (|beta| * X)) * v := by field_simp
  simp_rw [hshift, mul_sub, Finset.sum_sub_distrib]
  simp [faithfulTranslatedCriticalSum]

theorem faithful_translatedSum_kernel_integrable
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    Integrable (fun v : ℝ ↦ faithfulTranslatedCriticalSum X H beta f g
      ((2 * Real.pi * eta / (|beta| * X)) * v) * cutoffFourierKernel faithfulCutoff v) := by
  have hG := faithful_logarithmicDual_integrable_half_range (beta := beta) hX hH hHalf hg hgSupport
  have hs : 2 * Real.pi * eta / (|beta| * X) ≠ 0 := by positivity
  unfold faithfulTranslatedCriticalSum
  simp_rw [Finset.sum_mul, mul_assoc]
  apply integrable_finset_sum
  intro n hn
  simpa only [mul_assoc] using ((faithful_translated_kernel_integrable (u := Real.log n - Real.log X) hs hG).const_mul
        ((Real.sqrt n : ℂ)⁻¹)).const_mul (f n)

/-- The raw high projection has the source `eta` gain. -/
theorem faithful_highProjectedSum_norm_le
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H) (heta : 0 < eta)
    (hg : Integrable g) (hgL2 : MemLp g 2)
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
      highFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g) (Real.log n - Real.log X)‖ ≤
      (2 * Real.pi * faithfulHighDerivativeBudget * faithfulHighKernelMoment) * eta *
        Real.sqrt (1088 * ordinarySlidingMass X H f) := by
  let S := faithfulTranslatedCriticalSum X H beta f g
  let s := 2 * Real.pi * eta / (|beta| * X)
  let D := faithfulHighDerivativeBudget * (|beta| * X) * Real.sqrt (1088 * ordinarySlidingMass X H f)
  have hs : 0 < s := by dsimp [s]; positivity
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg faithfulHighDerivativeBudget_nonneg
    (mul_nonneg (abs_nonneg _) hX.le)) (Real.sqrt_nonneg _)
  have hi := faithful_translatedSum_kernel_integrable (f := f)
    hX (lt_of_lt_of_le zero_lt_one hH) hHalf hbeta heta hg hgSupport
  rw [faithful_highProjectedSum_eq_translated hX (lt_of_lt_of_le zero_lt_one hH)
    hHalf hbeta heta hg hgSupport]
  change ‖S 0 - ∫ v : ℝ, S (s * v) * cutoffFourierKernel faithfulCutoff v‖ ≤ _
  have heq : S 0 - (∫ v : ℝ, S (s * v) * cutoffFourierKernel faithfulCutoff v) =
      ∫ v : ℝ, (S 0 - S (s * v)) * cutoffFourierKernel faithfulCutoff v := by
    simp_rw [sub_mul]
    rw [integral_sub (faithfulCutoffFourierKernel_integrable.const_mul (S 0)) hi,
      integral_const_mul, faithfulCutoffFourierKernel_mass, mul_one]
  rw [heq]
  have hn : ‖∫ v : ℝ, (S 0 - S (s * v)) * cutoffFourierKernel faithfulCutoff v‖ ≤
      D * s * faithfulHighKernelMoment := by
    calc
      _ ≤ ∫ v : ℝ, ‖(S 0 - S (s * v)) * cutoffFourierKernel faithfulCutoff v‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (D * s) * (|v| * ‖cutoffFourierKernel faithfulCutoff v‖) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun v ↦ norm_nonneg _)
          (faithfulHighKernelMoment_integrable.const_mul _)
        filter_upwards with v
        rw [norm_mul]
        have hm := faithfulTranslatedCriticalSum_sub_le (f := f) hX hH hHalf hhard hg hgL2 hgOne hgSupport (s * v)
        change ‖S 0 - S (s * v)‖ ≤ D * |s * v| at hm
        rw [abs_mul, abs_of_pos hs] at hm
        calc
          _ ≤ (D * (s * |v|)) * ‖cutoffFourierKernel faithfulCutoff v‖ :=
            mul_le_mul_of_nonneg_right hm (norm_nonneg _)
          _ = _ := by ring
      _ = _ := by rw [integral_const_mul]; rfl
  refine hn.trans_eq ?_
  dsimp [D, s]
  field_simp [hX.ne', abs_ne_zero.mpr hbeta]
  <;> ring

def faithfulHighProjectionConstant : ℝ :=
  1088 * (2 * Real.pi * faithfulHighDerivativeBudget * faithfulHighKernelMoment) ^ 2

theorem faithful_highProjectedSum_sq_le
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H) (heta : 0 < eta)
    (hg : Integrable g) (hgL2 : MemLp g 2)
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
      highFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g) (Real.log n - Real.log X)‖ ^ 2 ≤
      faithfulHighProjectionConstant * eta ^ 2 * ordinarySlidingMass X H f := by
  have h := faithful_highProjectedSum_norm_le (f := f) hX hH hHalf hbeta hhard heta hg hgL2 hgOne hgSupport
  have hM : 0 ≤ ordinarySlidingMass X H f := integral_nonneg fun x ↦ sq_nonneg _
  calc
    _ ≤ ((2 * Real.pi * faithfulHighDerivativeBudget * faithfulHighKernelMoment) * eta *
        Real.sqrt (1088 * ordinarySlidingMass X H f)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hM)]
      unfold faithfulHighProjectionConstant
      ring

#print axioms faithful_highProjectedSum_sq_le
#print axioms faithfulTranslatedCriticalSum_sub_le
#print axioms faithfulCutoffFourierKernel_mass
#print axioms faithfulTranslatedCriticalDerivative_norm_le
#print axioms faithful_sourceDualIntegrandDerivative_le_physical
end
end MAPMRTFaithfulHighProjection
