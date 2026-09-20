import AppendixA4DetectorDichotomy
import AppendixA8A9Certified
import GuthMaynardJIterationDeterministic

/-!
# Set-level post-A.5 detector adapter

This module turns the certified pointwise detector alternative into an exact
finite-set partition.  On the Type-I fiber it performs the simultaneous
multiplicative dyadic pigeonhole step, producing one block index common to a
large subset.  The Type-II fiber retains the literal critical-line witness.

No large-value theorem is assumed or asserted here.
-/

namespace MAPAppendixA4PostA5SetAdapter

open Set MeasureTheory Complex
open scoped BigOperators FourierTransform
open MAPAppendixA4GammaEndpoint MAPAppendixA4DetectorDichotomy
  FixedCharacterPoweredBridge CGLProofDAG SchwartzMap

noncomputable section

variable {q : ℕ} [NeZero q]

/-! ## Subpower detector coefficient normalization -/

/-- The surviving truncated divisor pairs inject into the ordinary divisor
set.  Unlike the crude U+1 bound, this is subpolynomial in the Dirichlet
polynomial length. -/
theorem card_detectorSupport_le_divisors
    {n : ℕ} (hn : n ≠ 0) (U : ℕ) :
    ((n.divisorsAntidiagonal).filter (fun p => p.2 ≤ U)).card ≤
      n.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    have hpa := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hp).1
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn⟩
    refine ⟨p.1, ?_⟩
    rw [mul_comm]
    exact hpa.1.symm
  · intro p hp r hr heq
    have hpa := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hp).1
    have hra := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hr).1
    have hspos : 0 < p.2 := by
      by_contra h
      have hz : p.2 = 0 := Nat.eq_zero_of_not_pos h
      apply hn
      simpa [hz] using hpa.1.symm
    apply Prod.ext
    · apply Nat.eq_of_mul_eq_mul_right hspos
      calc
        p.1 * p.2 = n := hpa.1
        _ = r.1 * r.2 := hra.1.symm
        _ = r.1 * p.2 := by rw [heq]
    · exact heq

/-- The exact mollifier coefficient is bounded by the order-two convolution
divisor majorant, eliminating the power-sized U+1 normalization loss. -/
theorem norm_mollifierCoeff_le_orderedDivisorCount_two
    (U : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ‖MAPMollifierCoefficientIdentity.mollifierCoeff U n‖ ≤
      CGLProofDAG.orderedDivisorCount 2 n := by
  rw [MAPMollifierCoefficientIdentity.mollifierCoeff_apply]
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal,
        MAPMollifierCoefficientIdentity.truncatedMoebius U p.2‖
        ≤ ∑ p ∈ n.divisorsAntidiagonal,
          ‖MAPMollifierCoefficientIdentity.truncatedMoebius U p.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        if p.2 ≤ U then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      unfold MAPMollifierCoefficientIdentity.truncatedMoebius
      split_ifs with h
      · change ‖((ArithmeticFunction.moebius p.2 : ℤ) : ℂ)‖ ≤ 1
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.2)
      · simp
    _ = (((n.divisorsAntidiagonal).filter (fun p => p.2 ≤ U)).card : ℝ) := by
      simp
    _ ≤ n.divisors.card := by
      exact_mod_cast card_detectorSupport_le_divisors hn U
    _ = CGLProofDAG.orderedDivisorCount 2 n := by
      exact_mod_cast
        (GuthMaynardJIteration.orderedDivisorCount_two_eq_card_divisors hn).symm

/-! ## Exact phase and dyadic decomposition -/

/-- Separate the zero-real-part weight and zero-ordinate phase in one literal
detector summand. -/
theorem arithmeticDetectorTerm_eq_weight_phase
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ) (Y : ℝ)
    {n : ℕ} (hn : 0 < n) :
    arithmeticDetectorTerm chi U rho Y n =
      (((Real.rpow n (-rho.re) * Real.exp (-((n : ℝ) / Y)) : ℝ) : ℂ) *
        (detectorCoeff chi U n *
          Complex.exp (Complex.I * ((-rho.im) * Real.log n)))) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold arithmeticDetectorTerm
  rw [LSeries.term_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hnC]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_log hnRpos.le]
  have hrpow : Real.rpow (n : ℝ) (-rho.re) =
      Real.exp (Real.log n * (-rho.re)) :=
    Real.rpow_def_of_pos hnRpos _
  rw [hlog, hrpow]
  push_cast
  simp only [div_eq_mul_inv, ← Complex.exp_neg]
  rw [hlog]
  have hz : -((Real.log n : ℂ) * rho) =
      ((-(Real.log n * rho.re) : ℝ) : ℂ) +
        Complex.I * (((-rho.im) * Real.log n : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [hz, Complex.exp_add]
  have hre : ((-(Real.log n * rho.re) : ℝ) : ℂ) =
      -((Real.log n : ℂ) * (rho.re : ℂ)) := by push_cast; ring
  have him : Complex.I * (((-rho.im) * Real.log n : ℝ) : ℂ) =
      -(Complex.I * (Real.log n : ℂ) * (rho.im : ℂ)) := by push_cast; ring
  rw [hre, him]
  ring

private theorem log2_mono_of_pos_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m.log2 ≤ n.log2 := by
  by_contra h
  have hsucc : n.log2 + 1 ≤ m.log2 := by omega
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hn0 : n ≠ 0 := Nat.ne_of_gt (hm.trans_le hmn)
  have hlower : 2 ^ (n.log2 + 1) ≤ m :=
    (Nat.le_log2 hm0).mp hsucc
  have hupper : n < 2 ^ (n.log2 + 1) :=
    (Nat.log2_lt hn0).mp (lt_add_one n.log2)
  omega

/-- Number of literal standard shells (2^j,2^(j+1)] needed to cover
2 ≤ n ≤ N.  The shift by one in the logarithm makes both dyadic endpoints
agree exactly with the Finset.Ioc convention used by the powered bridge. -/
def detectorDyadicCount (N : ℕ) : ℕ := (N - 1).log2 + 1

/-- The j-th base-two dyadic shell of the finite arithmetic detector.  The
global cutoffs remain in the filter, so boundary shells are zero-padded rather
than silently enlarged. -/
def arithmeticDetectorDyadicBlock
    (chi : DirichletCharacter ℂ q) (U N : ℕ) (rho : ℂ) (Y : ℝ)
    (j : Fin (detectorDyadicCount N)) : ℂ :=
  ∑ n ∈ (Finset.Ico (U + 1) (N + 1)).filter
      (fun n => (n - 1).log2 = (j : ℕ)),
    arithmeticDetectorTerm chi U rho Y n

/-- The shifted logarithmic bucket is exactly the standard half-open dyadic
interval used by dirichletPolynomial. -/
theorem log2_sub_one_eq_iff_mem_Ioc
    {n j : ℕ} (hn : 2 ≤ n) :
    (n - 1).log2 = j ↔ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
  have hm0 : n - 1 ≠ 0 := by omega
  rw [Finset.mem_Ioc]
  constructor
  · intro hlog
    have hlo : 2 ^ (n - 1).log2 ≤ n - 1 := Nat.log2_self_le hm0
    have hhi : n - 1 < 2 ^ ((n - 1).log2 + 1) :=
      (Nat.log2_lt hm0).mp (lt_add_one (n - 1).log2)
    rw [hlog] at hlo hhi
    constructor
    · omega
    · rw [pow_succ] at hhi
      omega
  · rintro ⟨hlo, hhi⟩
    have hlowpow : 2 ^ j ≤ n - 1 := by omega
    have hhighpow : n - 1 < 2 ^ (j + 1) := by
      rw [pow_succ]
      omega
    have hjlow : j ≤ (n - 1).log2 := (Nat.le_log2 hm0).mpr hlowpow
    have hjhigh : (n - 1).log2 < j + 1 := (Nat.log2_lt hm0).mpr hhighpow
    omega

/-- Exact decomposition of the finite detector into its base-two dyadic
shells. -/
theorem sum_arithmeticDetectorDyadicBlock_eq
    (chi : DirichletCharacter ℂ q) {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    (rho : ℂ) (Y : ℝ) :
    ∑ j : Fin (detectorDyadicCount N),
        arithmeticDetectorDyadicBlock chi U N rho Y j =
      arithmeticDetectorBlock chi U N rho Y := by
  classical
  let s : Finset ℕ := Finset.Ico (U + 1) (N + 1)
  let g : ℕ → Fin (detectorDyadicCount N) := fun n =>
    if hn : n ∈ s then
      ⟨(n - 1).log2, by
        unfold detectorDyadicCount
        apply Nat.lt_succ_iff.mpr
        exact log2_mono_of_pos_le
          (by have := (Finset.mem_Ico.mp hn).1; omega)
          (Nat.sub_le_sub_right
            (Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hn).2) 1)⟩
    else ⟨0, by unfold detectorDyadicCount; omega⟩
  have hmaps : ∀ n ∈ s,
      g n ∈ (Finset.univ : Finset (Fin (detectorDyadicCount N))) :=
    fun n hn => Finset.mem_univ _
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => arithmeticDetectorTerm chi U rho Y n)
  have hfilter : ∀ j : Fin (detectorDyadicCount N),
      s.filter (fun n => (n - 1).log2 = (j : ℕ)) =
        s.filter (fun n => g n = j) := by
    intro j
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hlog⟩
      refine ⟨hn, ?_⟩
      simp only [g, dif_pos hn]
      exact Fin.ext hlog
    · rintro ⟨hn, hg⟩
      refine ⟨hn, ?_⟩
      simp only [g, dif_pos hn] at hg
      exact congrArg Fin.val hg
  calc
    (∑ j : Fin (detectorDyadicCount N),
        arithmeticDetectorDyadicBlock chi U N rho Y j) =
        ∑ j : Fin (detectorDyadicCount N),
          ∑ n ∈ s.filter (fun n => g n = j),
            arithmeticDetectorTerm chi U rho Y n := by
          apply Finset.sum_congr rfl
          intro j hj
          unfold arithmeticDetectorDyadicBlock
          rw [← hfilter j]
    _ = ∑ n ∈ s, arithmeticDetectorTerm chi U rho Y n := hfiber
    _ = arithmeticDetectorBlock chi U N rho Y := by
      rfl

/-! ## Generic simultaneous block choice -/

/-- Finite simultaneous pigeonhole over an arbitrary index set.  This is the
same argument as FixedCharacterPoweredBridge.exists_common_large_block, but
the points are complex zeros rather than ordinates. -/
theorem exists_common_large_block_on
    {α : Type*} [DecidableEq α]
    {r : ℕ} {Z : Finset α} {block : Fin r → α → ℂ}
    {total : α → ℂ} {V : ℝ}
    (hr : 0 < r)
    (hdecomp : ∀ z ∈ Z, total z = ∑ i, block i z)
    (hlarge : ∀ z ∈ Z, V ≤ ‖total z‖) :
    ∃ i : Fin r, ∃ S : Finset α,
      S ⊆ Z ∧ Z.card ≤ r * S.card ∧
      ∀ z ∈ S, V ≤ r * ‖block i z‖ := by
  classical
  let chooseIndex : α → Fin r := fun z =>
    if hz : z ∈ Z then
      Classical.choose (AppendixTypeIPower.exists_block_with_large_norm
        hr (fun i => block i z))
    else ⟨0, hr⟩
  have hchoice : ∀ z ∈ Z,
      ‖total z‖ ≤ r * ‖block (chooseIndex z) z‖ := by
    intro z hz
    rw [hdecomp z hz]
    simpa [chooseIndex, hz] using
      (Classical.choose_spec (AppendixTypeIPower.exists_block_with_large_norm
        hr (fun i => block i z)))
  let fiber : Fin r → Finset α := fun i => Z.filter (fun z => chooseIndex z = i)
  have hcard : Z.card = ∑ i, (fiber i).card := by
    calc
      Z.card = ∑ z ∈ Z, 1 := by simp
      _ = ∑ i : Fin r, ∑ z ∈ Z with chooseIndex z = i, 1 := by
        symm
        exact Finset.sum_fiberwise Z chooseIndex (fun _ => 1)
      _ = ∑ i, (fiber i).card := by simp [fiber]
  have hsum :
      (∑ _i : Fin r, Z.card) ≤ ∑ i : Fin r, r * (fiber i).card := by
    calc
      (∑ _i : Fin r, Z.card) = r * Z.card := by simp
      _ = r * ∑ i : Fin r, (fiber i).card := by rw [← hcard]
      _ ≤ ∑ i : Fin r, r * (fiber i).card := by rw [Finset.mul_sum]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩ hsum
  refine ⟨i, fiber i, Finset.filter_subset _ _, hi, ?_⟩
  intro z hz
  have hzZ : z ∈ Z := (Finset.mem_filter.mp hz).1
  have hzi : chooseIndex z = i := (Finset.mem_filter.mp hz).2
  calc
    V ≤ ‖total z‖ := hlarge z hzZ
    _ ≤ r * ‖block (chooseIndex z) z‖ := hchoice z hzZ
    _ = r * ‖block i z‖ := by rw [hzi]

/-- A common literal standard dyadic detector shell survives on at least a
1 / detectorDyadicCount N fraction of every finite Type-I zero set. -/
theorem exists_common_arithmeticDetectorDyadicBlock
    (chi : DirichletCharacter ℂ q) {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {Z : Finset ℂ} {Y V : ℝ}
    (hlarge : ∀ rho ∈ Z, V ≤ ‖arithmeticDetectorBlock chi U N rho Y‖) :
    ∃ j : Fin (detectorDyadicCount N), ∃ S : Finset ℂ,
      S ⊆ Z ∧
      Z.card ≤ detectorDyadicCount N * S.card ∧
      ∀ rho ∈ S,
        V ≤ detectorDyadicCount N *
          ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖ := by
  have hcount : 0 < detectorDyadicCount N := by
    unfold detectorDyadicCount
    omega
  apply exists_common_large_block_on hcount
    (total := fun rho => arithmeticDetectorBlock chi U N rho Y)
    (block := fun j rho => arithmeticDetectorDyadicBlock chi U N rho Y j)
  · intro rho hrho
    exact (sum_arithmeticDetectorDyadicBlock_eq chi hU hUN rho Y).symm
  · exact hlarge

/-! ## Concrete Fourier real-part removal on the common shell -/

/-- Fixed-width smooth bump centered at the logarithm of a dyadic length. -/
def detectorRealPartBump (D : ℕ) : ContDiffBump (Real.log D) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- Concrete Schwartz cutoff used to remove the varying real part.  It equals
exp(-a*x) throughout the unit logarithmic collar around log D. -/
def detectorRealPartCutoff (a : ℝ) (D : ℕ) : 𝓢(ℝ, ℂ) := by
  let zeta : ContDiffBump (Real.log D) := detectorRealPartBump D
  let f : ℝ → ℂ := fun x =>
    (zeta x : ℂ) * (Real.exp (-a * x) : ℂ)
  have hzeta : HasCompactSupport (fun x : ℝ => (zeta x : ℂ)) := by
    simpa only [Function.comp_apply] using
      zeta.hasCompactSupport.comp_left
        (show (fun x : ℝ => (x : ℂ)) 0 = 0 by norm_num)
  have hfcompact : HasCompactSupport f := by
    exact hzeta.mul_right
  have hfsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f := by
    dsimp [f]
    have hzR : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => zeta x) :=
      zeta.contDiff
    have hzC : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (zeta x : ℂ)) := by
      simpa only [Function.comp_apply] using Complex.ofRealCLM.contDiff.comp hzR
    have heR : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x : ℝ => Real.exp (-a * x)) := by fun_prop
    have heC : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x : ℝ => (Real.exp (-a * x) : ℂ)) := by
      simpa only [Function.comp_apply] using Complex.ofRealCLM.contDiff.comp heR
    exact hzC.mul heC
  exact hfcompact.toSchwartzMap hfsmooth

theorem detectorRealPartCutoff_apply_of_mem_closedBall
    {a x : ℝ} {D : ℕ}
    (hx : x ∈ Metric.closedBall (Real.log D) 1) :
    detectorRealPartCutoff a D x =
      (Real.exp (-a * x) : ℂ) := by
  let zeta : ContDiffBump (Real.log D) := detectorRealPartBump D
  have hzeta : zeta x = 1 := by
    apply zeta.one_of_mem_closedBall
    simpa [zeta, detectorRealPartBump] using hx
  change (zeta x : ℂ) * (Real.exp (-a * x) : ℂ) =
    (Real.exp (-a * x) : ℂ)
  rw [hzeta]
  simp

/-- The unit collar contains every logarithm in the standard dyadic shell. -/
theorem log_mem_detectorRealPartCutoff_collar
    {D n : ℕ} (hD : 1 ≤ D) (hn : n ∈ Finset.Ioc D (2 * D)) :
    Real.log n ∈ Metric.closedBall (Real.log D) 1 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < D) (Finset.mem_Ioc.mp hn).1.le)
  have hlo : Real.log D ≤ Real.log n := by
    apply Real.log_le_log hDpos
    exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
  have hnD : (n : ℝ) ≤ 2 * D := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hhi0 : Real.log n ≤ Real.log (2 * D) :=
    Real.log_le_log hnpos hnD
  have hlogmul : Real.log (2 * D : ℝ) = Real.log 2 + Real.log D := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < D)) : (D : ℝ) ≠ 0)]
  have hlogtwo : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  rw [hlogmul] at hhi0
  constructor <;> linarith

/-- The beta-independent coefficient before real-part removal, including the
literal global detector support and exponential smoothing. -/
def detectorFourierBaseCoefficient
    (chi : DirichletCharacter ℂ q) (U N : ℕ) (Y : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ico (U + 1) (N + 1) then
    (Real.exp (-((n : ℝ) / Y)) : ℂ) * detectorCoeff chi U n
  else 0

/-- The common coefficient on the fixed sigma line after Fourier removal. -/
def detectorCommonCoefficient
    (chi : DirichletCharacter ℂ q) (U N : ℕ) (Y sigma : ℝ) (n : ℕ) : ℂ :=
  (Real.rpow n (-sigma) : ℂ) *
    detectorFourierBaseCoefficient chi U N Y n

private theorem arithmeticDetectorTerm_eq_finiteDirichletTerm
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ) (Y : ℝ)
    {n : ℕ} (hn : 0 < n) :
    arithmeticDetectorTerm chi U rho Y n =
      ((Real.exp (-((n : ℝ) / Y)) : ℂ) * detectorCoeff chi U n) *
        FourierRealPartRemoval.dirichletWeight (Real.log n) rho.re rho.im := by
  rw [arithmeticDetectorTerm_eq_weight_phase chi U rho Y hn]
  unfold FourierRealPartRemoval.dirichletWeight
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrpow : Real.rpow (n : ℝ) (-rho.re) =
      Real.exp (Real.log n * (-rho.re)) :=
    Real.rpow_def_of_pos hnRpos _
  rw [hrpow]
  rw [show (-(rho.re * Real.log n) : ℂ) -
      Complex.I * (rho.im * Real.log n) =
        ((Real.log n * (-rho.re) : ℝ) : ℂ) +
          Complex.I * (((-rho.im) * Real.log n : ℝ) : ℂ) by
    apply Complex.ext <;> simp <;> ring]
  rw [Complex.exp_add]
  push_cast
  ring

/-- One literal detector shell is exactly a finite Dirichlet block with the
global cutoff encoded in a beta-independent coefficient. -/
theorem arithmeticDetectorDyadicBlock_eq_finiteDirichletBlock
    (chi : DirichletCharacter ℂ q) {U N : ℕ} (hU : 1 ≤ U)
    (rho : ℂ) (Y : ℝ) (j : Fin (detectorDyadicCount N)) :
    arithmeticDetectorDyadicBlock chi U N rho Y j =
      FourierRealPartRemoval.finiteDirichletBlock
        (Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)))
        (detectorFourierBaseCoefficient chi U N Y)
        (fun n => Real.log n) rho.re rho.im := by
  classical
  let G : Finset ℕ := Finset.Ico (U + 1) (N + 1)
  let D : ℕ := 2 ^ (j : ℕ)
  let S : Finset ℕ := G.filter (fun n => (n - 1).log2 = (j : ℕ))
  have hsub : S ⊆ Finset.Ioc D (2 * D) := by
    intro n hn
    have hnG : n ∈ G := (Finset.mem_filter.mp hn).1
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Ico.mp hnG).1
      omega
    exact (log2_sub_one_eq_iff_mem_Ioc hn2).mp
      (Finset.mem_filter.mp hn).2
  unfold arithmeticDetectorDyadicBlock
  change (∑ n ∈ S, arithmeticDetectorTerm chi U rho Y n) = _
  unfold FourierRealPartRemoval.finiteDirichletBlock
  apply Finset.sum_subset_zero_on_sdiff hsub
  · intro n hnDiff
    have hnI : n ∈ Finset.Ioc D (2 * D) := (Finset.mem_sdiff.mp hnDiff).1
    have hnnot : n ∉ S := (Finset.mem_sdiff.mp hnDiff).2
    have hnnotG : n ∉ G := by
      intro hnG
      apply hnnot
      apply Finset.mem_filter.mpr
      refine ⟨hnG, ?_⟩
      have hn2 : 2 ≤ n := by
        have := (Finset.mem_Ico.mp hnG).1
        omega
      exact (log2_sub_one_eq_iff_mem_Ioc hn2).mpr (by simpa [D] using hnI)
    simp only [detectorFourierBaseCoefficient, G]
    rw [if_neg hnnotG]
    simp
  · intro n hn
    have hnG : n ∈ G := (Finset.mem_filter.mp hn).1
    have hnpos : 0 < n := by
      have := (Finset.mem_Ico.mp hnG).1
      omega
    rw [arithmeticDetectorTerm_eq_finiteDirichletTerm chi U rho Y hnpos]
    simp only [detectorFourierBaseCoefficient, G] at hnG ⊢
    rw [if_pos hnG]

/-- The fixed-sigma finite block is exactly the standard common-coefficient
Dirichlet polynomial, with the sign conversion dictated by the two phase
conventions. -/
theorem finiteDirichletBlock_eq_common_dirichletPolynomial
    (chi : DirichletCharacter ℂ q) (U N : ℕ) (Y sigma gamma : ℝ)
    {D : ℕ} (hD : 1 ≤ D) :
    FourierRealPartRemoval.finiteDirichletBlock
        (Finset.Ioc D (2 * D))
        (detectorFourierBaseCoefficient chi U N Y)
        (fun n => Real.log n) sigma gamma =
      dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D (-gamma) := by
  classical
  unfold FourierRealPartRemoval.finiteDirichletBlock dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnposNat : 0 < n :=
    lt_of_lt_of_le (by omega : 0 < D) (Finset.mem_Ioc.mp hn).1.le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hrpow : Real.rpow (n : ℝ) (-sigma) =
      Real.exp (Real.log n * (-sigma)) :=
    Real.rpow_def_of_pos hnpos _
  unfold detectorCommonCoefficient FourierRealPartRemoval.dirichletWeight
  rw [hrpow]
  rw [show (-(sigma * Real.log n) : ℂ) -
      Complex.I * (gamma * Real.log n) =
        ((Real.log n * (-sigma) : ℝ) : ℂ) +
          Complex.I * (((-gamma) * Real.log n : ℝ) : ℂ) by
    apply Complex.ext <;> simp <;> ring]
  rw [Complex.exp_add]
  push_cast
  ring

/-- Literal A.9 real-part removal for the selected detector shell.  The
coefficient of the Dirichlet polynomial on the right is independent of rho;
all rho-dependence is now in the explicit Schwartz transform and shifted
ordinate. -/
theorem arithmeticDetectorDyadicBlock_fourier_removal
    (chi : DirichletCharacter ℂ q) {U N : ℕ} (hU : 1 ≤ U)
    (rho : ℂ) (Y sigma : ℝ) (j : Fin (detectorDyadicCount N)) :
    arithmeticDetectorDyadicBlock chi U N rho Y j =
      ∫ xi : ℝ,
        (𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi *
        dirichletPolynomial
          (detectorCommonCoefficient chi U N Y sigma)
          (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * xi) := by
  let D : ℕ := 2 ^ (j : ℕ)
  let psi : 𝓢(ℝ, ℂ) := detectorRealPartCutoff (rho.re - sigma) D
  have hD : 1 ≤ D := by
    dsimp [D]
    exact Nat.one_le_two_pow
  have hpsi : ∀ n ∈ Finset.Ioc D (2 * D),
      psi (Real.log n) =
        Complex.exp (-((rho.re - sigma) * Real.log n)) := by
    intro n hn
    dsimp [psi]
    rw [detectorRealPartCutoff_apply_of_mem_closedBall
      (log_mem_detectorRealPartCutoff_collar hD hn)]
    calc
      (Real.exp (-(rho.re - sigma) * Real.log n) : ℂ) =
          Complex.exp (((-(rho.re - sigma) * Real.log n : ℝ) : ℂ)) :=
        Complex.ofReal_exp _
      _ = Complex.exp (-((rho.re - sigma) * Real.log n : ℂ)) := by
        congr 1
        push_cast
        ring
  rw [arithmeticDetectorDyadicBlock_eq_finiteDirichletBlock chi hU]
  rw [FourierRealPartRemoval.finite_dirichlet_real_part_removal
    (s := Finset.Ioc D (2 * D))
    (c := detectorFourierBaseCoefficient chi U N Y)
    (x := fun n => Real.log n) (σ := sigma) (β := rho.re)
    (γ := rho.im) (ψ := psi) (hψ := hpsi)]
  apply integral_congr_ae
  filter_upwards with xi
  congr 1
  rw [finiteDirichletBlock_eq_common_dirichletPolynomial
    chi U N Y sigma (rho.im - 2 * Real.pi * xi) hD]
  congr 2
  ring

/-! ## Literal Type-I/Type-II partition -/

/-- Halving the outer loss parameter halves the reserved detector exponent
exactly. -/
theorem inputLoss_half (kappa eta : ℝ) :
    inputLoss kappa (eta / 2) = inputLoss kappa eta / 2 := by
  unfold inputLoss
  ring

/-- Pointwise detector alternative run at half the target loss.  This is the
strictly stronger endpoint whose saved half-exponent pays the subsequent
Fourier, dyadic, normalization, and fiber costs. -/
theorem post_A5_budgeted_detector_to_largeValue_with_half_reserve
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {kappa eta : ℝ} (hkappa : 0 < kappa) (heta : 0 < eta)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelope q U rho Y R +
          Real.rpow R (-(inputLoss kappa eta / 2)) +
          29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) *
            Real.rpow R (-(inputLoss kappa eta / 2)) ≤
        Real.exp (-(1 / Y))) :
    Real.rpow R (-(inputLoss kappa eta / 2)) ≤
        ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        Real.rpow R (-(inputLoss kappa eta / 2)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  have h := post_A5_budgeted_fixedCharacter_detector_to_largeValue
    chi hchi hkappa (half_pos heta) hU hrho hbetaLow hbetaHigh
      hY hR hUN hB
  rw [inputLoss_half] at h
  exact h hbudget

/-- Deterministic saved-reserve calculation.  Any explicit cost bounded by
R^(delta/2) can be inserted in front of the target R^(-delta) threshold and
is paid by a source threshold at R^(-delta/2). -/
theorem cost_mul_target_le_of_half_reserve
    {R delta cost value : ℝ} (hR : 0 < R) (hcost : cost ≤ Real.rpow R (delta / 2))
    (hstrong : Real.rpow R (-(delta / 2)) ≤ value) (hcost0 : 0 ≤ cost) :
    cost * Real.rpow R (-delta) ≤ value := by
  have hpow0 : 0 ≤ Real.rpow R (-delta) := Real.rpow_nonneg hR.le _
  calc
    cost * Real.rpow R (-delta) ≤
        Real.rpow R (delta / 2) * Real.rpow R (-delta) :=
      mul_le_mul_of_nonneg_right hcost hpow0
    _ = Real.rpow R (delta / 2 + (-delta)) :=
      (Real.rpow_add hR (delta / 2) (-delta)).symm
    _ = Real.rpow R (-(delta / 2)) := by congr 1 <;> ring
    _ ≤ value := hstrong

def postA5TypeISet
    (chi : DirichletCharacter ℂ q) (U : ℕ) (Y R V : ℝ)
    (Z : Finset ℂ) : Finset ℂ :=
  Z.filter fun rho =>
    V ≤ ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖

def postA5TypeIISet
    (chi : DirichletCharacter ℂ q) (R V : ℝ)
    (Z : Finset ℂ) : Finset ℂ := by
  classical
  exact Z.filter fun rho =>
    ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
      V ≤ ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖

theorem mem_postA5TypeIISet_iff
    (chi : DirichletCharacter ℂ q) (R V : ℝ) (Z : Finset ℂ) (rho : ℂ) :
    rho ∈ postA5TypeIISet chi R V Z ↔
      rho ∈ Z ∧
        ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
          V ≤ ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  classical
  simp only [postA5TypeIISet, Finset.mem_filter]

/-- The certified pointwise detector alternative partitions every finite zero
set into the literal Type-I detector fiber and literal Type-II critical-line
large-value fiber. -/
theorem post_A5_budgeted_zeroSet_subset_typeI_union_typeII
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    {U : ℕ} (hU : 1 ≤ U)
    {Z : Finset ℂ} {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hzero : ∀ rho ∈ Z, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z, 7 / 10 ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ Z, rho.re ≤ 1)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z,
      detectorTruncationErrorEnvelope q U rho Y R +
          Real.rpow R (-inputLoss κ η) +
          29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) *
            Real.rpow R (-inputLoss κ η) ≤
        Real.exp (-(1 / Y))) :
    Z ⊆ postA5TypeISet chi U Y R (Real.rpow R (-inputLoss κ η)) Z ∪
      postA5TypeIISet chi R (Real.rpow R (-inputLoss κ η)) Z := by
  classical
  intro rho hrho
  have halt := post_A5_budgeted_fixedCharacter_detector_to_largeValue
    chi hchi hκ hη hU (hzero rho hrho) (hbetaLow rho hrho)
      (hbetaHigh rho hrho) hY hR hUN hB (hbudget rho hrho)
  rcases halt with hI | hII
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrho, hI⟩)
  · apply Finset.mem_union_right
    exact (mem_postA5TypeIISet_iff chi R
      (Real.rpow R (-inputLoss κ η)) Z rho).mpr ⟨hrho, hII⟩

/-- Cardinal form of the honest two-branch finite-set partition. -/
theorem post_A5_budgeted_zeroSet_card_le_typeI_add_typeII
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    {U : ℕ} (hU : 1 ≤ U)
    {Z : Finset ℂ} {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hzero : ∀ rho ∈ Z, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z, 7 / 10 ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ Z, rho.re ≤ 1)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z,
      detectorTruncationErrorEnvelope q U rho Y R +
          Real.rpow R (-inputLoss κ η) +
          29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) *
            Real.rpow R (-inputLoss κ η) ≤
        Real.exp (-(1 / Y))) :
    Z.card ≤
      (postA5TypeISet chi U Y R (Real.rpow R (-inputLoss κ η)) Z).card +
      (postA5TypeIISet chi R (Real.rpow R (-inputLoss κ η)) Z).card := by
  have hsubset := post_A5_budgeted_zeroSet_subset_typeI_union_typeII
    chi hchi hκ hη hU hY hR hzero hbetaLow hbetaHigh hUN hB hbudget
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

/-- The complete finite set-level handoff: the zero set is split into the
actual Type-II L-value fiber, while one dyadic detector shell is common on a
quantitatively large subset of the Type-I fiber. -/
theorem post_A5_budgeted_zeroSet_common_dyadic_or_typeII
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    {U : ℕ} (hU : 1 ≤ U)
    {Z : Finset ℂ} {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hzero : ∀ rho ∈ Z, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z, 7 / 10 ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ Z, rho.re ≤ 1)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z,
      detectorTruncationErrorEnvelope q U rho Y R +
          Real.rpow R (-inputLoss κ η) +
          29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) *
            Real.rpow R (-inputLoss κ η) ≤
        Real.exp (-(1 / Y))) :
    ∃ j : Fin (detectorDyadicCount (detectorArithmeticCutoff Y R)),
      ∃ S : Finset ℂ,
        S ⊆ postA5TypeISet chi U Y R (Real.rpow R (-inputLoss κ η)) Z ∧
        (postA5TypeISet chi U Y R
          (Real.rpow R (-inputLoss κ η)) Z).card ≤
            detectorDyadicCount (detectorArithmeticCutoff Y R) * S.card ∧
        (∀ rho ∈ S,
          Real.rpow R (-inputLoss κ η) ≤
            detectorDyadicCount (detectorArithmeticCutoff Y R) *
              ‖arithmeticDetectorDyadicBlock chi U
                (detectorArithmeticCutoff Y R) rho Y j‖) ∧
        Z.card ≤
          (postA5TypeISet chi U Y R
            (Real.rpow R (-inputLoss κ η)) Z).card +
          (postA5TypeIISet chi R
            (Real.rpow R (-inputLoss κ η)) Z).card := by
  let ZI := postA5TypeISet chi U Y R (Real.rpow R (-inputLoss κ η)) Z
  have hlarge : ∀ rho ∈ ZI,
      Real.rpow R (-inputLoss κ η) ≤
        ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  obtain ⟨j, S, hS, hcardI, hblock⟩ :=
    exists_common_arithmeticDetectorDyadicBlock chi hU hUN hlarge
  refine ⟨j, S, hS, hcardI, hblock, ?_⟩
  exact post_A5_budgeted_zeroSet_card_le_typeI_add_typeII
    chi hchi hκ hη hU hY hR hzero hbetaLow hbetaHigh hUN hB hbudget

end
end MAPAppendixA4PostA5SetAdapter

#print axioms MAPAppendixA4PostA5SetAdapter.arithmeticDetectorTerm_eq_weight_phase
#print axioms MAPAppendixA4PostA5SetAdapter.sum_arithmeticDetectorDyadicBlock_eq
#print axioms MAPAppendixA4PostA5SetAdapter.exists_common_arithmeticDetectorDyadicBlock
#print axioms MAPAppendixA4PostA5SetAdapter.post_A5_budgeted_zeroSet_subset_typeI_union_typeII
#print axioms MAPAppendixA4PostA5SetAdapter.post_A5_budgeted_zeroSet_common_dyadic_or_typeII
