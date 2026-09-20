import FordMixedKernelBounds

noncomputable section
namespace FordMixedLogAntitone

open FordMixedReciprocalIntegral FordMixedKernelBounds

lemma hasDerivAt_signedMixedDiff
    (hs : List ℝ) {x : ℝ} (hx : 0 < x)
    (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    HasDerivAt (signedMixedDiff hs) (-signedKernelDiff 1 hs x) x := by
  have hlog := hasDerivAt_log_mixedDiff hs hx hsteps
  have hconst := hlog.const_mul ((-1 : ℝ) ^ (hs.length + 1))
  convert hconst using 1
  · unfold signedKernelDiff reciprocalKernel
    rw [pow_succ]
    ring_nf

theorem signedMixedDiff_antitone
    (hs : List ℝ) (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    AntitoneOn (signedMixedDiff hs) (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    exact (hasDerivAt_signedMixedDiff hs hx hsteps).continuousAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_signedMixedDiff hs hx hsteps).differentiableAt
      |>.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hbound := signedKernelDiff_bounds hs (p := 1) (by omega) hx hsteps
    have hsum := shiftSum_nonneg hsteps
    have hprod := shiftProd_nonneg hsteps
    have hcoeff := riseCoeff_pos (p := 1) (hs := hs)
      (by omega : 1 ≤ (1 : ℕ))
    have hx0 : 0 < x := hx
    have hden : 0 < x + shiftSum hs := by linarith
    have hlow0 : 0 ≤ riseCoeff 1 hs * shiftProd hs /
        (x + shiftSum hs) ^ (1 + hs.length) := by
      apply div_nonneg
      · exact mul_nonneg hcoeff.le hprod
      · positivity
    have hkernel0 : 0 ≤ signedKernelDiff 1 hs x := hlow0.trans hbound.1
    rw [(hasDerivAt_signedMixedDiff hs hx hsteps).deriv]
    exact neg_nonpos.mpr hkernel0

end FordMixedLogAntitone

#print axioms FordMixedLogAntitone.hasDerivAt_signedMixedDiff
#print axioms FordMixedLogAntitone.signedMixedDiff_antitone
