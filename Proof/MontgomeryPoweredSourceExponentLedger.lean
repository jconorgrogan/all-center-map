import MontgomeryTheorem12SourceDAG

/-!
# Montgomery low-strip powered-source exponent ledger

This file records the power arithmetic behind the source choice

`Y = (qT)^(3/(2(2-sigma)))`.

It also gives a fail-fast certificate for the unpowered hybrid absorption:
on the detector range `sigma <= 7/10`, even a shell as long as `Y` leaves a
positive power deficit of at least `1/26`.  Thus the unpowered dichotomy
cannot close the source theorem; the powered branch (or Montgomery's signed
Theorem 8.3) is genuinely necessary.
-/

namespace MAPMontgomeryPoweredSourceExponentLedger

open MAPMontgomeryLowStrip MAPMontgomeryTheorem12SourceDAG

noncomputable section

/-- Exponent of Montgomery's terminal detector length `Y`. -/
def sourceYExponent (sigma : ℝ) : ℝ :=
  3 / (2 * (2 - sigma))

/-- The length term of the powered hybrid mean square lands exactly on the
Ingham exponent. -/
theorem powered_length_exponent_eq_ingham
    {sigma : ℝ} (hsigma : sigma < 2) :
    sourceYExponent sigma * (2 * (1 - sigma)) =
      inghamExponent sigma := by
  rw [inghamExponent_eq]
  unfold sourceYExponent
  have hden : 2 - sigma ≠ 0 := by linarith
  field_simp

/-- The `qT` term in the powered hybrid mean square is no larger than the
same terminal exponent.  Equality occurs at `sigma = 1/2`; above it the
source has reserve. -/
theorem powered_hybrid_scale_exponent_le_ingham
    {sigma : ℝ} (hsigmaLow : 1 / 2 ≤ sigma)
    (hsigmaHigh : sigma < 2) :
    1 + sourceYExponent sigma * (1 - 2 * sigma) ≤
      inghamExponent sigma := by
  rw [inghamExponent_eq]
  unfold sourceYExponent
  have hden : 0 < 2 * (2 - sigma) := by linarith
  have hleft :
      1 + 3 / (2 * (2 - sigma)) * (1 - 2 * sigma) =
        (2 * (2 - sigma) + 3 * (1 - 2 * sigma)) /
          (2 * (2 - sigma)) := by
    have hsmall : 2 - sigma ≠ 0 := by linarith
    field_simp [hsmall]
    <;> ring
  have hright :
      3 * (1 - sigma) / (2 - sigma) =
        (6 * (1 - sigma)) / (2 * (2 - sigma)) := by
    have hsmall : 2 - sigma ≠ 0 := by linarith
    field_simp
    <;> ring
  rw [hleft, hright, div_le_div_iff_of_pos_right hden]
  nlinarith

/-- Exact exponent left in the attempted unpowered absorption at the
largest legal shell. -/
def unpoweredAbsorptionDeficit (sigma : ℝ) : ℝ :=
  1 / 2 + sourceYExponent sigma * (1 - 2 * sigma)

/-- On the actual low-strip detector range, the unpowered threshold misses
by at least `(qT)^(1/26)` before logarithmic losses.  At `sigma=7/10` the
bound is exact. -/
theorem one_div_twentySix_le_unpoweredAbsorptionDeficit
    {sigma : ℝ} (hsigmaLow : 1 / 2 ≤ sigma)
    (hsigmaHigh : sigma ≤ 7 / 10) :
    1 / 26 ≤ unpoweredAbsorptionDeficit sigma := by
  unfold unpoweredAbsorptionDeficit sourceYExponent
  have hden : 0 < 2 * (2 - sigma) := by linarith
  have hrhs :
      1 / 2 + 3 / (2 * (2 - sigma)) * (1 - 2 * sigma) =
        ((2 - sigma) + 3 * (1 - 2 * sigma)) /
          (2 * (2 - sigma)) := by
    have hsmall : 2 - sigma ≠ 0 := by linarith
    field_simp [hsmall]
    <;> ring
  rw [hrhs, le_div_iff₀ hden]
  nlinarith

theorem unpoweredAbsorptionDeficit_at_sevenTenths :
    unpoweredAbsorptionDeficit (7 / 10 : ℝ) = 1 / 26 := by
  norm_num [unpoweredAbsorptionDeficit, sourceYExponent]

/-! ## Theorem-3 Type-I kernel threshold -/

/-- Power of the fixed-modulus conductor-height scale in Montgomery's
1969 Theorem 3 kernel estimate.  The paper proves

`K ≪ (qT)^(1/2) (log(qT))^3 log log N`

after specializing its variable-modulus parameter `Q` to the square root of
the quotient-character conductor.  Thus equation (30) does **not** give a
subpower kernel. -/
def montgomeryTheorem3KernelExponent : ℝ := 1 / 2

/-- Largest power of `qT` that the off-diagonal Type-I kernel may cost when
the detector shell reaches the printed terminal length `Y`.  Logarithmic
factors are handled separately. -/
def typeIKernelExponentCeiling (sigma : ℝ) : ℝ :=
  sourceYExponent sigma * (2 * sigma - 1)

/-- The shell-energy exponent and the maximal admissible kernel exponent
cancel exactly.  This is the power ledger of the absorbed Halasz threshold
`energy * kernel <= V^2`. -/
theorem sourceY_energy_add_typeIKernel_ceiling (sigma : ℝ) :
    sourceYExponent sigma * (1 - 2 * sigma) +
      typeIKernelExponentCeiling sigma = 0 := by
  unfold typeIKernelExponentCeiling
  ring

/-- At the lower endpoint the crude detector-shell energy leaves no room for
any positive kernel power.  Since the actual Theorem-3 kernel has exponent
`1/2`, this says that the crude energy model is not the source proof of
Montgomery (12.33); it does not say that equation (30) has a subpower bound. -/
theorem typeIKernelExponentCeiling_at_oneHalf :
    typeIKernelExponentCeiling (1 / 2 : ℝ) = 0 := by
  norm_num [typeIKernelExponentCeiling]

/-- At the upper endpoint of the needed strip the full available reserve is
only `(qT)^(6/13)`. -/
theorem typeIKernelExponentCeiling_at_sevenTenths :
    typeIKernelExponentCeiling (7 / 10 : ℝ) = 6 / 13 := by
  norm_num [typeIKernelExponentCeiling, sourceYExponent]

/-- The current absolute region envelope has sixth-power height growth even
at `q=1`, far beyond the maximal `6/13` reserve.  Consequently inserting
that envelope into `typeIKernelBudget` cannot prove Montgomery's printed
threshold by the present absolute-value energy majorant. -/
theorem coarse_region_height_exponent_exceeds_typeI_ceiling :
    typeIKernelExponentCeiling (7 / 10 : ℝ) < 6 := by
  rw [typeIKernelExponentCeiling_at_sevenTenths]
  norm_num

/-- Even the sharp power in Montgomery's printed Theorem-3 kernel is larger
than the allowance produced by the crude terminal-shell energy model at
`sigma=7/10`.  The exact deficit is `1/26`. -/
theorem theorem3_kernel_exceeds_crude_ceiling_at_sevenTenths :
    montgomeryTheorem3KernelExponent -
      typeIKernelExponentCeiling (7 / 10 : ℝ) = 1 / 26 := by
  norm_num [montgomeryTheorem3KernelExponent,
    typeIKernelExponentCeiling, sourceYExponent]

/-- At `sigma=1/2`, no finite powered shell exponent can absorb the actual
Theorem-3 kernel against the crude energy `D^(1-2 sigma)`. -/
theorem theorem3_threshold_impossible_at_oneHalf (ell : ℝ) :
    ¬ (montgomeryTheorem3KernelExponent +
      ell * (1 - 2 * (1 / 2 : ℝ)) ≤ 0) := by
  norm_num [montgomeryTheorem3KernelExponent]

/-- If a powered detector polynomial has length exponent `ell`, absorption
of the printed Theorem-3 kernel forces `ell ≥ 1/(2(2 sigma-1))`. -/
theorem theorem3_threshold_forces_length
    {sigma ell : ℝ} (hsigma : 1 / 2 < sigma)
    (hthreshold : montgomeryTheorem3KernelExponent +
      ell * (1 - 2 * sigma) ≤ 0) :
    1 / (2 * (2 * sigma - 1)) ≤ ell := by
  unfold montgomeryTheorem3KernelExponent at hthreshold
  have hden : 0 < 2 * (2 * sigma - 1) := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- At the top of MAP's needed low strip, the shortest powered polynomial
that can absorb the printed Theorem-3 kernel has exponent `5/4`. -/
theorem theorem3_minimum_length_at_sevenTenths :
    1 / (2 * (2 * (7 / 10 : ℝ) - 1)) = 5 / 4 := by
  norm_num

/-- Its diagonal Halasz term then has exponent `3/4`, strictly larger than
the desired Ingham exponent `9/13`.  This is the terminal death test for a
direct `equation-(30) + crude coefficientEnergy` proof of (12.33). -/
theorem theorem3_direct_count_exponent_gap_at_sevenTenths :
    (5 / 4 : ℝ) * (2 * (1 - 7 / 10)) -
      inghamExponent (7 / 10 : ℝ) = 3 / 52 := by
  norm_num [inghamExponent, ZeroDensityArithmetic.inghamCoeff]

/-- More generally, throughout the open interval below `5/7`, the best
count exponent obtainable after absorbing the printed Theorem-3 kernel is
strictly worse than Montgomery's final Ingham exponent. -/
theorem theorem3_direct_minimum_exceeds_ingham
    {sigma : ℝ} (hsigmaLow : 1 / 2 < sigma)
    (hsigmaHigh : sigma < 5 / 7) :
    inghamExponent sigma < (1 - sigma) / (2 * sigma - 1) := by
  rw [inghamExponent_eq]
  have hden1 : 0 < 2 - sigma := by linarith
  have hden2 : 0 < 2 * sigma - 1 := by linarith
  rw [div_lt_div_iff₀ hden1 hden2]
  have hone : 0 < 1 - sigma := by linarith
  nlinarith

/-! ## Full shell-normalized power ledger

Here `loss` is the total power loss in the extracted polynomial threshold:
if the detector value is `S^(-v)`, the Fourier `L¹` mass is `S^a`, and the
dyadic count is subpower, then `loss = v+a` and the common-shell large value
is `S^(-loss+o(1))`.  Thus its square contributes `2*loss` both to the
absorption condition and, after division, to the count exponent. -/

def theorem3ThresholdExponent (sigma ell loss : ℝ) : ℝ :=
  montgomeryTheorem3KernelExponent + ell * (1 - 2 * sigma) + 2 * loss

def theorem3CountExponent (sigma ell loss : ℝ) : ℝ :=
  ell * (2 * (1 - sigma)) + 2 * loss

/-- At the lower endpoint, Theorem 3 cannot absorb any shell when the
detector/Fourier normalization has nonnegative power loss.  Logarithmic
dyadic and Fourier constants correspond to `loss=0` here and do not alter
the obstruction. -/
theorem theorem3_full_threshold_impossible_at_oneHalf
    {ell loss : ℝ} (hloss : 0 ≤ loss) :
    ¬ (theorem3ThresholdExponent (1 / 2) ell loss ≤ 0) := by
  unfold theorem3ThresholdExponent montgomeryTheorem3KernelExponent
  nlinarith

/-- At `sigma=7/10`, after including every threshold normalization in
`loss`, absorption forces a count exponent at least `3/4 + 5*loss`.
Consequently Fourier mass or detector losses only worsen the direct route. -/
theorem theorem3_full_count_lower_at_sevenTenths
    {ell loss : ℝ}
    (hthreshold : theorem3ThresholdExponent (7 / 10) ell loss ≤ 0) :
    3 / 4 + 5 * loss ≤
      theorem3CountExponent (7 / 10) ell loss := by
  unfold theorem3ThresholdExponent montgomeryTheorem3KernelExponent at hthreshold
  unfold theorem3CountExponent
  norm_num at hthreshold ⊢
  nlinarith

/-- Hence the fully normalized direct route misses the desired `9/13`
exponent at the top of the needed strip by at least `3/52`, even before any
positive threshold loss is charged. -/
theorem theorem3_full_count_exceeds_ingham_at_sevenTenths
    {ell loss : ℝ} (hloss : 0 ≤ loss)
    (hthreshold : theorem3ThresholdExponent (7 / 10) ell loss ≤ 0) :
    inghamExponent (7 / 10) + 3 / 52 ≤
      theorem3CountExponent (7 / 10) ell loss := by
  have hcount := theorem3_full_count_lower_at_sevenTenths hthreshold
  norm_num [inghamExponent, ZeroDensityArithmetic.inghamCoeff] at hcount ⊢
  linarith

/-! ## The integer-power coverage gap -/

theorem sourceYExponent_at_sevenTenths :
    sourceYExponent (7 / 10 : ℝ) = 15 / 13 := by
  norm_num [sourceYExponent]

theorem inghamExponent_at_sevenTenths :
    inghamExponent (7 / 10 : ℝ) = 9 / 13 := by
  norm_num [inghamExponent, ZeroDensityArithmetic.inghamCoeff]

/-- At `sigma=7/10`, a shell with exponent

`15/26 < d < 10/13`

cannot be handled by the plain powered hybrid mean square at any integral
power.  For `k=1` the `qT` term is too large; for `k>=2` the polynomial-length
term is too large.  This is the exact surviving need for Montgomery's signed
Theorem 8.3 mechanism (or a genuinely different replacement). -/
theorem no_integral_power_closes_intermediate_shell_at_sevenTenths
    {d : ℝ} (hdLow : 15 / 26 < d) (hdHigh : d < 10 / 13) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧
      1 + (k : ℝ) * d * (1 - 2 * (7 / 10 : ℝ)) ≤ 9 / 13 ∧
      (k : ℝ) * d * (2 * (1 - (7 / 10 : ℝ))) ≤ 9 / 13 := by
  rintro ⟨k, hk, hscale, hlength⟩
  by_cases hkone : k = 1
  · subst k
    norm_num at hscale
    linarith
  · have hktwo : 2 ≤ k := by omega
    have hkcast : (2 : ℝ) ≤ k := by exact_mod_cast hktwo
    norm_num at hlength
    nlinarith

end

end MAPMontgomeryPoweredSourceExponentLedger

#print axioms MAPMontgomeryPoweredSourceExponentLedger.powered_length_exponent_eq_ingham
#print axioms MAPMontgomeryPoweredSourceExponentLedger.powered_hybrid_scale_exponent_le_ingham
#print axioms MAPMontgomeryPoweredSourceExponentLedger.one_div_twentySix_le_unpoweredAbsorptionDeficit
#print axioms MAPMontgomeryPoweredSourceExponentLedger.sourceY_energy_add_typeIKernel_ceiling
#print axioms MAPMontgomeryPoweredSourceExponentLedger.typeIKernelExponentCeiling_at_oneHalf
#print axioms MAPMontgomeryPoweredSourceExponentLedger.typeIKernelExponentCeiling_at_sevenTenths
#print axioms MAPMontgomeryPoweredSourceExponentLedger.coarse_region_height_exponent_exceeds_typeI_ceiling
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_kernel_exceeds_crude_ceiling_at_sevenTenths
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_threshold_impossible_at_oneHalf
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_threshold_forces_length
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_direct_count_exponent_gap_at_sevenTenths
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_direct_minimum_exceeds_ingham
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_full_threshold_impossible_at_oneHalf
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_full_count_lower_at_sevenTenths
#print axioms MAPMontgomeryPoweredSourceExponentLedger.theorem3_full_count_exceeds_ingham_at_sevenTenths
#print axioms MAPMontgomeryPoweredSourceExponentLedger.no_integral_power_closes_intermediate_shell_at_sevenTenths
