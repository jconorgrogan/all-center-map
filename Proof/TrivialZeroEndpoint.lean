import APZeroFieldEnergy28Core

namespace MAPTrivialZeroEndpoint

open Complex Filter Set
open scoped ZMod ComplexConjugate Topology

noncomputable section

variable {q : ℕ} [NeZero q]

/-- A primitive Dirichlet character has a nonzero Gauss sum. -/
theorem gaussSum_ne_zero_of_primitive
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro hzero
  have hdft : ZMod.dft (χ : ZMod q → ℂ) = 0 := by
    ext k
    rw [hprim.fourierTransform_eq_inv_mul_gaussSum, hzero, mul_zero]
    rfl
  have hχzero : (χ : ZMod q → ℂ) = 0 :=
    ZMod.dft.injective (by simpa using hdft)
  have hone := congrFun hχzero (1 : ZMod q)
  simpa using hone

/-- Hence the root number in Mathlib's primitive functional equation is
nonzero. -/
theorem rootNumber_ne_zero_of_primitive
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by
  unfold DirichletCharacter.rootNumber
  apply div_ne_zero
  · apply div_ne_zero (gaussSum_ne_zero_of_primitive hprim)
    exact pow_ne_zero _ I_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      Nat.cast_ne_zero.mpr (NeZero.ne q)

/-- Away from the origin, a gamma factor on the boundary `Re s = 0` is
nonzero. -/
theorem gammaFactor_ne_zero_of_re_zero_of_im_ne_zero
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hre : s.re = 0) (him : s.im ≠ 0) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hi := congrArg Complex.im hn
    simp at hi
    exact him hi
  · rw [hodd.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp [hre]

/-- A primitive nonprincipal Dirichlet L-function has no supported zero on
`Re s = 0` away from the origin. -/
theorem regularizedLFunction_ne_zero_of_re_zero_of_im_ne_zero
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {s : ℂ} (hre : s.re = 0) (him : s.im ≠ 0) :
    DirichletZeros.regularizedLFunction χ s ≠ 0 := by
  intro hzero
  have hLzero : χ.LFunction s = 0 := by
    simpa [DirichletZeros.regularizedLFunction, hχ] using hzero
  have hgamma := gammaFactor_ne_zero_of_re_zero_of_im_ne_zero χ hre him
  have hcompleted : χ.completedLFunction s = 0 := by
    have heq := χ.LFunction_eq_completed_div_gammaFactor s
      (Or.inr (fun hq => hχ (χ.level_one' hq)))
    rw [heq, div_eq_zero_iff] at hLzero
    exact hLzero.resolve_right hgamma
  let u : ℂ := 1 - s
  have hFE := hprim.completedLFunction_one_sub u
  have hleft : 1 - u = s := by dsimp [u]; ring
  rw [hleft, hcompleted] at hFE
  have hqpow : (q : ℂ) ^ (u - 1 / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hroot := rootNumber_ne_zero_of_primitive hprim
  have hucomp : χ⁻¹.completedLFunction u = 0 := by
    rcases mul_eq_zero.mp hFE.symm with h | h
    · rcases mul_eq_zero.mp h with hq | hr
      · exact (hqpow hq).elim
      · exact (hroot hr).elim
    · exact h
  have huRe : u.re = 1 := by simp [u, hre]
  have huNe : u ≠ 1 := by
    intro hu
    have hi := congrArg Complex.im hu
    simp [u] at hi
    exact him (by linarith)
  have hLne : χ⁻¹.LFunction u ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inr huNe) (by rw [huRe])
  have hu0 : u ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [huRe] at this
  have heqInv := χ⁻¹.LFunction_eq_completed_div_gammaFactor u
    (Or.inl hu0)
  rw [hucomp, zero_div] at heqInv
  exact hLne heqInv

/-- The inverse real gamma factor has derivative `1/2` at zero. -/
theorem hasDerivAt_invGammaℝ_zero :
    HasDerivAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) (1 / 2) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hres := Complex.Gammaℝ_residue_zero
  have hinv := hres.inv₀ (by norm_num : (2 : ℂ) ≠ 0)
  have hinv' : Tendsto (fun s : ℂ => (s * Complex.Gammaℝ s)⁻¹)
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2 : ℂ)) := by
    simpa using hinv
  apply hinv'.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  simp only [slope, sub_zero]
  have hG0 : Complex.Gammaℝ (0 : ℂ) = 0 := by
    rw [Complex.Gammaℝ_eq_zero_iff]
    exact ⟨0, by simp⟩
  simp [hG0, slope, mul_inv_rev, mul_comm]

/-- The completed primitive nonprincipal L-function does not vanish at the
left endpoint.  This is the functional equation at `s = 1`, with every
factor made explicit. -/
theorem completedLFunction_zero_ne_zero_of_primitive_nonprincipal
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) :
    χ.completedLFunction 0 ≠ 0 := by
  have hq1 : q ≠ 1 := fun hq => hχ (χ.level_one' hq)
  have hinv : χ⁻¹ ≠ 1 := by
    intro h
    have := congrArg Inv.inv h
    apply hχ
    simpa using this
  have hLinv : χ⁻¹.LFunction 1 ≠ 0 :=
    DirichletCharacter.LFunction_apply_one_ne_zero hinv
  have heqInv := χ⁻¹.LFunction_eq_completed_div_gammaFactor 1
    (Or.inr hq1)
  have hcompInv : χ⁻¹.completedLFunction 1 ≠ 0 := by
    intro h
    rw [h, zero_div] at heqInv
    exact hLinv heqInv
  have hFE := hprim.completedLFunction_one_sub (1 : ℂ)
  norm_num at hFE
  rw [hFE]
  exact mul_ne_zero
    (mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
        Nat.cast_ne_zero.mpr (NeZero.ne q))
      (rootNumber_ne_zero_of_primitive hprim))
    hcompInv

/-- For an even primitive nonprincipal character, the boundary zero at the
origin is simple. -/
theorem analyticOrderAt_regularizedLFunction_zero_eq_one_of_even
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) (heven : χ.Even) :
    analyticOrderAt (DirichletZeros.regularizedLFunction χ) 0 = 1 := by
  have hq1 : q ≠ 1 := fun hq => hχ (χ.level_one' hq)
  have hcompNe :=
    completedLFunction_zero_ne_zero_of_primitive_nonprincipal χ hprim hχ
  have hcompAn : AnalyticAt ℂ χ.completedLFunction 0 :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt 0
  have hcompOrder : analyticOrderAt χ.completedLFunction 0 = 0 :=
    hcompAn.analyticOrderAt_eq_zero.mpr hcompNe
  have hgammaAn : AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 :=
    Complex.differentiable_Gammaℝ_inv.analyticAt 0
  have hgammaZero : (Complex.Gammaℝ (0 : ℂ))⁻¹ = 0 := by
    rw [Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩, inv_zero]
  have hgammaDeriv : deriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 ≠ 0 := by
    rw [hasDerivAt_invGammaℝ_zero.deriv]
    norm_num
  have hgammaOrder :
      analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 = 1 :=
    hgammaAn.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hgammaZero hgammaDeriv
  have hfun : DirichletZeros.regularizedLFunction χ =
      χ.completedLFunction * (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) := by
    funext s
    rw [DirichletZeros.regularizedLFunction, if_neg hχ]
    rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inr hq1)]
    rw [heven.gammaFactor_def, div_eq_mul_inv]
    rfl
  rw [hfun, analyticOrderAt_mul hcompAn hgammaAn,
    hcompOrder, hgammaOrder, zero_add]

/-- The endpoint contribution to the literal zero support has multiplicity
at most one.  Odd characters contribute no endpoint zero; even characters
have the simple trivial zero just proved. -/
theorem zeroMultiplicity_zero_le_one
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {T : ℝ}
    (hmem : (0 : ℂ) ∈ DirichletZeros.zeroSupport χ 0 T) :
    DirichletZeros.zeroMultiplicity χ 0 T 0 ≤ 1 := by
  rcases χ.even_or_odd with heven | hodd
  · have horder :=
      analyticOrderAt_regularizedLFunction_zero_eq_one_of_even
        χ hprim hχ heven
    have hmult := PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
      χ 0 T hmem
    rw [horder] at hmult
    have hnat : DirichletZeros.zeroMultiplicity χ 0 T 0 = 1 := by
      exact_mod_cast ENat.coe_inj.mp hmult.symm
    exact hnat.le
  · have hcompNe :=
      completedLFunction_zero_ne_zero_of_primitive_nonprincipal χ hprim hχ
    have hq1 : q ≠ 1 := fun hq => hχ (χ.level_one' hq)
    have heq := χ.LFunction_eq_completed_div_gammaFactor 0 (Or.inr hq1)
    have hgamma : χ.gammaFactor 0 ≠ 0 := by
      rw [hodd.gammaFactor_def]
      simpa using Complex.Gammaℝ_one
    have hLne : χ.LFunction 0 ≠ 0 := by
      rw [heq]
      exact div_ne_zero hcompNe hgamma
    have hregNe : DirichletZeros.regularizedLFunction χ 0 ≠ 0 := by
      simpa [DirichletZeros.regularizedLFunction, hχ] using hLne
    exact (hregNe (DirichletZeros.regularizedLFunction_eq_zero_of_mem_zeroSupport
      χ 0 T hmem)).elim

#print axioms gaussSum_ne_zero_of_primitive
#print axioms rootNumber_ne_zero_of_primitive
#print axioms regularizedLFunction_ne_zero_of_re_zero_of_im_ne_zero
#print axioms hasDerivAt_invGammaℝ_zero
#print axioms completedLFunction_zero_ne_zero_of_primitive_nonprincipal
#print axioms analyticOrderAt_regularizedLFunction_zero_eq_one_of_even
#print axioms zeroMultiplicity_zero_le_one

end
end MAPTrivialZeroEndpoint
