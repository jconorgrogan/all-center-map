import JutilaLemma1DirichletSeries

/-!
# Outer finite-sieve sum in Jutila (2.2)

This module supplies the singleton-shift convolution used to weld the inner
Euler identity to the outer finite `xi_d` sum.
-/

namespace MAPJutilaLemma1OuterSum

open scoped BigOperators LSeries.notation
open MAPJutilaPseudocharacterMExact
open MAPJutilaMEntire
open MAPJutilaLemma1CoefficientAlgebra
open MAPJutilaLemma1DirichletSeries

noncomputable section

def natSingletonCoeff (d : ℕ) (c : ℂ) (n : ℕ) : ℂ :=
  if n = d then c else 0

theorem natSingletonCoeff_LSeriesSummable
    (d : ℕ) (c : ℂ) (s : ℂ) :
    LSeriesSummable (natSingletonCoeff d c) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  exact (Finset.finite_toSet ({d} : Finset ℕ)).subset (by
    intro n hn
    by_contra hmem
    change n ∉ ({d} : Finset ℕ) at hmem
    have hne : n ≠ d := by simpa only [Finset.mem_singleton] using hmem
    exact hn (by simp [LSeries.term, natSingletonCoeff, hne]))

theorem LSeries_natSingletonCoeff
    {d : ℕ} (hd : d ≠ 0) (c s : ℂ) :
    LSeries (natSingletonCoeff d c) s =
      c * jutilaNatPower d s := by
  unfold LSeries
  rw [tsum_eq_sum (s := ({d} : Finset ℕ))]
  · rw [Finset.sum_singleton, LSeries.term_of_ne_zero hd]
    simp [natSingletonCoeff, jutilaNatPower]
    rw [Complex.cpow_neg]
    ring
  · intro n hn
    have hne : n ≠ d := by
      simpa only [Finset.mem_singleton] using hn
    simp [LSeries.term, natSingletonCoeff, hne]

/-- Convolution with a singleton coefficient shifts an index by `d`. -/
theorem natSingletonCoeff_convolution_apply
    {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0)
    (c : ℂ) (f : ℕ → ℂ) :
    (natSingletonCoeff d c ⍟ f) n =
      if d ∣ n then c * f (n / d) else 0 := by
  rw [LSeries.convolution_def,
    show (fun n => ∑ p ∈ n.divisorsAntidiagonal,
      natSingletonCoeff d c p.1 * f p.2) n =
      ∑ p ∈ n.divisorsAntidiagonal,
        natSingletonCoeff d c p.1 * f p.2 by rfl,
    Nat.sum_divisorsAntidiagonal
      (fun a b => natSingletonCoeff d c a * f b)]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    have hdmem : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdn, hn⟩
    rw [Finset.sum_eq_single d]
    · simp [natSingletonCoeff]
    · intro a ha had
      simp [natSingletonCoeff, had]
    · intro hdnot
      exact (hdnot hdmem).elim
  · rw [if_neg hdn]
    apply Finset.sum_eq_zero
    intro a ha
    have had : a ≠ d := by
      intro h
      subst a
      exact hdn (Nat.dvd_of_mem_divisors ha)
    simp [natSingletonCoeff, had]

/-- One shifted inner coefficient is the literal `d`-summand in (2.3). -/
theorem shifted_inner_coefficient_eq
    {q r d n : ℕ} (chi : DirichletCharacter ℂ q)
    (hr : Squarefree r) (hd : d ≠ 0) (hn : n ≠ 0)
    (xi : ℕ → ℂ) :
    (natSingletonCoeff d
        (xi d * chi d * selbergPseudoAt r d) ⍟
      (((chi ·) : ℕ → ℂ) *
        selbergPseudoAt (r / r.gcd d))) n =
      if d ∣ n then
        xi d * chi n * selbergPseudoAt r n
      else 0 := by
  rw [natSingletonCoeff_convolution_apply hd hn]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn, if_pos hdn]
    have hmul : n / d * d = n := Nat.div_mul_cancel hdn
    have hchi : chi (n / d) * chi d = chi n := by
      rw [← map_mul, ← Nat.cast_mul, hmul]
    have hf := selbergPseudoAt_mul_split (r := r) (d := d)
      (n := n / d) hr hd
    rw [hmul] at hf
    simp only [Pi.mul_apply]
    rw [hf, ← hchi]
    ring
  · rw [if_neg hdn, if_neg hdn]

def jutilaOuterDivisorCoeff
    (xi : ℕ → ℂ) (D : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ d ∈ D, if d ∣ n then xi d else 0

def jutilaEquation22Coeff {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D : Finset ℕ) (r n : ℕ) : ℂ :=
  jutilaOuterDivisorCoeff xi D n * chi n * selbergPseudoAt r n

/-- Pointwise outer finite-sum coefficient identity. -/
theorem sum_shifted_inner_coefficient_eq
    {q r n : ℕ} (chi : DirichletCharacter ℂ q)
    (hr : Squarefree r) (hn : n ≠ 0)
    (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, d ≠ 0) :
    (∑ d ∈ D,
      (natSingletonCoeff d
          (xi d * chi d * selbergPseudoAt r d) ⍟
        (((chi ·) : ℕ → ℂ) *
          selbergPseudoAt (r / r.gcd d))) n) =
      jutilaEquation22Coeff chi xi D r n := by
  rw [show (∑ d ∈ D,
      (natSingletonCoeff d
          (xi d * chi d * selbergPseudoAt r d) ⍟
        (((chi ·) : ℕ → ℂ) *
          selbergPseudoAt (r / r.gcd d))) n) =
      ∑ d ∈ D, if d ∣ n then
        xi d * chi n * selbergPseudoAt r n else 0 by
    apply Finset.sum_congr rfl
    intro d hdmem
    exact shifted_inner_coefficient_eq chi hr (hDpos d hdmem) hn xi]
  unfold jutilaEquation22Coeff jutilaOuterDivisorCoeff
  simp only [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [Finset.sum_mul, Finset.sum_mul]

/-- One outer `d`-summand of (2.2), now as an exact L-series. -/
theorem LFunction_mul_jutilaMTermComplex_eq_LSeries
    {q r d : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (xi : ℕ → ℂ) (hr : Squarefree r) (hd : d ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s *
        jutilaMTermComplex chi xi r d s =
      LSeries
        (natSingletonCoeff d
            (xi d * chi d * selbergPseudoAt r d) ⍟
          (((chi ·) : ℕ → ℂ) *
            selbergPseudoAt (r / r.gcd d))) s := by
  let t := r / r.gcd d
  let c := xi d * chi d * selbergPseudoAt r d
  have htDvd : t ∣ r := by
    dsimp [t]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d)
  have ht : Squarefree t := Squarefree.squarefree_of_dvd htDvd hr
  have ht0 : t ≠ 0 := ht.ne_zero
  have hsingle := natSingletonCoeff_LSeriesSummable d c s
  have hinner := LSeriesSummable_chi_mul_selbergPseudoAt chi ht0 hs
  have hconv := LSeries_convolution' hsingle hinner
  have hlocal := LFunction_mul_localEulerProduct_eq chi ht hs
  unfold jutilaMTermComplex jutilaLocalEulerProductComplex
  change DirichletCharacter.LFunction chi s *
      (c * jutilaNatPower d s *
        (∏ p ∈ t.primeFactors,
          (1 + (selbergPseudoCoeff p - 1) * chi p *
            jutilaNatPower p s))) = _
  calc
    DirichletCharacter.LFunction chi s *
          (c * jutilaNatPower d s *
            (∏ p ∈ t.primeFactors,
              (1 + (selbergPseudoCoeff p - 1) * chi p *
                jutilaNatPower p s))) =
        (c * jutilaNatPower d s) *
          (DirichletCharacter.LFunction chi s *
            (∏ p ∈ t.primeFactors,
              (1 + (selbergPseudoCoeff p - 1) * chi p *
                jutilaNatPower p s))) := by ring
    _ = LSeries (natSingletonCoeff d c) s *
          LSeries (((chi ·) : ℕ → ℂ) * selbergPseudoAt t) s := by
      rw [hlocal]
      rw [LSeries_natSingletonCoeff hd]
    _ = LSeries
          (natSingletonCoeff d c ⍟
            (((chi ·) : ℕ → ℂ) * selbergPseudoAt t)) s := hconv.symm

/-- Jutila's equation (2.2), with the finite support `D` explicit. -/
theorem JutilaEquation22Finite
    {q r : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, d ≠ 0) (hr : Squarefree r)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s *
        jutilaMFiniteComplex chi xi D r s =
      LSeries (jutilaEquation22Coeff chi xi D r) s := by
  let F : ℕ → ℕ → ℂ := fun d =>
    natSingletonCoeff d (xi d * chi d * selbergPseudoAt r d) ⍟
      (((chi ·) : ℕ → ℂ) * selbergPseudoAt (r / r.gcd d))
  have hFsummable : ∀ d ∈ D, LSeriesSummable (F d) s := by
    intro d hdmem
    have hd0 := hDpos d hdmem
    have htDvd : r / r.gcd d ∣ r :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d)
    have ht : Squarefree (r / r.gcd d) :=
      Squarefree.squarefree_of_dvd htDvd hr
    exact (natSingletonCoeff_LSeriesSummable d
      (xi d * chi d * selbergPseudoAt r d) s).convolution
        (LSeriesSummable_chi_mul_selbergPseudoAt chi ht.ne_zero hs)
  unfold jutilaMFiniteComplex
  rw [Finset.mul_sum]
  calc
    ∑ d ∈ D,
          DirichletCharacter.LFunction chi s *
            jutilaMTermComplex chi xi r d s =
        ∑ d ∈ D, LSeries (F d) s := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact LFunction_mul_jutilaMTermComplex_eq_LSeries
        chi xi hr (hDpos d hdmem) hs
    _ = LSeries (∑ d ∈ D, F d) s := by
      exact (LSeries_sum hFsummable).symm
    _ = LSeries (jutilaEquation22Coeff chi xi D r) s := by
      apply LSeries_congr
      intro n hn
      rw [Finset.sum_apply]
      exact sum_shifted_inner_coefficient_eq chi hr hn xi hDpos

/-- Absolute convergence of the coefficient side of (2.2).  This is kept
separate so the selected outer `r`-sum can use `LSeries_sum` without hiding a
summability premise. -/
theorem LSeriesSummable_jutilaEquation22Coeff
    {q r : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, d ≠ 0) (hr : Squarefree r)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (jutilaEquation22Coeff chi xi D r) s := by
  let F : ℕ → ℕ → ℂ := fun d =>
    natSingletonCoeff d (xi d * chi d * selbergPseudoAt r d) ⍟
      (((chi ·) : ℕ → ℂ) * selbergPseudoAt (r / r.gcd d))
  have hFsummable : ∀ d ∈ D, LSeriesSummable (F d) s := by
    intro d hdmem
    have hd0 := hDpos d hdmem
    have htDvd : r / r.gcd d ∣ r :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d)
    have ht : Squarefree (r / r.gcd d) :=
      Squarefree.squarefree_of_dvd htDvd hr
    exact (natSingletonCoeff_LSeriesSummable d
      (xi d * chi d * selbergPseudoAt r d) s).convolution
        (LSeriesSummable_chi_mul_selbergPseudoAt chi ht.ne_zero hs)
  have hsum : LSeriesSummable (∑ d ∈ D, F d) s :=
    LSeriesSummable.sum hFsummable
  have heq : (∑ d ∈ D, F d) = (fun n => ∑ d ∈ D, F d n) := by
    funext n
    simp
  have hsum' : LSeriesSummable
      (fun n => ∑ d ∈ D, F d n) s := by
    rw [← heq]
    exact hsum
  exact (LSeriesSummable_congr s (fun {n} hn =>
    sum_shifted_inner_coefficient_eq chi hr hn xi hDpos)).mp hsum'

/-- Coefficient sequence after Jutila's literal primed/selected `r`-sum. -/
def jutilaEquation22SelectedCoeff {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (n : ℕ) : ℂ :=
  (∑ r ∈ S, ((r : ℂ)⁻¹ • jutilaEquation22Coeff chi xi D r)) n

theorem LSeriesSummable_jutilaEquation22SelectedCoeff
    {q R : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (xi : ℕ → ℂ) {D S : Finset ℕ}
    (hDpos : ∀ d ∈ D, d ≠ 0)
    (_hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (_hrcop : ∀ r ∈ S, r.Coprime q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (jutilaEquation22SelectedCoeff chi xi D S) s := by
  have hparts : ∀ r ∈ S,
      LSeriesSummable
        ((r : ℂ)⁻¹ • jutilaEquation22Coeff chi xi D r) s := by
    intro r hrmem
    exact (LSeriesSummable_jutilaEquation22Coeff
      chi xi hDpos (hrsq r hrmem) hs).smul (r : ℂ)⁻¹
  have hsum := LSeriesSummable.sum hparts
  unfold jutilaEquation22SelectedCoeff
  simpa only using hsum

/-- Source-faithful selected form of equation (2.2).  The range,
squarefreeness, and modulus-coprimality hypotheses make the prime on Jutila's
`r`-sum explicit.  The algebra uses squarefreeness; coprimality is retained in
the API because it is part of the source system and is needed downstream. -/
theorem JutilaEquation22SelectedFinite
    {q R : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (xi : ℕ → ℂ) {D S : Finset ℕ}
    (hDpos : ∀ d ∈ D, d ≠ 0)
    (_hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (_hrcop : ∀ r ∈ S, r.Coprime q)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s *
        jutilaMWeightedSumComplex chi xi D S s =
      LSeries (jutilaEquation22SelectedCoeff chi xi D S) s := by
  have hsummable : ∀ r ∈ S,
      LSeriesSummable
        ((r : ℂ)⁻¹ • jutilaEquation22Coeff chi xi D r) s := by
    intro r hrmem
    exact (LSeriesSummable_jutilaEquation22Coeff
      chi xi hDpos (hrsq r hrmem) hs).smul (r : ℂ)⁻¹
  unfold jutilaMWeightedSumComplex
  rw [Finset.mul_sum]
  calc
    ∑ r ∈ S, DirichletCharacter.LFunction chi s *
          ((r : ℂ)⁻¹ * jutilaMFiniteComplex chi xi D r s) =
        ∑ r ∈ S, (r : ℂ)⁻¹ *
          (DirichletCharacter.LFunction chi s *
            jutilaMFiniteComplex chi xi D r s) := by
      apply Finset.sum_congr rfl
      intro r hrmem
      ring
    _ = ∑ r ∈ S, (r : ℂ)⁻¹ *
          LSeries (jutilaEquation22Coeff chi xi D r) s := by
      apply Finset.sum_congr rfl
      intro r hrmem
      rw [JutilaEquation22Finite chi xi hDpos (hrsq r hrmem) hs]
    _ = ∑ r ∈ S,
          LSeries ((r : ℂ)⁻¹ • jutilaEquation22Coeff chi xi D r) s := by
      apply Finset.sum_congr rfl
      intro r hrmem
      rw [LSeries_smul]
    _ = LSeries (jutilaEquation22SelectedCoeff chi xi D S) s := by
      change (∑ r ∈ S,
        LSeries ((r : ℂ)⁻¹ • jutilaEquation22Coeff chi xi D r) s) =
        LSeries (∑ r ∈ S,
          ((r : ℂ)⁻¹ • jutilaEquation22Coeff chi xi D r)) s
      exact (LSeries_sum hsummable).symm

end

end MAPJutilaLemma1OuterSum

#print axioms MAPJutilaLemma1OuterSum.natSingletonCoeff_convolution_apply
#print axioms MAPJutilaLemma1OuterSum.shifted_inner_coefficient_eq
#print axioms MAPJutilaLemma1OuterSum.JutilaEquation22Finite
#print axioms MAPJutilaLemma1OuterSum.JutilaEquation22SelectedFinite
