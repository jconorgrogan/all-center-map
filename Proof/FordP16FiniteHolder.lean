import FordP16FiniteFourierBridge

open scoped BigOperators ZMod ComplexConjugate

namespace MAPFordP16FiniteHolder
noncomputable section

open MAPFordP16FiniteFourierBridge
open MAPFordP16ResidueHolder MAPFordP16ResidueAggregation

/-- The finite-character analogue of Ford's target sum, using the literal
residue-class blocks from the p.16 carrier. -/
def fordFiniteResidueSum
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (alpha : Fin k → ZMod L) (q : ℕ) (target : Fin d → ZMod p) : ℂ :=
  residueSum (s := s) (d := d)
    (fun b : ZMod p =>
      fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
        b alpha q) target

abbrev fordFiniteZeroPairs
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) : Type :=
  {r : fordFinitePair (L := L) (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) hdk hp psi b //
    ∀ j, fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0}

/-- Real-valued form of the checked finite Fourier count, obtained by taking
real parts of its complex identity. -/
theorem finite_grid_energy_count_real
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p)
    (hbound : ∀ r j,
      |fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j| < (L : ℤ)) :
    (∑ alpha : Fin k → ZMod L,
      ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
        hdk hp psi alpha‖ ^ 2 *
        ‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
          b alpha q‖ ^ (2*s)) =
      (L : ℝ) ^ k * Fintype.card (fordFiniteZeroPairs
        (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
        (q := q) hdk hp psi b) := by
  have h := finite_grid_energy_count hdk hp psi b hbound
  have hr := congrArg Complex.re h
  have hleft :
      Complex.re (∑ alpha : Fin k → ZMod L,
        (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
            hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
          ((‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
            b alpha q‖ ^ (2*s) : ℝ) : ℂ))) =
      ∑ alpha : Fin k → ZMod L,
        ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
          hdk hp psi alpha‖ ^ 2 *
        ‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
          b alpha q‖ ^ (2*s) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hright :
      Complex.re ((L : ℂ) ^ k *
        Fintype.card (fordFiniteZeroPairs
          (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
          (q := q) hdk hp psi b)) =
      (L : ℝ) ^ k * Fintype.card (fordFiniteZeroPairs
        (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
        (q := q) hdk hp psi b) := by
    have hpow_all : ∀ n : ℕ, ((L : ℂ) ^ n).re = (L : ℝ) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, Complex.mul_re, Complex.natCast_re,
            Complex.natCast_im, ih]
          ring
    have hpow := hpow_all k
    rw [Complex.mul_re, hpow, Complex.natCast_re, Complex.natCast_im]
    ring
  calc
    (∑ alpha : Fin k → ZMod L,
      ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
        hdk hp psi alpha‖ ^ 2 *
      ‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
        b alpha q‖ ^ (2*s)) =
      Complex.re (∑ alpha : Fin k → ZMod L,
        (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
            hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
          ((‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
            b alpha q‖ ^ (2*s) : ℝ) : ℂ))) := hleft.symm
    _ = Complex.re ((L : ℂ) ^ k *
        Fintype.card (fordFiniteZeroPairs
          (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
          (q := q) hdk hp psi b)) := hr
    _ = (L : ℝ) ^ k * Fintype.card (fordFiniteZeroPairs
        (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
        (q := q) hdk hp psi b) := hright

/-- Weighted finite target-energy closure.  The right side is the literal
sum of integer-zero S4 cardinalities, with the source norm-square as the
nonnegative weight over the finite character grid. -/
theorem finite_target_energy_holder
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hbound : ∀ b r j,
      |fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j| < (L : ℤ)) :
    ∑ alpha : Fin k → ZMod L,
      (‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
        hdk hp psi alpha‖ ^ 2) *
        (∑ target : Fin d → ZMod p,
          ‖fordFiniteResidueSum (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi alpha q target‖ ^ 2) ≤
      (Nat.factorial d * p ^ (2*s-d-1) : ℝ) *
        (L : ℝ) ^ k *
          ∑ b : ZMod p, Fintype.card (fordFiniteZeroPairs
            (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
            (q := q) hdk hp psi b) := by
  let W : (Fin k → ZMod L) → ℝ := fun alpha =>
    ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
      hdk hp psi alpha‖ ^ 2
  let G : (Fin k → ZMod L) → ZMod p → ℂ := fun alpha b =>
    fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
      b alpha q
  let C : ℝ := (Nat.factorial d * p ^ (2*s-d-1) : ℝ)
  have hpoint : ∀ alpha : Fin k → ZMod L,
      ∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) (G alpha) target‖ ^ 2 ≤
      C * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s) := by
    intro alpha
    simpa [C] using
      (residueSum_targets_holder hp hd hds hs (G alpha))
  have hweighted : ∀ alpha : Fin k → ZMod L,
      W alpha * (∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) (G alpha) target‖ ^ 2) ≤
      W alpha * (C * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s)) := by
    intro alpha
    exact mul_le_mul_of_nonneg_left (hpoint alpha) (sq_nonneg _)
  have hsum :
      ∑ alpha : Fin k → ZMod L,
        W alpha * (∑ target : Fin d → ZMod p,
          ‖residueSum (s := s) (d := d) (G alpha) target‖ ^ 2) ≤
      ∑ alpha : Fin k → ZMod L,
        W alpha * (C * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s)) := by
    exact Finset.sum_le_sum (fun alpha _ => hweighted alpha)
  have hbound_sum :
      ∑ alpha : Fin k → ZMod L,
        W alpha * (C * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s)) =
      C * ∑ b : ZMod p, ∑ alpha : Fin k → ZMod L,
        W alpha * ‖G alpha b‖ ^ (2*s) := by
    calc
      (∑ alpha : Fin k → ZMod L,
          W alpha * (C * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s))) =
          ∑ alpha : Fin k → ZMod L,
            ∑ b : ZMod p, C * (W alpha * ‖G alpha b‖ ^ (2*s)) := by
        apply Finset.sum_congr rfl
        intro alpha halpha
        calc
          W alpha * (C * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s)) =
              (W alpha * C) * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s) := by ring
          _ = ∑ b : ZMod p, (W alpha * C) * ‖G alpha b‖ ^ (2*s) := by
            rw [Finset.mul_sum]
          _ = ∑ b : ZMod p, C * (W alpha * ‖G alpha b‖ ^ (2*s)) := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
      _ = ∑ b : ZMod p, ∑ alpha : Fin k → ZMod L,
            C * (W alpha * ‖G alpha b‖ ^ (2*s)) := by
        rw [Finset.sum_comm]
      _ = C * ∑ b : ZMod p, ∑ alpha : Fin k → ZMod L,
            W alpha * ‖G alpha b‖ ^ (2*s) := by
        calc
          (∑ b : ZMod p, ∑ alpha : Fin k → ZMod L,
              C * (W alpha * ‖G alpha b‖ ^ (2*s))) =
              ∑ b : ZMod p, C * (∑ alpha : Fin k → ZMod L,
                W alpha * ‖G alpha b‖ ^ (2*s)) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.mul_sum]
          _ = C * ∑ b : ZMod p, ∑ alpha : Fin k → ZMod L,
              W alpha * ‖G alpha b‖ ^ (2*s) := by
            rw [Finset.mul_sum]
  have hcount : ∀ b : ZMod p,
      (∑ alpha : Fin k → ZMod L,
        W alpha * ‖G alpha b‖ ^ (2*s)) =
      (L : ℝ) ^ k * Fintype.card (fordFiniteZeroPairs
        (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
        (q := q) hdk hp psi b) := by
    intro b
    simpa [W, G] using
      (finite_grid_energy_count_real (hdk := hdk) (hp := hp) (psi := psi)
        (b := b) (hbound := hbound b))
  calc
    ∑ alpha : Fin k → ZMod L,
        (‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
          hdk hp psi alpha‖ ^ 2) *
        (∑ target : Fin d → ZMod p,
          ‖fordFiniteResidueSum (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi alpha q target‖ ^ 2) =
      ∑ alpha : Fin k → ZMod L,
        W alpha * (∑ target : Fin d → ZMod p,
          ‖residueSum (s := s) (d := d) (G alpha) target‖ ^ 2) := by rfl
    _ ≤ ∑ alpha : Fin k → ZMod L,
        W alpha * (C * ∑ b : ZMod p, ‖G alpha b‖ ^ (2*s)) := hsum
    _ = C * ∑ b : ZMod p, ∑ alpha : Fin k → ZMod L,
        W alpha * ‖G alpha b‖ ^ (2*s) := hbound_sum
    _ = C * ∑ b : ZMod p, ((L : ℝ) ^ k * Fintype.card (fordFiniteZeroPairs
        (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
        (q := q) hdk hp psi b)) := by
      apply congrArg (fun t : ℝ => C * t)
      apply Finset.sum_congr rfl
      intro b hb
      exact hcount b
    _ = (Nat.factorial d * p ^ (2*s-d-1) : ℝ) *
        (L : ℝ) ^ k *
          ∑ b : ZMod p, Fintype.card (fordFiniteZeroPairs
            (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
            (q := q) hdk hp psi b) := by
      dsimp [C]
      push_cast
      rw [← Finset.mul_sum]
      ring

end
end MAPFordP16FiniteHolder

#print axioms MAPFordP16FiniteHolder.finite_grid_energy_count_real
#print axioms MAPFordP16FiniteHolder.finite_target_energy_holder
