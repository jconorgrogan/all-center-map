import FordP16ResidueAggregation
import FordLemma32LiteralContract

open scoped BigOperators

namespace MAPFordP16LiteralResidueBridge
noncomputable section

open MAPFordP16ResidueAggregation MAPFordP16ResidueHolder
open MAPFordLemma32LiteralContract

/-- Ford's `e(t)=exp(2*pi*I*t)` phase for the power block in p.16. -/
def fordPowerPhase {k q : ℕ} (alpha : Fin k → ℝ) (x : ℕ) : ℂ :=
  Complex.exp (Complex.I *
    (2 * Real.pi * ∑ j : Fin k,
      alpha j * (q : ℝ) ^ (j.val + 1) * (x : ℝ) ^ (j.val + 1)))

/-- The literal finite `g(alpha;b)` from p.15: `1 <= x <= Q` and `x=b mod p`. -/
def fordQBlock {p q Q k : ℕ} [NeZero p]
    (alpha : Fin k → ℝ) (b : ZMod p) : ℂ :=
  ∑ x : Fin (Q + 1),
    if 1 ≤ x.val ∧ ((x.val : ℕ) : ZMod p) = b then
      fordPowerPhase alpha (q := q) x.val
    else 0

/-- The polynomial phase used by Ford's `F tilde(alpha)` mask. -/
def fordPolynomialPhase {k P : ℕ} (psi : Fin k → Polynomial ℤ)
    (alpha : Fin k → ℝ) (z : Fin k → Fin (P + 1)) : ℂ :=
  Complex.exp (Complex.I *
    (2 * Real.pi * ∑ j : Fin k,
      alpha j * (((∑ i : Fin k, (psi j).eval ((z i).val : ℤ)) : ℤ) : ℝ)))

def fordTailPolynomials {k d : ℕ} (hdk : d ≤ k)
    (psi : Fin k → Polynomial ℤ) : Fin (k-d) → Polynomial ℤ :=
  fun j => psi ⟨d + j.val, by omega⟩

def fordTailCoordinates {k d P : ℕ} (hdk : d ≤ k)
    (z : Fin k → Fin (P + 1)) : Fin (k-d) → Fin (P + 1) :=
  fun i => z ⟨i.val, by omega⟩

/-- The exact positive interval and nonsingular Jacobian mask in Ford's `F tilde`. -/
def fordPolynomialMask {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (z : Fin k → Fin (P + 1)) : Prop :=
  (∀ i, 1 ≤ (z i).val) ∧
    p.Coprime
      (MAPFordCoarseP18Jacobian.sourceJacobian
        (fordTailPolynomials hdk psi) (fordTailCoordinates hdk z)).det.natAbs

/-- Ford's literal finite polynomial block `F tilde(alpha)`, including its
positive interval and source-Jacobian coprimality mask. -/
def fordFBlock {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (alpha : Fin k → ℝ) : ℂ := by
  classical
  exact ∑ z : Fin k → Fin (P + 1),
    if fordPolynomialMask hdk hp psi z then
      fordPolynomialPhase psi alpha z
    else 0

def fordFWeight {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (alpha : Fin k → ℝ) : ℝ :=
  ‖fordFBlock (P := P) hdk hp psi alpha‖ ^ 2

/-- Finite integrated form of Ford's p.16 residue step.  The alpha index is
finite here, so this is an executable quadrature version of the source
integral; the polynomial and congruence masks are literal, not an abstract
`g`. -/
theorem ford_literal_residue_holder
    {A p s d k q Q P : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (alpha : Fin A → Fin k → ℝ) :
    ∑ a : Fin A,
        fordFWeight (P := P) hdk hp psi (alpha a) *
          ∑ target : Fin d → ZMod p,
            ‖residueSum (s := s) (d := d)
              (fordQBlock (p := p) (q := q) (Q := Q) (alpha a)) target‖ ^ 2 ≤
      (Nat.factorial d * p ^ (2*s-d-1) : ℝ) *
        ∑ b : ZMod p, ∑ a : Fin A,
          fordFWeight (P := P) hdk hp psi (alpha a) *
            ‖fordQBlock (p := p) (q := q) (Q := Q) (alpha a) b‖ ^ (2*s) := by
  let W : Fin A → ℝ := fun a => fordFWeight (P := P) hdk hp psi (alpha a)
  let G : Fin A → ZMod p → ℂ := fun a =>
    fordQBlock (p := p) (q := q) (Q := Q) (alpha a)
  let C : ℝ := (Nat.factorial d * p ^ (2*s-d-1) : ℝ)
  have hpoint : ∀ a : Fin A,
      ∑ target : Fin d → ZMod p, ‖residueSum (s := s) (d := d) (G a) target‖ ^ 2 ≤
        C * ∑ b : ZMod p, ‖G a b‖ ^ (2*s) := by
    intro a
    simpa [C] using (residueSum_targets_holder hp hd hds hs (G a))
  have hweighted : ∀ a : Fin A,
      W a * (∑ target : Fin d → ZMod p,
        ‖residueSum (s := s) (d := d) (G a) target‖ ^ 2) ≤
      W a * (C * ∑ b : ZMod p, ‖G a b‖ ^ (2*s)) := by
    intro a
    exact mul_le_mul_of_nonneg_left (hpoint a) (sq_nonneg _)
  have hsum :
      (∑ a : Fin A, W a *
        ∑ target : Fin d → ZMod p,
          ‖residueSum (s := s) (d := d) (G a) target‖ ^ 2) ≤
      ∑ a : Fin A, W a * (C * ∑ b : ZMod p, ‖G a b‖ ^ (2*s)) := by
    exact Finset.sum_le_sum (fun a _ => hweighted a)
  calc
    ∑ a : Fin A, W a *
        ∑ target : Fin d → ZMod p,
          ‖residueSum (s := s) (d := d) (G a) target‖ ^ 2 ≤
      ∑ a : Fin A, W a * (C * ∑ b : ZMod p, ‖G a b‖ ^ (2*s)) := hsum
    _ = C * ∑ b : ZMod p, ∑ a : Fin A, W a * ‖G a b‖ ^ (2*s) := by
      calc
        (∑ a : Fin A, W a * (C * ∑ b : ZMod p, ‖G a b‖ ^ (2*s))) =
            ∑ a : Fin A, ∑ b : ZMod p, C * (W a * ‖G a b‖ ^ (2*s)) := by
          apply Finset.sum_congr rfl
          intro a ha
          calc
            W a * (C * ∑ b : ZMod p, ‖G a b‖ ^ (2*s)) =
                (W a * C) * ∑ b : ZMod p, ‖G a b‖ ^ (2*s) := by ring
            _ = ∑ b : ZMod p, (W a * C) * ‖G a b‖ ^ (2*s) := by
              rw [Finset.mul_sum]
            _ = ∑ b : ZMod p, C * (W a * ‖G a b‖ ^ (2*s)) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
        _ = ∑ b : ZMod p, ∑ a : Fin A, C * (W a * ‖G a b‖ ^ (2*s)) := by
          rw [Finset.sum_comm]
        _ = C * ∑ b : ZMod p, ∑ a : Fin A, W a * ‖G a b‖ ^ (2*s) := by
          calc
            (∑ b : ZMod p, ∑ a : Fin A, C * (W a * ‖G a b‖ ^ (2*s))) =
                ∑ b : ZMod p, C * (∑ a : Fin A, W a * ‖G a b‖ ^ (2*s)) := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [Finset.mul_sum]
            _ = C * ∑ b : ZMod p, ∑ a : Fin A, W a * ‖G a b‖ ^ (2*s) := by
              rw [Finset.mul_sum]
    _ = (Nat.factorial d * p ^ (2*s-d-1) : ℝ) *
        ∑ b : ZMod p, ∑ a : Fin A,
          fordFWeight (P := P) hdk hp psi (alpha a) *
            ‖fordQBlock (p := p) (q := q) (Q := Q) (alpha a) b‖ ^ (2*s) := by
      rfl

end
end MAPFordP16LiteralResidueBridge

#print axioms MAPFordP16LiteralResidueBridge.ford_literal_residue_holder
