import FordP16FiniteHolder

open scoped BigOperators ZMod ComplexConjugate
set_option maxHeartbeats 5000000

namespace MAPFordP16FiniteTargetCount
noncomputable section

open MAPFordP16FiniteFourierBridge
open MAPFordFiniteFourierCharacterSum
open MAPFordP16FiniteHolder
open MAPFordP16ResidueHolder MAPFordP16PowerFiber

def fordFiniteTargetResidueSum
    {L p s k d Q : ℕ} [NeZero L] [NeZero p]
    (alpha : Fin k → ZMod L) (q : ℕ) (target : Fin d → ZMod p) : ℂ :=
  residueSum (s := s) (d := d)
    (fun b : ZMod p =>
      fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
        b alpha q) target

/-- A target state remembers the truncated power target fibre and, independently,
one literal positive `x` carrier in the corresponding residue class for each
coordinate. -/
def fordFiniteTargetState
    {p s d Q : ℕ} [NeZero p]
    (target : Fin d → ZMod p) : Type :=
  Sigma (fun c : powerFiberTruncated (p := p) (s := s) (d := d) target =>
    ∀ i : Fin s, fordFiniteQCarrier (p := p) (Q := Q) (c.1 i))

instance fordFiniteTargetStateFintype
    {p s d Q : ℕ} [NeZero p]
    (target : Fin d → ZMod p) :
    Fintype (fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target) := by
  classical
  dsimp [fordFiniteTargetState]
  infer_instance

abbrev fordFiniteTargetStatePair
    {p s d Q : ℕ} [NeZero p] : Type :=
  Sigma (fun target : Fin d → ZMod p =>
    fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target ×
      fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target)

instance fordFiniteTargetStatePairFintype
    {p s d Q : ℕ} [NeZero p] :
    Fintype (fordFiniteTargetStatePair (p := p) (s := s) (d := d) (Q := Q)) := by
  classical
  dsimp [fordFiniteTargetStatePair]
  infer_instance

/-- Full cross-residue source pair over one common truncated power target. -/
abbrev fordFiniteTargetPair
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) : Type :=
  (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
    fordFiniteTargetStatePair (p := p) (s := s) (d := d) (Q := Q)) ×
    fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi

instance fordFiniteTargetPairFintype
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) :
    Fintype (fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) := by
  classical
  dsimp [fordFiniteTargetPair]
  infer_instance

def fordFiniteTargetPairFrequency
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) : Fin k → ℤ :=
  fordSourceFrequencyAt psi r.1.1.1 - fordSourceFrequencyAt psi r.2.1 +
    fordQFrequencyAt (q := q) (fun i => (r.1.2.2.1.2 i).1) -
    fordQFrequencyAt (q := q) (fun i => (r.1.2.2.2.2 i).1)

lemma finite_target_residue_expand
    {L p s k d Q : ℕ} [NeZero L] [NeZero p]
    (alpha : Fin k → ZMod L) (q : ℕ) (target : Fin d → ZMod p) :
    fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) alpha q target =
      ∑ u : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target,
        fordIntegerCharTerm alpha
          (fordQFrequencyAt (q := q) (fun i => (u.2 i).1)) := by
  classical
  rw [fordFiniteTargetResidueSum, residueSum]
  simp only [residueWeight, fordFiniteQBlock]
  change
    (∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
      ∏ i : Fin s,
        ∑ x : fordFiniteQCarrier (p := p) (Q := Q) (c.1 i),
          fordIntegerCharTerm alpha (fordQScalarFrequency (q := q) x.1)) =
    ∑ u : Sigma (fun c : powerFiberTruncated
        (p := p) (s := s) (d := d) target =>
      ∀ i : Fin s, fordFiniteQCarrier (p := p) (Q := Q) (c.1 i)),
      fordIntegerCharTerm alpha
        (fordQFrequencyAt (q := q) (fun i => (u.2 i).1))
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro u hu
  exact char_prod_term_sum alpha
    (fun i => fordQScalarFrequency (q := q) (u i).1)

lemma finite_target_residue_norm_expand
    {L p s k d Q : ℕ} [NeZero L] [NeZero p]
    (alpha : Fin k → ZMod L) (q : ℕ) (target : Fin d → ZMod p) :
    ((‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) alpha q target‖ ^ 2 : ℝ) : ℂ) =
      ∑ u : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target,
        ∑ v : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target,
          fordIntegerCharTerm alpha
            (fordQFrequencyAt (q := q) (fun i => (u.2 i).1)) *
          fordIntegerCharTerm alpha
            (fun j => -fordQFrequencyAt (q := q) (fun i => (v.2 i).1) j) := by
  rw [finite_target_residue_expand]
  rw [norm_sum_expand]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [char_term_neg]

lemma finite_target_residue_energy_sum_expand
    {L p s k d Q : ℕ} [NeZero L] [NeZero p]
    (alpha : Fin k → ZMod L) (q : ℕ) :
    ∑ target : Fin d → ZMod p,
      ((‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) alpha q target‖ ^ 2 : ℝ) : ℂ) =
      ∑ u : fordFiniteTargetStatePair (p := p) (s := s) (d := d) (Q := Q),
        fordIntegerCharTerm alpha
          (fordQFrequencyAt (q := q) (fun i => (u.2.1.2 i).1)) *
        fordIntegerCharTerm alpha
          (fun j => -fordQFrequencyAt (q := q) (fun i => (u.2.2.2 i).1) j) := by
  simp_rw [finite_target_residue_norm_expand]
  have hprod : ∀ target : Fin d → ZMod p,
      (∑ u : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target,
        ∑ v : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target,
          fordIntegerCharTerm alpha
            (fordQFrequencyAt (q := q) (fun i => (u.2 i).1)) *
          fordIntegerCharTerm alpha
            (fun j => -fordQFrequencyAt (q := q) (fun i => (v.2 i).1) j)) =
      ∑ uv : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target ×
          fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target,
        fordIntegerCharTerm alpha
            (fordQFrequencyAt (q := q) (fun i => (uv.1.2 i).1)) *
          fordIntegerCharTerm alpha
            (fun j => -fordQFrequencyAt (q := q) (fun i => (uv.2.2 i).1) j) := by
    intro target
    rw [Fintype.sum_prod_type]
  simp_rw [hprod]
  have hsigma :
      (∑ u : fordFiniteTargetStatePair (p := p) (s := s) (d := d) (Q := Q),
        fordIntegerCharTerm alpha
            (fordQFrequencyAt (q := q) (fun i => (u.2.1.2 i).1)) *
          fordIntegerCharTerm alpha
            (fun j => -fordQFrequencyAt (q := q) (fun i => (u.2.2.2 i).1) j)) =
      ∑ target : Fin d → ZMod p,
        ∑ uv : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target ×
            fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target,
          fordIntegerCharTerm alpha
              (fordQFrequencyAt (q := q) (fun i => (uv.1.2 i).1)) *
            fordIntegerCharTerm alpha
              (fun j => -fordQFrequencyAt (q := q) (fun i => (uv.2.2 i).1) j) := by
    simpa using (Fintype.sum_sigma (fun u : fordFiniteTargetStatePair
      (p := p) (s := s) (d := d) (Q := Q) =>
      fordIntegerCharTerm alpha
          (fordQFrequencyAt (q := q) (fun i => (u.2.1.2 i).1)) *
        fordIntegerCharTerm alpha
          (fun j => -fordQFrequencyAt (q := q) (fun i => (u.2.2.2 i).1) j)))
  rw [← hsigma]

lemma finite_target_energy_at_alpha
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (alpha : Fin k → ZMod L) :
    ((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
        hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
      ∑ target : Fin d → ZMod p,
        ((‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) alpha q target‖ ^ 2 : ℝ) : ℂ) =
      ∑ r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) (q := q) hdk hp psi,
        fordIntegerCharTerm alpha
          (fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r) := by
  rw [finiteFBlock_norm_expand]
  rw [finite_target_residue_energy_sum_expand]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have hcombine : ∀
      (z w : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi)
      (uv : fordFiniteTargetStatePair (p := p) (s := s) (d := d) (Q := Q)),
      (fordIntegerCharTerm alpha (fordSourceFrequencyAt psi z.1) *
        fordIntegerCharTerm alpha (fun j => -fordSourceFrequencyAt psi w.1 j)) *
        (fordIntegerCharTerm alpha
          (fordQFrequencyAt (q := q) (fun i => (uv.2.1.2 i).1)) *
         fordIntegerCharTerm alpha
          (fun j => -fordQFrequencyAt (q := q) (fun i => (uv.2.2.2 i).1) j)) =
        fordIntegerCharTerm alpha
          (fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi
            ((z, uv), w)) := by
    intro z w uv
    rw [char_term_add alpha (fordSourceFrequencyAt psi z.1)
      (fun j => -fordSourceFrequencyAt psi w.1 j)]
    rw [← mul_assoc]
    rw [char_term_add alpha
      (fun j => fordSourceFrequencyAt psi z.1 j + -fordSourceFrequencyAt psi w.1 j)
      (fordQFrequencyAt (q := q) (fun i => (uv.2.1.2 i).1))]
    rw [char_term_add alpha
      (fun j => fordSourceFrequencyAt psi z.1 j + -fordSourceFrequencyAt psi w.1 j +
        fordQFrequencyAt (q := q) (fun i => (uv.2.1.2 i).1) j)
      (fun j => -fordQFrequencyAt (q := q) (fun i => (uv.2.2.2 i).1) j)]
    congr 1
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  change
    (∑ r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi,
      (fordIntegerCharTerm alpha (fordSourceFrequencyAt psi r.1.1.1) *
        fordIntegerCharTerm alpha (fun j => -fordSourceFrequencyAt psi r.2.1 j)) *
       (fordIntegerCharTerm alpha
          (fordQFrequencyAt (q := q) (fun i => (r.1.2.2.1.2 i).1)) *
        fordIntegerCharTerm alpha
          (fun j => -fordQFrequencyAt (q := q) (fun i => (r.1.2.2.2.2 i).1) j))) = _
  apply Finset.sum_congr rfl
  intro r hr
  rcases r with ⟨⟨z, uv⟩, w⟩
  exact hcombine z w uv

theorem finite_target_energy_count
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hbound : ∀ r j,
      |fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j| < (L : ℤ)) :
    ∑ alpha : Fin k → ZMod L,
      (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
          hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
        ∑ target : Fin d → ZMod p,
          ((‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) alpha q target‖ ^ 2 : ℝ) : ℂ)) =
      (L : ℂ) ^ k *
        Fintype.card {r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
          ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} := by
  calc
    ∑ alpha : Fin k → ZMod L,
        (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
            hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
          ∑ target : Fin d → ZMod p,
            ((‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) alpha q target‖ ^ 2 : ℝ) : ℂ)) =
        ∑ alpha : Fin k → ZMod L,
          ∑ r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi,
            fordIntegerCharTerm alpha
              (fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
                (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      exact finite_target_energy_at_alpha hdk hp psi alpha
    _ = (L : ℂ) ^ k *
        Fintype.card {r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
          ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} := by
      exact finite_masked_integer_character_count
        (freq := fordFiniteTargetPairFrequency (L := L) (p := p) (s := s)
          (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) hbound

end
end MAPFordP16FiniteTargetCount

#print axioms MAPFordP16FiniteTargetCount.finite_target_residue_expand
#print axioms MAPFordP16FiniteTargetCount.finite_target_residue_energy_sum_expand
#print axioms MAPFordP16FiniteTargetCount.finite_target_energy_at_alpha
#print axioms MAPFordP16FiniteTargetCount.finite_target_energy_count
