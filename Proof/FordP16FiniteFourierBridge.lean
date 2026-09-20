import FordP16LiteralResidueBridge
import FordFiniteFourierCharacterSum

open scoped BigOperators ZMod ComplexConjugate

namespace MAPFordP16FiniteFourierBridge
noncomputable section

open MAPFordP16LiteralResidueBridge
open MAPFordFiniteFourierCharacterSum

lemma star_stdAddChar {L : ℕ} [NeZero L] (x : ZMod L) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  simpa using (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := L)) x).symm

def fordFiniteFCarrier {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) : Type :=
  {z : Fin k → Fin (P + 1) // fordPolynomialMask hdk hp psi z}

instance fordFiniteFCarrierFintype {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) : Fintype (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi) := by
  classical
  dsimp [fordFiniteFCarrier]
  infer_instance

def fordFiniteQCarrier {p Q : ℕ} [NeZero p]
    (b : ZMod p) : Type :=
  {x : Fin (Q + 1) // 1 ≤ x.val ∧ ((x.val : ℕ) : ZMod p) = b}

instance fordFiniteQCarrierFintype {p Q : ℕ} [NeZero p]
    (b : ZMod p) : Fintype (fordFiniteQCarrier (p := p) (Q := Q) b) := by
  classical
  dsimp [fordFiniteQCarrier]
  infer_instance

def fordIntegerCharTerm {L k : ℕ} [NeZero L]
    (alpha : Fin k → ZMod L) (freq : Fin k → ℤ) : ℂ :=
  ∏ j : Fin k, ZMod.stdAddChar (alpha j * (freq j : ZMod L))

/-- Source polynomial frequency, with the actual source tuple as input. -/
def fordSourceFrequencyAt {k P : ℕ} (psi : Fin k → Polynomial ℤ)
    (z : Fin k → Fin (P + 1)) : Fin k → ℤ :=
  fun j => ∑ i : Fin k, (psi j).eval ((z i).val : ℤ)

def fordQScalarFrequency {k q Q : ℕ}
    (x : Fin (Q + 1)) : Fin k → ℤ :=
  fun j => (q : ℤ) ^ (j.val + 1) * ((x.val : ℤ) ^ (j.val + 1))

def fordQFrequencyAt {s k q Q : ℕ}
    (x : Fin s → Fin (Q + 1)) : Fin k → ℤ :=
  fun j => ∑ i : Fin s, fordQScalarFrequency (q := q) (x i) j

def fordFiniteFBlock {L p k d P : ℕ} [NeZero L]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (alpha : Fin k → ZMod L) : ℂ :=
  ∑ z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi,
    fordIntegerCharTerm alpha (fordSourceFrequencyAt psi z.1)

def fordFiniteQBlock {L p s k Q : ℕ} [NeZero L] [NeZero p]
    (b : ZMod p) (alpha : Fin k → ZMod L) (q : ℕ) : ℂ :=
  ∑ x : fordFiniteQCarrier (p := p) (Q := Q) b,
    fordIntegerCharTerm alpha (fordQScalarFrequency (q := q) x.1)

abbrev fordFinitePair {L p s k d Q P : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) : Type :=
  ((fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
    (Fin s → fordFiniteQCarrier (p := p) (Q := Q) b)) ×
    (Fin s → fordFiniteQCarrier (p := p) (Q := Q) b)) ×
    fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi

def fordFinitePairFrequency {L p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) (r : fordFinitePair (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) hdk hp psi b) : Fin k → ℤ :=
  fun j => fordSourceFrequencyAt psi r.1.1.1.1 j -
    fordSourceFrequencyAt psi r.2.1 j +
    fordQFrequencyAt (q := q) (fun i => (r.1.1.2 i).1) j -
    fordQFrequencyAt (q := q) (fun i => (r.1.2 i).1) j

lemma finite_square_expansion {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i : ι, f i) * star (∑ j : ι, f j) =
      ∑ i : ι, ∑ j : ι, f i * star (f j) := by
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

lemma norm_sum_expand {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((‖∑ i : ι, f i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : ι, ∑ j : ι, f i * star (f j) := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  exact finite_square_expansion f

lemma norm_pow_expand {ι : Type*} [Fintype ι] (f : ι → ℂ) (s : ℕ) :
    ((‖∑ i : ι, f i‖ ^ (2*s) : ℝ) : ℂ) =
      (∑ x : Fin s → ι, ∏ n : Fin s, f (x n)) *
        star (∑ y : Fin s → ι, ∏ n : Fin s, f (y n)) := by
  let z : ℂ := ∑ i : ι, f i
  have hpow : ((‖z‖ ^ (2*s) : ℝ) : ℂ) =
      ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s := by
    push_cast
    rw [pow_mul]
  have hnorm : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [Complex.sq_norm, ← Complex.mul_conj]
    change z * (starRingEnd ℂ) z = z * (starRingEnd ℂ) z
    rfl
  rw [show ((‖∑ i : ι, f i‖ ^ (2*s) : ℝ) : ℂ) =
      ((‖z‖ ^ (2*s) : ℝ) : ℂ) by rfl]
  rw [hpow, hnorm, mul_pow, ← star_pow]
  rw [Fintype.sum_pow]

lemma char_prod_sum {L s : ℕ} [NeZero L] (a : Fin s → ZMod L) :
    (∏ i : Fin s, ZMod.stdAddChar (a i)) =
      ZMod.stdAddChar (∑ i : Fin s, a i) := by
  induction s with
  | zero => simp
  | succ s ih =>
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ]
      rw [ih]
      rw [← (ZMod.stdAddChar (N := L)).map_add_eq_mul]

lemma char_prod_term_sum {L s k : ℕ} [NeZero L]
    (alpha : Fin k → ZMod L) (f : Fin s → Fin k → ℤ) :
    (∏ i : Fin s, fordIntegerCharTerm alpha (f i)) =
      fordIntegerCharTerm alpha (fun j => ∑ i : Fin s, f i j) := by
  simp only [fordIntegerCharTerm]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  rw [char_prod_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma char_term_add {L k : ℕ} [NeZero L]
    (alpha : Fin k → ZMod L) (f g : Fin k → ℤ) :
    fordIntegerCharTerm alpha f * fordIntegerCharTerm alpha g =
      fordIntegerCharTerm alpha (fun j => f j + g j) := by
  simp only [fordIntegerCharTerm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← (ZMod.stdAddChar (N := L)).map_add_eq_mul]
  congr 1
  push_cast
  ring

lemma char_term_neg {L k : ℕ} [NeZero L]
    (alpha : Fin k → ZMod L) (f : Fin k → ℤ) :
    star (fordIntegerCharTerm alpha f) =
      fordIntegerCharTerm alpha (fun j => -f j) := by
  simp only [fordIntegerCharTerm, star_prod, star_stdAddChar]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  push_cast
  ring


lemma finiteFBlock_norm_expand
    {L p k d P : ℕ} [NeZero L]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (alpha : Fin k → ZMod L) :
    ((‖fordFiniteFBlock (L := L) (P := P) hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) =
      ∑ z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi,
        ∑ w : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi,
          fordIntegerCharTerm alpha (fordSourceFrequencyAt psi z.1) *
            fordIntegerCharTerm alpha
              (fun j => -fordSourceFrequencyAt psi w.1 j) := by
  rw [show fordFiniteFBlock (L := L) (P := P) hdk hp psi alpha =
      ∑ z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi,
        fordIntegerCharTerm alpha (fordSourceFrequencyAt psi z.1) by rfl]
  rw [norm_sum_expand]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  rw [char_term_neg]

lemma finiteQBlock_norm_pow_expand
    {L p s k Q : ℕ} [NeZero L] [NeZero p]
    (b : ZMod p) (alpha : Fin k → ZMod L) (q : ℕ) :
    ((‖fordFiniteQBlock (L := L) (p := p) (s := s) (Q := Q) b alpha q‖ ^ (2*s) : ℝ) : ℂ) =
      ∑ x : Fin s → fordFiniteQCarrier (p := p) (Q := Q) b,
        ∑ y : Fin s → fordFiniteQCarrier (p := p) (Q := Q) b,
          (∏ i : Fin s,
            fordIntegerCharTerm alpha
              (fordQScalarFrequency (q := q) (x i).1)) *
          (∏ i : Fin s,
            fordIntegerCharTerm alpha
              (fun j => -fordQScalarFrequency (q := q) (y i).1 j)) := by
  rw [show fordFiniteQBlock (L := L) (p := p) (s := s) (Q := Q) b alpha q =
      ∑ x : fordFiniteQCarrier (p := p) (Q := Q) b,
        fordIntegerCharTerm alpha (fordQScalarFrequency (q := q) x.1) by rfl]
  rw [norm_pow_expand]
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [star_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [char_term_neg]

lemma finiteQTupleChar
    {L p s k Q : ℕ} [NeZero L] [NeZero p]
    (b : ZMod p) (alpha : Fin k → ZMod L) (q : ℕ)
    (x : Fin s → fordFiniteQCarrier (p := p) (Q := Q) b) :
    (∏ i : Fin s,
      fordIntegerCharTerm alpha
        (fordQScalarFrequency (q := q) (x i).1)) =
      fordIntegerCharTerm alpha
        (fordQFrequencyAt (q := q) (fun i => (x i).1)) := by
  exact char_prod_term_sum alpha (fun i => fordQScalarFrequency (q := q) (x i).1)

lemma finiteQTupleCharNeg
    {L p s k Q : ℕ} [NeZero L] [NeZero p]
    (b : ZMod p) (alpha : Fin k → ZMod L) (q : ℕ)
    (y : Fin s → fordFiniteQCarrier (p := p) (Q := Q) b) :
    (∏ i : Fin s,
      fordIntegerCharTerm alpha
        (fun j => -fordQScalarFrequency (q := q) (y i).1 j)) =
      fordIntegerCharTerm alpha
        (fun j => -fordQFrequencyAt (q := q) (fun i => (y i).1) j) := by
  have h := char_prod_term_sum alpha
    (fun i => fun j => -fordQScalarFrequency (q := q) (y i).1 j)
  simpa [fordQFrequencyAt, Finset.sum_neg_distrib] using h


lemma finite_energy_at_alpha
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) (alpha : Fin k → ZMod L) :
    ((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
        hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
      ((‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
        b alpha q‖ ^ (2*s) : ℝ) : ℂ) =
      ∑ r : fordFinitePair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) hdk hp psi b,
        fordIntegerCharTerm alpha
          (fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r) := by
  rw [finiteFBlock_norm_expand, finiteQBlock_norm_pow_expand]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [finiteQTupleChar, finiteQTupleCharNeg]
  have hcombine : ∀
      (z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi)
      (x y : Fin s → fordFiniteQCarrier (p := p) (Q := Q) b)
      (w : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi),
      fordIntegerCharTerm alpha (fordSourceFrequencyAt psi z.1) *
          fordIntegerCharTerm alpha (fun j => -fordSourceFrequencyAt psi w.1 j) *
          (fordIntegerCharTerm alpha
            (fun j => fordQFrequencyAt (q := q) (fun i => (x i).1) j) *
           fordIntegerCharTerm alpha
            (fun j => -fordQFrequencyAt (q := q) (fun i => (y i).1) j)) =
        fordIntegerCharTerm alpha
          (fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b
            (((z, x), y), w)) := by
    intro z x y w
    rw [char_term_add alpha
      (fordSourceFrequencyAt psi z.1)
      (fun j => -fordSourceFrequencyAt psi w.1 j)]
    rw [← mul_assoc]
    rw [char_term_add alpha
      (fun j => fordSourceFrequencyAt psi z.1 j + -fordSourceFrequencyAt psi w.1 j)
      (fun j => fordQFrequencyAt (q := q) (fun i => (x i).1) j)]
    rw [char_term_add alpha
      (fun j => fordSourceFrequencyAt psi z.1 j + -fordSourceFrequencyAt psi w.1 j +
        fordQFrequencyAt (q := q) (fun i => (x i).1) j)
      (fun j => -fordQFrequencyAt (q := q) (fun i => (y i).1) j)]
    congr 1
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  change
    (∑ r : fordFinitePair (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) hdk hp psi b,
      (fordIntegerCharTerm alpha (fordSourceFrequencyAt psi r.1.1.1.1) *
        fordIntegerCharTerm alpha (fun j =>
          -fordSourceFrequencyAt psi r.2.1 j)) *
        (fordIntegerCharTerm alpha (fordQFrequencyAt (q := q)
            (fun i => (r.1.1.2 i).1)) *
          fordIntegerCharTerm alpha (fun j =>
            -fordQFrequencyAt (q := q) (fun i => (r.1.2 i).1) j))) = _
  apply Finset.sum_congr rfl
  intro r hr
  rcases r with ⟨⟨⟨z, x⟩, y⟩, w⟩
  exact hcombine z x y w



theorem finite_grid_energy_count
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) (hbound : ∀ r j,
      |fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j| < (L : ℤ)) :
    ∑ alpha : Fin k → ZMod L,
      (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
          hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
        ((‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
          b alpha q‖ ^ (2*s) : ℝ) : ℂ)) =
      (L : ℂ) ^ k *
        Fintype.card {r : fordFinitePair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) hdk hp psi b //
          ∀ j, fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
  calc
    ∑ alpha : Fin k → ZMod L,
        (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
            hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
          ((‖fordFiniteQBlock (L := L) (p := p) (s := s) (k := k) (Q := Q)
            b alpha q‖ ^ (2*s) : ℝ) : ℂ)) =
        ∑ alpha : Fin k → ZMod L,
          ∑ r : fordFinitePair (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) hdk hp psi b,
            fordIntegerCharTerm alpha
              (fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
                (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      exact finite_energy_at_alpha hdk hp psi b alpha
    _ = (L : ℂ) ^ k *
        Fintype.card {r : fordFinitePair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) hdk hp psi b //
          ∀ j, fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
      exact finite_masked_integer_character_count
        (freq := fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b) hbound


end
end MAPFordP16FiniteFourierBridge

#print axioms MAPFordP16FiniteFourierBridge.char_term_add
#print axioms MAPFordP16FiniteFourierBridge.norm_pow_expand

#print axioms MAPFordP16FiniteFourierBridge.finite_energy_at_alpha
#print axioms MAPFordP16FiniteFourierBridge.finite_grid_energy_count
