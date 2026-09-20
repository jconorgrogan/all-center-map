import FordP16Source35Reparam
import FordTypeTriangularTranslation

open scoped BigOperators ZMod

namespace MAPFordP16Source35Triangular
noncomputable section
set_option maxHeartbeats 1500000

open MAPFordP16FiniteFourierBridge
open MAPFordP16Source35Reparam
open MAPFordP16SourceCountBridge
open MAPFordType
open Polynomial

def psiNat {k : ℕ} (psi : Fin k → Polynomial ℤ) (n : ℕ) : Polynomial ℤ :=
  if h : n < k then psi ⟨n, h⟩ else 0

def psiNatSucc {k : ℕ} (psi : Fin k → Polynomial ℤ) (n : ℕ) : Polynomial ℤ :=
  if h : n = 0 then 0 else psiNat psi (n - 1)

def phiRow {k : ℕ} (psi : Fin k → Polynomial ℤ) (q c : ℤ) (j : Fin k) : Polynomial ℤ :=
  triangularTranslation (psiNatSucc psi) (q * c) (j.val + 1)

lemma psiNat_eq {k : ℕ} (psi : Fin k → Polynomial ℤ) {n : ℕ}
    (hn : n < k) : psiNat psi n = psi ⟨n, hn⟩ := by
  simp [psiNat, hn]

lemma phiRow_eval
    {k : ℕ} (psi : Fin k → Polynomial ℤ) (q c : ℤ) (j : Fin k) (z : ℤ) :
    (phiRow psi q c j).eval z =
        ∑ ell ∈ Finset.range (j.val + 1 + 1),
        (Nat.choose (j.val + 1) ell : ℤ) *
            (psiNatSucc psi ell).eval z * (q * c) ^ (j.val + 1 - ell) := by
  simp only [phiRow, triangularTranslation]
  change (Polynomial.eval₂RingHom (RingHom.id ℤ) z)
      (∑ ell ∈ Finset.range (j.val + 1 + 1),
        C (Nat.choose (j.val + 1) ell : ℤ) * psiNatSucc psi ell *
          C ((q * c) ^ (j.val + 1 - ell))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  simp [map_mul, Polynomial.eval_C]

lemma source_sum_phi_expand
    {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ)
    (z : Fin k → Fin (P + 1)) (j : Fin k) :
    fordSourceFrequencyAt (phiRow psi q c) z j =
      ∑ ell ∈ Finset.range (j.val + 2),
        (Nat.choose (j.val + 1) ell : ℤ) *
            (∑ i : Fin k, (psiNatSucc psi ell).eval ((z i).val : ℤ)) *
              (q * c) ^ (j.val + 1 - ell) := by
  simp only [fordSourceFrequencyAt]
  simp_rw [phiRow_eval]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]

lemma binomial_qc_power
    (p q c u : ℤ) (j : ℕ) :
    ∑ ell ∈ Finset.range (j + 1),
        (Nat.choose j ell : ℤ) * (q * c) ^ (j - ell) *
          q ^ ell * (p * u - c) ^ ell =
      (p * q) ^ j * u ^ j := by
  have hbin := add_pow (p * u - c) c j
  rw [sub_add_cancel] at hbin
  have hbin' :
      ∑ ell ∈ Finset.range (j + 1),
          (Nat.choose j ell : ℤ) * c ^ (j - ell) * (p * u - c) ^ ell =
        (p * u) ^ j := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbin.symm
  have hcoeff : ∀ ell ∈ Finset.range (j + 1),
      (q * c) ^ (j - ell) * q ^ ell = q ^ j * c ^ (j - ell) := by
    intro ell hell
    have hle : ell ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hell)
    calc
      (q * c) ^ (j - ell) * q ^ ell =
          q ^ (j - ell) * c ^ (j - ell) * q ^ ell := by rw [mul_pow]
      _ = q ^ (j - ell) * q ^ ell * c ^ (j - ell) := by ring
      _ = q ^ j * c ^ (j - ell) := by
        rw [← pow_add]
        rw [Nat.sub_add_cancel hle]
  calc
    _ = ∑ ell ∈ Finset.range (j + 1),
          q ^ j * ((Nat.choose j ell : ℤ) * c ^ (j - ell) *
            (p * u - c) ^ ell) := by
      apply Finset.sum_congr rfl
      intro ell hell
      calc
        _ = (Nat.choose j ell : ℤ) *
            ((q * c) ^ (j - ell) * q ^ ell * (p * u - c) ^ ell) := by ring
        _ = _ := by rw [hcoeff ell hell]; ring
    _ = q ^ j * ∑ ell ∈ Finset.range (j + 1),
          (Nat.choose j ell : ℤ) * c ^ (j - ell) *
            (p * u - c) ^ ell := by rw [Finset.mul_sum]
    _ = q ^ j * (p * u) ^ j := by rw [hbin']
    _ = (p * q) ^ j * u ^ j := by
      rw [mul_pow]
      ring

def phiFrequency
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (qNat : ℕ) (c : Fin p)
    (r : ((fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi) : Fin k → ℤ :=
  fordSourceFrequencyAt (phiRow psi (qNat : ℤ) (c.val : ℤ)) r.1.1.1.1 -
    fordSourceFrequencyAt (phiRow psi (qNat : ℤ) (c.val : ℤ)) r.2.1 +
    fun j => ((p * qNat : ℕ) : ℤ) ^ (j.val + 1) *
      (∑ i : Fin s, (((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1) -
        ((r.1.2 i).1.val : ℤ) ^ (j.val + 1)))

def source35FrequencyNat
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (c : Fin p) (r : ((fordFiniteFCarrier (p := p) (k := k) (d := d)
      (P := P) hdk hp psi × (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi)
    (ell : ℕ) : ℤ :=
  if h : ell < k then source35Frequency (q := q) hdk hp psi c r ⟨ell, h⟩ else 0

def source35FrequencySucc
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (c : Fin p) (r : ((fordFiniteFCarrier (p := p) (k := k) (d := d)
      (P := P) hdk hp psi × (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi)
    (n : ℕ) : ℤ :=
  if h : n = 0 then 0 else source35FrequencyNat (q := q) hdk hp psi c r (n - 1)

lemma source35_to_phi_frequency
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (r : source35Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c) (j : Fin k) :
    phiFrequency (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q)
      hdk hp psi q c r.1 j = 0 := by
  let coeff : ℕ → ℤ := fun ell =>
    (Nat.choose (j.val + 1) ell : ℤ) * ((q : ℤ) * c.val) ^ (j.val + 1 - ell)
  have hweighted :
      ∑ ell ∈ Finset.range (j.val + 2),
        coeff ell * source35FrequencySucc (q := q) hdk hp psi c r.1 ell = 0 := by
    apply Finset.sum_eq_zero
    intro ell hell
    have hellle : ell ≤ j.val + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hell)
    by_cases hzero : ell = 0
    · simp [coeff, source35FrequencySucc, hzero]
    · have hellpos : 1 ≤ ell := Nat.one_le_iff_ne_zero.mpr hzero
      have hellk : ell - 1 < k := by omega
      simp [coeff, source35FrequencySucc, hzero, source35FrequencyNat, hellk,
        r.2 ⟨ell - 1, hellk⟩]
  change fordSourceFrequencyAt (phiRow psi (q : ℤ) c.val) r.1.1.1.1.1 j -
      fordSourceFrequencyAt (phiRow psi (q : ℤ) c.val) r.1.2.1 j +
      ((p * q : ℕ) : ℤ) ^ (j.val + 1) *
        (∑ i : Fin s, (((r.1.1.1.2 i).1.val : ℤ) ^ (j.val + 1) -
          ((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1))) = 0
  rw [source_sum_phi_expand hdk hp psi (q : ℤ) c.val r.1.1.1.1.1 j,
    source_sum_phi_expand hdk hp psi (q : ℤ) c.val r.1.2.1 j]
  -- The remaining finite rearrangement is the weighted binomial identity.
  have hweighted_expanded :
      ∑ ell ∈ Finset.range (j.val + 2),
        coeff ell * (
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.1.1.1.1 i).val : ℤ)) -
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.2.1 i).val : ℤ)) +
          (q : ℤ) ^ ell *
            (∑ i : Fin s,
              (((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell))) = 0 := by
    calc
      _ = ∑ ell ∈ Finset.range (j.val + 2),
          coeff ell * source35FrequencySucc (q := q) hdk hp psi c r.1 ell := by
        apply Finset.sum_congr rfl
        intro ell hell
        have hellle : ell ≤ j.val + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hell)
        by_cases hzero : ell = 0
        · have hpsi0 : psiNatSucc psi 0 = 0 := by simp [psiNatSucc]
          simp [coeff, source35FrequencySucc, hzero, hpsi0]
        · have hellk : ell - 1 < k := by omega
          have hpsi : psiNatSucc psi ell = psi ⟨ell - 1, hellk⟩ := by
            simp [psiNatSucc, hzero, psiNat_eq psi hellk]
          have hpow : ell - 1 + 1 = ell := by omega
          simp [coeff, source35FrequencySucc, source35FrequencyNat, hzero, hellk,
            hpsi, hpow, source35Frequency, fordSourceFrequencyAt]
      _ = 0 := hweighted
  have hpower :
      ((p * q : ℕ) : ℤ) ^ (j.val + 1) *
          (∑ i : Fin s, (((r.1.1.1.2 i).1.val : ℤ) ^ (j.val + 1) -
            ((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1))) =
        (∑ ell ∈ Finset.range (j.val + 2),
          coeff ell * (q : ℤ) ^ ell *
            (∑ i : Fin s,
              (((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell))) := by
    calc
      _ = ∑ i : Fin s,
          (((p * q : ℕ) : ℤ) ^ (j.val + 1) *
              ((r.1.1.1.2 i).1.val : ℤ) ^ (j.val + 1) -
            ((p * q : ℕ) : ℤ) ^ (j.val + 1) *
              ((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1)) := by
        rw [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin s,
          ((∑ ell ∈ Finset.range (j.val + 2),
            coeff ell * (q : ℤ) ^ ell *
              ((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell) -
           (∑ ell ∈ Finset.range (j.val + 2),
            coeff ell * (q : ℤ) ^ ell *
              ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hu := binomial_qc_power (p : ℤ) (q : ℤ) (c.val : ℤ)
          (r.1.1.1.2 i).1.val (j.val + 1)
        have hv := binomial_qc_power (p : ℤ) (q : ℤ) (c.val : ℤ)
          (r.1.1.2 i).1.val (j.val + 1)
        have hpq : ((p * q : ℕ) : ℤ) = (p : ℤ) * (q : ℤ) := by norm_num
        rw [hpq, ← hu, ← hv]
      _ = (∑ ell ∈ Finset.range (j.val + 2),
            ∑ i : Fin s, coeff ell * (q : ℤ) ^ ell *
              ((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell) -
          (∑ ell ∈ Finset.range (j.val + 2),
            ∑ i : Fin s, coeff ell * (q : ℤ) ^ ell *
              ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        · exact Finset.sum_comm
        · exact Finset.sum_comm
      _ = ∑ ell ∈ Finset.range (j.val + 2),
            ((∑ i : Fin s, coeff ell * (q : ℤ) ^ ell *
                ((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell) -
             (∑ i : Fin s, coeff ell * (q : ℤ) ^ ell *
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ell hell
        calc
          (∑ i : Fin s, coeff ell * (q : ℤ) ^ ell *
              ((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell) -
              (∑ i : Fin s, coeff ell * (q : ℤ) ^ ell *
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell) =
            ∑ i : Fin s, (coeff ell * (q : ℤ) ^ ell *
              ((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
              coeff ell * (q : ℤ) ^ ell *
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell) := by
              rw [Finset.sum_sub_distrib]
          _ = ∑ i : Fin s, coeff ell * (q : ℤ) ^ ell *
              (((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = coeff ell * (q : ℤ) ^ ell *
              (∑ i : Fin s, (((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell)) := by
              rw [Finset.mul_sum]
  have hsource :
      (∑ ell ∈ Finset.range (j.val + 2),
        (Nat.choose (j.val + 1) ell : ℤ) *
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.1.1.1.1 i).val : ℤ)) *
            ((q : ℤ) * c.val) ^ (j.val + 1 - ell)) -
      (∑ ell ∈ Finset.range (j.val + 2),
        (Nat.choose (j.val + 1) ell : ℤ) *
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.2.1 i).val : ℤ)) *
            ((q : ℤ) * c.val) ^ (j.val + 1 - ell)) =
      ∑ ell ∈ Finset.range (j.val + 2),
        coeff ell * (
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.1.1.1.1 i).val : ℤ)) -
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.2.1 i).val : ℤ))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ell hell
    dsimp [coeff]
    ring
  calc
    _ = (∑ ell ∈ Finset.range (j.val + 2),
          coeff ell * (
            (∑ i : Fin k, (psiNatSucc psi ell).eval
              ((r.1.1.1.1.1 i).val : ℤ)) -
            (∑ i : Fin k, (psiNatSucc psi ell).eval
              ((r.1.2.1 i).val : ℤ)))) +
        (∑ ell ∈ Finset.range (j.val + 2),
          coeff ell * (q : ℤ) ^ ell *
            (∑ i : Fin s,
              (((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell))) := by
      rw [hsource, hpower]
    _ = ∑ ell ∈ Finset.range (j.val + 2),
        (coeff ell * (
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.1.1.1.1 i).val : ℤ)) -
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.2.1 i).val : ℤ))) +
         coeff ell * (q : ℤ) ^ ell *
           (∑ i : Fin s,
             (((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
               ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell))) := by
      rw [← Finset.sum_add_distrib]
    _ = ∑ ell ∈ Finset.range (j.val + 2),
        coeff ell * (
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.1.1.1.1 i).val : ℤ)) -
          (∑ i : Fin k, (psiNatSucc psi ell).eval
            ((r.1.2.1 i).val : ℤ)) +
          (q : ℤ) ^ ell *
            (∑ i : Fin s,
              (((p : ℤ) * (r.1.1.1.2 i).1.val - c.val) ^ ell -
                ((p : ℤ) * (r.1.1.2 i).1.val - c.val) ^ ell))) := by
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ = 0 := hweighted_expanded

def source36Carrier
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) : Type :=
  {r : ((fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi //
    ∀ j, phiFrequency (q := q) hdk hp psi q c r j = 0}

instance source36CarrierFintype
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Fintype (source36Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c) := by
  classical
  dsimp [source36Carrier]
  infer_instance

def source35To36
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (r : source35Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c) :
    source36Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c := by
  refine ⟨r.1, ?_⟩
  intro j
  exact source35_to_phi_frequency hdk hp psi c r j

lemma source35To36_injective
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Function.Injective (source35To36 (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun z => z.1) hab)

theorem source35_card_le_source36_card
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Fintype.card (source35Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c) ≤
      Fintype.card (source36Carrier (p := p) (s := s) (k := k) (d := d)
        (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  exact Fintype.card_le_of_injective _
    (source35To36_injective (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c)

def rawS4ToSource36
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (b : ZMod p)
    (r : fordFiniteRawS4Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b) :
    source36Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi (negResidue b) :=
  source35To36 (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
    (q := q) hdk hp psi (negResidue b)
    (rawS4ToSource35 (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi b r)

lemma rawS4ToSource36_injective
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (b : ZMod p) :
    Function.Injective (rawS4ToSource36 (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b) := by
  exact (source35To36_injective (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp psi (negResidue b)).comp
    (rawS4ToSource35_injective (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b)

theorem rawS4_card_le_source36_card
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (b : ZMod p) :
    Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b) ≤
      Fintype.card (source36Carrier (p := p) (s := s) (k := k) (d := d)
        (Q := Q) (P := P) (q := q) hdk hp psi (negResidue b)) := by
  exact Fintype.card_le_of_injective _
    (rawS4ToSource36_injective (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b)

end
end MAPFordP16Source35Triangular

#print axioms MAPFordP16Source35Triangular.source35_to_phi_frequency
#print axioms MAPFordP16Source35Triangular.source36CarrierFintype
#print axioms MAPFordP16Source35Triangular.source35To36_injective
#print axioms MAPFordP16Source35Triangular.rawS4ToSource36_injective
