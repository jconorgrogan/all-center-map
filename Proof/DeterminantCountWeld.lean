import MixedMellinCert

/-!
# Literal determinant-sector certificate

This file keeps the four integer variables and their dyadic ranges visible.
It certifies the sign-reversing involution on the actual tuple set, the exact
zero-determinant parametrization with the dyadic inequalities retained, and
the content/divisor-floor identity attached to every positive determinant
fiber.
-/

namespace DeterminantCountWeld

open MixedMellinCert

/-- A literal tuple `((m₁,m₂),(n₁,n₂))` from the expanded mixed mean. -/
abbrev LiteralTuple := (ℕ × ℕ) × (ℕ × ℕ)

/-- The paper's half-open dyadic interval `(X,2X]`. -/
def dyadic (X : ℕ) : Finset ℕ := Finset.Ioc X (2 * X)

/-- The literal determinant `m₁ n₁ - m₂ n₂`. -/
def determinant (t : LiteralTuple) : ℤ :=
  (t.1.1 * t.2.1 : ℕ) - (t.1.2 * t.2.2 : ℕ)

/-- Simultaneously swap the two short and the two long indices. -/
def swapTuple (t : LiteralTuple) : LiteralTuple :=
  ((t.1.2, t.1.1), (t.2.2, t.2.1))

@[simp] theorem swapTuple_involutive (t : LiteralTuple) :
    swapTuple (swapTuple t) = t := by
  rcases t with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  rfl

@[simp] theorem determinant_swap (t : LiteralTuple) :
    determinant (swapTuple t) = -determinant t := by
  rcases t with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  simp [determinant, swapTuple]

/-- The integer determinant magnitude is exactly the paper's natural-number
product collar. -/
theorem determinant_natAbs_eq_product_dist (t : LiteralTuple) :
    (determinant t).natAbs =
      Nat.dist (t.1.1 * t.2.1) (t.1.2 * t.2.2) := by
  rcases t with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  change (Int.natAbs ((m₁ * n₁ : ℕ) - (m₂ * n₂ : ℕ))) =
    (m₁ * n₁).dist (m₂ * n₂)
  by_cases h : m₂ * n₂ ≤ m₁ * n₁
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
  · have hle : m₁ * n₁ ≤ m₂ * n₂ := Nat.le_of_not_ge h
    rw [Int.natAbs_natCast_sub_natCast_of_le hle]
    rw [Nat.dist_eq_sub_of_le hle]

/-- The exact finite tuple set surviving the two arithmetic windows, with the
unequal-short-index restriction already imposed. -/
def literalTuples (M N K Y : ℕ) : Finset LiteralTuple :=
  ((((dyadic M).product (dyadic M)).product
      ((dyadic N).product (dyadic N))).filter fun t =>
    t.1.1 ≠ t.1.2 ∧
      Nat.dist t.1.1 t.1.2 ≤ K ∧
      (determinant t).natAbs ≤ Y)

/-- Positive, negative, and zero determinant sectors of the literal set. -/
def positiveSector (M N K Y : ℕ) : Finset LiteralTuple :=
  (literalTuples M N K Y).filter fun t => 0 < determinant t

def negativeSector (M N K Y : ℕ) : Finset LiteralTuple :=
  (literalTuples M N K Y).filter fun t => determinant t < 0

def zeroSector (M N K Y : ℕ) : Finset LiteralTuple :=
  (literalTuples M N K Y).filter fun t => determinant t = 0

/-- The nonzero literal tuples with fixed short indices
`(m₁,m₂)=(d*a,d*b)`. -/
def fixedNonzeroLiteralSlice (M N K Y d a b : ℕ) : Finset LiteralTuple :=
  (literalTuples M N K Y).filter fun t =>
    t.1 = (d * a, d * b) ∧ determinant t ≠ 0

theorem mem_literalTuples_swap_iff (M N K Y : ℕ) (t : LiteralTuple) :
    swapTuple t ∈ literalTuples M N K Y ↔
      t ∈ literalTuples M N K Y := by
  simp only [literalTuples, Finset.mem_filter]
  rw [show determinant (swapTuple t) = -determinant t from determinant_swap t]
  simp only [Int.natAbs_neg]
  rcases t with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  simp only [dyadic, swapTuple]
  have hdist : m₂.dist m₁ = m₁.dist m₂ := Nat.dist_comm _ _
  constructor <;> aesop

theorem swapTuple_injective : Function.Injective swapTuple := by
  intro s t h
  calc
    s = swapTuple (swapTuple s) := (swapTuple_involutive s).symm
    _ = swapTuple (swapTuple t) := by rw [h]
    _ = t := swapTuple_involutive t

theorem mem_negativeSector_swap_iff (M N K Y : ℕ) (t : LiteralTuple) :
    swapTuple t ∈ negativeSector M N K Y ↔
      t ∈ positiveSector M N K Y := by
  simp only [negativeSector, positiveSector, Finset.mem_filter,
    mem_literalTuples_swap_iff, determinant_swap]
  constructor <;> rintro ⟨ht, hsign⟩
  · exact ⟨ht, (neg_lt_zero.mp hsign)⟩
  · exact ⟨ht, (neg_lt_zero.mpr hsign)⟩

theorem mem_positiveSector_swap_iff (M N K Y : ℕ) (t : LiteralTuple) :
    swapTuple t ∈ positiveSector M N K Y ↔
      t ∈ negativeSector M N K Y := by
  simp only [positiveSector, negativeSector, Finset.mem_filter,
    mem_literalTuples_swap_iff, determinant_swap]
  constructor <;> rintro ⟨ht, hsign⟩
  · exact ⟨ht, (neg_pos.mp hsign)⟩
  · exact ⟨ht, (neg_pos.mpr hsign)⟩

/-- The swap involution carries the literal positive sector onto the literal
negative sector, not merely an abstract determinant-index sum. -/
theorem image_swap_positiveSector (M N K Y : ℕ) :
    (positiveSector M N K Y).image swapTuple =
      negativeSector M N K Y := by
  ext t
  constructor
  · intro ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact (mem_negativeSector_swap_iff M N K Y u).2 hu
  · intro ht
    apply Finset.mem_image.mpr
    refine ⟨swapTuple t, ?_, swapTuple_involutive t⟩
    exact (mem_positiveSector_swap_iff M N K Y t).2 ht

/-- Hence the actual positive and negative tuple sectors have equal size. -/
theorem card_positiveSector_eq_negativeSector (M N K Y : ℕ) :
    (positiveSector M N K Y).card =
      (negativeSector M N K Y).card := by
  rw [← image_swap_positiveSector M N K Y]
  exact (Finset.card_image_of_injective _ swapTuple_injective).symm

/-- The zero determinant fiber at fixed coprime reduced short indices, with
the long variables still restricted to `(N,2N]`. -/
def zeroFiber (N a b : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadic N).product (dyadic N)).filter fun n =>
    a * n.1 = b * n.2

/-- Exactly those parameters whose two multiples lie in `(N,2N]`.
The ambient `range (2N+1)` is a proved finite envelope, not an extra bound. -/
def zeroParameters (N a b : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter fun s =>
    N < b * s ∧ b * s ≤ 2 * N ∧
      N < a * s ∧ a * s ≤ 2 * N

/-- Under the actual dyadic bounds, the zero fiber is precisely
`(n₁,n₂)=(b s,a s)`. -/
theorem image_zeroParameters_eq_zeroFiber (N a b : ℕ)
    (hab : a.Coprime b) (hb : 0 < b) :
    (zeroParameters N a b).image (fun s => (b * s, a * s)) =
      zeroFiber N a b := by
  ext n
  constructor
  · intro hn
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
    simp only [zeroParameters, Finset.mem_filter, Finset.mem_range] at hs
    rcases hs with ⟨_, hbLower, hbUpper, haLower, haUpper⟩
    simp only [zeroFiber, Finset.mem_filter]
    constructor
    · simp [dyadic, hbLower, hbUpper, haLower, haUpper]
    · exact zero_determinant_of_parametrization a b s
  · intro hn
    simp only [zeroFiber, Finset.mem_filter] at hn
    rcases hn with ⟨hbox, hdet⟩
    simp [dyadic] at hbox
    rcases hbox with ⟨⟨hn₁Lower, hn₁Upper⟩, ⟨hn₂Lower, hn₂Upper⟩⟩
    obtain ⟨s, hs₁, hs₂⟩ :=
      zero_determinant_parametrization hab hb hdet
    have hn : n = (b * s, a * s) := Prod.ext hs₁ hs₂
    subst n
    apply Finset.mem_image.mpr
    refine ⟨s, ?_, rfl⟩
    simp only [zeroParameters, Finset.mem_filter, Finset.mem_range]
    have hs_le_mul : s ≤ b * s := Nat.le_mul_of_pos_left s hb
    have hs_le : s ≤ 2 * N := hs_le_mul.trans hn₁Upper
    exact ⟨by omega, hn₁Lower, hn₁Upper, hn₂Lower, hn₂Upper⟩

/-- Exact cardinality form of the range-sensitive zero parametrization. -/
theorem card_zeroFiber_eq_card_zeroParameters (N a b : ℕ)
    (hab : a.Coprime b) (hb : 0 < b) :
    (zeroFiber N a b).card = (zeroParameters N a b).card := by
  rw [← image_zeroParameters_eq_zeroFiber N a b hab hb]
  apply Finset.card_image_of_injective
  intro s t h
  have hbst : b * s = b * t := congrArg Prod.fst h
  exact Nat.eq_of_mul_eq_mul_left hb hbst

/-- The reduced determinant `a n₁-b n₂` on a long-index pair. -/
def reducedDeterminant (a b : ℕ) (n : ℕ × ℕ) : ℤ :=
  ((a * n.1 : ℕ) : ℤ) - ((b * n.2 : ℕ) : ℤ)

/-- The literal positive reduced-determinant fiber in `(N,2N]^2`, truncated
at the exact natural length `L`. -/
def positiveReducedFiber (N a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadic N).product (dyadic N)).filter fun n =>
    0 < reducedDeterminant a b n ∧
      (reducedDeterminant a b n).natAbs ≤ L

/-- A single positive determinant equation on the literal dyadic long box. -/
def positiveEquationFiber (N a b ell : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadic N).product (dyadic N)).filter fun n =>
    a * n.1 = ell + b * n.2

/-- A single negative determinant equation on the literal dyadic long box. -/
def negativeEquationFiber (N a b ell : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadic N).product (dyadic N)).filter fun n =>
    b * n.2 = ell + a * n.1

/-- The nonzero part of the exact product collar for a fixed reduced short
pair `m₁=d*a`, `m₂=d*b`. -/
def nonzeroReducedCollar (N H d a b : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadic N).product (dyadic N)).filter fun n =>
    (d * a * n.1).dist (d * b * n.2) ≠ 0 ∧
      (d * a * n.1).dist (d * b * n.2) ≤ H

/-- The union of all exact positive and negative determinant fibers with
`1 ≤ ell ≤ H/d`. -/
def signedEquationFibers (N H d a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (H / d)).biUnion fun ell =>
    positiveEquationFiber N a b ell ∪ negativeEquationFiber N a b ell

/-- Divisibility plus a nonzero `Nat.dist` collar is equivalent to the two
literal sign equations, including the floor endpoint `H/d`. -/
theorem collar_iff_sign_equations {x y d H : ℕ} (hd : 0 < d)
    (hdx : d ∣ x) (hdy : d ∣ y) :
    (x.dist y ≠ 0 ∧ x.dist y ≤ H) ↔
      ∃ ell ∈ Finset.Icc 1 (H / d),
        x = d * ell + y ∨ y = d * ell + x := by
  constructor
  · rintro ⟨hne, hH⟩
    have hxy : x ≠ y := by
      intro h
      subst y
      simp at hne
    rcases lt_or_gt_of_ne hxy with hxy | hyx
    · have hdist : x.dist y = y - x :=
        Nat.dist_eq_sub_of_le (Nat.le_of_lt hxy)
      have hdsub : d ∣ y - x := Nat.dvd_sub hdy hdx
      obtain ⟨ell, hell⟩ := hdsub
      have hellpos : 0 < ell := by
        by_contra hz
        simp only [Nat.not_lt, Nat.le_zero] at hz
        subst ell
        simp at hell
        omega
      have helldiv : ell ≤ H / d := by
        rw [Nat.le_div_iff_mul_le hd]
        have hmul : d * ell ≤ H := by simpa [hdist, hell] using hH
        simpa [Nat.mul_comm] using hmul
      refine ⟨ell, by simp only [Finset.mem_Icc]; omega, Or.inr ?_⟩
      exact (Nat.sub_eq_iff_eq_add (Nat.le_of_lt hxy)).mp hell
    · have hdist : x.dist y = x - y := by
        rw [Nat.dist_comm]
        exact Nat.dist_eq_sub_of_le (Nat.le_of_lt hyx)
      have hdsub : d ∣ x - y := Nat.dvd_sub hdx hdy
      obtain ⟨ell, hell⟩ := hdsub
      have hellpos : 0 < ell := by
        by_contra hz
        simp only [Nat.not_lt, Nat.le_zero] at hz
        subst ell
        simp at hell
        omega
      have helldiv : ell ≤ H / d := by
        rw [Nat.le_div_iff_mul_le hd]
        have hmul : d * ell ≤ H := by simpa [hdist, hell] using hH
        simpa [Nat.mul_comm] using hmul
      refine ⟨ell, by simp only [Finset.mem_Icc]; omega, Or.inl ?_⟩
      exact (Nat.sub_eq_iff_eq_add (Nat.le_of_lt hyx)).mp hell
  · rintro ⟨ell, hell, hpos | hneg⟩
    · simp only [Finset.mem_Icc] at hell
      have hle : y ≤ x := by omega
      have hdist : x.dist y = d * ell := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle, hpos]
        simp
      rw [hdist]
      constructor
      · exact Nat.ne_of_gt (Nat.mul_pos hd hell.1)
      · have hmul : ell * d ≤ H := (Nat.le_div_iff_mul_le hd).mp hell.2
        simpa [Nat.mul_comm] using hmul
    · simp only [Finset.mem_Icc] at hell
      have hle : x ≤ y := by omega
      have hdist : x.dist y = d * ell := by
        rw [Nat.dist_eq_sub_of_le hle, hneg]
        simp
      rw [hdist]
      constructor
      · exact Nat.ne_of_gt (Nat.mul_pos hd hell.1)
      · have hmul : ell * d ≤ H := (Nat.le_div_iff_mul_le hd).mp hell.2
        simpa [Nat.mul_comm] using hmul

theorem reduced_collar_iff_sign_equations {d a b n₁ n₂ H : ℕ}
    (hd : 0 < d) :
    ((d * a * n₁).dist (d * b * n₂) ≠ 0 ∧
      (d * a * n₁).dist (d * b * n₂) ≤ H) ↔
      ∃ ell ∈ Finset.Icc 1 (H / d),
        a * n₁ = ell + b * n₂ ∨ b * n₂ = ell + a * n₁ := by
  rw [collar_iff_sign_equations hd]
  · constructor
    · rintro ⟨ell, hell, hpos | hneg⟩
      · refine ⟨ell, hell, Or.inl ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hd
        calc
          d * (a * n₁) = d * a * n₁ := by ac_rfl
          _ = d * ell + d * b * n₂ := hpos
          _ = d * (ell + b * n₂) := by ring
      · refine ⟨ell, hell, Or.inr ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hd
        calc
          d * (b * n₂) = d * b * n₂ := by ac_rfl
          _ = d * ell + d * a * n₁ := hneg
          _ = d * (ell + a * n₁) := by ring
    · rintro ⟨ell, hell, hpos | hneg⟩
      · refine ⟨ell, hell, Or.inl ?_⟩
        calc
          d * a * n₁ = d * (a * n₁) := by ac_rfl
          _ = d * (ell + b * n₂) := by rw [hpos]
          _ = d * ell + d * b * n₂ := by ring
      · refine ⟨ell, hell, Or.inr ?_⟩
        calc
          d * b * n₂ = d * (b * n₂) := by ac_rfl
          _ = d * (ell + a * n₁) := by rw [hneg]
          _ = d * ell + d * a * n₁ := by ring
  · simpa [mul_assoc] using dvd_mul_right d (a * n₁)
  · simpa [mul_assoc] using dvd_mul_right d (b * n₂)

/-- Exact finite-set decomposition of the fixed-pair nonzero collar. -/
theorem nonzeroReducedCollar_eq_signedEquationFibers
    (N H d a b : ℕ) (hd : 0 < d) :
    nonzeroReducedCollar N H d a b = signedEquationFibers N H d a b := by
  ext n
  simp only [nonzeroReducedCollar, signedEquationFibers,
    positiveEquationFiber, negativeEquationFiber, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨hbox, hcollar⟩
    obtain ⟨ell, hell, hpos | hneg⟩ :=
      (reduced_collar_iff_sign_equations hd).1 hcollar
    · exact ⟨ell, hell, Or.inl ⟨hbox, hpos⟩⟩
    · exact ⟨ell, hell, Or.inr ⟨hbox, hneg⟩⟩
  · rintro ⟨ell, hell, ⟨hbox, hpos⟩ | ⟨hbox, hneg⟩⟩
    · exact ⟨hbox, (reduced_collar_iff_sign_equations hd).2
        ⟨ell, hell, Or.inl hpos⟩⟩
    · exact ⟨hbox, (reduced_collar_iff_sign_equations hd).2
        ⟨ell, hell, Or.inr hneg⟩⟩

/-- Once the fixed short pair satisfies its literal dyadic and `K` bounds,
projecting its nonzero four-index slice onto `(n₁,n₂)` is exactly the reduced
product collar. -/
theorem image_fixedNonzeroLiteralSlice_eq_nonzeroReducedCollar
    (M N K Y d a b : ℕ)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    (fixedNonzeroLiteralSlice M N K Y d a b).image Prod.snd =
      nonzeroReducedCollar N Y d a b := by
  ext n
  constructor
  · intro hn
    obtain ⟨t, ht, ht₂⟩ := Finset.mem_image.mp hn
    rcases Finset.mem_filter.mp ht with ⟨htLiteral, htShort, htDetNe⟩
    have htEq : t = ((d * a, d * b), n) := Prod.ext htShort ht₂
    subst t
    rcases Finset.mem_filter.mp htLiteral with
      ⟨htBox, _, _, htLength⟩
    have hnBox : n ∈ (dyadic N).product (dyadic N) :=
      (Finset.mem_product.mp htBox).2
    have hdistNe :
        (d * a * n.1).dist (d * b * n.2) ≠ 0 := by
      rw [← determinant_natAbs_eq_product_dist
        (((d * a, d * b), n) : LiteralTuple)]
      exact Int.natAbs_ne_zero.mpr htDetNe
    have hdistLe :
        (d * a * n.1).dist (d * b * n.2) ≤ Y := by
      rw [← determinant_natAbs_eq_product_dist
        (((d * a, d * b), n) : LiteralTuple)]
      exact htLength
    exact Finset.mem_filter.mpr ⟨hnBox, hdistNe, hdistLe⟩
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnBox, hdistNe, hdistLe⟩
    apply Finset.mem_image.mpr
    refine ⟨(((d * a, d * b), n) : LiteralTuple), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hshortBox, hnBox⟩,
        hshortNe, hshortK, ?_⟩
      rw [determinant_natAbs_eq_product_dist]
      exact hdistLe
    · refine ⟨rfl, ?_⟩
      apply Int.natAbs_ne_zero.mp
      rw [determinant_natAbs_eq_product_dist]
      exact hdistNe

/-- Every member of the literal positive fiber has a unique positive natural
determinant index in `[1,L]`; this statement records the exact reconstruction
after the common factor `d` is restored. -/
theorem positiveReducedFiber_determinant_index {N a b L : ℕ} {n : ℕ × ℕ}
    (hn : n ∈ positiveReducedFiber N a b L) :
    ∃ ell ∈ Finset.Icc 1 L,
      a * n.1 = ell + b * n.2 ∧
        ∀ d : ℕ, (d * a) * n.1 = d * ell + (d * b) * n.2 := by
  simp only [positiveReducedFiber, Finset.mem_filter] at hn
  rcases hn with ⟨_, hpos, hlength⟩
  have hcast : ((b * n.2 : ℕ) : ℤ) < ((a * n.1 : ℕ) : ℤ) := by
    exact (sub_pos.mp hpos)
  have hlt : b * n.2 < a * n.1 := by
    exact_mod_cast hcast
  let ell := a * n.1 - b * n.2
  have hellPos : 0 < ell := by
    exact Nat.sub_pos_of_lt hlt
  have habs : (reducedDeterminant a b n).natAbs = ell := by
    exact Int.natAbs_natCast_sub_natCast_of_ge hlt.le
  have hellLength : ell ≤ L := by simpa [habs] using hlength
  have hdet : a * n.1 = ell + b * n.2 := by
    dsimp [ell]
    omega
  refine ⟨ell, ?_, hdet, ?_⟩
  · simp only [Finset.mem_Icc]
    omega
  · intro d
    exact determinant_reconstruction hdet

/-- The two residue contents and their product are the paper's literal
`d₁`, `d₂`, and `gcd(ell,a*b)` on every bounded positive fiber. -/
theorem positiveReducedFiber_content {N a b L : ℕ} {n : ℕ × ℕ}
    (hab : a.Coprime b) (hn : n ∈ positiveReducedFiber N a b L) :
    ∃ ell ∈ Finset.Icc 1 L,
      a * n.1 = ell + b * n.2 ∧
      n.1.gcd b = ell.gcd b ∧
      n.2.gcd a = ell.gcd a ∧
      n.1.gcd b * n.2.gcd a = ell.gcd (a * b) := by
  obtain ⟨ell, hell, hdet, _⟩ :=
    positiveReducedFiber_determinant_index hn
  have hleft := left_residue_content hab hdet
  have hright := right_residue_content hab hdet
  refine ⟨ell, hell, hdet, hleft, hright, ?_⟩
  rw [hleft, hright]
  rw [mul_comm]
  exact gcd_mul_gcd_of_coprime hab

/-- Content identities on a named positive equation fiber. -/
theorem positiveEquationFiber_content {N a b ell : ℕ} {n : ℕ × ℕ}
    (hab : a.Coprime b) (hn : n ∈ positiveEquationFiber N a b ell) :
    a * n.1 = ell + b * n.2 ∧
    n.1.gcd b = ell.gcd b ∧
    n.2.gcd a = ell.gcd a ∧
    n.1.gcd b * n.2.gcd a = ell.gcd (a * b) := by
  simp only [positiveEquationFiber, Finset.mem_filter] at hn
  rcases hn with ⟨_, hdet⟩
  have hleft := left_residue_content hab hdet
  have hright := right_residue_content hab hdet
  refine ⟨hdet, hleft, hright, ?_⟩
  rw [hleft, hright, mul_comm]
  exact gcd_mul_gcd_of_coprime hab

/-- Content identities on a named negative equation fiber, obtained by the
literal substitution `(a,b,n₁,n₂) ↦ (b,a,n₂,n₁)`. -/
theorem negativeEquationFiber_content {N a b ell : ℕ} {n : ℕ × ℕ}
    (hab : a.Coprime b) (hn : n ∈ negativeEquationFiber N a b ell) :
    b * n.2 = ell + a * n.1 ∧
    n.1.gcd b = ell.gcd b ∧
    n.2.gcd a = ell.gcd a ∧
    n.1.gcd b * n.2.gcd a = ell.gcd (a * b) := by
  simp only [negativeEquationFiber, Finset.mem_filter] at hn
  rcases hn with ⟨_, hdet⟩
  have hn₂ := left_residue_content hab.symm hdet
  have hn₁ := right_residue_content hab.symm hdet
  refine ⟨hdet, hn₁, hn₂, ?_⟩
  rw [hn₁, hn₂, mul_comm]
  exact gcd_mul_gcd_of_coprime hab

/-- The determinant-level content envelope for both signs.  This is
deliberately named an envelope: it is the arithmetic weight obtained after a
fiber estimate, not the unweighted number of tuples in a fiber. -/
def signedContentEnvelope (r H d a b : ℕ) : ℕ :=
  ∑ e ∈ Finset.range (H / d),
    (tauAF (r + 1) ((e + 1).gcd (a * b)) +
      tauAF (r + 1) ((e + 1).gcd (a * b)))

/-- Exact signed divisor-floor identity with the paper's literal length
`floor(H/d)` and no additive `+1`. -/
theorem signedContentEnvelope_eq_divisorFloor (r H d a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    signedContentEnvelope r H d a b =
      2 * ∑ v ∈ (a * b).divisors,
        (H / (d * v)) * tauAF r v := by
  have hq : a * b ≠ 0 := Nat.mul_ne_zero ha.ne' hb.ne'
  unfold signedContentEnvelope
  calc
    (∑ e ∈ Finset.range (H / d),
      (tauAF (r + 1) ((e + 1).gcd (a * b)) +
        tauAF (r + 1) ((e + 1).gcd (a * b)))) =
        2 * (∑ e ∈ Finset.range (H / d),
          tauAF (r + 1) ((e + 1).gcd (a * b))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            omega
    _ = 2 * ∑ v ∈ (a * b).divisors,
          ((H / d) / v) * tauAF r v :=
      signed_tau_gcd_sum_exact r (H / d) (a * b) hq
    _ = 2 * ∑ v ∈ (a * b).divisors,
          (H / (d * v)) * tauAF r v := by
      simp only [Nat.div_div_eq_div_mul]

/-- Weighted mass of a literal determinant fiber. -/
def fiberMass (w : ℕ → ℕ → ℕ) (s : Finset (ℕ × ℕ)) : ℕ :=
  ∑ n ∈ s, w n.1 n.2

/-- Total positive-plus-negative mass for a fixed reduced short pair and the
exact determinant range `1 ≤ ell ≤ H/d`. -/
def nonzeroFixedMass (w : ℕ → ℕ → ℕ)
    (N H d a b : ℕ) : ℕ :=
  ∑ e ∈ Finset.range (H / d),
    (fiberMass w (positiveEquationFiber N a b (e + 1)) +
      fiberMass w (negativeEquationFiber N a b (e + 1)))

/-- Honest conditional bridge from literal tuple mass to the exact
divisor-floor expression.  The two displayed hypotheses are precisely the
still-unformalized Shiu/Cauchy fiber estimates; the arithmetic summation and
normalization are unconditional below them. -/
theorem conditional_nonzeroFixedMass_divisorFloor
    (r N H d a b C : ℕ) (w : ℕ → ℕ → ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hpos : ∀ e ∈ Finset.range (H / d),
      fiberMass w (positiveEquationFiber N a b (e + 1)) ≤
        C * tauAF (r + 1) ((e + 1).gcd (a * b)))
    (hneg : ∀ e ∈ Finset.range (H / d),
      fiberMass w (negativeEquationFiber N a b (e + 1)) ≤
        C * tauAF (r + 1) ((e + 1).gcd (a * b))) :
    nonzeroFixedMass w N H d a b ≤
      2 * C * ∑ v ∈ (a * b).divisors,
        (H / (d * v)) * tauAF r v := by
  have hq : a * b ≠ 0 := Nat.mul_ne_zero ha.ne' hb.ne'
  unfold nonzeroFixedMass
  calc
    (∑ e ∈ Finset.range (H / d),
      (fiberMass w (positiveEquationFiber N a b (e + 1)) +
        fiberMass w (negativeEquationFiber N a b (e + 1)))) ≤
        ∑ e ∈ Finset.range (H / d),
          (C * tauAF (r + 1) ((e + 1).gcd (a * b)) +
            C * tauAF (r + 1) ((e + 1).gcd (a * b))) := by
              apply Finset.sum_le_sum
              intro e he
              exact Nat.add_le_add (hpos e he) (hneg e he)
    _ = 2 * C * (∑ e ∈ Finset.range (H / d),
          tauAF (r + 1) ((e + 1).gcd (a * b))) := by
            rw [Finset.mul_sum]
            simp only [← two_mul, mul_assoc]
    _ = 2 * C * (∑ v ∈ (a * b).divisors,
          ((H / d) / v) * tauAF r v) := by
            rw [tau_gcd_sum_exact r (H / d) (a * b) hq]
    _ = 2 * C * (∑ v ∈ (a * b).divisors,
          (H / (d * v)) * tauAF r v) := by
            simp only [Nat.div_div_eq_div_mul]

/-- The exact content envelope for all positive determinant indices is the
divisor-floor sum, with no additive `+1`.  The quantifier over the literal
fiber welds that arithmetic identity to the bounded tuples it controls. -/
theorem positiveFiber_content_floor_weld (r N a b L : ℕ)
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    (∀ n ∈ positiveReducedFiber N a b L,
      ∃ ell ∈ Finset.Icc 1 L,
        a * n.1 = ell + b * n.2 ∧
        n.1.gcd b = ell.gcd b ∧
        n.2.gcd a = ell.gcd a ∧
        n.1.gcd b * n.2.gcd a = ell.gcd (a * b)) ∧
    (∑ e ∈ Finset.range L,
        tauAF (r + 1) ((e + 1).gcd (a * b))) =
      ∑ v ∈ (a * b).divisors,
        (L / v) * tauAF r v := by
  constructor
  · intro n hn
    exact positiveReducedFiber_content hab hn
  · exact tau_gcd_sum_exact r L (a * b) (Nat.mul_ne_zero ha.ne' hb.ne')

/-- One checked statement containing the paper's finite tuple ranges, the
positive/negative sign-sector bijection, the exact bounded zero sector, the
content factors on every positive fiber, and the divisor-floor sum. -/
theorem literal_determinant_count_weld (M N K Y r d a b L : ℕ)
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    (positiveSector M N K Y).card =
        (negativeSector M N K Y).card ∧
    (zeroFiber N a b).card = (zeroParameters N a b).card ∧
    (∀ n ∈ positiveReducedFiber N a b L,
      ∃ ell ∈ Finset.Icc 1 L,
        a * n.1 = ell + b * n.2 ∧
        (d * a) * n.1 = d * ell + (d * b) * n.2 ∧
        n.1.gcd b = ell.gcd b ∧
        n.2.gcd a = ell.gcd a ∧
        n.1.gcd b * n.2.gcd a = ell.gcd (a * b)) ∧
    (∑ e ∈ Finset.range L,
        tauAF (r + 1) ((e + 1).gcd (a * b))) =
      ∑ v ∈ (a * b).divisors,
        (L / v) * tauAF r v := by
  refine ⟨card_positiveSector_eq_negativeSector M N K Y,
    card_zeroFiber_eq_card_zeroParameters N a b hab hb, ?_, ?_⟩
  · intro n hn
    obtain ⟨ell, hell, hdet, hall⟩ :=
      positiveReducedFiber_determinant_index hn
    have hleft := left_residue_content hab hdet
    have hright := right_residue_content hab hdet
    refine ⟨ell, hell, hdet, hall d, hleft, hright, ?_⟩
    rw [hleft, hright, mul_comm]
    exact gcd_mul_gcd_of_coprime hab
  · exact tau_gcd_sum_exact r L (a * b) (Nat.mul_ne_zero ha.ne' hb.ne')

/-- The full exact arithmetic weld at fixed reduced short indices.  It links
the literal four-index collar to its signed fibers, retains the true dyadic
zero-sector range, certifies both sign-specific content identities, and ends
at the exact divisor-floor envelope with `L=Y/d`. -/
theorem literal_determinant_count_weld_exact
    (M N K Y r d a b : ℕ)
    (hab : a.Coprime b) (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    (positiveSector M N K Y).card =
        (negativeSector M N K Y).card ∧
    (fixedNonzeroLiteralSlice M N K Y d a b).image Prod.snd =
        nonzeroReducedCollar N Y d a b ∧
    nonzeroReducedCollar N Y d a b =
        signedEquationFibers N Y d a b ∧
    (zeroFiber N a b).card = (zeroParameters N a b).card ∧
    (∀ ell ∈ Finset.Icc 1 (Y / d),
      ∀ n ∈ positiveEquationFiber N a b ell,
        a * n.1 = ell + b * n.2 ∧
        (d * a) * n.1 = d * ell + (d * b) * n.2 ∧
        n.1.gcd b = ell.gcd b ∧
        n.2.gcd a = ell.gcd a ∧
        n.1.gcd b * n.2.gcd a = ell.gcd (a * b)) ∧
    (∀ ell ∈ Finset.Icc 1 (Y / d),
      ∀ n ∈ negativeEquationFiber N a b ell,
        b * n.2 = ell + a * n.1 ∧
        (d * b) * n.2 = d * ell + (d * a) * n.1 ∧
        n.1.gcd b = ell.gcd b ∧
        n.2.gcd a = ell.gcd a ∧
        n.1.gcd b * n.2.gcd a = ell.gcd (a * b)) ∧
    signedContentEnvelope r Y d a b =
      2 * ∑ v ∈ (a * b).divisors,
        (Y / (d * v)) * tauAF r v := by
  refine ⟨card_positiveSector_eq_negativeSector M N K Y,
    image_fixedNonzeroLiteralSlice_eq_nonzeroReducedCollar
      M N K Y d a b hshortBox hshortNe hshortK,
    nonzeroReducedCollar_eq_signedEquationFibers N Y d a b hd,
    card_zeroFiber_eq_card_zeroParameters N a b hab hb, ?_, ?_,
    signedContentEnvelope_eq_divisorFloor r Y d a b ha hb⟩
  · intro ell hell n hn
    obtain ⟨hdet, hleft, hright, hproduct⟩ :=
      positiveEquationFiber_content hab hn
    exact ⟨hdet, determinant_reconstruction hdet, hleft, hright, hproduct⟩
  · intro ell hell n hn
    obtain ⟨hdet, hleft, hright, hproduct⟩ :=
      negativeEquationFiber_content hab hn
    have hreconstruct :
        (d * b) * n.2 = d * ell + (d * a) * n.1 :=
      determinant_reconstruction hdet
    exact ⟨hdet, hreconstruct, hleft, hright, hproduct⟩

end DeterminantCountWeld
