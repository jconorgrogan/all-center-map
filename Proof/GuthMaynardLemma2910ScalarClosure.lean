import GuthMaynardJutilaLemma29NineKTwo

/-!
# The deterministic regime algebra in Jutila--Heath--Brown Lemma 29.10

The analytic part of Lemma 29.10 supplies a reflection inequality, the
`k = 2` powering inequality of Lemma 29.9, a bound at a longer comparison
length, and a length-comparison inequality.  This file proves the scalar
algebra that converts those inputs into the three range bounds.

All analytic statements remain hypotheses.  In particular, nothing here
asserts the reflection formula, the prime reciprocal estimate, or the
high-range estimate.
-/

namespace GuthMaynardLemma2910ScalarClosure

noncomputable section

/-! ## Quadratic feedback -/

/-- The exact quadratic completion used when reflection and `k = 2`
powering feed back into the original moment.  This form avoids division by
`c`, so it also covers the endpoint `c = 0`.

The source application has `x = S(N)`, `y = S(M)`,
`a` equal to the diagonal term, `b` equal to the reflection loss, and
`y^2 <= c x` supplied by Lemma 29.9 with comparison length `P = N`. -/
theorem quadratic_feedback_le
    {x y a b c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hreflect : x ≤ a + b * y)
    (hpower : y ^ 2 ≤ c * x) :
    x ≤ 2 * a + b ^ 2 * c := by
  rcases hc.eq_or_lt with rfl | hcpos
  · have hyzero : y = 0 := by
      have : y ^ 2 ≤ 0 := by simpa using hpower
      nlinarith [sq_nonneg y]
    subst y
    nlinarith
  · have hyoung : 2 * b * y ≤ x + b ^ 2 * c := by
      have hsq : 0 ≤ (y - b * c) ^ 2 := sq_nonneg (y - b * c)
      have hscaled : 2 * b * c * y ≤ c * x + b ^ 2 * c ^ 2 := by
        nlinarith
      nlinarith
    nlinarith

/-- Square-root version of `quadratic_feedback_le`. -/
theorem sqrt_feedback_le
    {x a b c : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hreflect : x ≤ a + b * Real.sqrt (c * x)) :
    x ≤ 2 * a + b ^ 2 * c := by
  have hcx : 0 ≤ c * x := mul_nonneg hc hx
  apply quadratic_feedback_le (x := x) (y := Real.sqrt (c * x))
    (a := a) (b := b) (c := c) ha hc hreflect
  rw [Real.sq_sqrt hcx]

/-! ## Reflection into an already controlled range -/

/-- If powering sends the reflected moment to a comparison length whose
moment is already bounded, the reflected moment is bounded by the square
root of that known bound.  This is the scalar step in the second middle
range of Lemma 29.10. -/
theorem reflection_powering_controlled_target
    {x y z a b c d : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hreflect : x ≤ a + b * y)
    (hpower : y ^ 2 ≤ c * z)
    (htarget : z ≤ d) :
    x ≤ a + b * Real.sqrt (c * d) := by
  have hd : 0 ≤ d := hz.trans htarget
  have hcd : 0 ≤ c * d := mul_nonneg hc hd
  have hySq : y ^ 2 ≤ c * d := hpower.trans
    (mul_le_mul_of_nonneg_left htarget hc)
  have hroot : y ≤ Real.sqrt (c * d) := by
    have hsqrt0 := Real.sqrt_nonneg (c * d)
    have hsqrtSq := Real.sq_sqrt hcd
    nlinarith [sq_nonneg (y - Real.sqrt (c * d))]
  exact hreflect.trans (by
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hroot hb) a))

/-- The direct middle-range feedback in source-facing functional form. -/
theorem reflection_powering_feedback
    {I : Type*} {S : I → ℝ} {N M : I} {a b c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hreflect : S N ≤ a + b * S M)
    (hpower : (S M) ^ 2 ≤ c * S N) :
    S N ≤ 2 * a + b ^ 2 * c :=
  quadratic_feedback_le ha hc hreflect hpower

/-- The second middle-range bootstrap in source-facing functional form. -/
theorem reflection_powering_bootstrap
    {I : Type*} {S : I → ℝ} {N M P : I} {a b c d : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hSP : 0 ≤ S P)
    (hreflect : S N ≤ a + b * S M)
    (hpower : (S M) ^ 2 ≤ c * S P)
    (htarget : S P ≤ d) :
    S N ≤ a + b * Real.sqrt (c * d) :=
  reflection_powering_controlled_target hb hc hSP
    hreflect hpower htarget

/-- The low-range scalar step: length comparison transports a bound from a
chosen anchor length. -/
theorem length_comparison_to_anchor
    {x z q d : ℝ} (hq : 0 ≤ q)
    (hlength : x ≤ q * z) (hanchor : z ≤ d) :
    x ≤ q * d :=
  hlength.trans (mul_le_mul_of_nonneg_left hanchor hq)

/-! ## The complete abstract regime weld -/

/-- A source-facing four-branch presentation of Lemma 29.10's three named
ranges.  The middle range has two subranges: direct feedback (`P = N`) and
bootstrap to a length already controlled by the preceding subrange.

The conclusion is deliberately a maximum of the four literal scalar bounds.
Consequently every nonalgebraic input is visible in the hypotheses:

* `hhigh` is the high-range reflection estimate;
* `hreflectDirect` and `hpowerDirect` are (29.41) and Lemma 29.9 with `P=N`;
* `hreflectBoot`, `hpowerBoot`, and `hbootTarget` are the second middle step;
* `hlength` and `hanchor` are the low-range comparison and anchor estimate.
-/
theorem lemma2910_four_regime_closure
    {I : Type*}
    (S A B C D H Q : I → ℝ) (M P : I → I)
    (High MiddleDirect MiddleBootstrap Low : I → Prop)
    (hcover : ∀ i, High i ∨ MiddleDirect i ∨ MiddleBootstrap i ∨ Low i)
    (hSnonneg : ∀ i, 0 ≤ S i)
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hCnonneg : ∀ i, 0 ≤ C i)
    (hQnonneg : ∀ i, 0 ≤ Q i)
    (hhigh : ∀ i, High i → S i ≤ H i)
    (hreflectDirect : ∀ i, MiddleDirect i →
      S i ≤ A i + B i * S (M i))
    (hpowerDirect : ∀ i, MiddleDirect i →
      (S (M i)) ^ 2 ≤ C i * S i)
    (hreflectBoot : ∀ i, MiddleBootstrap i →
      S i ≤ A i + B i * S (M i))
    (hpowerBoot : ∀ i, MiddleBootstrap i →
      (S (M i)) ^ 2 ≤ C i * S (P i))
    (hbootTarget : ∀ i, MiddleBootstrap i → S (P i) ≤ D i)
    (hlength : ∀ i, Low i → S i ≤ Q i * S (P i))
    (hanchor : ∀ i, Low i → S (P i) ≤ D i) :
    ∀ i, S i ≤ max (H i)
      (max (2 * A i + (B i) ^ 2 * C i)
        (max (A i + B i * Real.sqrt (C i * D i)) (Q i * D i))) := by
  intro i
  rcases hcover i with hhi | hmid | hboot | hlow
  · exact (hhigh i hhi).trans (le_max_left _ _)
  · have hdirect : S i ≤ 2 * A i + (B i) ^ 2 * C i :=
      reflection_powering_feedback (S := S) (N := i) (M := M i)
        (a := A i) (b := B i) (c := C i)
        (hAnonneg i) (hCnonneg i)
        (hreflectDirect i hmid) (hpowerDirect i hmid)
    exact hdirect.trans <| le_max_of_le_right <|
      le_max_left _ _
  · have hbootBound :
        S i ≤ A i + B i * Real.sqrt (C i * D i) :=
      reflection_powering_bootstrap (S := S) (N := i) (M := M i)
        (P := P i) (a := A i) (b := B i) (c := C i) (d := D i)
        (hBnonneg i) (hCnonneg i) (hSnonneg (P i))
        (hreflectBoot i hboot)
        (hpowerBoot i hboot) (hbootTarget i hboot)
    exact hbootBound.trans <| le_max_of_le_right <|
      le_max_of_le_right <| le_max_left _ _
  · have hlowBound : S i ≤ Q i * D i :=
      length_comparison_to_anchor (hQnonneg i)
        (hlength i hlow) (hanchor i hlow)
    exact hlowBound.trans <| le_max_of_le_right <|
      le_max_of_le_right <| le_max_right _ _


/-- A square-root target bound with every cardinality factor retained. -/
theorem bootstrap_root_le
    {R M F K b c : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : b^2*c ≤ F) :
    b * Real.sqrt (c*R^2*(K*F*(R*(4*M^2)+R^2+1))) ≤
      (K+1)*F*(2*R*Real.sqrt R*M+R^2+R) := by
  have hsR := Real.sq_sqrt hR
  have hsR0 := Real.sqrt_nonneg R
  have hshape : 0 ≤ R*(4*M^2)+R^2+1 := by positivity
  have hrhs : 0 ≤ (K+1)*F*(2*R*Real.sqrt R*M+R^2+R) := by positivity
  have hroot := Real.sq_sqrt
    (show 0 ≤ c*R^2*(K*F*(R*(4*M^2)+R^2+1)) by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hbc
    (show 0 ≤ R^2*(K*F*(R*(4*M^2)+R^2+1)) by positivity)
  have hKsq : K ≤ (K+1)^2 := by nlinarith [sq_nonneg K]
  have hcard : R^2*(R*(4*M^2)+R^2+1) ≤
      (2*R*Real.sqrt R*M+R^2+R)^2 := by
    have heq : (2*R*Real.sqrt R*M)^2 = 4*R^3*M^2 := by
      simp only [mul_pow, hsR]
      ring
    have hcross : 0 ≤ (2*R*Real.sqrt R*M)*(R^2+R) := by positivity
    have hRcube : 0 ≤ R^3 := by positivity
    nlinarith only [heq, hcross, hRcube]
  have hstep := mul_le_mul_of_nonneg_left hcard (show 0 ≤ K*F^2 by positivity)
  have hstep2 := mul_le_mul_of_nonneg_right hKsq
    (show 0 ≤ F^2*(2*R*Real.sqrt R*M+R^2+R)^2 by positivity)
  have hsq : (b*Real.sqrt (c*R^2*(K*F*(R*(4*M^2)+R^2+1))))^2 ≤
      ((K+1)*F*(2*R*Real.sqrt R*M+R^2+R))^2 := by
    calc
      _ = b^2*(c*R^2*(K*F*(R*(4*M^2)+R^2+1))) := by rw [mul_pow,hroot]
      _ ≤ K*F^2*(R^2*(R*(4*M^2)+R^2+1)) := by nlinarith only [hscaled]
      _ ≤ K*F^2*(2*R*Real.sqrt R*M+R^2+R)^2 := hstep
      _ ≤ ((K+1)*F*(2*R*Real.sqrt R*M+R^2+R))^2 := by nlinarith only [hstep2]
  nlinarith only [hsq, hrhs, sq_nonneg
    (b*Real.sqrt (c*R^2*(K*F*(R*(4*M^2)+R^2+1))) +
      (K+1)*F*(2*R*Real.sqrt R*M+R^2+R))]

end

end GuthMaynardLemma2910ScalarClosure

#print axioms GuthMaynardLemma2910ScalarClosure.quadratic_feedback_le
#print axioms GuthMaynardLemma2910ScalarClosure.sqrt_feedback_le
#print axioms GuthMaynardLemma2910ScalarClosure.reflection_powering_controlled_target
#print axioms GuthMaynardLemma2910ScalarClosure.lemma2910_four_regime_closure
