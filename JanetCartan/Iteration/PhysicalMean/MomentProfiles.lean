module

public import JanetCartan.Iteration.PhysicalMean.MomentExpansion
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.PrimitiveBounds

/-!
# Reserve-preserving bounds for the sampled moment amplitudes

The coefficient products in Step 2 of
`app:ch_mean_pairs:prop:canonical-estimates` spend only their TOTAL primitive
derivative count. The positive-part exponent is not multiplied by the number
of factors. This is the profile calculation behind
`app:ch_mean_pairs:eq:raw-adjoint-moments`.

The primitive amplitude and inverse phase directions must be the actual
sampled ones. Their physical reserve profiles are separate original-data
obligations; neither a moment operator estimate nor a generated-amplitude
bound is assumed here.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels ContinuumRow

variable {n : ℕ}

/-- A primitive reserve survives all products and physical derivatives in an
actual adjoint coefficient expression. The explicit constant is independent
of the coefficient scale `T` and of the original functions
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_iteratedFDeriv_adjointExpression_le_reserve (L V a η)
    (ha : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (p : AdjointJetPoint n) (r₀ : ℕ) (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i, ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ a p.1 p.2 η) p‖ ≤
      B i * T ^ (i - r₀))
    (ds : List (InitialCarrierDerivative n))
    (hcoeff : ∀ d ∈ ds, ∀ j i, ‖iteratedFDeriv ℝ i (branchField L V d j) p‖ ≤
      B i * T ^ (i - r₀))
    (e : AdjointCoefficientExpression n) (hdirs : e.UsesDirections ds) (q : ℕ) :
    ‖iteratedFDeriv ℝ q (e.evaluate L V a η) p‖ ≤
      e.jetConstant B q * T ^ (e.degree + q - r₀) := by
  have hT₀ : 0 ≤ T := zero_le_one.trans hT
  have smooth (e : AdjointCoefficientExpression n) :=
    AdjointCoefficientExpression.contDiff_evaluate L V a η ha hfield e
  have mono (e : AdjointCoefficientExpression n) (q b : ℕ) (hb : e.degree + q ≤ b) :
      e.jetConstant B q * T ^ (e.degree + q - r₀) ≤ e.jetConstant B q * T ^ (b - r₀) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (Nat.sub_le_sub_right hb r₀))
      (e.jetConstant_nonneg B hB q)
  induction e generalizing q with
  | amplitude => simpa [AdjointCoefficientExpression.evaluate,
      AdjointCoefficientExpression.degree, AdjointCoefficientExpression.jetConstant] using hamp q
  | field d j =>
      simpa [AdjointCoefficientExpression.evaluate,
        AdjointCoefficientExpression.degree, AdjointCoefficientExpression.jetConstant] using hcoeff d hdirs j q
  | add e f he hf =>
      have he' := (he hdirs.1 q).trans (mono e q _
        (Nat.add_le_add_right (le_max_left e.degree f.degree) q))
      have hf' := (hf hdirs.2 q).trans (mono f q _
        (Nat.add_le_add_right (le_max_right e.degree f.degree) q))
      dsimp only [AdjointCoefficientExpression.evaluate]
      rw [show (fun p ↦ e.evaluate L V a η p + f.evaluate L V a η p) =
          e.evaluate L V a η + f.evaluate L V a η from rfl,
        iteratedFDeriv_add ((smooth e).of_le (by simp)) ((smooth f).of_le (by simp))]
      exact (norm_add_le _ _).trans ((add_le_add he' hf').trans_eq (by
        simp only [AdjointCoefficientExpression.jetConstant,
          AdjointCoefficientExpression.degree, add_mul]))
  | neg e he =>
      change ‖iteratedFDeriv ℝ q (-e.evaluate L V a η) p‖ ≤ _
      rw [iteratedFDeriv_neg]
      simpa only [Pi.neg_apply, norm_neg, AdjointCoefficientExpression.degree,
        AdjointCoefficientExpression.jetConstant] using he hdirs q
  | mul e f he hf =>
      apply (norm_iteratedFDeriv_mul_le (smooth e) (smooth f) p (by simp)).trans
      simp only [AdjointCoefficientExpression.jetConstant, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      calc
        _ ≤ (q.choose i : ℝ) * (e.jetConstant B i * T ^ (e.degree + i - r₀)) *
            (f.jetConstant B (q-i) * T ^ (f.degree + (q-i) - r₀)) := by
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left (he hdirs.1 i) (Nat.cast_nonneg _))
            (hf hdirs.2 (q-i)) (norm_nonneg _)
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (e.jetConstant_nonneg B hB i) (pow_nonneg hT₀ _))
        _ = ((q.choose i : ℝ) * e.jetConstant B i * f.jetConstant B (q-i)) *
            T ^ ((e.degree + i - r₀) + (f.degree + (q-i) - r₀)) := by
          rw [pow_add]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (e.jetConstant_nonneg B hB i))
              (f.jetConstant_nonneg B hB (q-i)))
          apply pow_le_pow_right₀ hT
          simp only [AdjointCoefficientExpression.degree]
          omega
  | deriv h e he =>
      have hd := norm_iteratedFDeriv_clm_apply_const
        ((smooth e).fderiv_right (by simp)).contDiffAt
        (show (q : ℕ∞ω) ≤ ∞ by simp) (c := h) (x := p)
      rw [norm_iteratedFDeriv_fderiv] at hd
      exact hd.trans ((mul_le_mul_of_nonneg_left (he hdirs (q+1)) (norm_nonneg h)).trans_eq (by
        simp [AdjointCoefficientExpression.jetConstant, AdjointCoefficientExpression.degree,
          Nat.add_assoc, Nat.add_comm 1, mul_assoc]))

/-- The finite coefficient syntax is chosen from the derivative word alone,
before any current history, sample, phase or source. -/
def adjointMomentExpressions : List (InitialCarrierDerivative n) → List (AdjointCoefficientExpression n)
  | [] => [.amplitude]
  | d :: ds => (adjointMomentExpressions ds).flatMap (fun e ↦
      e.zeroBranch d :: List.ofFn (fun j : Fin n ↦ e.firstBranch d j))

/-- Every actual amplitude has one of the PRESELECTED differential expressions.
This strengthens the primitive-expression result by recording a finite set
independent of the actual coefficients (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_fixed_expression_of_mem_adjointExpansion (L V)
    (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    ∃ e ∈ adjointMomentExpressions ds,
      e.degree + t.dataDerivatives.length ≤ ds.length ∧ e.UsesDirections ds ∧
        t.amplitude = fun z x η ↦ e.evaluate L V a η (z, x) := by
  induction ds generalizing t with
  | nil =>
      simp only [adjointDerivativeExpansion, List.mem_singleton] at ht
      subst t
      exact ⟨.amplitude, by simp [adjointMomentExpressions],
        by simp [AdjointCoefficientExpression.degree], trivial, rfl⟩
  | cons d ds ih =>
      obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨e, hes, he, hdirs, hue⟩ := ih u hu
      simp only [differentiateAdjointTerm, List.mem_cons, List.mem_ofFn] at ht
      rcases ht with rfl | ⟨j, rfl⟩
      · refine ⟨e.zeroBranch d, List.mem_flatMap.mpr ⟨e, hes, by simp⟩,
          ?_, (e.usesDirections_branches ds d hdirs).1, ?_⟩
        · have := e.degree_zeroBranch_le d
          simp only [List.length_cons]
          omega
        · dsimp only
          rw [hue]
          funext z x η
          exact (e.evaluate_zeroBranch L V a η (ha η) hfield d (z, x)).symm
      · refine ⟨e.firstBranch d j, List.mem_flatMap.mpr ⟨e, hes, by simp⟩,
          ?_, (e.usesDirections_branches ds d hdirs).2 j, ?_⟩
        · simp only [AdjointCoefficientExpression.degree_firstBranch, List.length_cons]
          omega
        · dsimp only
          rw [hue]
          funext z x η
          exact (e.evaluate_firstBranch L V a η d j (z, x)).symm

/-- Uniform finite constant for all actual moment terms; its definition uses
only the primitive profile constants and the derivative word, never the
history, sample weights, source, frequency, or coefficient scale. -/
def adjointMomentJetConstant (B : ℕ → ℝ) (ds : List (InitialCarrierDerivative n)) (q : ℕ) : ℝ :=
  ((adjointMomentExpressions ds).map (fun e ↦ e.jetConstant B q)).sum

/-- All constants in the fixed finite moment family are nonnegative. -/
theorem adjointMomentJetConstant_nonneg (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    (ds : List (InitialCarrierDerivative n)) (q : ℕ) : 0 ≤ adjointMomentJetConstant B ds q := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  exact e.jetConstant_nonneg B hB q

private theorem jetConstant_le_momentConstant (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    (ds : List (InitialCarrierDerivative n)) (q : ℕ) (e : AdjointCoefficientExpression n)
    (he : e ∈ adjointMomentExpressions ds) : e.jetConstant B q ≤ adjointMomentJetConstant B ds q := by
  have hsum (es : List (AdjointCoefficientExpression n)) :
      0 ≤ (es.map (fun e ↦ e.jetConstant B q)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    exact f.jetConstant_nonneg B hB q
  have hb (es : List (AdjointCoefficientExpression n)) :
      ∀ e ∈ es, e.jetConstant B q ≤ (es.map (fun e ↦ e.jetConstant B q)).sum := by
    induction es with
    | nil => simp
    | cons f fs ih =>
        intro e he
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.mp he with rfl | he
        · exact le_add_of_nonneg_right (hsum fs)
        · exact (ih e he).trans (le_add_of_nonneg_left (f.jetConstant_nonneg B hB q))
  exact hb _ e he

/-- The actual `q`th coefficient jets in the finite integration-by-parts
expansion have the precise reserve exponent `s-i+q-r₀`, where `i` is the
number of derivatives on the datum. The constant is fixed BEFORE all
functions and scales (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_iteratedFDeriv_adjointExpansionTerm_le_reserve
    (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q) (ds : List (InitialCarrierDerivative n))
    (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (η : Euclidean (n - 1)) (p : AdjointJetPoint n) (r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i, ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ a p.1 p.2 η) p‖ ≤ B i * T ^ (i - r₀))
    (hcoeff : ∀ d ∈ ds, ∀ j i, ‖iteratedFDeriv ℝ i (branchField L V d j) p‖ ≤ B i * T ^ (i - r₀))
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a) (q : ℕ) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointJetPoint n ↦ t.amplitude p.1 p.2 η) p‖ ≤
      adjointMomentJetConstant B ds q * T ^ (ds.length - t.dataDerivatives.length + q - r₀) := by
  obtain ⟨e, hes, he, hdirs, hte⟩ := exists_fixed_expression_of_mem_adjointExpansion L V a ha hfield ds t ht
  have heq : (fun p : AdjointJetPoint n ↦ t.amplitude p.1 p.2 η) = e.evaluate L V a η := by
    simp only [hte]
  rw [heq]
  apply (norm_iteratedFDeriv_adjointExpression_le_reserve L V a η (ha η) hfield
    p r₀ B hB hT hamp ds hcoeff e hdirs q).trans
  exact mul_le_mul (jetConstant_le_momentConstant B hB ds q e hes)
    (pow_le_pow_right₀ hT (by omega)) (pow_nonneg (zero_le_one.trans hT) _)
    (adjointMomentJetConstant_nonneg B hB ds q)

end JanetCartan.PhysicalMean
