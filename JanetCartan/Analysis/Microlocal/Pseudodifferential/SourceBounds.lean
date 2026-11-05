module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.FullOperator
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointBounds

/-!
# Source derivative budgets from symbol bounds

For `app:ch_regular_base:thm:actual-calculus`, finite pointwise bounds for the
source derivatives of a symbol give the integral budgets used to construct its
actual operator. The Leibniz sum retains every derivative of the source test.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.Pseudodifferential
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: the finite Leibniz integral budget
of a source test and a sequence of pointwise amplitude derivative bounds. -/
def sourceLeibnizBudget (u : V → ℂ) (M : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * (∫ y, ‖iteratedFDeriv ℝ i u y‖) * M (j - i)

/-- `app:ch_regular_base:thm:actual-calculus`: primitive pointwise source
bounds imply the finite integral budget; no estimate for the product is assumed. -/
theorem sourceDerivativeMass_smul_le (u : V → ℂ) (f : V → F) (n : ℕ)
    (hu : ContDiff ℝ n u) (huc : HasCompactSupport u) (hf : ContDiff ℝ n f)
    (M : ℕ → ℝ) (hM : ∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ M j) :
    sourceDerivativeMass (fun y ↦ u y • f y) n ≤ sourceLeibnizBudget u M n := by
  unfold sourceDerivativeMass sourceLeibnizBudget
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      Integrable (fun y ↦ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i u y‖ * M (j - i)) := by
    have hin : i ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hjn
    exact (((hu.continuous_iteratedFDeriv (by exact_mod_cast hin)).integrable_of_hasCompactSupport
      (huc.iteratedFDeriv i)).norm.const_mul _).mul_const _
  calc
    _ ≤ ∫ y, ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i u y‖ * M (j - i) := by
      apply integral_mono
      · exact (((hu.smul hf).continuous_iteratedFDeriv (by exact_mod_cast hjn)).integrable_of_hasCompactSupport
          (huc.smul_right.iteratedFDeriv j)).norm
      · exact integrable_finsetSum _ hterm
      · intro y
        apply (norm_iteratedFDeriv_smul_le hu hf y (by exact_mod_cast hjn)).trans
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hM (j - i) ((Nat.sub_le _ _).trans hjn) y)
          (by positivity)
    _ = _ := by
      rw [integral_finsetSum _ hterm]
      simp_rw [integral_mul_const, integral_const_mul]

/-- `app:ch_regular_base:thm:actual-calculus`: a common frequency-growth
factor passes through the finite source-test budget exactly. -/
theorem sourceLeibnizBudget_mul (u : V → ℂ) (M : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    sourceLeibnizBudget u (fun j ↦ M j * a) n = sourceLeibnizBudget u M n * a := by
  simp only [sourceLeibnizBudget, Finset.sum_mul, mul_assoc]

/-- `app:ch_regular_base:thm:actual-calculus`: pointwise polynomial symbol
bounds through source order `m + dim V + 1` give absolute convergence of the
source-first frequency integral. -/
theorem integrable_sourceAmplitudeTransform_of_sourceSymbolBounds
    (c : V → V → V → F) (u : V → ℂ) (x : V) (m : ℕ)
    (hc : Continuous (fun p : V × V ↦ c x p.2 p.1))
    (hu : ContDiff ℝ (m + Module.finrank ℝ V + 1) u) (huc : HasCompactSupport u)
    (hs : ∀ ξ, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun y ↦ c x y ξ))
    (M : ℕ → ℝ) (hM : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ c x z ξ) y‖ ≤ M j * (1 + ‖ξ‖) ^ m) :
    Integrable (sourceAmplitudeTransform c u x) := by
  apply integrable_sourceFourier_of_compact_derivativeMass (fun ξ y ↦ u y • c x y ξ)
    ((hu.continuous.comp continuous_snd).smul hc) m _ (Nat.lt_succ_self _)
    (fun ξ ↦ hu.smul (hs ξ)) (fun _ ↦ huc.smul_right)
    (sourceLeibnizBudget u M (m + Module.finrank ℝ V + 1))
  intro ξ
  exact (sourceDerivativeMass_smul_le u _ _ hu huc (hs ξ)
    (fun j ↦ M j * (1 + ‖ξ‖) ^ m) (fun j hj y ↦ hM j hj y ξ)).trans_eq
      (sourceLeibnizBudget_mul u M _ _)


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: restricting joint derivatives
to the source coordinate costs no extra derivative and has norm at most one. -/
theorem norm_iteratedFDeriv_source_le_joint
    (c : V → V → V → F)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (x y ξ : V) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z ↦ c x z ξ) y‖ ≤
      ‖iteratedFDeriv ℝ n (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ := by
  let f : V × V × V → F := fun p ↦ c p.1 p.2.1 p.2.2
  let a : V × V × V := (x, 0, ξ)
  have hf : ContDiff ℝ ∞ (fun p ↦ f (a + p)) := hc.comp (contDiff_const.add contDiff_id)
  have h := norm_iteratedFDeriv_comp_linear_le (sourceCoordinateInclusion (V := V))
    (fun p ↦ f (a + p)) hf n y
  have hpow : ‖sourceCoordinateInclusion (V := V)‖ ^ n ≤ 1 :=
    pow_le_one₀ (norm_nonneg (sourceCoordinateInclusion (V := V))) norm_sourceCoordinateInclusion_le
  have hh := h.trans (mul_le_of_le_one_right (norm_nonneg _) hpow)
  simp only [iteratedFDeriv_comp_add_left'] at hh
  simpa only [Function.comp_def, a, f,
    sourceCoordinateInclusion, ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.id_apply, Prod.mk_add_mk, add_zero, zero_add] using hh


/-- `app:ch_regular_base:thm:actual-calculus`: joint smoothness and compact
source tests discharge all regularity inputs to the derivative-mass criterion. -/
theorem integrable_sourceAmplitudeTransform_of_joint_derivativeMass
    (c : V → V → V → F) (u : V → ℂ) (x : V) (m : ℕ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hu : ContDiff ℝ (m + Module.finrank ℝ V + 1) u) (huc : HasCompactSupport u)
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • c x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ A * (1 + ‖ξ‖) ^ m) :
    Integrable (sourceAmplitudeTransform c u x) := by
  apply integrable_sourceFourier_of_compact_derivativeMass (fun ξ y ↦ u y • c x y ξ)
    _ m _ (Nat.lt_succ_self _) _ (fun _ ↦ huc.smul_right) A hA
  · exact (hu.continuous.comp continuous_snd).smul
      (hc.continuous.comp (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop))
  · intro ξ
    exact hu.smul ((hc.comp (f := fun y : V ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp))

end JanetCartan.Pseudodifferential
