module

public import JanetCartan.Analysis.ODE.SmoothDependence.Variational
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Picard iteration on a whole compact interval

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, a linear equation must be solved on every
compact subinterval of the flow domain. A globally Lipschitz vector field
admits such solutions without a short-time assumption. We use all continuous
curves, rather than curves constrained to a ball, in the Picard construction.
-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace JanetCartan.ODE

namespace CompactPicard

variable {F : Type*} [NormedAddCommGroup F]
  {a b : ℝ} (t₀ : Icc a b)

/-- Constant extension of a continuous curve beyond its compact time interval. -/
noncomputable def extend (α : C(Icc a b, F)) : ℝ → F :=
  fun t ↦ α (projIcc a b (t₀.2.1.trans t₀.2.2) t)

lemma extend_of_mem (α : C(Icc a b, F)) {t : ℝ} (ht : t ∈ Icc a b) :
    extend t₀ α t = α ⟨t, ht⟩ := by
  exact congrArg α (projIcc_of_mem _ ht)

lemma continuous_extend (α : C(Icc a b, F)) : Continuous (extend t₀ α) :=
  α.continuous.comp continuous_projIcc

variable [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → F → F}
  (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ (univ : Set F))) (x : F)

omit [CompleteSpace F] in
include hf in
lemma continuousOn_integrand (α : C(Icc a b, F)) :
    ContinuousOn (fun t ↦ f t (extend t₀ α t)) (Icc a b) :=
  _root_.ODE.continuousOn_comp hf (continuous_extend t₀ α).continuousOn
    (fun _ _ ↦ mem_univ _)

omit [CompleteSpace F] in
include hf in
lemma integrable_integrand (α : C(Icc a b, F)) (t : Icc a b) :
    IntervalIntegrable (fun τ ↦ f τ (extend t₀ α τ)) volume t₀ t :=
  ((continuousOn_integrand t₀ hf α).mono (uIcc_subset_Icc t₀.2 t.2)).intervalIntegrable

/-- Picard's map on the Banach space of all continuous curves on the interval. -/
noncomputable def next (α : C(Icc a b, F)) : C(Icc a b, F) where
  toFun t := _root_.ODE.picard f t₀ x (extend t₀ α) t
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    (HasDerivWithinAt.continuousOn (fun _ ht ↦
      _root_.ODE.hasDerivWithinAt_picard_Icc t₀.2 hf
        (continuous_extend t₀ α).continuousOn (fun _ _ ↦ mem_univ _) x ht))

lemma next_apply (α : C(Icc a b, F)) (t : Icc a b) :
    next t₀ hf x α t = x + ∫ τ in t₀.1..t.1, f τ (extend t₀ α τ) := rfl

variable {K : ℝ≥0} (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t))

include hlip in
/-- The factorial bound for iterated Picard maps, with no restriction on interval length. -/
lemma dist_iterate_next_apply_le (α β : C(Icc a b, F)) (n : ℕ) (t : Icc a b) :
    dist ((next t₀ hf x)^[n] α t) ((next t₀ hf x)^[n] β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (integrable_integrand t₀ hf _ t)
        (integrable_integrand t₀ hf _ t)]
    calc
      _ ≤ ∫ τ in uIoc t₀.1 t.1, K ^ (n + 1) * |τ - t₀| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro τ hτ
        have hτ : τ ∈ Icc a b :=
          (uIoc_subset_uIcc.trans (uIcc_subset_Icc t₀.2 t.2)) hτ
        rw [← dist_eq_norm, extend_of_mem t₀ _ hτ, extend_of_mem t₀ _ hτ]
        calc
          _ ≤ K * dist ((next t₀ hf x)^[n] α ⟨τ, hτ⟩)
              ((next t₀ hf x)^[n] β ⟨τ, hτ⟩) := (hlip τ hτ).dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |τ - t₀.1| ^ n / n ! * dist α β := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [mul_pow] using hn ⟨τ, hτ⟩
      _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

include hlip in
lemma dist_iterate_next_le (α β : C(Icc a b, F)) (n : ℕ) :
    dist ((next t₀ hf x)^[n] α) ((next t₀ hf x)^[n] β) ≤
      (K * max (b - t₀) (t₀ - a)) ^ n / n ! * dist α β := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply (dist_iterate_next_apply_le t₀ hf x hlip α β n t).trans
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have : 0 ≤ max (b - t₀) (t₀ - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity

include hlip in
lemma exists_fixedPoint : ∃ α : C(Icc a b, F), IsFixedPt (next t₀ hf x) α := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop
    (K * max (b - t₀) (t₀ - a)) |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : 0 ≤ (K * max (b - t₀) (t₀ - a)) ^ n / n ! := by
    have : 0 ≤ max (b - t₀) (t₀ - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity
  have hc : ContractingWith ⟨_, hnonneg⟩ (next t₀ hf x)^[n] :=
    ⟨hn, LipschitzWith.of_dist_le_mul (fun α β ↦ dist_iterate_next_le t₀ hf x hlip α β n)⟩
  exact ⟨_, hc.isFixedPt_fixedPoint_iterate⟩

end CompactPicard

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `app:lem:common-hamilton-phase`: a continuous, globally Lipschitz field
has a solution on an entire compact time interval, with arbitrary initial value. -/
theorem exists_solution_compact_of_lipschitzWith {a b : ℝ} (t₀ : Icc a b)
    {f : ℝ → F → F} (x : F) {K : ℝ≥0}
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ (univ : Set F)))
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t)) :
    ∃ α : ℝ → F, α t₀ = x ∧ Continuous α ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t := by
  obtain ⟨α, hα⟩ := CompactPicard.exists_fixedPoint t₀ hf x hlip
  have heq (t : ℝ) (ht : t ∈ Icc a b) :
      CompactPicard.extend t₀ α t = _root_.ODE.picard f t₀ x
        (CompactPicard.extend t₀ α) t := by
    rw [CompactPicard.extend_of_mem t₀ α ht]
    exact (congrArg (fun β : C(Icc a b, F) ↦ β ⟨t, ht⟩) hα).symm
  refine ⟨CompactPicard.extend t₀ α, ?_, CompactPicard.continuous_extend t₀ α, ?_⟩
  · rw [heq t₀ t₀.2, _root_.ODE.picard_apply₀]
  · intro t ht
    exact (_root_.ODE.hasDerivWithinAt_picard_Icc t₀.2 hf
      (CompactPicard.continuous_extend t₀ α).continuousOn
      (fun _ _ ↦ mem_univ _) x ht).congr_of_mem heq ht

end JanetCartan.ODE
