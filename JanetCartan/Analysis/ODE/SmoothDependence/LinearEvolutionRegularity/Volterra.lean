module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.LinearEvolution.CompactExistence
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The Volterra operator on continuous curves

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, rescaling a time segment to `[0,1]` reduces
linear evolution to a Volterra equation in a Banach space of curves. The
operator is invertible without a smallness assumption on its coefficient.
-/

@[expose] public section

open Set Filter Function
open scoped Topology NNReal

namespace JanetCartan.ODE.LinearEvolutionRegularity

/-- The fixed initial time for rescaled curves (`app:lem:common-hamilton-phase`). -/
def initial : Icc (0 : ℝ) 1 := ⟨0, by simp⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration from zero on continuous curves, used for the rescaled Volterra
operator in `app:ch_regular_base:lem:buffered-interpolation`. -/
noncomputable def primitive : C(Icc (0 : ℝ) 1, F) →L[ℝ] C(Icc (0 : ℝ) 1, F) :=
  LinearMap.mkContinuous
    { toFun := fun g ↦
        ⟨fun t ↦ ∫ τ in (0 : ℝ)..t.1, CompactPicard.extend initial g τ,
          ((intervalIntegral.continuous_primitive
            (fun a b ↦ (CompactPicard.continuous_extend initial g).intervalIntegrable a b)
            0).comp continuous_subtype_val)⟩
      map_add' := by
        intro g h
        ext t
        exact intervalIntegral.integral_add
          ((CompactPicard.continuous_extend initial g).intervalIntegrable _ _)
          ((CompactPicard.continuous_extend initial h).intervalIntegrable _ _)
      map_smul' := by
        intro c g
        ext t
        exact intervalIntegral.integral_smul c _ }
    1 (by
      intro g
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
      intro t
      change ‖∫ τ in (0 : ℝ)..t.1, CompactPicard.extend initial g τ‖ ≤ ‖g‖
      apply (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun τ _ ↦ g.norm_coe_le_norm _)).trans
      rw [sub_zero, abs_of_nonneg t.2.1]
      exact mul_le_of_le_one_right (norm_nonneg _) t.2.2)

lemma primitive_apply (g : C(Icc (0 : ℝ) 1, F)) (t : Icc (0 : ℝ) 1) :
    primitive g t = ∫ τ in (0 : ℝ)..t.1, CompactPicard.extend initial g τ := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous operator curves on the unit time interval, for the linear
regularity argument of `app:lem:common-hamilton-phase`. -/
abbrev OperatorCurve (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  C(Icc (0 : ℝ) 1, E →L[ℝ] E)

noncomputable local instance : NormedAddCommGroup (OperatorCurve E) := inferInstance

noncomputable local instance : NormedSpace ℝ (OperatorCurve E) := inferInstance

/-- The Volterra operator `Y ↦ ∫ A Y`, depending continuously and linearly on
its coefficient (`app:ch_regular_base:lem:buffered-interpolation`). -/
noncomputable def volterra : OperatorCurve E →L[ℝ] OperatorCurve E →L[ℝ] OperatorCurve E :=
  ((ContinuousLinearMap.compL ℝ (OperatorCurve E) (OperatorCurve E) (OperatorCurve E))
    primitive).comp
    (ContinuousLinearMap.mul ℝ (OperatorCurve E))

lemma volterra_apply (A Y : OperatorCurve E) (t : Icc (0 : ℝ) 1) :
    volterra A Y t = ∫ τ in (0 : ℝ)..t.1,
      (CompactPicard.extend initial A τ).comp (CompactPicard.extend initial Y τ) := rfl

private lemma continuous_field (A q : OperatorCurve E) :
    ContinuousOn (uncurry (fun τ y ↦ (CompactPicard.extend initial A τ).comp
      (y + CompactPicard.extend initial q τ)))
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set (E →L[ℝ] E))) :=
  ((CompactPicard.continuous_extend initial A).comp continuous_fst |>.clm_comp
    (continuous_snd.add ((CompactPicard.continuous_extend initial q).comp continuous_fst))).continuousOn

private lemma lipschitz_field (A q : OperatorCurve E) (t : ℝ) :
    LipschitzWith ‖A‖₊ (fun y ↦ (CompactPicard.extend initial A t).comp
      (y + CompactPicard.extend initial q t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm, ← ContinuousLinearMap.comp_sub, add_sub_add_right_eq_sub,
    dist_eq_norm]
  exact ((CompactPicard.extend initial A t).opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _))

variable [CompleteSpace E]

private lemma next_eq (A q Y : OperatorCurve E) :
    CompactPicard.next initial (continuous_field A q) 0 Y = volterra A (Y + q) := by
  ext t
  rw [CompactPicard.next_apply, zero_add, volterra_apply]
  rfl

/-- `app:lem:common-hamilton-phase`: the Volterra equation is uniquely solvable
on the entire unit interval, with no bound on the size of the coefficient. -/
theorem isInvertible_id_sub_volterra (A : OperatorCurve E) :
    (ContinuousLinearMap.id ℝ (OperatorCurve E) - volterra A).IsInvertible := by
  let T := ContinuousLinearMap.id ℝ (OperatorCurve E) - volterra A
  have hsurj : Surjective T := by
    intro q
    obtain ⟨Y, hY⟩ := CompactPicard.exists_fixedPoint initial (continuous_field A q) 0
      (fun t _ ↦ lipschitz_field A q t)
    have heq : volterra A (Y + q) = Y := (next_eq A q Y).symm.trans hY
    refine ⟨Y + q, ?_⟩
    change Y + q - volterra A (Y + q) = q
    rw [heq]
    abel
  have hker : ∀ Y, T Y = 0 → Y = 0 := by
    intro Y hY
    have hfix : IsFixedPt (CompactPicard.next initial (continuous_field A 0) 0) Y := by
      rw [IsFixedPt, next_eq A 0 Y, add_zero]
      exact (sub_eq_zero.mp hY).symm
    have hzero : IsFixedPt (CompactPicard.next initial (continuous_field A 0) 0) 0 := by
      rw [IsFixedPt, next_eq A 0 0, add_zero, map_zero]
    obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop
      (‖A‖ : ℝ) |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
    have hbound := CompactPicard.dist_iterate_next_le initial (continuous_field A 0) 0
      (fun t _ ↦ lipschitz_field A 0 t) Y 0 n
    rw [hfix.iterate n, hzero.iterate n] at hbound
    simp only [initial, sub_zero, sub_self, max_eq_left zero_le_one, mul_one,
      coe_nnnorm] at hbound
    have : dist Y 0 = 0 := by nlinarith [dist_nonneg (x := Y) (y := 0)]
    exact dist_eq_zero.mp this
  have hinj : Injective T := by
    intro Y Z h
    exact sub_eq_zero.mp (hker (Y - Z) (by rw [map_sub, h, sub_self]))
  refine ⟨ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective T _ _

/-- The solution of a Volterra equation, used in the time-rescaled evolution
argument for `app:ch_regular_base:lem:buffered-interpolation`. -/
noncomputable def solve (A q : OperatorCurve E) : OperatorCurve E :=
  (ContinuousLinearMap.id ℝ (OperatorCurve E) - volterra A).inverse q

/-- `app:lem:common-hamilton-phase`: the inverse Volterra operator is smooth
in both the coefficient and the inhomogeneous term, at every finite order. -/
theorem contDiff_solve (n : ℕ) :
    ContDiff ℝ n (fun z : OperatorCurve E × OperatorCurve E ↦ solve z.1 z.2) := by
  have hT : ContDiff ℝ n (fun A : OperatorCurve E ↦
      ContinuousLinearMap.id ℝ (OperatorCurve E) - volterra A) :=
    contDiff_const.sub (volterra (E := E)).contDiff
  have hInv : ContDiff ℝ n (fun A : OperatorCurve E ↦
      (ContinuousLinearMap.id ℝ (OperatorCurve E) - volterra A).inverse) := by
    apply contDiff_iff_contDiffAt.mpr
    intro A
    exact (isInvertible_id_sub_volterra A).contDiffAt_map_inverse.comp A hT.contDiffAt
  exact (hInv.comp contDiff_fst).clm_apply contDiff_snd

/-- `app:lem:common-hamilton-phase`: the constructed inverse solves exactly
the Volterra integral equation. -/
theorem solve_eq_iff (A q Y : OperatorCurve E) :
    solve A q = Y ↔ Y = q + volterra A Y := by
  rw [solve, (isInvertible_id_sub_volterra A).inverse_apply_eq]
  change q = Y - volterra A Y ↔ Y = q + volterra A Y
  rw [eq_sub_iff_add_eq, eq_comm]


/-- `app:lem:common-hamilton-phase`: a differentiable curve satisfying the
linear ODE is exactly the solution of the associated Volterra equation.
This uses the fundamental theorem of calculus, without interchanging derivatives. -/
theorem solve_const_eq_of_hasDerivAt (A Y : OperatorCurve E)
    (y : ℝ → E →L[ℝ] E) (hy : ∀ t : Icc (0 : ℝ) 1, y t = Y t)
    (hd : ∀ t : Icc (0 : ℝ) 1, HasDerivAt y ((A t).comp (Y t)) t) :
    solve A (ContinuousMap.const _ (y 0)) = Y := by
  apply (solve_eq_iff _ _ _).mpr
  apply ContinuousMap.ext
  intro t
  change Y t = y 0 + volterra A Y t
  rw [volterra_apply]
  have hc := (CompactPicard.continuous_extend initial A).clm_comp
    (CompactPicard.continuous_extend initial Y)
  have hi : (∫ τ in (0 : ℝ)..t.1,
      (CompactPicard.extend initial A τ).comp (CompactPicard.extend initial Y τ)) =
      Y t - y 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := y) _
      (hc.intervalIntegrable _ _), hy t]
    intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := uIcc_subset_Icc (by simp) t.2 hτ
    rw [CompactPicard.extend_of_mem _ _ hτ', CompactPicard.extend_of_mem _ _ hτ']
    exact hd ⟨τ, hτ'⟩
  rw [hi]
  abel

end JanetCartan.ODE.LinearEvolutionRegularity
