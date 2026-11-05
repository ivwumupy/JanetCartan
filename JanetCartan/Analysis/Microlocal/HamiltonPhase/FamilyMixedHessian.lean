module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FamilyConstruction

/-!
# Comparing mixed Hamilton derivatives across symbols

A uniform mixed-Hessian gap for the actual common projection charts in
`app:lem:common-hamilton-phase`. The mixed derivative comparison is deduced
from the projection derivatives and the canonical pairing, with the product
norm on canonical coordinates. The resulting value comparison and integral
derivative formula construct one buffered inverse domain for all symbols and
both physical endpoints in `app:ch_regular_base:eq:averaged-gradient`.
-/

@[expose] public noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace NNReal

namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

namespace ProjectionChart
variable {H H₀ : HomogeneousSymbol E} {Φ : HamiltonFlow H U} {Φ₀ : HamiltonFlow H₀ U}
  (C : ProjectionChart Φ) (C₀ : ProjectionChart Φ₀)

/-- Physical derivative of the full inverse lift, used to transfer projection
`C¹` estimates to `S_{xη}` in `app:lem:common-hamilton-phase`. -/
def liftPositionDerivative (z : E × (ℝ × U)) : E →L[ℝ] ℝ × InitialData U :=
  ((ContinuousLinearMap.fst ℝ ℝ U).comp (C.coordinatePositionDerivative z)).prod
    (((ContinuousLinearMap.snd ℝ ℝ U).comp (C.coordinatePositionDerivative z)).prod 0)

/-- Differentiate the actual inverse identity with canonical coordinates fixed
(`app:lem:common-hamilton-phase`). -/
theorem projection_comp_liftPositionDerivative {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    (fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z)).comp
      (C.liftPositionDerivative z) = ContinuousLinearMap.inl ℝ E (ℝ × U) := by
  have hg : HasFDerivAt (fun x ↦ chartLift C.coordinates (x, z.2))
      (C.liftPositionDerivative z) z.1 :=
    (C.hasFDerivAt_coordinates_position hz).fst.prodMk
      ((C.hasFDerivAt_coordinates_position hz).snd.prodMk (hasFDerivAt_const z.2 z.1))
  have hf := (Φ.hasFDerivAt_augmentedProjection
    (C.source_admissible _ (C.maps_to_source _ hz))).differentiableAt.hasFDerivAt
  have he : (fun x ↦ Φ.augmentedProjection (chartLift C.coordinates (x, z.2))) =ᶠ[𝓝 z.1]
      (fun x ↦ (x, z.2)) := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (C.isOpen_target.mem_nhds hz)
    filter_upwards [hn] with x hx
    exact Prod.ext (C.right_inverse (x, z.2) hx) rfl
  exact ((hf.comp z.1 hg).congr_of_eventuallyEq he.symm).unique
    ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))

private theorem norm_le_of_projection_gap
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (P : (ℝ × InitialData U) →L[ℝ] (E × (ℝ × U)))
    (hgap : ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp P - ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
    (v : ℝ × InitialData U) : ‖v‖ ≤ 2 * ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ * ‖P v‖ := by
  have h₁ := (ContinuousLinearMap.le_opNorm
    ((A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp P - ContinuousLinearMap.id ℝ _) v).trans
      (mul_le_mul_of_nonneg_right hgap (norm_nonneg v))
  have h₂ := norm_sub_le (A.symm (P v)) (A.symm (P v) - v)
  have h₃ := (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).le_opNorm (P v)
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply] at h₁
  rw [sub_sub_cancel] at h₂
  change ‖A.symm (P v)‖ ≤ _ at h₃
  linarith

/-- The normalized projection half gap bounds the physical inverse derivative.
This is an input to the family mixed-Hessian estimate of
`app:lem:common-hamilton-phase`. -/
theorem norm_liftPositionDerivative_le
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    {z : E × (ℝ × U)} (hz : z ∈ C.target)
    (hgap : ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
      (fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z)) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) :
    ‖C.liftPositionDerivative z‖ ≤ 2 * ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he := congrArg (fun L : E →L[ℝ] (E × (ℝ × U)) ↦ L v)
    (C.projection_comp_liftPositionDerivative hz)
  have hn := norm_le_of_projection_gap A _ hgap (C.liftPositionDerivative z v)
  change fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z)
    (C.liftPositionDerivative z v) = (v, 0) at he
  rw [he] at hn
  simpa using hn

/-- Compare actual inverse physical derivatives at a common target point from
projection derivatives at their respective inverse lifts. No inverse-derivative
closeness is assumed (`app:lem:common-hamilton-phase`). -/
theorem norm_coordinatePositionDerivative_sub_le
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    {z : E × (ℝ × U)} (hz : z ∈ C.target) (hz₀ : z ∈ C₀.target)
    (hgap : ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
      (fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z)) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
    (hgap₀ : ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
      (fderiv ℝ Φ₀.augmentedProjection (chartLift C₀.coordinates z)) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) :
    ‖C.coordinatePositionDerivative z - C₀.coordinatePositionDerivative z‖ ≤
      4 * ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ ^ 2 *
        ‖fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z) -
          fderiv ℝ Φ₀.augmentedProjection (chartLift C₀.coordinates z)‖ := by
  let P := fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z)
  let P₀ := fderiv ℝ Φ₀.augmentedProjection (chartLift C₀.coordinates z)
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hb := C₀.norm_liftPositionDerivative_le A hz₀ hgap₀
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : P ((C.liftPositionDerivative z - C₀.liftPositionDerivative z) v) =
      (P₀ - P) (C₀.liftPositionDerivative z v) := by
    have h₁ := congrArg (fun L : E →L[ℝ] (E × (ℝ × U)) ↦ L v)
      (C.projection_comp_liftPositionDerivative hz)
    have h₀ := congrArg (fun L : E →L[ℝ] (E × (ℝ × U)) ↦ L v)
      (C₀.projection_comp_liftPositionDerivative hz₀)
    change P (C.liftPositionDerivative z v) = (v, 0) at h₁
    change P₀ (C₀.liftPositionDerivative z v) = (v, 0) at h₀
    simp only [sub_apply, map_sub, h₁, h₀]
  have hn := norm_le_of_projection_gap A P hgap
    ((C.liftPositionDerivative z - C₀.liftPositionDerivative z) v)
  rw [he] at hn
  have hv : ‖C₀.liftPositionDerivative z v‖ ≤ (2 * N) * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg v))
  have hp : ‖(P₀ - P) (C₀.liftPositionDerivative z v)‖ ≤
      ‖P - P₀‖ * ((2 * N) * ‖v‖) := by
    calc
      _ ≤ ‖P₀ - P‖ * ‖C₀.liftPositionDerivative z v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by rw [norm_sub_rev P₀ P]; exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
  have heN : ‖(C.liftPositionDerivative z - C₀.liftPositionDerivative z) v‖ =
      ‖(C.coordinatePositionDerivative z - C₀.coordinatePositionDerivative z) v‖ := by
    simp [liftPositionDerivative, Prod.norm_def]
  rw [heN] at hn
  have hh := hn.trans (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * N))
  convert hh using 1
  dsimp [N, P, P₀]
  ring

private theorem norm_canonicalCovector_apply_le (q η : ℝ × U) :
    ‖canonicalCovector q η‖ ≤ 2 * ‖q‖ * ‖η‖ := by
  calc
    _ ≤ ‖q.1 * η.1‖ + ‖⟪q.2, η.2⟫_ℝ‖ := norm_add_le _ _
    _ ≤ ‖q.1‖ * ‖η.1‖ + ‖q.2‖ * ‖η.2‖ := by
      rw [norm_mul]; exact add_le_add le_rfl (norm_inner_le_norm _ _)
    _ ≤ ‖q‖ * ‖η‖ + ‖q‖ * ‖η‖ := add_le_add
      (mul_le_mul (norm_fst_le q) (norm_fst_le η) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (norm_snd_le q) (norm_snd_le η) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- The canonical pairing transfers inverse-derivative comparison to the actual
mixed phase derivative, with the factor two required by the split maximum norm
(`app:lem:common-hamilton-phase`). -/
theorem norm_mixedMomentumDerivative_sub_le [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    (hp₀ : ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters))
    (hC₀ : ContDiffOn ℝ ∞ C₀.coordinates C₀.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) (hz₀ : z ∈ C₀.target) :
    ‖C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z‖ ≤
      2 * ‖C.coordinatePositionDerivative z - C₀.coordinatePositionDerivative z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro η
  let w := (C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z) η
  have he : ⟪w, w⟫_ℝ = canonicalCovector
      ((C.coordinatePositionDerivative z - C₀.coordinatePositionDerivative z) w) η := by
    dsimp [w]
    rw [sub_apply, inner_sub_left,
      C.mixedMomentumDerivative_pairing hp hC hz,
      C₀.mixedMomentumDerivative_pairing hp₀ hC₀ hz₀]
    simp [canonicalCovector_apply, sub_mul, inner_sub_left]
    ring
  have hn := norm_canonicalCovector_apply_le
    ((C.coordinatePositionDerivative z - C₀.coordinatePositionDerivative z) w) η
  rw [← he, real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _)] at hn
  have hd := (C.coordinatePositionDerivative z - C₀.coordinatePositionDerivative z).le_opNorm w
  have hh := hn.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)) (norm_nonneg η))
  change ‖w‖ ≤ _
  by_cases hw : ‖w‖ = 0
  · rw [hw]; positivity
  · have hw' := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    nlinarith

/-- Projection `C¹` control, including the shift of the inverse lift, gives a
quantitative mixed-Hessian comparison (`app:lem:common-hamilton-phase`). In the
common symbol construction, `hclose` is supplied by
`exists_common_buffered_symbol_charts`; smoothness of the reference projection
supplies `hLip` on a smaller closed source ball. -/
theorem norm_mixedMomentumDerivative_sub_le_of_projection_C1_close [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    (hp₀ : ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters))
    (hC₀ : ContDiffOn ℝ ∞ C₀.coordinates C₀.target)
    {D : Set (ℝ × InitialData U)} (hD : Convex ℝ D)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hadm : D ⊆ Φ.time ×ˢ Φ.parameters)
    (hgap : ∀ q ∈ D, ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
      (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
    (hgap₀ : ∀ q ∈ D, ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
      (fderiv ℝ Φ₀.augmentedProjection q) - ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
    {L : ℝ≥0} (hLip : LipschitzOnWith L (fderiv ℝ Φ₀.augmentedProjection) D)
    {ε : ℝ} (hclose : ∀ q ∈ D,
      ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤ ε ∧
      ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤ ε)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) (hz₀ : z ∈ C₀.target)
    (hlift : chartLift C.coordinates z ∈ D) (hlift₀ : chartLift C₀.coordinates z ∈ D) :
    let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
    ‖C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z‖ ≤
      8 * N ^ 2 * (1 + 2 * N * L) * ε := by
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  have hc := C.norm_coordinates_sub_le_of_projection_close C₀ hD A hadm hgap
    (fun q hq ↦ (hclose q hq).1) hz hz₀ hlift hlift₀
  have he : ‖chartLift C.coordinates z - chartLift C₀.coordinates z‖ =
      ‖C.coordinates z - C₀.coordinates z‖ := by simp [chartLift, Prod.norm_def]
  have hL : ‖fderiv ℝ Φ₀.augmentedProjection (chartLift C.coordinates z) -
      fderiv ℝ Φ₀.augmentedProjection (chartLift C₀.coordinates z)‖ ≤
        L * (2 * N * ε) := by
    have hh := hLip.dist_le_mul _ hlift _ hlift₀
    rw [dist_eq_norm, dist_eq_norm, he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hc L.coe_nonneg)
  have hd : ‖fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z) -
      fderiv ℝ Φ₀.augmentedProjection (chartLift C₀.coordinates z)‖ ≤
        (1 + 2 * N * L) * ε := by
    have hh := norm_sub_le_norm_sub_add_norm_sub
      (fderiv ℝ Φ.augmentedProjection (chartLift C.coordinates z))
      (fderiv ℝ Φ₀.augmentedProjection (chartLift C.coordinates z))
      (fderiv ℝ Φ₀.augmentedProjection (chartLift C₀.coordinates z))
    nlinarith [(hclose _ hlift).2]
  have hi := C.norm_coordinatePositionDerivative_sub_le C₀ A hz hz₀
    (hgap _ hlift) (hgap₀ _ hlift₀)
  have hm := C.norm_mixedMomentumDerivative_sub_le C₀ hp hC hp₀ hC₀ hz hz₀
  have hh := hi.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  change _ ≤ 8 * N ^ 2 * (1 + 2 * N * L) * ε
  change _ ≤ 4 * N ^ 2 * ((1 + 2 * N * L) * ε) at hh
  linarith

/-- The phase formula identifies momentum with the mixed derivative applied to
the canonical covector. This converts the family mixed comparison to a value
comparison for `app:ch_regular_base:eq:averaged-gradient`. -/
theorem chartMomentum_eq_mixedMomentumDerivative_apply [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    C.chartMomentum z = C.mixedMomentumDerivative z z.2 := by
  have hd := C.hasFDerivAt_coordinates_position hz
  have hf := (hd.fst.const_mul z.2.1).add (hd.snd.inner ℝ (hasFDerivAt_const z.2.2 z.1))
  have hg := (C.hasFDerivAt_phase hz).comp
    (g := phase C.coordinates) (f := fun x ↦ (x, z.2)) z.1
    ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))
  have he := hf.unique hg
  apply ext_inner_right ℝ
  intro v
  rw [C.mixedMomentumDerivative_pairing hp hC hz]
  have hv := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) he
  simpa [phaseDifferential_apply, canonicalCovector_apply, chartMomentum,
    add_comm, mul_comm] using hv.symm

/-- Mixed-Hessian comparison controls the values of the actual averaged
Hamilton gradients on a common physical segment. This estimate supplies the
value hypothesis of `common_buffered_inverse_domains`, rather than assuming a
common inverse domain (`app:ch_regular_base:eq:averaged-gradient`). -/
theorem norm_averagedPhaseGradient_sub_le [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    (hp₀ : ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters))
    (hC₀ : ContDiffOn ℝ ∞ C₀.coordinates C₀.target)
    {x y : E} {η : ℝ × U}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (y + t • (x - y), η) ∈ C.target)
    (hseg₀ : ∀ t ∈ Icc (0 : ℝ) 1, (y + t • (x - y), η) ∈ C₀.target)
    {ε : ℝ} (hclose : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖C.mixedMomentumDerivative (y + t • (x - y), η) -
        C₀.mixedMomentumDerivative (y + t • (x - y), η)‖ ≤ ε) :
    ‖averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y -
      averagedPhaseGradient (fun η x ↦ phase C₀.coordinates (x, η)) η x y‖ ≤ ε * ‖η‖ := by
  have hc : ContinuousOn (fun t : ℝ ↦ C.chartMomentum (y + t • (x - y), η)) (Icc 0 1) :=
    (C.contDiffOn_chartMomentum hp hC).continuousOn.comp (by fun_prop) hseg
  have hc₀ : ContinuousOn (fun t : ℝ ↦ C₀.chartMomentum (y + t • (x - y), η)) (Icc 0 1) :=
    (C₀.contDiffOn_chartMomentum hp₀ hC₀).continuousOn.comp (by fun_prop) hseg₀
  rw [C.averagedPhaseGradient_eq_integral_chartMomentum hseg,
    C₀.averagedPhaseGradient_eq_integral_chartMomentum hseg₀,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc zero_le_one)
      (hc₀.intervalIntegrable_of_Icc zero_le_one)]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
    (by simp : (ε * ‖η‖) * |(1 : ℝ) - 0| = ε * ‖η‖)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using uIoc_subset_uIcc ht
  rw [C.chartMomentum_eq_mixedMomentumDerivative_apply hp hC (hseg t ht'),
    C₀.chartMomentum_eq_mixedMomentumDerivative_apply hp₀ hC₀ (hseg₀ t ht')]
  exact (ContinuousLinearMap.le_opNorm
    (C.mixedMomentumDerivative (y + t • (x - y), η) -
      C₀.mixedMomentumDerivative (y + t • (x - y), η)) η).trans
    (mul_le_mul_of_nonneg_right (hclose t ht') (norm_nonneg η))

/-- The integral derivative formula preserves the sharper family gap needed by
`exists_commonBufferedAveragedGradient` (`app:ch_regular_base:eq:averaged-gradient`). -/
private theorem averagedPhaseGradient_derivative_gap_of_bound [CompleteSpace E] [FiniteDimensional ℝ U]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {V : Set (ℝ × U)} (hV : IsOpen V) {x y : E}
    (hseg : ∀ η ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C.target)
    (A : (ℝ × U) ≃L[ℝ] E) {c : ℝ} {η : ℝ × U} (hη : η ∈ V)
    (hgap : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
        (C.mixedMomentumDerivative (y + t • (x - y), η)) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ c) :
    ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (fderiv ℝ (fun η ↦ averagedPhaseGradient
        (fun η x ↦ phase C.coordinates (x, η)) η x y) η) -
      ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ c := by
  let : NormedSpace ℝ (ℝ × U) := inferInstance
  let : NormedAddCommGroup ((ℝ × U) →L[ℝ] E) := inferInstance
  let : NormedAddCommGroup ((ℝ × U) →L[ℝ] (ℝ × U)) := inferInstance
  rw [(C.hasFDerivAt_averagedPhaseGradient hp hC hV hseg hη).fderiv]
  have hc : ContinuousOn (fun t : ℝ ↦ C.mixedMomentumDerivative
      (y + t • (x - y), η)) (Icc 0 1) :=
    (C.continuousOn_mixedMomentumDerivative hp hC).comp (by fun_prop) (hseg η hη)
  let L := (ContinuousLinearMap.compL ℝ (ℝ × U) E (ℝ × U))
    (A.symm : E →L[ℝ] (ℝ × U))
  have hi : IntervalIntegrable (fun t : ℝ ↦ C.mixedMomentumDerivative
      (y + t • (x - y), η)) volume 0 1 := hc.intervalIntegrable_of_Icc zero_le_one
  change ‖L (∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative
    (y + t • (x - y), η)) - ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ _
  have hL : (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
      (y + t • (x - y), η))) = L (∫ t in (0 : ℝ)..1,
        C.mixedMomentumDerivative (y + t • (x - y), η)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) L hi
  rw [← hL]
  have hiL : IntervalIntegrable (fun t ↦ L (C.mixedMomentumDerivative
      (y + t • (x - y), η))) volume 0 1 :=
    ⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩
  have he : (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
      (y + t • (x - y), η)) - ContinuousLinearMap.id ℝ (ℝ × U)) =
      (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
        (y + t • (x - y), η))) - ContinuousLinearMap.id ℝ (ℝ × U) := by
    rw [intervalIntegral.integral_sub hiL intervalIntegrable_const]
    simp
  rw [← he]
  simpa [L] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := c)
    (fun t ht ↦ hgap t (by simpa using uIoc_subset_uIcc ht))

end ProjectionChart
variable [CompleteSpace E] [CompleteSpace U]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]

/-- Actual common buffered charts have uniformly close mixed derivatives for a
scalar `C³` neighborhood (`app:lem:common-hamilton-phase`). All constants and the
reference chart are chosen before the perturbed symbol. This quantitative
comparison is the input to the common mixed gap and averaged-gradient domains. -/
theorem exists_commonBufferedMixedComparison
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀)
      (r b δ K : ℝ) (V : Set (E × (ℝ × U))),
      0 < r ∧ 0 < b ∧ 0 < δ ∧ 0 < K ∧
      IsOpen V ∧ IsCompact (closure V) ∧ (j s₀.1, s₀.2) ∈ V ∧
      C₀.target = V ∧
      ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters) ∧
      ContDiffOn ℝ ∞ C₀.coordinates V ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          C.target = V ∧
          C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          ∀ z ∈ V, ‖C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z‖ ≤
            K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨Ψ₀, A, r, b, δ, B, V, hr, hb, hδ, hB, hV, hVc, hzV, hadm, hfamily⟩ :=
    exists_common_buffered_symbol_charts H₀ hD hDH₀ hH₀ j ν horth hspan
      hR hRD henergy htrans
  have hzero : cNorm (closedBall z₀ R) 3 (fun z ↦ H₀.h z - H₀.h z) = 0 := by
    simp only [sub_self]; exact cNorm_zero _ _
  obtain ⟨Φ₀, C₀, ht₀, hp₀, _, hx₀, hξ₀, _, hC₀t, _, hbuf₀, hC₀,
    _, _, _, hgap₀, hclose₀⟩ := hfamily H₀ hDH₀ hH₀ (by rw [hzero]; exact hδ.le)
  have hadm₀ : closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ₀.time ×ˢ Φ₀.parameters := by
    simpa only [ht₀, hp₀] using hadm
  have hsub : closedBall ((0 : ℝ), s₀) (2 * r) ⊆ ball ((0 : ℝ), s₀) (3 * r) :=
    closedBall_subset_ball (by linarith)
  have hP₀ : ContDiffOn ℝ ∞ Φ₀.augmentedProjection (Φ₀.time ×ˢ Φ₀.parameters) :=
    hx₀.prodMk contDiff_snd.snd.contDiffOn
  have hDP₀ := hP₀.fderiv_of_isOpen (Φ₀.isOpen_time.prod Φ₀.isOpen_parameters)
    (m := ∞) (by simp)
  obtain ⟨L, hL⟩ := (hDP₀.mono (hsub.trans (subset_closure.trans hadm₀))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  let K := 8 * N ^ 2 * (1 + 2 * N * L) * B + 1
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have heq₀ (q) (hq : q ∈ ball ((0 : ℝ), s₀) (3 * r)) :
      Φ₀.augmentedProjection q = Ψ₀.augmentedProjection q ∧
      fderiv ℝ Φ₀.augmentedProjection q = fderiv ℝ Ψ₀.augmentedProjection q := by
    have hh := hclose₀ q hq
    rw [hzero, mul_zero] at hh
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh.1 (norm_nonneg _))),
      sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh.2
        (norm_nonneg (fderiv ℝ Φ₀.augmentedProjection q - fderiv ℝ Ψ₀.augmentedProjection q))))⟩
  refine ⟨Φ₀, C₀, r, b, δ, K, V, hr, hb, hδ, hK, hV, hVc, hzV, hC₀t, hξ₀, hC₀, ?_⟩
  intro H hDH hH hsmall
  obtain ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hbuf, hC,
    hinner, houter, hpre, hgap, hclose⟩ := hfamily H hDH hH hsmall
  have hadm' : closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters := by
    simpa only [ht, hp] using hadm
  have hclose' (q) (hq : q ∈ closedBall ((0 : ℝ), s₀) (2 * r)) :
      ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤
        B * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) ∧
      ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤
        B * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) := by
    rw [(heq₀ q (hsub hq)).1, (heq₀ q (hsub hq)).2]
    exact hclose q (hsub hq)
  refine ⟨Φ, C, ht.trans ht₀.symm, hp.trans hp₀.symm, hj, hx, hξ, hrange,
    hCt, hCs, hbuf, hadm', hC, hinner, houter, hpre, ?_⟩
  intro z hz
  have hzC : z ∈ C.target := hCt.symm ▸ hz
  have hzC₀ : z ∈ C₀.target := hC₀t.symm ▸ hz
  have hh := C.norm_mixedMomentumDerivative_sub_le_of_projection_C1_close C₀
    hξ (hCt.symm ▸ hC) hξ₀ (hC₀t.symm ▸ hC₀) (convex_closedBall _ _) A
    (hsub.trans (subset_closure.trans hadm'))
    (fun q hq ↦ hgap q (hsub hq)) (fun q hq ↦ hgap₀ q (hsub hq)) hL hclose'
    hzC hzC₀ (ball_subset_closedBall (hbuf (C.maps_to_source z hzC)))
    (ball_subset_closedBall (hbuf₀ (C₀.maps_to_source z hzC₀)))
  have hn := CompositionBounds.cNorm_nonneg (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)
  change _ ≤ 8 * N ^ 2 * (1 + 2 * N * L) * (B * _) at hh
  dsimp [K]
  nlinarith

/-- A scalar-symbol `C³` neighborhood has one mixed-Hessian equivalence and
one physical/canonical box, chosen before the symbol
(`app:lem:common-hamilton-phase`). The projection charts and all their buffers
are the actual charts of `exists_common_buffered_symbol_charts`. -/
theorem exists_commonBufferedMixedGap
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀)
      (A : (ℝ × U) ≃L[ℝ] E) (r b ρ δ K : ℝ) (V : Set (E × (ℝ × U))),
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < δ ∧ 0 < K ∧
      IsOpen V ∧ IsCompact (closure V) ∧
      closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * ρ) ⊆ V ∧
      C₀.target = V ∧
      ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters) ∧
      ContDiffOn ℝ ∞ C₀.coordinates V ∧
      (A : (ℝ × U) →L[ℝ] E) = C₀.mixedMomentumDerivative (j s₀.1, s₀.2) ∧
      (∀ z ∈ closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * ρ),
        ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C₀.mixedMomentumDerivative z) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 16) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          C.target = V ∧
          C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ z ∈ V, ‖C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z‖ ≤
            K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)) ∧
          ∀ z ∈ closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * ρ),
            ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative z) -
              ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8 := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨Φ₀, C₀, r, b, δ, K, V, hr, hb, hδ, hK, hV, hVc, hzV,
    hCt₀, hp₀, hC₀, hfamily⟩ := exists_commonBufferedMixedComparison
      H₀ hD hDH₀ hH₀ j ν horth hspan hR hRD henergy htrans
  have hzC₀ : (j s₀.1, s₀.2) ∈ C₀.target := hCt₀.symm ▸ hzV
  obtain ⟨A, hA⟩ := C₀.exists_mixedMomentumEquiv hp₀ (hCt₀.symm ▸ hC₀) hzC₀
  have hc := (C₀.continuousOn_mixedMomentumDerivative hp₀ (hCt₀.symm ▸ hC₀)).continuousAt
    (C₀.isOpen_target.mem_nhds hzC₀)
  have hn : ContinuousAt (fun z ↦ ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (C₀.mixedMomentumDerivative z) - ContinuousLinearMap.id ℝ (ℝ × U)‖)
      (j s₀.1, s₀.2) := ((continuousAt_const.clm_comp hc).sub continuousAt_const).norm
  have he : (A.symm : E →L[ℝ] (ℝ × U)).comp
      (C₀.mixedMomentumDerivative (j s₀.1, s₀.2)) = ContinuousLinearMap.id ℝ (ℝ × U) := by
    rw [← hA]
    apply ContinuousLinearMap.ext
    intro η
    exact A.symm_apply_apply η
  have hnear := hn.eventually (gt_mem_nhds (show ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (C₀.mixedMomentumDerivative (j s₀.1, s₀.2)) - ContinuousLinearMap.id ℝ (ℝ × U)‖ <
        (1 / 16 : ℝ) by
          rw [he, sub_self]
          rw [norm_zero (E := ((ℝ × U) →L[ℝ] (ℝ × U)))]
          norm_num))
  have htarget : ∀ᶠ z in 𝓝 (j s₀.1, s₀.2), z ∈ V := hV.mem_nhds hzV
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (htarget.and hnear)
  have hbox : ∀ z ∈ closedBall (j s₀.1) (3 * (ε / 4)) ×ˢ closedBall s₀.2 (3 * (ε / 4)),
      z ∈ V ∧ ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C₀.mixedMomentumDerivative z) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 16 := by
    intro z hz
    have hz' : z ∈ ball (j s₀.1, s₀.2) ε := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨(mem_closedBall.mp hz.1).trans_lt (by linarith),
        (mem_closedBall.mp hz.2).trans_lt (by linarith)⟩
    exact ⟨(hεsub hz').1, (hεsub hz').2.le⟩
  let M := ‖(A.symm : E →L[ℝ] (ℝ × U))‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ' := min δ (1 / (16 * (M + 1) * (K + 1)))
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  refine ⟨Φ₀, C₀, A, r, b, ε / 4, δ', K, V, hr, hb, by positivity, hδ', hK,
    hV, hVc, fun z hz ↦ (hbox z hz).1, hCt₀, hp₀, hC₀, hA,
    fun z hz ↦ (hbox z hz).2, ?_⟩
  intro H hDH hH hsmall
  obtain ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hbuf, hadm, hC,
    hinner, houter, hpre, hclose⟩ := hfamily H hDH hH (hsmall.trans (min_le_left _ _))
  refine ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hbuf, hadm, hC,
    hinner, houter, hpre, hclose, ?_⟩
  intro z hz
  have hsmall' := hsmall.trans (min_le_right _ _)
  have hbudget : M * (K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)) ≤ 1 / 16 := by
    have hpos : 0 < 16 * (M + 1) * (K + 1) := by positivity
    have hh := (le_div_iff₀ hpos).mp hsmall'
    have hnorm := CompositionBounds.cNorm_nonneg (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)
    have hm : M * K ≤ (M + 1) * (K + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hm hnorm
    nlinarith
  have hpert : ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z)‖ ≤ 1 / 16 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (hclose z (hbox z hz).1) hM).trans hbudget)
  have heq : (A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative z) -
      ContinuousLinearMap.id ℝ (ℝ × U) =
      (A.symm : E →L[ℝ] (ℝ × U)).comp
        (C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z) +
      ((A.symm : E →L[ℝ] (ℝ × U)).comp (C₀.mixedMomentumDerivative z) -
        ContinuousLinearMap.id ℝ (ℝ × U)) := by
    apply ContinuousLinearMap.ext
    intro η
    simp
  rw [heq]
  have hsum := norm_add_le
    ((A.symm : E →L[ℝ] (ℝ × U)).comp
      (C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z))
    ((A.symm : E →L[ℝ] (ℝ × U)).comp (C₀.mixedMomentumDerivative z) -
      ContinuousLinearMap.id ℝ (ℝ × U))
  linarith [(hbox z hz).2]

/-- Uniform family version of `app:ch_regular_base:eq:averaged-gradient` and the
mixed-Hessian assertion of `app:lem:common-hamilton-phase`. The reference
Hamilton chart, equivalence, physical and canonical radii, symbol tolerance,
and both buffered targets are chosen before the perturbed symbol. In particular
`W` is one inverse domain for all symbols and both physical endpoints. Its
entire preimage in the outer canonical ball lies in the middle ball.

The mixed gap comes from actual projection `C¹` comparison; the averaged gap
comes from the integral derivative formula. The value tolerance required by
`common_buffered_inverse_domains` is discharged by the mixed comparison and
continuity of the reference phase. No mixed gap or inverse domain is assumed. -/
theorem exists_commonBufferedAveragedGradient
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀)
      (A : (ℝ × U) ≃L[ℝ] E) (r b ρ σ δ K β : ℝ)
      (V : Set (E × (ℝ × U))) (W : Set E),
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < σ ∧ 0 < δ ∧ 0 < K ∧ 0 < β ∧
      IsOpen V ∧ IsCompact (closure V) ∧ IsOpen W ∧ IsCompact (closure W) ∧
      closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * σ) ⊆ V ∧
      C₀.target = V ∧
      ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters) ∧
      ContDiffOn ℝ ∞ C₀.coordinates V ∧
      (A : (ℝ × U) →L[ℝ] E) = C₀.mixedMomentumDerivative (j s₀.1, s₀.2) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          let Ξ : E → E → (ℝ × U) → E := fun x y η ↦
            averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          C.target = V ∧
          C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ z ∈ V, ‖C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z‖ ≤
            K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)) ∧
          (∀ z ∈ closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * σ),
            ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative z) -
              ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8) ∧
          ContDiffOn ℝ ∞ (fun q : (E × E) × (ℝ × U) ↦ Ξ q.1.1 q.1.2 q.2)
            ((ball (j s₀.1) ρ ×ˢ ball (j s₀.1) ρ) ×ˢ ball s₀.2 (3 * σ)) ∧
          ∀ x ∈ ball (j s₀.1) ρ, ∀ y ∈ ball (j s₀.1) ρ,
            (∀ η ∈ ball s₀.2 (3 * σ), ∀ t ∈ Icc (0 : ℝ) 1,
              (y + t • (x - y), η) ∈ C.target) ∧
            (∀ η ∈ ball s₀.2 (3 * σ), HasFDerivAt (Ξ x y)
              (∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative (y + t • (x - y), η)) η) ∧
            (∀ η ∈ ball s₀.2 (3 * σ),
              ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
                ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8) ∧
            InjOn (Ξ x y) (ball s₀.2 (3 * σ)) ∧
            (∀ η ∈ ball s₀.2 (3 * σ), ∀ θ ∈ ball s₀.2 (3 * σ),
              ‖η - θ‖ / 2 ≤ ‖A.symm (Ξ x y η - Ξ x y θ)‖) ∧
            IsCompact (Ξ x y '' closedBall s₀.2 σ) ∧
            cthickening β (Ξ x y '' closedBall s₀.2 σ) ⊆ W ∧
            cthickening β (closure W) ⊆ Ξ x y '' ball s₀.2 (2 * σ) ∧
            (Ξ x y) ⁻¹' cthickening β (closure W) ∩ ball s₀.2 (3 * σ) ⊆
              ball s₀.2 (2 * σ) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  let x₀ := j s₀.1
  obtain ⟨Φ₀, C₀, A, r, b, a, δ, K, V, hr, hb, ha, hδ, hK,
    hV, hVc, hbox, hCt₀, hp₀, hC₀, hA, hgap₀, hfamily⟩ :=
    exists_commonBufferedMixedGap H₀ hD hDH₀ hH₀ j ν horth hspan hR hRD henergy htrans
  have hC₀' : ContDiffOn ℝ ∞ C₀.coordinates C₀.target := hCt₀.symm ▸ hC₀
  let Ξ₀ : E → E → (ℝ × U) → E := fun x y η ↦
    averagedPhaseGradient (fun η x ↦ phase C₀.coordinates (x, η)) η x y
  let σ := a / 2
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hsmall : closedBall s₀.2 (3 * σ) ⊆ ball s₀.2 (3 * a) :=
    closedBall_subset_ball (by dsimp [σ]; linarith)
  have hDR : ball s₀.2 (3 * σ) ⊆ ball s₀.2 (3 * a) :=
    ball_subset_closedBall.trans hsmall
  have hBB : ball x₀ (3 * a) ×ˢ ball s₀.2 (3 * a) ⊆ V :=
    (Set.prod_mono ball_subset_closedBall ball_subset_closedBall).trans hbox
  have hseg (x) (hx : x ∈ ball x₀ (3 * a)) (y) (hy : y ∈ ball x₀ (3 * a)) :
      ∀ η ∈ ball s₀.2 (3 * a), ∀ t ∈ Icc (0 : ℝ) 1,
        (y + t • (x - y), η) ∈ V :=
    fun η hη t ht ↦ hBB ⟨(convex_ball _ _).add_smul_sub_mem hy hx ht, hη⟩
  have hx₀ : x₀ ∈ ball x₀ (3 * a) := mem_ball_self (by positivity)
  have hd₀ (η) (hη : η ∈ ball s₀.2 (3 * σ)) :=
    C₀.hasFDerivAt_averagedPhaseGradient hp₀ hC₀' isOpen_ball
      (fun θ hθ t ht ↦ hCt₀.symm ▸ hseg x₀ hx₀ x₀ hx₀ θ hθ t ht) (hDR hη)
  have hg₀ (η) (hη : η ∈ ball s₀.2 (3 * σ)) :
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 16 : ℝ) := by
    apply C₀.averagedPhaseGradient_derivative_gap_of_bound hp₀ hC₀' isOpen_ball
      (fun θ hθ t ht ↦ hCt₀.symm ▸ hseg x₀ hx₀ x₀ hx₀ θ hθ t ht) A (hDR hη)
    intro t ht
    exact hgap₀ _ ⟨ball_subset_closedBall ((convex_ball _ _).add_smul_sub_mem hx₀ hx₀ ht),
      ball_subset_closedBall (hDR hη)⟩
  have h₁D : ball s₀.2 (2 * σ) ⊆ ball s₀.2 (3 * σ) := ball_subset_ball (by linarith)
  obtain ⟨β, hβ, W, hW, hWc, hstable⟩ := common_buffered_inverse_domains
    (isCompact_closedBall s₀.2 σ) isOpen_ball
    (closedBall_subset_ball (by linarith : σ < 2 * σ)) h₁D (convex_ball _ _) A
    (fun η hη ↦ (hd₀ η hη).differentiableAt)
    (fun η hη ↦ (hg₀ η hη).trans (by norm_num))
  let F : (E × E) × (ℝ × U) → E := fun q ↦ Ξ₀ q.1.1 q.1.2 q.2
  have hcF : ContinuousOn F
      ((ball x₀ (3 * a) ×ˢ ball x₀ (3 * a)) ×ˢ ball s₀.2 (3 * a)) :=
    (C₀.contDiffOn_averagedPhaseGradient hp₀ hC₀' isOpen_ball (convex_ball _ _)
      isOpen_ball (hBB.trans (by rw [hCt₀]))).continuousOn
  have hnear : ∀ᶠ p : E × E in 𝓝 (x₀, x₀), ∀ η ∈ closedBall s₀.2 σ,
      ‖Ξ₀ p.1 p.2 η - Ξ₀ x₀ x₀ η‖ ≤ β / 2 := by
    apply (isCompact_closedBall s₀.2 σ).eventually_forall_of_forall_eventually
    intro η hη
    have hη' : η ∈ ball s₀.2 (3 * a) :=
      hsmall (closedBall_subset_closedBall (by linarith) hη)
    have hm : ((x₀, x₀), η) ∈
        ((ball x₀ (3 * a) ×ˢ ball x₀ (3 * a)) ×ˢ ball s₀.2 (3 * a)) :=
      ⟨⟨hx₀, hx₀⟩, hη'⟩
    have hc := hcF.continuousAt
      (((isOpen_ball.prod isOpen_ball).prod isOpen_ball).mem_nhds hm)
    have hproj : ContinuousAt (fun q : (E × E) × (ℝ × U) ↦ ((x₀, x₀), q.2))
        ((x₀, x₀), η) := continuousAt_const.prodMk continuousAt_snd
    have hn : ContinuousAt (fun q : (E × E) × (ℝ × U) ↦
        ‖F q - F ((x₀, x₀), q.2)‖) ((x₀, x₀), η) :=
      (hc.sub (hc.comp (g := F) (f := fun q : (E × E) × (ℝ × U) ↦
        ((x₀, x₀), q.2)) hproj)).norm
    exact (hn.eventually (gt_mem_nhds (show
      ‖F ((x₀, x₀), η) - F ((x₀, x₀), η)‖ < β / 2 by
        simpa using half_pos hβ))).mono (fun _ h ↦ h.le)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := min a ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρa : ρ ≤ a := by dsimp [ρ]; linarith [min_le_left a ε]
  have hρε : ρ ≤ ε := by dsimp [ρ]; linarith [min_le_right a ε]
  let N := ‖s₀.2‖ + σ + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let δ' := min δ (β / (2 * (K + 1) * N))
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hbox' : closedBall x₀ (3 * ρ) ×ˢ closedBall s₀.2 (3 * σ) ⊆ V :=
    (Set.prod_mono (closedBall_subset_closedBall (by linarith))
      (closedBall_subset_closedBall (by dsimp [σ]; linarith))).trans hbox
  refine ⟨Φ₀, C₀, A, r, b, ρ, σ, δ', K, β, V, W, hr, hb, hρ, hσ, hδ', hK, hβ,
    hV, hVc, hW, hWc, hbox', hCt₀, hp₀, hC₀, hA, ?_⟩
  intro H hDH hH hsmallH
  obtain ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hbuf, hadm, hC,
    hinner, houter, hpre, hclose, hgap⟩ :=
    hfamily H hDH hH (hsmallH.trans (min_le_left _ _))
  let Ξ : E → E → (ℝ × U) → E := fun x y η ↦
    averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y
  have hC' : ContDiffOn ℝ ∞ C.coordinates C.target := hCt.symm ▸ hC
  have hρR : ball x₀ ρ ⊆ ball x₀ (3 * a) :=
    ball_subset_ball (hρa.trans (by linarith))
  refine ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hbuf, hadm, hC,
    hinner, houter, hpre, hclose, ?_, ?_, ?_⟩
  · intro z hz
    exact hgap z ⟨closedBall_subset_closedBall (by linarith) hz.1,
      closedBall_subset_closedBall (by dsimp [σ]; linarith) hz.2⟩
  · exact C.contDiffOn_averagedPhaseGradient hξ hC' isOpen_ball (convex_ball _ _)
      isOpen_ball ((Set.prod_mono hρR hDR).trans (hBB.trans (by rw [hCt])))
  intro x hx y hy
  have hxR := hρR hx
  have hyR := hρR hy
  have hsegC : ∀ η ∈ ball s₀.2 (3 * a), ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C.target :=
    fun η hη t ht ↦ hCt.symm ▸ hseg x hxR y hyR η hη t ht
  have hsegC₀ : ∀ η ∈ ball s₀.2 (3 * a), ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C₀.target :=
    fun η hη t ht ↦ hCt₀.symm ▸ hseg x hxR y hyR η hη t ht
  have hd (η) (hη : η ∈ ball s₀.2 (3 * σ)) :=
    C.hasFDerivAt_averagedPhaseGradient hξ hC' isOpen_ball hsegC (hDR hη)
  have hg (η) (hη : η ∈ ball s₀.2 (3 * σ)) :
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 8 : ℝ) := by
    apply C.averagedPhaseGradient_derivative_gap_of_bound hξ hC' isOpen_ball hsegC A (hDR hη)
    intro t ht
    exact hgap _ ⟨ball_subset_closedBall ((convex_ball _ _).add_smul_sub_mem hyR hxR ht),
      ball_subset_closedBall (hDR hη)⟩
  have hderiv (η) (hη : η ∈ ball s₀.2 (3 * σ)) :
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
        (fderiv ℝ (Ξ x y) η - fderiv ℝ (Ξ₀ x₀ x₀) η)‖ ≤ (1 / 4 : ℝ) := by
    have he : (A.symm : E →L[ℝ] (ℝ × U)).comp
        (fderiv ℝ (Ξ x y) η - fderiv ℝ (Ξ₀ x₀ x₀) η) =
        ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)) -
        ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)) := by
      apply ContinuousLinearMap.ext
      intro v
      simp
    rw [he]
    calc
      _ ≤ ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ +
          ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ :=
        norm_sub_le
          ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
            ContinuousLinearMap.id ℝ (ℝ × U))
          ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
            ContinuousLinearMap.id ℝ (ℝ × U))
      _ ≤ 1 / 4 := by linarith [hg η hη, hg₀ η hη]
  have hxy : (x, y) ∈ ball (x₀, x₀) ε := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hx).trans_le hρε, (mem_ball.mp hy).trans_le hρε⟩
  have hvalue (η) (hη : η ∈ closedBall s₀.2 σ) :
      ‖Ξ x y η - Ξ₀ x₀ x₀ η‖ ≤ β := by
    have hη' : η ∈ ball s₀.2 (3 * a) :=
      hsmall (closedBall_subset_closedBall (by linarith) hη)
    have hval := C.norm_averagedPhaseGradient_sub_le C₀ hξ hC' hp₀ hC₀'
      (hsegC η hη') (hsegC₀ η hη')
      (fun t ht ↦ hclose _ (hseg x hxR y hyR η hη' t ht))
    have hnorm : ‖η‖ ≤ N := by
      have hn' := norm_add_le (η - s₀.2) s₀.2
      rw [sub_add_cancel] at hn'
      have hd := mem_closedBall.mp hη
      rw [dist_eq_norm] at hd
      dsimp [N]
      linarith
    have hcn := CompositionBounds.cNorm_nonneg (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)
    have hbudget : (K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)) * N ≤ β / 2 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2 * (K + 1) * N)).mp
        (hsmallH.trans (min_le_right _ _))
      have hn : 0 ≤ cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) * N :=
        mul_nonneg hcn hN.le
      nlinarith
    have hval' : ‖Ξ x y η - Ξ₀ x y η‖ ≤ β / 2 :=
      hval.trans ((mul_le_mul_of_nonneg_left hnorm (mul_nonneg hK.le hcn)).trans hbudget)
    exact (norm_sub_le_norm_sub_add_norm_sub (Ξ x y η) (Ξ₀ x y η) (Ξ₀ x₀ x₀ η)).trans
      (by linarith [(hεsub hxy) η hη])
  obtain ⟨hinj, hlower, hcompact, hinner', houter'⟩ :=
    hstable (Ξ x y) (fun η hη ↦ (hd η hη).differentiableAt) hderiv hvalue
  refine ⟨fun η hη ↦ hsegC η (hDR hη), hd, hg, hinj, hlower, hcompact,
    hinner', houter', ?_⟩
  intro η hη
  obtain ⟨θ, hθ, heq⟩ := houter' hη.1
  exact (hinj (h₁D hθ) hη.2 heq) ▸ hθ

end JanetCartan.HamiltonPhase
