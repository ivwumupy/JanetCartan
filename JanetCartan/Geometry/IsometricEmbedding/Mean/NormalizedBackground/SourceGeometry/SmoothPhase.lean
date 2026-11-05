module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Hamilton
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CompactFamily

/-!
# The actual differentials of the extended source phase

For `app:ch_background:prop:bg-normalized`, the integral extension has the
physical covector of the constructed Hamilton phase and its divided canonical
footpoint. All statements concern the same seed phase on its original open box.
The common buffer is chosen before any derivative order.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.NormalizedBackground.SourceGeometry

variable {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Joint smoothness of the actual physical phase covector, needed for the
normal and transport in `app:ch_background:eq:bg-Nsigma`. -/
theorem contDiffOn_phase_positionGradient {S : E × Z → ℝ} {U : Set E} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun p : E × Z ↦ gradient (fun x ↦ S (x, p.2)) p.1)
      (U ×ˢ V) := by
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn
    (contDiffOn_parameterFDeriv hU hV hS)

/-- The positive-scale physical differential of the integral extension is
exactly the seed covector at `ρx` (`app:ch_background:eq:bg-Nsigma`). -/
theorem gradient_sourcePhaseExtension_position {S : E × Z → ℝ}
    {U : Set E} {V : Set Z} (hU : IsOpen U) (hc : Convex ℝ U)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hzero : ∀ z ∈ V, S (0, z) = 0) (h0 : (0 : E) ∈ U)
    {ρ : ℝ} (hρ : ρ ≠ 0) {x : E} {z : Z} (hx : ρ • x ∈ U) (hz : z ∈ V) :
    gradient (fun y ↦ sourcePhaseExtension S (ρ, (y, z))) x =
      gradient (fun y ↦ S (y, z)) (ρ • x) := by
  have hs : ContDiffOn ℝ ∞ (fun y ↦ S (y, z)) U :=
    hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hz⟩)
  have he : (fun y ↦ sourcePhaseExtension S (ρ, (y, z))) =ᶠ[𝓝 x]
      (fun y ↦ sourcePhase S ρ (y, z)) := by
    filter_upwards [(hU.preimage (continuous_id.const_smul ρ)).mem_nhds hx] with y hy
    exact (sourcePhase_eq_extension hU hc (hs.of_le (by simp)) (hzero z hz) h0 hy hρ).symm
  exact he.gradient_eq.trans (gradient_sourcePhase_position hρ
    ((hs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)))

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- At zero scale the physical derivative of the very same extended phase is
the frozen seed covector (`app:ch_background:prop:bg-normalized`). -/
theorem gradient_sourcePhaseExtension_position_zero (S : E × Z → ℝ) (x : E) (z : Z) :
    gradient (fun y ↦ sourcePhaseExtension S (0, (y, z))) x =
      gradient (fun y ↦ S (y, z)) 0 := by
  have he : (fun y ↦ sourcePhaseExtension S (0, (y, z))) =
      (InnerProductSpace.toDual ℝ E) (gradient (fun y ↦ S (y, z)) 0) := by
    funext y
    exact sourcePhaseExtension_zero S y z
  rw [he]
  exact (((InnerProductSpace.toDual ℝ E)
    (gradient (fun y ↦ S (y, z)) 0)).hasFDerivAt.hasGradientAt.gradient).trans
      ((InnerProductSpace.toDual ℝ E).symm_apply_apply _)

/-- The canonical differential of the integral extension retains the inverse
scale factor. This is the footpoint used with the unchanged initial measure
in `app:ch_background:eq:bg-Nsigma`. -/
theorem fderiv_sourcePhaseExtension_parameter {S : E × Z → ℝ}
    {U : Set E} {V : Set Z} (hU : IsOpen U) (hc : Convex ℝ U)
    (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hzero : ∀ z ∈ V, S (0, z) = 0) (h0 : (0 : E) ∈ U)
    {ρ : ℝ} (hρ : ρ ≠ 0) {x : E} {z : Z} (hx : ρ • x ∈ U) (hz : z ∈ V) :
    fderiv ℝ (fun w ↦ sourcePhaseExtension S (ρ, (x, w))) z =
      ρ⁻¹ • fderiv ℝ (fun w ↦ S (ρ • x, w)) z := by
  have he : (fun w ↦ sourcePhaseExtension S (ρ, (x, w))) =ᶠ[𝓝 z]
      (fun w ↦ sourcePhase S ρ (x, w)) := by
    filter_upwards [hV.mem_nhds hz] with w hw
    have hs : ContDiffOn ℝ ∞ (fun y ↦ S (y, w)) U :=
      hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hw⟩)
    exact (sourcePhase_eq_extension hU hc (hs.of_le (by simp)) (hzero w hw) h0 hx hρ).symm
  rw [he.fderiv_eq]
  exact (hasFDerivAt_sourcePhase_parameter
    (((hS.contDiffAt ((hU.prod hV).mem_nhds ⟨hx, hz⟩)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)).hasFDerivAt).fderiv

/-- A fixed physical buffer and an open scale interval through zero contain
every segment in the phase integral. The compact physical set is prescribed,
and the interval is chosen before the mixed derivative order
(`app:ch_background:prop:bg-normalized`). -/
theorem exists_source_phase_buffer {U D : Set E} (hU : IsOpen U)
    (h0 : (0 : E) ∈ U) (hD : IsCompact D) :
    ∃ B : Set E, IsOpen B ∧ D ⊆ B ∧ ∃ r : ℝ, 0 < r ∧
      ∀ ρ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2,
        (t * ρ) • x ∈ U := by
  obtain ⟨R, hR, hDR⟩ := hD.isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hd⟩ := exists_scale_mapsTo (isCompact_closedBall (0 : E) (R + 1))
    (hU.mem_nhds h0)
  refine ⟨Metric.ball 0 (R + 1), Metric.isOpen_ball, ?_, δ / 8, by positivity, ?_⟩
  · intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using (hDR x hx).trans_lt (by linarith)
  · intro ρ hρ x hx t ht
    apply hd (t * ρ) _ (Metric.ball_subset_closedBall hx)
    have hp : |ρ| ≤ δ / 4 := (abs_le).mpr ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
    have htp : |t| ≤ 2 := (abs_le).mpr ⟨by linarith [ht.1], ht.2.le⟩
    rw [abs_mul]
    calc
      |t| * |ρ| ≤ 2 * (δ / 4) := mul_le_mul htp hp (abs_nonneg _) (by norm_num)
      _ ≤ δ := by linarith

/-- Smooth phase and actual canonical footpoint differential, with bounds on
every mixed derivative on the same compact scale/physical/carrier set. The
segment hypothesis is the conclusion of `exists_source_phase_buffer` (or of
`exists_common_source_geometry_bounds`); it is solely domain containment
(`app:ch_background:prop:bg-normalized`). -/
theorem sourcePhaseExtension_joint_bounds [FiniteDimensional ℝ Z]
    {S : E × Z → ℝ} {U B D : Set E} {V K : Set Z} {r : ℝ}
    (hU : IsOpen U) (hB : IsOpen B) (hV : IsOpen V) (hr : 0 < r)
    (hD : IsCompact D) (hDB : D ⊆ B) (hK : IsCompact K) (hKV : K ⊆ V)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hseg : ∀ ρ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2,
      (t * ρ) • x ∈ U) :
    let J := fun q : ℝ × (E × Z) ↦ (sourcePhaseExtension S q,
      fderiv ℝ (fun z ↦ sourcePhaseExtension S (q.1, (q.2.1, z))) q.2.2)
    ContDiffOn ℝ ∞ J (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Icc (0 : ℝ) r, ∀ x ∈ D, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ s J (ρ, (x, z))‖ ≤ C := by
  have hIW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hm : ∀ q ∈ Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V, ∀ t ∈ Ioo (-1 : ℝ) 2,
      ((t * q.1) • q.2.1, q.2.2) ∈ U ×ˢ V :=
    fun q hq t ht ↦ ⟨hseg q.1 hq.1 q.2.1 hq.2.1 t ht, hq.2.2⟩
  have hj := (contDiffOn_sourcePhaseExtension hU hV
    (isOpen_Ioo.prod (hB.prod hV)) isOpen_Ioo hIW hS hm).prodMk
      (contDiffOn_sourcePhaseExtension_parameterFDeriv hU hV hB isOpen_Ioo
        isOpen_Ioo hIW hS hm)
  refine ⟨hj, ?_⟩
  intro s
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hD.prod hK)).exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hj
      (isOpen_Ioo.prod (hB.prod hV)) (by simp)).mono
        (show Icc (0 : ℝ) r ×ˢ D ×ˢ K ⊆ Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V from by
          intro q hq
          exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hDB hq.2.1, hKV hq.2.2⟩))
  exact ⟨|C| + 1, by positivity, fun ρ hρ x hx z hz ↦
    (hC (ρ, (x, z)) ⟨hρ, hx, hz⟩).trans ((le_abs_self C).trans (by linarith))⟩

section HamiltonFootpoint

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  {H : HamiltonPhase.HomogeneousSymbol E} {Φ : HamiltonPhase.HamiltonFlow H Y}

omit [FiniteDimensional ℝ E] in
/-- The canonical differential of the named constructed source phase is its
actual inverse footpoint, including the divided time coordinate
(`app:ch_background:eq:bg-Nsigma`). -/
theorem fderiv_sourceHamiltonPhase_parameter (C : HamiltonPhase.ProjectionChart Φ)
    {ρ : ℝ} (hρ : ρ ≠ 0) {x : E} {η : ℝ × Y} (hz : (ρ • x, η) ∈ C.target) :
    fderiv ℝ (fun ζ ↦ sourcePhase (HamiltonPhase.phase C.coordinates) ρ (x, ζ)) η =
      HamiltonPhase.canonicalCovector (sourceCoordinates C.coordinates ρ (x, η)) := by
  have hd := (hasFDerivAt_sourceHamiltonPhase C hρ hz).comp η
    ((hasFDerivAt_const x η).prodMk (hasFDerivAt_id η))
  have he := hd.fderiv
  simp only [Function.comp_def, id_eq] at he
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  simp [HamiltonPhase.phaseDifferential]

/-- The smooth canonical differential of the integral extension is the
actual divided inverse-chart footpoint. The centered Cauchy value is derived
from the seed chart, rather than assumed for an independently selected phase
(`app:ch_background:eq:bg-Nsigma`). -/
theorem fderiv_sourceHamiltonPhaseExtension_parameter
    (C : HamiltonPhase.ProjectionChart Φ) {U : Set E} {V : Set (ℝ × Y)}
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ (HamiltonPhase.phase C.coordinates) (U ×ˢ V))
    (hsection : ∀ η ∈ V, (0, (0, η)) ∈ C.source) (h0 : (0 : E) ∈ U)
    {ρ : ℝ} (hρ : ρ ≠ 0) {x : E} {η : ℝ × Y}
    (hx : ρ • x ∈ U) (hη : η ∈ V) (hz : (ρ • x, η) ∈ C.target) :
    fderiv ℝ (fun ζ ↦ sourcePhaseExtension (HamiltonPhase.phase C.coordinates)
      (ρ, (x, ζ))) η =
      HamiltonPhase.canonicalCovector (sourceCoordinates C.coordinates ρ (x, η)) := by
  rw [fderiv_sourcePhaseExtension_parameter hU hc hV hS
    (fun η hη ↦ seedHamiltonPhase_zero C (hsection η hη)) h0 hρ hx hη]
  have hs := (((hS.contDiffAt ((hU.prod hV).mem_nhds ⟨hx, hη⟩)).comp η
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)).hasFDerivAt
  exact (hasFDerivAt_sourcePhase_parameter (ρ := ρ) (x := x) hs).fderiv.symm.trans
    (fderiv_sourceHamiltonPhase_parameter C hρ hz)

end HamiltonFootpoint

end JanetCartan.NormalizedBackground.SourceGeometry
