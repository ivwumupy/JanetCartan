module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.CommonFamily
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.Eikonal
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.Normalized

/-!
# Output data for local comparison charts

These are output specifications for the local construction in the finite
comparison-phase paragraph of `app:ch_regular:thm:no-return`. The actual
Hamilton flow, inverse chart, and homogeneous phase are retained. Smoothness,
the eikonal identity, and tangency below follow from those actual objects.

`LocalComparisonFamily` specifies the local construction from the fixed scalar
symbol, proved in `LocalConstruction.lean`. `PhaseCover.lean` instantiates that
producer and the finite assembly to construct the complete cover. The types
in this file are output specifications, not assumptions of that theorem.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Fixed physical and canonical geometry for a single comparison chart.
The submodule is the transverse section; all geometry precedes the variable
symbol (`app:ch_regular:thm:no-return`). -/
structure ComparisonGeometry (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  tangentSpace : Submodule ℝ E
  normalizer : (ℝ × tangentSpace) →L[ℝ] ℝ
  center : ℝ × tangentSpace
  center_energy : center.1 = 0
  radius : ℝ
  radius_pos : 0 < radius
  parameterRadius : ℝ
  parameterRadius_pos : 0 < parameterRadius

namespace ComparisonGeometry

/-- The compact zero-energy parameter slice used for graph coverage in
`app:ch_regular:thm:no-return`. -/
def parameters (g : ComparisonGeometry E) : Set (ℝ × g.tangentSpace) :=
  closedBall g.center (2 * g.parameterRadius) ∩ {η | η.1 = 0}

/-- An open neighborhood of the entire physical and canonical estimate box
(`app:ch_regular:thm:no-return`). -/
def domain (g : ComparisonGeometry E) : Set (E × (ℝ × g.tangentSpace)) :=
  ball 0 (3 * g.radius) ×ˢ ball g.center (3 * g.parameterRadius)

/-- The zero-energy parameter set is compact, including its boundary
(`app:ch_regular:thm:no-return`). -/
theorem isCompact_parameters (g : ComparisonGeometry E) : IsCompact g.parameters :=
  (isCompact_closedBall _ _).inter_right (isClosed_eq continuous_fst continuous_const)

omit [FiniteDimensional ℝ E] in
/-- The phase domain is open (`app:ch_regular:thm:no-return`). -/
theorem isOpen_domain (g : ComparisonGeometry E) : IsOpen g.domain :=
  isOpen_ball.prod isOpen_ball

omit [FiniteDimensional ℝ E] in
/-- The entire outer physical ball and the compact zero-energy slice lie
strictly inside the phase domain (`app:ch_regular:thm:no-return`). -/
theorem outer_product_subset_domain (g : ComparisonGeometry E) :
    closedBall (0 : E) (2 * g.radius) ×ˢ g.parameters ⊆ g.domain := by
  intro z hz
  exact ⟨closedBall_subset_ball (by linarith [g.radius_pos]) hz.1,
    closedBall_subset_ball (by linarith [g.parameterRadius_pos]) hz.2.1⟩

end ComparisonGeometry

/-- An actual comparison chart with its positive source and target buffers.
All fields are properties of the retained Hamilton flow and projection chart,
as supplied by `exists_commonTameContinuousConicHamiltonPhases`. This is an
output type, not a phase-existence hypothesis for the final theorem
(`app:ch_regular:thm:no-return`). -/
structure ComparisonChart (H : HomogeneousSymbol E) (g : ComparisonGeometry E) where
  homogeneous : H.ConicHomogeneous
  flow : HamiltonFlow H g.tangentSpace
  chart : ProjectionChart flow
  section_eq : flow.sectionMap = g.tangentSpace.subtypeL
  momentum_smooth : ContDiffOn ℝ ∞ flow.momentum (flow.time ×ˢ flow.parameters)
  coordinates_smooth : ContDiffOn ℝ ∞ chart.coordinates chart.target
  target_contains : g.domain ⊆ chart.target
  conic_contains : g.domain ⊆ CharacteristicRoot.conicDomain g.normalizer chart.target
  phase_eq : ∀ z ∈ g.domain, chart.conicPhase g.normalizer z = phase chart.coordinates z
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  buffer : ℝ
  buffer_pos : 0 < buffer
  source_eq : chart.source = ball ((0 : ℝ), (0, g.center)) (3 * sourceRadius) ∩
    flow.augmentedProjection ⁻¹' chart.target
  source_subset : chart.source ⊆ ball ((0 : ℝ), (0, g.center)) (2 * sourceRadius)
  source_admissible : closure (ball ((0 : ℝ), (0, g.center)) (3 * sourceRadius)) ⊆
    flow.time ×ˢ flow.parameters
  source_target_buffer : cthickening buffer
    (flow.augmentedProjection '' closure (ball ((0 : ℝ), (0, g.center)) sourceRadius)) ⊆
      chart.target
  target_source_buffer : cthickening buffer (closure chart.target) ⊆
    flow.augmentedProjection '' ball ((0 : ℝ), (0, g.center)) (2 * sourceRadius)
  preimage_buffer : flow.augmentedProjection ⁻¹' cthickening buffer (closure chart.target) ∩
    ball ((0 : ℝ), (0, g.center)) (3 * sourceRadius) ⊆
      ball ((0 : ℝ), (0, g.center)) (2 * sourceRadius)

namespace ComparisonChart

variable {H : HomogeneousSymbol E} {g : ComparisonGeometry E} (C : ComparisonChart H g)

/-- The literal homogeneous Hamilton phase of the retained chart
(`app:ch_regular:thm:no-return`). -/
def phaseFunction : E × (ℝ × g.tangentSpace) → ℝ := C.chart.conicPhase g.normalizer

/-- Physical gradient of the actual comparison phase
(`app:ch_regular:thm:no-return`). -/
def gradientMap (η : ℝ × g.tangentSpace) (x : E) : E :=
  gradient (fun y ↦ C.phaseFunction (y, η)) x

omit [FiniteDimensional ℝ E] in
/-- The retained phase is positively homogeneous at every scale
(`app:lem:common-hamilton-phase`). -/
theorem phase_homogeneous (z : E × (ℝ × g.tangentSpace)) {a : ℝ} (ha : 0 < a) :
    C.phaseFunction (z.1, a • z.2) = a * C.phaseFunction z :=
  C.chart.conicPhase_smul g.normalizer z ha

/-- On the comparison domain the physical gradient is the momentum of the
literal retained flow and inverse chart (`app:ch_regular:thm:no-return`).
This lets the local producer transfer its state-ball bounds to every graph. -/
theorem gradient_eq_chartMomentum {z : E × (ℝ × g.tangentSpace)}
    (hz : z ∈ g.domain) : C.gradientMap z.2 z.1 = C.chart.chartMomentum z := by
  have he : (fun x ↦ C.phaseFunction (x, z.2)) =ᶠ[𝓝 z.1]
      (fun x ↦ phase C.chart.coordinates (x, z.2)) := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (g.isOpen_domain.mem_nhds hz)
    exact eventuallyEq_of_mem hn (fun x hx ↦ C.phase_eq (x, z.2) hx)
  exact he.gradient_eq.trans (C.chart.gradient_phase_eq_chartMomentum (C.target_contains hz))

omit [FiniteDimensional ℝ E] in
/-- The actual comparison phase is smooth on a neighborhood of the entire
outer physical ball and compact parameter set (`app:ch_regular:thm:no-return`). -/
theorem phase_smooth : ContDiffOn ℝ ∞ C.phaseFunction g.domain :=
  (C.chart.contDiffOn_conicPhase g.normalizer C.coordinates_smooth).mono C.conic_contains

/-- Joint smoothness of the physical gradient on the same open domain
(`app:ch_regular:thm:no-return`). -/
theorem gradient_smooth :
    ContDiffOn ℝ ∞ (fun z : E × (ℝ × g.tangentSpace) ↦ C.gradientMap z.2 z.1) g.domain :=
  (C.chart.contDiffOn_gradient_conicPhase g.normalizer C.momentum_smooth
    C.coordinates_smooth).mono C.conic_contains

include C in
omit [FiniteDimensional ℝ E] in
/-- The compact zero-energy parameter set avoids zero because it lies in
the actual positive normalization cone (`app:ch_regular:thm:no-return`). -/
theorem parameters_nonzero {η : ℝ × g.tangentSpace} (hη : η ∈ g.parameters) : η ≠ 0 := by
  have h0 : (0 : E) ∈ closedBall 0 (2 * g.radius) :=
    mem_closedBall_self (by linarith [g.radius_pos])
  have hpos := (C.conic_contains (g.outer_product_subset_domain (a := (0, η)) ⟨h0, hη⟩)).1
  intro he
  simp [he] at hpos

include C in
/-- The fixed compact zero-energy parameter slice is annular, with both
positive lower and finite upper norm bounds (`app:ch_regular:thm:no-return`). -/
theorem exists_parameter_annulus : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ η ∈ g.parameters, a ≤ ‖η‖ ∧ ‖η‖ ≤ b := by
  obtain ⟨a, ha, hlow⟩ := g.isCompact_parameters.exists_forall_le'
    continuous_norm.continuousOn (fun η hη ↦ norm_pos_iff.mpr (C.parameters_nonzero hη))
  let b := ‖g.center‖ + 2 * g.parameterRadius
  have hb : 0 < b := by dsimp [b]; positivity [g.parameterRadius_pos]
  refine ⟨a, b, ha, hb, fun η hη ↦ ⟨hlow η hη, ?_⟩⟩
  have hh : ‖η - g.center‖ ≤ 2 * g.parameterRadius := by
    simpa only [mem_closedBall, dist_eq_norm] using hη.1
  calc
    ‖η‖ = ‖g.center + (η - g.center)‖ := by congr 1; abel
    _ ≤ ‖g.center‖ + ‖η - g.center‖ := norm_add_le _ _
    _ ≤ b := by dsimp [b]; linarith

/-- The chart's actual gradient solves the eikonal equation, also for
nonzero energy parameters (`app:ch_regular_base:eq:actual-eikonal`). -/
theorem eikonal {z : E × (ℝ × g.tangentSpace)} (hz : z ∈ g.domain) :
    (z.1, C.gradientMap z.2 z.1) ∈ H.domain ∧
      H.h (z.1, C.gradientMap z.2 z.1) = z.2.1 :=
  C.chart.conicPhase_eikonal g.normalizer C.homogeneous (C.conic_contains hz)

/-- Every compact-slice graph is characteristic on the entire outer ball
(`app:ch_regular:thm:no-return`). -/
theorem zero_energy {x : E} {η : ℝ × g.tangentSpace}
    (hx : x ∈ closedBall 0 (2 * g.radius)) (hη : η ∈ g.parameters) :
    (x, C.gradientMap η x) ∈ H.domain ∧ H.h (x, C.gradientMap η x) = 0 := by
  obtain ⟨hmem, he⟩ := C.eikonal (z := (x, η)) (g.outer_product_subset_domain ⟨hx, hη⟩)
  exact ⟨hmem, he.trans hη.2⟩

/-- Eikonal differentiation proves Hamilton tangency for the actual chart,
using `ProtectedFlow.hamilton_tangent_of_eikonal`. No tangency assumption is
part of `ComparisonChart` (`app:ch_regular:thm:no-return`). -/
theorem hamilton_tangent {x : E} {η : ℝ × g.tangentSpace}
    (hz : (x, η) ∈ g.domain) :
    -H.hx (x, C.gradientMap η x) =
      (fderiv ℝ (C.gradientMap η) x) (H.hp (x, C.gradientMap η x)) := by
  have hψ : ContDiffAt ℝ ∞ (fun y ↦ C.phaseFunction (y, η)) x :=
    (C.phase_smooth.contDiffAt (g.isOpen_domain.mem_nhds hz)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  have hg : ContDiffAt ℝ ∞ (C.gradientMap η) x :=
    (C.gradient_smooth.contDiffAt (g.isOpen_domain.mem_nhds hz)).comp x
      (g := fun z : E × (ℝ × g.tangentSpace) ↦ C.gradientMap z.2 z.1)
      (f := fun y : E ↦ (y, η)) (contDiffAt_id.prodMk contDiffAt_const)
  apply hamilton_tangent_of_eikonal H (e := η.1) (hψ.of_le (by simp))
    (hg.differentiableAt (by simp)).hasFDerivAt (C.eikonal hz).1
  have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
    (g.isOpen_domain.mem_nhds hz)
  exact eventuallyEq_of_mem hn (fun y hy ↦ (C.eikonal hy).2)

end ComparisonChart

/-- Required output of the local comparison-phase producer. Its construction
must start from the fixed scalar symbol and a regular frozen characteristic
covector. Every chart, graph-coverage property, and regular-image bound below
is an output obligation of that producer (`app:ch_regular:thm:no-return`).
The final `exists_finite_comparison_cover` instantiates this producer. The
reference member, common source radius and buffer, physical Lipschitz bound
and scalar C³ inverse-coordinate comparison are retained for
`LocalComparisonFamily.exists_uniform_rectangle_margin`; the actual producer
proves these fields by identifying its auxiliary flow and inverse by uniqueness. -/
structure LocalComparisonFamily (H₀ : HomogeneousSymbol E) (D : Set (E × E))
    (G M : Set E) (ξ : E) where
  geometry : ComparisonGeometry E
  covectors : Set E
  covectors_open : IsOpen covectors
  center_mem : ξ ∈ covectors
  stateRadius : ℝ
  stateRadius_pos : 0 < stateRadius
  state_subset : closedBall (0, ξ) stateRadius ⊆ D
  threshold : ℝ
  threshold_pos : 0 < threshold
  lower : ℝ
  lower_pos : 0 < lower
  upper : ℝ
  angularBuffer : ℝ
  angularBuffer_pos : 0 < angularBuffer
  charts : (H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
    H.ConicHomogeneous ∧ cNorm (closedBall (0, ξ) stateRadius) 3
      (fun z ↦ H.h z - H₀.h z) ≤ threshold}) → ComparisonChart H.1 geometry
  reference : ComparisonChart H₀ geometry
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  sourceRadius_eq : ∀ H, (charts H).sourceRadius = sourceRadius
  buffer : ℝ
  buffer_pos : 0 < buffer
  buffer_eq : ∀ H, (charts H).buffer = buffer
  flowBound : ℝ
  flowBound_pos : 0 < flowBound
  position_dist_le : ∀ H, ∀ q ∈ ball ((0 : ℝ), (0, geometry.center)) (3 * sourceRadius),
    ∀ w ∈ ball ((0 : ℝ), (0, geometry.center)) (3 * sourceRadius),
      dist ((charts H).flow.position q) ((charts H).flow.position w) ≤ flowBound * dist q w
  coordinateBound : ℝ
  coordinateBound_pos : 0 < coordinateBound
  coordinates_dist_le : ∀ H, ∀ z ∈ geometry.domain,
    dist ((charts H).chart.coordinates z) (reference.chart.coordinates z) ≤
      coordinateBound * cNorm (closedBall (0, ξ) stateRadius) 3
        (fun z ↦ H.1.h z - H₀.h z)
  regular : ∀ H, ∀ x ∈ closedBall 0 (2 * geometry.radius),
    ∀ η ∈ geometry.parameters,
      lower ≤ ‖(charts H).gradientMap η x‖ ∧ ‖(charts H).gradientMap η x‖ ≤ upper ∧
      closedBall (normalizedCovector ((charts H).gradientMap η x)) angularBuffer ⊆ G \ M
  covers : ∀ H, ∀ x ∈ closedBall 0 geometry.radius, ∀ p ∈ covectors,
    H.1.h (x, p) = 0 → ∃ η ∈ geometry.parameters, p = (charts H).gradientMap η x

end JanetCartan.ProtectedFlow.PhaseCover
