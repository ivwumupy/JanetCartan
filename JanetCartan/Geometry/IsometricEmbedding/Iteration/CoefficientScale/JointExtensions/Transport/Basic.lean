module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.FixedCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.TransportProfiles.Refinement

/-!
# Fixed extensions in the transport variables

The transport part of `app:eq:uniform-high-coeff` uses the original product
norm. The agreement balls below are smaller than the input balls. The finite
cover must therefore be selected using these agreement balls.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions

/-- Fixed Hilbert coordinates for the joint transport variables in
`app:eq:uniform-high-coeff`. -/
def transportExtensionCoordinates (n : ℕ) :
    WithLp 2 (Euclidean n × Euclidean 3) ≃L[ℝ] (Euclidean n × Euclidean 3) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ _ _

/-- The fixed coordinate map is a contraction. This also keeps the SUPPORT
ellipsoid in the larger coefficient ball (`app:eq:uniform-high-coeff`). -/
theorem norm_transportExtensionCoordinates_le (n : ℕ) :
    ‖(transportExtensionCoordinates n).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change max ‖q.ofLp.1‖ ‖q.ofLp.2‖ ≤ 1 * ‖q‖
  rw [one_mul]
  exact max_le (WithLp.norm_fst_le _ q) (WithLp.norm_snd_le _ q)

variable {n : ℕ} (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)

/-- Parameters chosen from the larger coefficient ball, before the current
immersion or derivative order (`app:eq:uniform-high-coeff`). -/
def transportExtensionParameters :
    BallExtension.Parameters (WithLp 2 (Euclidean n × Euclidean 3)) :=
  coordinateBallParameters (transportExtensionCoordinates n) a hρ

/-- Radius of the agreement ball in the ORIGINAL product norm
(`app:eq:uniform-high-coeff`). -/
def transportExtensionRadius : ℝ :=
  coordinateWorkingRadius (transportExtensionCoordinates n) a hρ

/-- Fixed support shared by all six extensions on this minor patch
(`app:eq:uniform-high-coeff`). -/
def transportExtensionSupport : Set (Euclidean n × Euclidean 3) :=
  transportExtensionCoordinates n ''
    closedBall (transportExtensionParameters a hρ).center
      ((transportExtensionParameters a hρ).radius +
        (transportExtensionParameters a hρ).width / 2)

/-- The support set is compact independently of the coefficient
(`app:eq:uniform-high-coeff`). -/
theorem isCompact_transportExtensionSupport : IsCompact (transportExtensionSupport a hρ) :=
  (isCompact_closedBall _ _).image (transportExtensionCoordinates n).continuous

/-- The smaller balls used in the finite subcover have positive radii
(`main:prop:current-scale`). -/
theorem transportExtensionRadius_pos : 0 < transportExtensionRadius a hρ :=
  coordinateWorkingRadius_pos _ _ _

/-- The input ellipsoid fits in the larger original ball where the actual
coefficient producer gives estimates (`app:eq:uniform-high-coeff`). -/
theorem transportExtensionParameters_mapsTo :
    MapsTo (transportExtensionCoordinates n)
      (closedBall (transportExtensionParameters a hρ).center
        (transportExtensionParameters a hρ).radius) (closedBall a ρ) :=
  coordinateBallParameters_mapsTo _ _ _

/-- Explicit inclusion of the smaller agreement ball in the input
ellipsoid (`app:eq:uniform-high-coeff`). -/
theorem transportExtensionRadius_ball_subset :
    closedBall a (transportExtensionRadius a hρ) ⊆
      transportExtensionCoordinates n ''
        closedBall (transportExtensionParameters a hρ).center
          (transportExtensionParameters a hρ).radius :=
  coordinateWorkingBall_subset _ _ _

/-- The agreement ball lies in the larger original coefficient ball
(`app:eq:uniform-high-coeff`). -/
theorem transportExtensionWorkingBall_subset :
    closedBall a (transportExtensionRadius a hρ) ⊆ closedBall a ρ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := transportExtensionRadius_ball_subset a hρ hx
  exact transportExtensionParameters_mapsTo a hρ hy

/-- The fixed support itself lies in the larger original coefficient ball,
and hence in its open minor domain in the finite refinement. This verifies
the outer buffer of `app:eq:uniform-high-coeff` in the product norm. -/
theorem transportExtensionSupport_subset :
    transportExtensionSupport a hρ ⊆ closedBall a ρ := by
  rintro _ ⟨x, hx, rfl⟩
  let L := transportExtensionCoordinates n
  let p := transportExtensionParameters a hρ
  have hd : dist (L x) a ≤ ‖L.toContinuousLinearMap‖ * dist x (L.symm a) := by
    simpa only [dist_eq_norm, map_sub, ContinuousLinearEquiv.coe_coe, L.apply_symm_apply] using
      L.toContinuousLinearMap.le_opNorm (x - L.symm a)
  have hr : (1 + ‖L.toContinuousLinearMap‖) * p.radius = ρ :=
    mul_div_cancel₀ _ (by positivity)
  have hw : ‖L.toContinuousLinearMap‖ * (p.width / 2) ≤ p.radius := by
    calc
      _ ≤ 1 * (p.width / 2) := mul_le_mul_of_nonneg_right
        (norm_transportExtensionCoordinates_le n) (div_nonneg p.width_pos.le (by norm_num))
      _ ≤ p.radius := by linarith [p.width_lt, p.radius_pos]
  apply (hd.trans (mul_le_mul_of_nonneg_left (mem_closedBall.mp hx) (norm_nonneg _))).trans
  change ‖L.toContinuousLinearMap‖ * (p.radius + p.width / 2) ≤ ρ
  nlinarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The same fixed Seeley operator for each literal transport coefficient
(`app:eq:uniform-high-coeff`). -/
def extendTransportCoefficient (f : (Euclidean n × Euclidean 3) → V) :
    (Euclidean n × Euclidean 3) → V :=
  coordinateSeeley (transportExtensionCoordinates n) (transportExtensionParameters a hρ) f

/-- Smoothness, agreement on the smaller ball, and the prescribed support
of a coefficient extension. This is an output property, instantiated for
all six actual coefficients in `exists_transport_extensions_before_geometry`
(`app:eq:uniform-high-coeff`). -/
def TransportExtensionProperties (f : (Euclidean n × Euclidean 3) → V) : Prop :=
  ContDiff ℝ ∞ (extendTransportCoefficient a hρ f) ∧
  EqOn (extendTransportCoefficient a hρ f) f
    (closedBall a (transportExtensionRadius a hρ)) ∧
  tsupport (extendTransportCoefficient a hρ f) ⊆ transportExtensionSupport a hρ

/-- Smooth local coefficients give the actual fixed extension, with no
extension estimate assumed (`app:eq:uniform-high-coeff`). -/
theorem transportExtensionProperties_of_contDiffAt
    {f : (Euclidean n × Euclidean 3) → V}
    (hf : ∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ f x) :
    TransportExtensionProperties a hρ f := by
  refine ⟨?_, ?_, tsupport_coordinateSeeley_subset _ _ _⟩
  · apply contDiff_coordinateSeeley
    rintro _ ⟨x, hx, rfl⟩
    exact hf _ (transportExtensionParameters_mapsTo a hρ hx)
  · exact (coordinateSeeley_eqOn _ _ _).mono (transportExtensionRadius_ball_subset a hρ)

/-- Same-order global bound by the literal larger-ball seminorm. This
supplies the extension step of `app:ch_waves:eq:joint-tame`. -/
theorem exists_extendTransportCoefficient_cNorm_le (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ f : (Euclidean n × Euclidean 3) → V,
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ f x) →
      cNorm univ m (extendTransportCoefficient a hρ f) ≤ C * cNorm (closedBall a ρ) m f := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_coordinateSeeley_le (F := V)
    (transportExtensionCoordinates n) (transportExtensionParameters a hρ) m
  exact ⟨C, hC, fun f hf ↦ hb _ (isCompact_closedBall _ _)
    (transportExtensionParameters_mapsTo a hρ) f hf⟩

end JanetCartan.CurrentCoefficientProfiles.JointExtensions
