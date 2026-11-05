module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.Geometry
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactNormal

/-!
# Normal geometry is unchanged by a local phase extension

Agreement on the entire physical convex box and source covector chart gives
agreement of the averaged gradients, their whole image domains, the exact
normal kernels and the chart used by `LowBounds`. In particular, no common
target subset is substituted for the full averaged-gradient image.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open NormalComparison LowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Agreement on an open physical chart implies local agreement of each
physical phase slice. Source: actual-calculus Step 1. -/
theorem phase_slice_eventuallyEq {S S' : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D))
    {x η : E} (hx : x ∈ X) (hη : η ∈ D) :
    (fun z ↦ S' z η) =ᶠ[𝓝 x] (fun z ↦ S z η) := by
  filter_upwards [hX.mem_nhds hx] with z hz
  exact he (x := (z, η)) ⟨hz, hη⟩

/-- Physical segment differentiation sees the same phase after extension.
The convexity hypothesis concerns the whole output box, not just the support
of one amplitude. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem averagedGradient_phase_congr {S S' : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hcX : Convex ℝ X)
    (he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D))
    {x y η : E} (hx : x ∈ X) (hy : y ∈ X) (hη : η ∈ D) :
    averagedGradient S' x y η = averagedGradient S x y η := by
  unfold averagedGradient averagedPhaseDifferential
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (phase_slice_eventuallyEq hX he
    (hcX.add_smul_sub_mem hy hx (by simpa using ht)) hη).fderiv_eq

/-- The full averaged-gradient inverse domain is unchanged, including every
normal dyadic shell used by the low estimate.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem bufferedNormalDomain_phase_congr {S S' : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hcX : Convex ℝ X)
    (he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D)) :
    bufferedNormalDomain X D S' = bufferedNormalDomain X D S := by
  ext q
  by_cases hx : q.1 ∈ X
  · by_cases hy : q.2.1 ∈ X
    · have hi : averagedGradient S' q.1 q.2.1 '' D =
          averagedGradient S q.1 q.2.1 '' D :=
        Set.image_congr (fun _ hη ↦ averagedGradient_phase_congr hX hcX he hx hy hη)
      simp only [bufferedNormalDomain, mem_ofPred_eq, hi]
    · simp [bufferedNormalDomain, hy]
  · simp [bufferedNormalDomain, hx]

/-- Extension preserves the actual inverse equations, Jacobian and gap on
the original chart. No analytic field of the chart is assumed anew for the
extension. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem LowBounds.AveragedGradientChart.congr_phase
    {S S' : E → E → ℝ} {X D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S X D η J δ)
    (hX : IsOpen X) (hcX : Convex ℝ X)
    (he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D)) :
    AveragedGradientChart S' X D η J δ := by
  have hg (x) (hx : x ∈ X) (y) (hy : y ∈ X) :
      EqOn (averagedGradient S' x y) (averagedGradient S x y) D :=
    fun _ hu ↦ averagedGradient_phase_congr hX hcX he hx hy hu
  refine ⟨G.measurable, G.gap_pos, ?_, ?_, ?_, ?_, ?_, G.gap⟩
  · intro x hx y hy u hu t ht
    exact (G.segment x hx y hy u hu t ht).congr_of_eventuallyEq
      (phase_slice_eventuallyEq hX he
        (hcX.add_smul_sub_mem hy hx (by simpa using ht)) hu)
  · intro x hx y hy u hu
    apply (G.integrable x hx y hy u hu).congr
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
    exact (phase_slice_eventuallyEq hX he
      (hcX.add_smul_sub_mem hy hx ⟨ht'.1.le, ht'.2⟩) hu).fderiv_eq.symm
  · intro x hx y hy u hu
    exact (G.derivative x hx y hy u hu).congr' (hg x hx y hy) hu
  · intro x hx y hy u hu v hv huv
    apply G.injective x hx y hy hu hv
    simpa only [← hg x hx y hy hu, ← hg x hx y hy hv] using huv
  · intro x hx y hy u hu
    rw [hg x hx y hy hu]
    exact G.leftInverse x hx y hy u hu

/-- Both physical positions are retained when transporting the full normal
coordinates. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem normalForwardCoordinates_phase_congr {S S' : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hcX : Convex ℝ X)
    (he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D)) :
    EqOn (normalForwardCoordinates S') (normalForwardCoordinates S) (X ×ˢ (X ×ˢ D)) := by
  intro q hq
  simp only [normalForwardCoordinates,
    averagedGradient_phase_congr hX hcX he hq.1 hq.2.1 hq.2.2]

/-- The supplied left inverse maps the entire averaged-gradient image back
into the original input chart. This uses no common-target restriction.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem LowBounds.AveragedGradientChart.mapsTo_normalInverseCoordinates
    {S : E → E → ℝ} {X D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S X D η J δ) :
    MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D S) (X ×ˢ (X ×ˢ D)) := by
  rintro q ⟨hx, hy, u, hu, he⟩
  refine ⟨hx, hy, ?_⟩
  change η q.1 q.2.1 q.2.2 ∈ D
  rw [← he, G.leftInverse q.1 hx q.2.1 hy u hu]
  exact hu

/-- All primitive support and inverse geometry fields transfer to the
extended phase. The original carrier must lie in its declared chart; this
is a support hypothesis on the original data, not an estimate for a normal
amplitude. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem LowBounds.PrimitiveNormalGeometry.congr_phase
    {S S' : E → E → ℝ} {X D : Set E} {A B : E → E → Mat}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    {W K : Set (NormalVariables n)}
    (G : PrimitiveNormalGeometry X D S A B η J W K)
    (chart : AveragedGradientChart S X D η J δ)
    (hX : IsOpen X) (hcX : Convex ℝ X)
    (he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D))
    (hK : K ⊆ X ×ˢ (X ×ˢ D)) :
    PrimitiveNormalGeometry X D S' A B η J W K := by
  have hdom := bufferedNormalDomain_phase_congr hX hcX he
  have hf := normalForwardCoordinates_phase_congr hX hcX he
  have himage : normalForwardCoordinates S' '' K = normalForwardCoordinates S '' K :=
    Set.image_congr (fun _ hq ↦ hf (hK hq))
  refine ⟨hdom.symm ▸ G.open_domain, hdom.symm ▸ G.inverse_smooth,
    hdom.symm ▸ G.mapsTo, G.input_smooth, G.gap, ?_, G.carrier,
    himage.symm ▸ G.closed_image, ?_, G.left_output, G.right_output⟩
  · intro q hq
    have hq' : q ∈ bufferedNormalDomain X D S := hdom ▸ hq
    rw [hf (chart.mapsTo_normalInverseCoordinates hq')]
    exact G.rightInverse q hq'
  · rw [himage, hdom]
    exact G.buffer

/-- The literal cross-normal matrix kernel is unchanged by phase extension
on the original amplitude supports. Both physical positions and all source
covectors are retained. Source: `app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem crossNormalKernel_phase_congr (S S' : E → E → ℝ) (A B : E → E → Mat)
    (D : Set E) (heA : ∀ x u, A x u ≠ 0 → S' x u = S x u)
    (heB : ∀ y u, B y u ≠ 0 → S' y u = S y u) :
    crossNormalKernel D S' A B = crossNormalKernel D S A B := by
  funext x y
  unfold crossNormalKernel
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases ha : A x u = 0
  · simp [crossNormalNumerator, ha]
  · by_cases hb : B y u = 0
    · simp [crossNormalNumerator, hb]
    · rw [heA x u ha, heB y u hb]

end JanetCartan.FourierIntegral
