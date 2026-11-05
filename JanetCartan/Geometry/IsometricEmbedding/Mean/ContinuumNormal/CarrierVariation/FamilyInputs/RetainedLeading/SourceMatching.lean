module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.ChartAdapter
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.CanonicalFields
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Amplitude

/-!
# Source dilation of the retained leading maps

The existing source-flow uniqueness theorem applies directly to two charts
obtained from the SAME retained producer: their minor, adapted buffer and
existence time are fixed before the immersion. All trajectory-range, ODE and
coefficient-regularity premises are discharged from those retained fields.
The scalar is the literal prescribed source scalar, not a new solution.

Consumer: the source-scale part of `FamilyInputs.RetainedLeading`, for
`app:ch_background:eq:bg-Nsigma` and `app:ch_background:prop:bg-normalized`.
The seed and all scaled immersions must still be instantiated in the same
retained producer by the parent source-cap construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase NormalizedBackground.SourceGeometry SourceMatching
open ContinuumRow CanonicalCarrier

/-- ODE uniqueness matches the SAME retained forward and inverse maps, the
literal scalar with initial value `σ`, its full null amplitude and canonical
normal. All chart-specific hypotheses of the source-flow theorem are proved
from the primitive retained outputs. No equality between independently selected
minors or scalar gauges is used (`app:ch_background:eq:bg-Nsigma`). -/
theorem retained_charts_source_dilation
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {z₀ : Euclidean 3} {ρ Rc B τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), z₀) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc)
      (closedBall ((0 : Euclidean n), z₀) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (cσ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col (sourceDilation F σ)) :
    let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
    EqOn cσ.forward (sourceTransportFlow c₀.forward σ)
      (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
    EqOn cσ.inverse (sourceTransportFlow c₀.inverse σ) cσ.D ∧
    EqOn (cσ.scalar (fun _ ↦ σ)) (sourceAmplitude (c₀.scalar (fun _ ↦ 1)) σ)
      (C ⁻¹' cσ.D) ∧
    EqOn (fun w ↦ cσ.scalar (fun _ ↦ σ) w • carrierNullvector T cσ.Q col w)
      (sourceAmplitude (fun w ↦ c₀.scalar (fun _ ↦ 1) w • carrierNullvector T c₀.Q col w) σ)
      (C ⁻¹' cσ.D) ∧
    ∀ (measurement : Euclidean n → ℝ)
      (angular : CarrierParameter × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
      (p : Euclidean n × CarrierParameter),
      densityCoordinates T p ∈ cσ.D →
      (normalizedSourceCoefficients F
        (fun q ↦ T.carrierGradient c₀.Q q.1 (parameter q.2))
        (fun q ↦ c₀.scalar (fun _ ↦ 1) (q.1, parameter q.2) •
          carrierNullvector T c₀.Q col (q.1, parameter q.2))
        measurement angular high σ).normal p = cσ.normal (fun _ ↦ σ) p := by
  have hreg (w) (hw : w ∈ closedBall ((0 : Euclidean n), z₀) ρ) :=
    c₀.direction_smooth.contDiffAt (hΩ.mem_nhds (hKΩ hw))
  have hkernel (w) (hw : w ∈ closedBall ((0 : Euclidean n), z₀) ρ) :=
    c₀.null_smooth.contDiffAt (hΩ.mem_nhds (hKΩ hw))
  have hrange₀ (p) (hp : p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
      (t) (ht : t ∈ Ioo (-τ) τ) := (c₀.subset_big (c₀.forward_range (show (t, p) ∈ Ioo (-τ) τ ×ˢ
        ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8) from ⟨ht, hp⟩))).2
  have hrangeσ (p) (hp : p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
      (t) (ht : t ∈ Ioo (-τ) τ) := (cσ.subset_big (cσ.forward_range (show (t, p) ∈ Ioo (-τ) τ ×ˢ
        ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8) from ⟨ht, hp⟩))).2
  have hpatchσ (p) (hp : p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
      (t) (ht : t ∈ Ioo (-τ) τ) := hpatch (cσ.domain_coefficients (cσ.forward_range (show (t, p) ∈ Ioo (-τ) τ ×ˢ
        ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8) from ⟨ht, hp⟩)))
  obtain ⟨hflow, hfoot⟩ := current_nullFlow_source_dilation T c₀.Q cσ.Q hF hrank
    hphysical c₀.frame_eq htrans hσ hσ1 cσ.frame_eq row col hRc hτ hτR hbuffer hreg
    c₀.initial cσ.initial hrange₀ hrangeσ hpatchσ c₀.ode cσ.ode
  obtain ⟨hscalar, hnull, hnormal⟩ := current_nullAmplitude_source_dilation T c₀.Q cσ.Q
    hF hrank hphysical c₀.frame_eq htrans hσ hσ1 cσ.frame_eq row col hRc hτ hτR
    hbuffer hreg c₀.initial cσ.initial hrange₀ hrangeσ hpatchσ c₀.ode cσ.ode hflat hkernel
    cσ.inverse_range c₀.inverse_forward cσ.forward_inverse
  exact ⟨hflow, hfoot c₀.inverse cσ.inverse cσ.D cσ.inverse_range c₀.inverse_forward
    cσ.forward_inverse, hscalar, hnull, hnormal⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
