module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Hamilton.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Hamilton.Determinant

/-!
# The actual source-dilated determinant flow and phase

For `app:ch_background:eq:bg-Nsigma`, this module constructs the Hamilton flow
and its named inverse from the seed flow and inverse of the actual projected
stress determinant. The inputs are the seed objects supplied by
`jc-hamilton-phase` and `jc-actual-carriers`; their instantiation belongs to
`jc-normalized-source-geometry`. All scaled equations, inverse identities, and
phase identities are proved here. No claim is made about immersion or inverse
charts at zero scale.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry
open HamiltonPhase ActualCarriers ActualCarriers.NormalizedSymbol ProjectedStressFrame

variable {n N : ℕ} {F : Euclidean n → Euclidean N} {Ω : Set (Euclidean n)}
  (hΩ : IsOpen Ω) (hF : ContDiff ℝ ∞ F)
  (hrank : HasFullNormalRankOn F Ω)
  (hQ : ContDiffOn ℝ ∞ (projectedStress F) Ω)
  {ρ : ℝ} (hρ : 0 < ρ)

/-- The actual `normalizedHomogeneousSymbol` of the scaled projected frame.
Its smoothness is derived from the seed data (`app:ch_background:eq:bg-Nsigma`). -/
abbrev sourceNormalizedHamiltonSymbol : HomogeneousSymbol (Euclidean n) :=
  normalizedHomogeneousSymbol (hΩ.preimage (continuous_id.const_smul ρ))
    (projectedStress (sourceDilation F ρ))
    (contDiffOn_sourceProjectedStress hF hrank hQ hρ)

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (Φ : HamiltonFlow (normalizedHomogeneousSymbol hΩ (projectedStress F) hQ) U)

/-- The literal determinant Hamilton flow after positive source dilation. Its
position is `ρ⁻¹ x̂(ρt,ρu,η)` and momentum is `p̂(ρt,ρu,η)`;
all equations follow from the open-domain derivative identities
(`app:ch_background:eq:bg-Nsigma`, `app:lem:common-hamilton-phase`). -/
def sourceNormalizedHamiltonFlow :
    HamiltonFlow (sourceNormalizedHamiltonSymbol hΩ hF hrank hQ hρ) U :=
  let Ψ := sourceHamiltonFlow Φ hρ.ne'
  { Ψ with
    state_mem := Ψ.state_mem
    position_derivative := by
      intro t ht s hs
      have hz := Ψ.state_mem t ht s hs
      change HasFDerivAt Ψ.position (flowDifferential
        (covectorGradient (normalizedSymbol (projectedStress (sourceDilation F ρ)))
          (Ψ.position (t, s), Ψ.momentum (t, s))) (Ψ.positionVariation (t, s))) (t, s)
      rw [covectorGradient_sourceNormalizedSymbol hΩ hF hrank hQ hρ (z := (Ψ.position (t, s), Ψ.momentum (t, s))) hz]
      exact Ψ.position_derivative t ht s hs
    momentum_derivative := by
      intro t ht s hs
      have hz := Ψ.state_mem t ht s hs
      change HasFDerivAt Ψ.momentum (flowDifferential
        (-physicalGradient (normalizedSymbol (projectedStress (sourceDilation F ρ)))
          (Ψ.position (t, s), Ψ.momentum (t, s))) (Ψ.momentumVariation (t, s))) (t, s)
      rw [physicalGradient_sourceNormalizedSymbol hΩ hF hrank hQ hρ (z := (Ψ.position (t, s), Ψ.momentum (t, s))) hz]
      exact Ψ.momentum_derivative t ht s hs
    variation_equation := by
      intro t ht s hs v
      have hz := Ψ.state_mem t ht s hs
      change HasDerivAt (fun r ↦ Ψ.positionVariation (r, s) v)
        (fderiv ℝ (covectorGradient (normalizedSymbol (projectedStress (sourceDilation F ρ))))
          (Ψ.position (t, s), Ψ.momentum (t, s))
          (Ψ.positionVariation (t, s) v, Ψ.momentumVariation (t, s) v)) t
      rw [fderiv_covectorGradient_sourceNormalizedSymbol hΩ hF hrank hQ hρ (z := (Ψ.position (t, s), Ψ.momentum (t, s))) hz]
      exact Ψ.variation_equation t ht s hs v
    initial_energy := by
      intro s hs
      have hz := Ψ.state_mem 0 Ψ.zero_mem_time s hs
      change normalizedSymbol (projectedStress (sourceDilation F ρ))
        (Ψ.position (0, s), Ψ.momentum (0, s)) = s.2.1
      rw [normalizedSymbol_sourceDilation hρ hF (Ψ.position (0, s)) (Ψ.momentum (0, s)) (hrank _ hz.1)]
      exact Ψ.initial_energy s hs }

/-- The named inverse chart of the literal determinant flow, with both inverse
identities and explicit source/target containment
(`app:ch_background:eq:bg-Nsigma`). -/
def sourceNormalizedProjectionChart (C : ProjectionChart Φ) :
    ProjectionChart (sourceNormalizedHamiltonFlow hΩ hF hrank hQ hρ Φ) :=
  { sourceProjectionChart C hρ.ne' with }

/-- The actual scaled inverse uses the divided seed coordinates
(`app:ch_background:eq:bg-Nsigma`). -/
@[simp] theorem sourceNormalizedProjectionChart_coordinates (C : ProjectionChart Φ) :
    (sourceNormalizedProjectionChart hΩ hF hrank hQ hρ Φ C).coordinates =
      sourceCoordinates C.coordinates ρ := rfl

/-- Exact identification of the literal determinant phase and the divided seed
phase (`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceNormalizedProjectionChart_phase (C : ProjectionChart Φ) :
    phase (sourceNormalizedProjectionChart hΩ hF hrank hQ hρ Φ C).coordinates =
      sourcePhase (phase C.coordinates) ρ :=
  sourceProjectionChart_phase C hρ.ne'

include hF hrank hρ in
/-- The literal determinant eikonal identity for the constructed phase
(`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceNormalizedHamiltonPhase_eikonal (C : ProjectionChart Φ)
    {x : Euclidean n} {η : ℝ × U} (hz : (ρ • x, η) ∈ C.target) :
    normalizedSymbol (projectedStress (sourceDilation F ρ))
      (x, gradient (fun y ↦ sourcePhase (phase C.coordinates) ρ (y, η)) x) = η.1 := by
  have he := (sourceNormalizedProjectionChart hΩ hF hrank hQ hρ Φ C).eikonal (z := (x, η)) hz
  rw [sourceNormalizedProjectionChart_phase] at he
  exact he

end JanetCartan.NormalizedBackground.SourceGeometry
