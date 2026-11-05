module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Hamilton.Symbol

/-!
# Derivative scaling for the literal projected determinant

The pointwise stress-frame identity is used on an open full-normal-rank
neighborhood before differentiating. These results identify the intermediate
Hamilton symbol with the actual source-dilated determinant in
`app:ch_background:eq:bg-Nsigma`.
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

include hF hrank hQ hρ in
/-- Smoothness of the actual scaled frame follows from the seed frame and the
proved stress identity (`app:ch_background:eq:bg-Nsigma`). -/
theorem contDiffOn_sourceProjectedStress :
    ContDiffOn ℝ ∞ (projectedStress (sourceDilation F ρ)) ((fun x ↦ ρ • x) ⁻¹' Ω) := by
  apply (hQ.comp (contDiff_id.const_smul ρ).contDiffOn (fun _ hx ↦ hx)).congr
  intro x hx
  exact funext fun i ↦ projectedStress_sourceDilation hρ hF x (hrank _ hx) i

include hΩ hF hrank hρ in
/-- Equality on a neighborhood, not just at a point, permits differentiation of
`app:ch_background:eq:bg-Nsigma`. -/
theorem normalizedSymbol_sourceDilation_eventuallyEq {z : Euclidean n × Euclidean n}
    (hz : ρ • z.1 ∈ Ω) :
    normalizedSymbol (projectedStress (sourceDilation F ρ)) =ᶠ[𝓝 z]
      (fun w ↦ normalizedSymbol (projectedStress F) (ρ • w.1, w.2)) := by
  have ho : IsOpen {w : Euclidean n × Euclidean n | ρ • w.1 ∈ Ω} :=
    hΩ.preimage (continuous_fst.const_smul ρ)
  filter_upwards [ho.mem_nhds hz] with w hw
  exact normalizedSymbol_sourceDilation hρ hF w.1 w.2 (hrank _ hw)

include hΩ hF hrank hQ hρ

/-- Full differential of the literal source determinant, derived on the open
full-rank domain (`app:ch_background:eq:bg-Nsigma`). -/
theorem hasFDerivAt_sourceNormalizedSymbol {z : Euclidean n × Euclidean n}
    (hz : (ρ • z.1, z.2) ∈ normalizedSymbolDomain Ω) :
    HasFDerivAt (normalizedSymbol (projectedStress (sourceDilation F ρ)))
      (hamiltonDifferential
        (ρ • physicalGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2))
        (covectorGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2))) z := by
  exact ((sourceHamiltonSymbol (normalizedHomogeneousSymbol hΩ (projectedStress F) hQ) ρ).hasFDerivAt_h z hz).congr_of_eventuallyEq
      (normalizedSymbol_sourceDilation_eventuallyEq hΩ hF hrank hρ hz.1)

/-- Physical gradient gains exactly one source factor
(`app:ch_background:eq:bg-Nsigma`). -/
theorem physicalGradient_sourceNormalizedSymbol {z : Euclidean n × Euclidean n}
    (hz : (ρ • z.1, z.2) ∈ normalizedSymbolDomain Ω) :
    physicalGradient (normalizedSymbol (projectedStress (sourceDilation F ρ))) z =
      ρ • physicalGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2) := by
  rw [physicalGradient, (hasFDerivAt_sourceNormalizedSymbol hΩ hF hrank hQ hρ hz).fderiv]
  have he : (hamiltonDifferential
      (ρ • physicalGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2))
      (covectorGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2))).comp
      (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean n)) =
      InnerProductSpace.toDual ℝ (Euclidean n)
        (ρ • physicalGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2)) := by
    ext v
    simp [real_inner_smul_left]
  rw [he, LinearIsometryEquiv.symm_apply_apply]

/-- The Hamilton velocity is the unscaled covector gradient at the dilated point
(`app:ch_background:eq:bg-Nsigma`). -/
theorem covectorGradient_sourceNormalizedSymbol {z : Euclidean n × Euclidean n}
    (hz : (ρ • z.1, z.2) ∈ normalizedSymbolDomain Ω) :
    covectorGradient (normalizedSymbol (projectedStress (sourceDilation F ρ))) z =
      covectorGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2) := by
  rw [covectorGradient, (hasFDerivAt_sourceNormalizedSymbol hΩ hF hrank hQ hρ hz).fderiv]
  have he : (hamiltonDifferential
      (ρ • physicalGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2))
      (covectorGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2))).comp
      (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n)) =
      InnerProductSpace.toDual ℝ (Euclidean n)
        (covectorGradient (normalizedSymbol (projectedStress F)) (ρ • z.1, z.2)) := by
    ext v
    simp
  rw [he, LinearIsometryEquiv.symm_apply_apply]

/-- The velocity derivative required by the variational equation is also the
literal determinant derivative (`app:lem:common-hamilton-phase`). -/
theorem fderiv_covectorGradient_sourceNormalizedSymbol {z : Euclidean n × Euclidean n}
    (hz : (ρ • z.1, z.2) ∈ normalizedSymbolDomain Ω) :
    fderiv ℝ (covectorGradient (normalizedSymbol (projectedStress (sourceDilation F ρ)))) z =
      (fderiv ℝ (covectorGradient (normalizedSymbol (projectedStress F)))
        (ρ • z.1, z.2)).comp (sourceDilationMap ρ) := by
  let H := sourceHamiltonSymbol (normalizedHomogeneousSymbol hΩ (projectedStress F) hQ) ρ
  have he : covectorGradient (normalizedSymbol (projectedStress (sourceDilation F ρ)))
      =ᶠ[𝓝 z] H.hp := by
    filter_upwards [H.isOpen_domain.mem_nhds hz] with w hw
    exact covectorGradient_sourceNormalizedSymbol hΩ hF hrank hQ hρ hw
  exact ((H.hasFDerivAt_hp z hz).congr_of_eventuallyEq he).fderiv

end JanetCartan.NormalizedBackground.SourceGeometry
