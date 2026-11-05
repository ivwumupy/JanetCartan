module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Hamilton.Symbol

/-!
# The source-dilated Hamilton flow

Constructs the flow and its first variational equation used in
`app:ch_background:eq:bg-Nsigma` from the genuine seed flow. No scaled
Hamilton equation or conserved quantity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology InnerProductSpace

namespace JanetCartan.NormalizedBackground.SourceGeometry
open HamiltonPhase

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Scale Hamilton time and section position, retaining the canonical label
(`app:ch_background:eq:bg-Nsigma`). -/
def sourceFlowMap (ρ : ℝ) : ℝ × InitialData U →L[ℝ] ℝ × InitialData U :=
  (ρ • ContinuousLinearMap.fst ℝ ℝ (InitialData U)).prod
    ((sourceDilationMap ρ).comp (ContinuousLinearMap.snd ℝ ℝ (InitialData U)))

@[simp] theorem sourceFlowMap_apply (ρ : ℝ) (q : ℝ × InitialData U) :
    sourceFlowMap ρ q = (ρ * q.1, (ρ • q.2.1, q.2.2)) := rfl

/-- The genuine rescaled Hamilton flow, including its first variation
(`app:lem:common-hamilton-phase`, `app:ch_background:eq:bg-Nsigma`). -/
def sourceHamiltonFlow {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)
    {ρ : ℝ} (hρ : ρ ≠ 0) : HamiltonFlow (sourceHamiltonSymbol H ρ) U where
  time := (fun t ↦ ρ * t) ⁻¹' Φ.time
  isOpen_time := Φ.isOpen_time.preimage (continuous_const.mul continuous_id)
  isPreconnected_time := by
    exact (Homeomorph.smul (α := ℝ) (Units.mk0 ρ hρ)).isPreconnected_preimage.mpr
      Φ.isPreconnected_time
  zero_mem_time := by simpa using Φ.zero_mem_time
  parameters := sourceDilationMap ρ ⁻¹' Φ.parameters
  isOpen_parameters := Φ.isOpen_parameters.preimage (sourceDilationMap ρ).continuous
  sectionMap := Φ.sectionMap
  position q := ρ⁻¹ • Φ.position (sourceFlowMap ρ q)
  momentum q := Φ.momentum (sourceFlowMap ρ q)
  positionVariation q := ρ⁻¹ • (Φ.positionVariation (sourceFlowMap ρ q)).comp (sourceDilationMap ρ)
  momentumVariation q := (Φ.momentumVariation (sourceFlowMap ρ q)).comp (sourceDilationMap ρ)
  state_mem := by
    intro t ht s hs
    simpa [sourceHamiltonSymbol, smul_smul, hρ] using Φ.state_mem _ ht _ hs
  position_derivative := by
    intro t ht s hs
    have hd := ((Φ.position_derivative _ ht _ hs).comp (t, s)
      (sourceFlowMap (U := U) ρ).hasFDerivAt).const_smul ρ⁻¹
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [sourceHamiltonSymbol, flowDifferential, smul_add, smul_smul, hρ]
  momentum_derivative := by
    intro t ht s hs
    have hd := (Φ.momentum_derivative _ ht _ hs).comp (t, s)
      (sourceFlowMap (U := U) ρ).hasFDerivAt
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [sourceHamiltonSymbol, flowDifferential, smul_smul, hρ, mul_comm]
  variation_equation := by
    intro t ht s hs v
    have hd := ((Φ.variation_equation _ ht _ hs (sourceDilationMap ρ v)).scomp t
      ((hasDerivAt_id t).const_mul ρ))
    have hd := HasDerivAt.const_smul ρ⁻¹ hd
    convert! hd using 1
    simp [sourceHamiltonSymbol, smul_smul, hρ]
  initial_position := by
    intro s hs
    simpa [smul_smul, hρ] using congrArg (fun x ↦ ρ⁻¹ • x) (Φ.initial_position _ hs)
  initial_energy := by
    intro s hs
    simpa [sourceHamiltonSymbol, smul_smul, hρ] using Φ.initial_energy _ hs
  initial_momentum := by
    intro s hs v
    simpa using Φ.initial_momentum _ hs v

end JanetCartan.NormalizedBackground.SourceGeometry
