module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Phase

/-!
# Hamilton symbol pulled back by source dilation

The intermediate symbol used to construct the named Hamilton chart in
`app:ch_background:eq:bg-Nsigma`. Its derivative fields are computed by the
chain rule. The literal projected determinant is identified on its full-rank
open domain in `Hamilton.Determinant`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology InnerProductSpace

namespace JanetCartan.NormalizedBackground.SourceGeometry
open HamiltonPhase

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Scale the physical component, keeping the label unchanged
(`app:ch_background:eq:bg-Nsigma`). -/
def sourceDilationMap (ρ : ℝ) : E × V →L[ℝ] E × V :=
  (ρ • ContinuousLinearMap.fst ℝ E V).prod (ContinuousLinearMap.snd ℝ E V)

@[simp] theorem sourceDilationMap_apply (ρ : ℝ) (z : E × V) :
    sourceDilationMap (E := E) (V := V) ρ z = (ρ • z.1, z.2) := rfl

/-- The chain-rule Hamilton symbol for physical source dilation
(`app:ch_background:eq:bg-Nsigma`). -/
def sourceHamiltonSymbol (H : HomogeneousSymbol E) (ρ : ℝ) : HomogeneousSymbol E where
  domain := sourceDilationMap (E := E) (V := E) ρ ⁻¹' H.domain
  isOpen_domain := H.isOpen_domain.preimage (sourceDilationMap (E := E) (V := E) ρ).continuous
  h z := H.h (sourceDilationMap (E := E) (V := E) ρ z)
  hx z := ρ • H.hx (sourceDilationMap (E := E) (V := E) ρ z)
  hp z := H.hp (sourceDilationMap (E := E) (V := E) ρ z)
  hpDerivative z := (H.hpDerivative (sourceDilationMap (E := E) (V := E) ρ z)).comp (sourceDilationMap (E := E) (V := E) ρ)
  hasFDerivAt_h := by
    intro z hz
    convert! (H.hasFDerivAt_h _ hz).comp z (sourceDilationMap (E := E) (V := E) ρ).hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [hamiltonDifferential]
  hasFDerivAt_hp := by
    intro z hz
    exact (H.hasFDerivAt_hp _ hz).comp z (sourceDilationMap (E := E) (V := E) ρ).hasFDerivAt
  homogeneous := by
    intro z hz
    exact H.homogeneous _ hz

end JanetCartan.NormalizedBackground.SourceGeometry
