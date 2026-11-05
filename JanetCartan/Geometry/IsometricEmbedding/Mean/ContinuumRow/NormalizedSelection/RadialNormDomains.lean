module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RadialInputGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.Canonical

/-!
# Original coefficient domains on the full radial input domain

The radial extension changes only frequency. Every endpoint and physical
segment therefore remains in its original coefficient or scalar chart. This
supplies the endpoint domain of the normalized normal limit on the same
full input cone used by the common inverse.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormalReduction.TransportSymbol
open ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity

/-- The same original field or scalar domain contains the physical endpoint
throughout the radial extension. This is `hend` in
`NormalizedNormalLimit.exists_source_family_half_gap`; no frequency-dependent
extension of the scalar is used (`bg-full-complex-amplitude`, `bg-mixed-input`). -/
theorem mapsTo_densityEndpoint_radialInputDomain {n : ℕ} (side : Bool)
    {W : Set (InputVariables n)} {E : Set (Euclidean n × CarrierParameter)}
    (h : MapsTo (densityEndpoint side) W E) :
    MapsTo (densityEndpoint side) (radialInputDomain W) E := by
  rintro p ⟨t, _, hp⟩
  simpa only [densityEndpoint, scaleInput] using h hp

/-- The same original segment buffer contains all physical segments after
radial extension. The time parameter is unchanged, so both the closed unit
interval and any supplied open time buffer are retained (`bg-Psi`,
`bg-mixed-input`). -/
theorem mapsTo_transportSegmentInput_radialInputDomain {n : ℕ} (t : ℝ)
    {W : Set (InputVariables n)} {E : Set (Euclidean n × CarrierParameter)}
    (h : MapsTo (transportSegmentInput n t) W E) :
    MapsTo (transportSegmentInput n t) (radialInputDomain W) E := by
  rintro p ⟨r, _, hp⟩
  simpa only [transportSegmentInput_apply, scaleInput] using h hp

end JanetCartan.ContinuumRow.NormalizedSelection
