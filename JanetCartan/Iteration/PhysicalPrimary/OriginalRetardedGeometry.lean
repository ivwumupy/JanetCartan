module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers.Carriers
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedGeometryTemplate

/-!
# Actual original retarded source and physical boxes

Discharge the source-support, full physical-footprint and time-window premises
of the whole-source retarded constructors from the SAME native family. The
small source is the literal `tsupport χ₂`; neither the complex retarded input
mask nor the final output measurement is substituted for it. The critical
window may be restricted to the native mask radius, but the actual operator's
ENTIRE elapsed interval `[0, 3*maskRadius/4]` is unchanged.

Consumers: the native specialization of `CharacteristicPaired` and the exact
complete residual/solver one-step constructors
(`app:ch_response:eq:fixed-factor-transfer`, `app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 12000
open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.PhysicalPrimary.OriginalRetardedGeometry
open CompatibleResponse RegularSector.Characteristic.ResidualCoordinates

/-- Use only the native input plateau on the actual source, not a fictitious
compact cutoff equal to one on the entire physical space. -/
theorem physical_source_preimage_subset {d : ℕ} (i : Fin (d+1))
    {S U : Set (Euclidean (d+1))} {μ ν : Euclidean (d+1) → ℝ}
    (hplateau : ∀ y ∈ S, μ =ᶠ[𝓝 y] (fun _ ↦ 1))
    (hbox : MapsTo (primaryCoordinateChange i) (tsupport μ ∪ tsupport ν) U) :
    (physicalCoordinates i) ⁻¹' S ⊆ U := by
  intro y hy
  have hmem : physicalCoordinates i y ∈ tsupport μ :=
    subset_tsupport μ (show physicalCoordinates i y ∈ Function.support μ from by
      change μ (physicalCoordinates i y) ≠ 0
      rw [(hplateau _ hy).self_of_nhds]
      exact one_ne_zero)
  have h := hbox (x := physicalCoordinates i y) (Or.inl hmem)
  simpa only [primaryCoordinateChange, physicalCoordinates,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h

/-- The original full elapsed interval fits the smaller critical window, which
is contained in the native stationary window. No operator is shortened. -/
theorem native_mask_time_interval {r τ : ℝ} (hr : 0 < r) (hτ : r ≤ τ) :
    Icc (0 : ℝ) (3*r/4) ⊆ Ioo (-2*r) (2*r) ∧
      Ioo (-2*r) (2*r) ⊆ Ioo (-2*τ) (2*τ) := by
  constructor
  · intro t ht
    constructor <;> linarith [ht.1,ht.2]
  · intro t ht
    constructor <;> linarith [ht.1,ht.2]

retain_original_retarded_source_geometry
retain_original_retarded_physical_footprints

end JanetCartan.PhysicalPrimary.OriginalRetardedGeometry
