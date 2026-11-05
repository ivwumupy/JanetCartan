module

public import JanetCartan.Iteration.PhysicalBackground.OriginalProductWeights
import all JanetCartan.Iteration.PhysicalBackground.OriginalProductWeights
public meta import JanetCartan.Iteration.PhysicalBackground.OriginalOuterCutoffTemplate

/-!
# One actual original outer cutoff in the protected parameter window

Choose χ once, before σ/history/reference mean/source/raw inversion, supported
inside the original product collar intersected with the strict original patch
parameter window. It equals one on the WHOLE unchanged original carrier support.
The original row, masks, current and inverse are retained; their baseline mean
and measured source must be formed from THIS χ, not identified with the old
SourceFull weighted mean (`app:ch_background:prop:bg-current`,
`app:ch_waves:thm:sampling`, `new:sec:order-of-choices`).

The generated ABI is the already-selected original21. This module applies no
sampling or strong cap. The original22 caller passes samplingCappedExtra and
then strongCappedExtra exactly once; NativeDensity instead receives the raw
sampling-capped input because it applies its strong cap internally.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalBackground
open ContinuumRow CanonicalCarrier CanonicalConic ActualCarriers FrozenMenu
open ContinuumAdjoint.Canonical.PhaseExtension

/-- The original product collar intersected with the protected strict patch
parameter window; no physical radius or original detector is changed. -/
def originalOuterWindow (V : Set CarrierParameter) (R : ℝ) : Set CarrierParameter :=
  V ∩ parameter ⁻¹' parameterInterior R

/-- The retained full-support collar is open before any source is formed. -/
theorem originalOuterWindow_open {V : Set CarrierParameter} (hV : IsOpen V) (R : ℝ) :
    IsOpen (originalOuterWindow V R) :=
  hV.inter ((isOpen_parameterInterior R).preimage parameter.continuous)

/-- The same full native supported chart lies in the smaller parameter window;
its physical factor and all original carrier masks are unchanged. -/
theorem originalOuterWindow_supported {n : ℕ} {z : Euclidean 3} {a R S : ℝ}
    {V : Set CarrierParameter}
    (h : supportedChart (n := n) z a ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hs : MapsTo parameter (carrierSupport z (r := a)) (parameterInterior S)) :
    supportedChart (n := n) z a ⊆ ball (0 : Euclidean n) R ×ˢ originalOuterWindow V S := by
  intro p hp
  exact ⟨(h hp).1, (h hp).2, hs hp.2⟩

/-- The chosen protected weight is valid for the original current-source ABI. -/
theorem originalOuterWindow_support_original {χ : CarrierParameter → ℝ}
    {V : Set CarrierParameter} {R : ℝ}
    (h : tsupport χ ⊆ originalOuterWindow V R) : tsupport χ ⊆ V :=
  fun _ hz ↦ (h hz).1

/-- The whole outer weight support, not merely the inner angular support,
remains in the strict signed parameter domain used by the finite family. -/
theorem originalOuterWindow_support_parameter {χ : CarrierParameter → ℝ}
    {V : Set CarrierParameter} {R : ℝ}
    (h : tsupport χ ⊆ originalOuterWindow V R) :
    MapsTo parameter (tsupport χ) (parameterInterior R) :=
  fun _ hz ↦ (h hz).2

/-- The same full outer support also lies in the unchanged closed signed cube. -/
theorem originalOuterWindow_support_signed {χ : CarrierParameter → ℝ}
    {V : Set CarrierParameter} {R : ℝ}
    (h : tsupport χ ⊆ originalOuterWindow V R) :
    MapsTo parameter (tsupport χ) (parameterCube R) := by
  intro z hz j
  exact ((h hz).2 j).le

/-- Outside the protected parameter window the actual outer weight is zero;
no division by this weight or nonzero-node premise is used. -/
theorem originalOuterWindow_off_parameter {χ : CarrierParameter → ℝ}
    {V : Set CarrierParameter} {R : ℝ}
    (h : tsupport χ ⊆ originalOuterWindow V R) :
    ∀ z, parameter z ∉ parameterInterior R → χ z = 0 := by
  intro z hz
  by_contra hne
  exact hz ((h (subset_tsupport χ hne)).2)

/-- The whole original closed carrier support has the exact value one. -/
theorem originalOuterWindow_on_carrier {χ : CarrierParameter → ℝ}
    {K : Set CarrierParameter} (h : K ⊆ interior {z | χ z = 1}) :
    ∀ z ∈ K, χ z = 1 := by
  intro z hz
  change z ∈ {w | χ w = 1}
  exact interior_subset (h hz)

end JanetCartan.PhysicalBackground
end

construct_original_protected_outer_cutoff
