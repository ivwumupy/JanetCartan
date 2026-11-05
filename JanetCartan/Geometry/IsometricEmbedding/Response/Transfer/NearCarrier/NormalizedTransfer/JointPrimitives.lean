module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.JointSpatial
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Assembly.Consumer

/-!
# The producer's primitive tuple in joint transfer coordinates

`GradedPrimitives.exists_global_selected_primitives` uses `((x,y,ε),c)`.
The mixed transfer calculus uses `((c,(x,y)),ε)`. This fixed permutation has
norm one and preserves total derivative order and the selected support.
Its scalar linear extractions supply `hasFullSourceSymbolBound_frozen_expression`
and the coefficient-agreement inputs of the joint transfer assemblies for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral NearCarrierParameter GradedPrimitives
variable {n p r : ℕ} {ι : Type*}
local notation "Z" => JointAmplitudePoint n p
local notation "W" => ParameterAmplitudePoint n (Euclidean p)

local instance jointPrimitiveRealMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

local instance jointPrimitiveComplexMatrixTopology (r : ℕ) :
    TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Reorder the producer's joint variables without changing any physical
position, covector, or parameter (`app:ch_response:eq:direct-envelope-profile`). -/
def jointPrimitivePointMap : Z →L[ℝ] W :=
  ((ContinuousLinearMap.fst ℝ _ _ |>.comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))).prod
    (((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))).prod
        (ContinuousLinearMap.snd ℝ _ _))).prod
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))

/-- Literal coordinate identity for the primitive producer's buffer and
support (`app:ch_response:eq:direct-envelope-profile`). -/
@[simp] theorem jointPrimitivePointMap_apply (z : Z) :
    jointPrimitivePointMap z = ((z.1.2.1, z.1.2.2, z.2), z.1.1) := rfl

/-- Reordering spends no jet norm factor in the mixed low budget of
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jointPrimitivePointMap_le : ‖jointPrimitivePointMap (n := n) (p := p)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [jointPrimitivePointMap_apply, Prod.norm_def, one_mul]
  exact max_le
    (max_le ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
      (max_le ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
        (le_max_right _ _)))
    ((le_max_left _ _).trans (le_max_left _ _))

/-- Scalar entries of the actual global primitive tuple in the common joint
transfer coordinates. Fixed linear extractions include the selected matrix
entry, `B`, `B⁻¹`, `C`, and `-C B⁻¹` entries.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
def jointPrimitiveFields (T : ι → SelectedPrimitiveValues n r p →L[ℝ] ℂ)
    (f : W → SelectedPrimitiveValues n r p) (i : ι) : Z → ℂ :=
  T i ∘ f ∘ jointPrimitivePointMap

/-- The actual producer's smooth global tuple supplies smooth scalar joint
primitives (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_jointPrimitiveFields
    (T : ι → SelectedPrimitiveValues n r p →L[ℝ] ℂ)
    {f : W → SelectedPrimitiveValues n r p} (hf : ContDiff ℝ ∞ f) (i : ι) :
    ContDiff ℝ ∞ (jointPrimitiveFields T f i) := by
  change ContDiff ℝ ∞ (T i ∘ f ∘ jointPrimitivePointMap)
  exact (T i).contDiff.comp (hf.comp jointPrimitivePointMap.contDiff)

/-- The producer's total-order reserve survives joint reordering and scalar
entry extraction. This is precisely the primitive jet premise of
`hasFullSourceSymbolBound_frozen_expression` and the mixed Sobolev assembly,
with no added derivative order (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_jointPrimitiveFields_le
    (T : ι → SelectedPrimitiveValues n r p →L[ℝ] ℂ)
    {f : W → SelectedPrimitiveValues n r p} (hf : ContDiff ℝ ∞ f)
    {G : ℕ → ℝ} {L : ℝ} {N R : ℕ}
    (hj : ∀ j ≤ N, ∀ w, ‖iteratedFDeriv ℝ j f w‖ ≤ G j * L ^ (j + 2 - R))
    (i : ι) {j : ℕ} (hjN : j ≤ N) (z : Z) :
    ‖iteratedFDeriv ℝ j (jointPrimitiveFields T f i) z‖ ≤
      (‖T i‖ * G j) * L ^ (j + 2 - R) := by
  have hg : ContDiff ℝ ∞ (T i ∘ f) := (T i).contDiff.comp hf
  change ‖iteratedFDeriv ℝ j ((T i ∘ f) ∘ jointPrimitivePointMap) z‖ ≤ _
  rw [jointPrimitivePointMap.iteratedFDeriv_comp_right hg z (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply (mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
      (fun _ _ ↦ norm_jointPrimitivePointMap_le))).trans
  exact ((T i).norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hj j hjN _) (norm_nonneg (T i)))

/-- The producer's neighborhood agreement on its buffered selector becomes
the exact support-restricted coefficient equality used by both transfer
assemblies. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem jointPrimitiveFields_eqOn_of_eventuallyEq
    (T : ι → SelectedPrimitiveValues n r p →L[ℝ] ℂ)
    {f f₀ : W → SelectedPrimitiveValues n r p} {Ω : Set W} {K : Set Z}
    (hK : MapsTo jointPrimitivePointMap K Ω)
    (he : ∀ w ∈ Ω, f =ᶠ[𝓝 w] f₀) (i : ι) :
    EqOn (jointPrimitiveFields T f i) (jointPrimitiveFields T f₀ i) K := by
  intro z hz
  exact congrArg (T i) ((he _ (hK hz)).eq_of_nhds)

end JanetCartan.ResponseTransfer.NormalizedTransfer
