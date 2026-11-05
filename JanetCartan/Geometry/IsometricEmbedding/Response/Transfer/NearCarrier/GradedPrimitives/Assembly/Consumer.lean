module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Assembly.Literal
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SymbolBudget

/-!
# Matrix primitive families for the expression consumer

A fixed linear extraction from the actual primitive tuple preserves its global
reserve, as does freezing a compact parameter. The reassociation retains both
physical positions and uses the exact `FullAmplitudePrimitiveBudget.Point`
domain consumed by `SymbolBudget` and `BranchRealization`.

The analytic input in these final algebraic adapters is the global tuple profile
proved by `exists_global_selected_primitives` or `exists_global_literal_primitives`.
No new geometry or inverse/coefficient estimate is required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives
open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local

local instance consumerRealMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

local instance consumerComplexMatrixTopology (r : ℕ) :
    TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Linear part of freezing the carrier parameter, retaining both physical
positions in `app:ch_response:eq:direct-envelope-profile`. -/
def primitiveParameterEmbedding (n p : ℕ) :
    Point n →L[ℝ] ParameterAmplitudePoint n (Euclidean p) :=
  (((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      (ContinuousLinearMap.snd ℝ _ _))).prod 0

/-- The affine slice used by the fixed-parameter graph calculus
(`app:ch_response:eq:direct-envelope-profile`). -/
def primitiveParameterSlice {n p : ℕ} (c : Euclidean p) (w : Point n) :
    ParameterAmplitudePoint n (Euclidean p) := ((w.1.1, w.1.2, w.2), c)

/-- Freezing the parameter costs no positive derivative norm in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_primitiveParameterEmbedding_le (n p : ℕ) :
    ‖primitiveParameterEmbedding n p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  change ‖((w.1.1, w.1.2, w.2), (0 : Euclidean p))‖ ≤ 1 * ‖w‖
  simp only [Prod.norm_def, norm_zero, one_mul]
  exact max_le (max_le ((norm_fst_le w.1).trans (norm_fst_le w))
    (max_le ((norm_snd_le w.1).trans (norm_fst_le w)) (norm_snd_le w))) (by simpa only [Prod.norm_def] using norm_nonneg w)

/-- Fixed linear extraction of the assembled primitive tuple gives the exact
smooth matrix family and global jets required by
`NearCarrierSymbol.hasFullSourceSymbolBound_of_expression`. This preserves all
joint parameter derivatives (`app:ch_response:eq:direct-envelope-profile`). -/
theorem primitive_linear_extractions {n r p : ℕ} {ι : Type*}
    (T : ι → SelectedPrimitiveValues n r p →L[ℝ] Matrix (Fin r) (Fin r) ℂ)
    {f : ParameterAmplitudePoint n (Euclidean p) → SelectedPrimitiveValues n r p}
    (hf : ContDiff ℝ ∞ f) {G : ℕ → ℝ} (hG : ∀ j, 0 ≤ G j)
    {L : ℝ} {N Rstar : ℕ}
    (hjet : ∀ j ≤ N, ∀ w, ‖iteratedFDeriv ℝ j f w‖ ≤ G j * L ^ (j + 2 - Rstar)) :
    (∀ i, ContDiff ℝ ∞ (T i ∘ f)) ∧
    (∀ i j, 0 ≤ ‖T i‖ * G j) ∧
    ∀ i j, j ≤ N → ∀ w, ‖iteratedFDeriv ℝ j (T i ∘ f) w‖ ≤
      (‖T i‖ * G j) * L ^ (j + 2 - Rstar) := by
  refine ⟨fun i ↦ (T i).contDiff.comp hf, fun i j ↦ mul_nonneg (norm_nonneg _) (hG j), ?_⟩
  intro i j hj w
  exact ((T i).norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hjet j hj w) (norm_nonneg (T i)))

/-- Freezing a compact parameter and reassociating the positions preserves the
full derivative budget; the profile is uniform in the chosen parameter.
The producer is `exists_global_selected_primitives` (or its literal inverse
specialization), whose global tuple is the `f` used here. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem primitive_slices_for_expression {n r p : ℕ} {ι : Type*}
    (T : ι → SelectedPrimitiveValues n r p →L[ℝ] Matrix (Fin r) (Fin r) ℂ)
    {f : ParameterAmplitudePoint n (Euclidean p) → SelectedPrimitiveValues n r p}
    (hf : ContDiff ℝ ∞ f) {G : ℕ → ℝ} (hG : ∀ j, 0 ≤ G j)
    {L : ℝ} {N Rstar : ℕ}
    (hjet : ∀ j ≤ N, ∀ w, ‖iteratedFDeriv ℝ j f w‖ ≤ G j * L ^ (j + 2 - Rstar))
    (c : Euclidean p) :
    (∀ i, ContDiff ℝ ∞ (T i ∘ f ∘ primitiveParameterSlice c)) ∧
    (∀ i j, 0 ≤ ‖T i‖ * G j) ∧
    ∀ i j, j ≤ N → ∀ w, ‖iteratedFDeriv ℝ j (T i ∘ f ∘ primitiveParameterSlice c) w‖ ≤
      (‖T i‖ * G j) * L ^ (j + 2 - Rstar) := by
  have hex := primitive_linear_extractions T hf hG hjet
  let offset : ParameterAmplitudePoint n (Euclidean p) := (0, c)
  have he : primitiveParameterSlice c = fun w ↦ primitiveParameterEmbedding n p w + offset := by
    funext w
    simp [primitiveParameterSlice, primitiveParameterEmbedding, offset]
  have hs : ContDiff ℝ ∞ (primitiveParameterSlice (n := n) c) := by
    rw [he]
    exact (primitiveParameterEmbedding n p).contDiff.add contDiff_const
  refine ⟨fun i ↦ (hex.1 i).comp hs, hex.2.1, ?_⟩
  intro i j hj w
  let g := fun z : ParameterAmplitudePoint n (Euclidean p) ↦ (T i ∘ f) (z + offset)
  have hg : ContDiff ℝ ∞ g := (hex.1 i).comp (contDiff_id.add contDiff_const)
  have hbound := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (primitiveParameterEmbedding n p) isOpen_univ hg.contDiffOn (x := w) (mem_univ _) j
  have hbound' := hbound.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_primitiveParameterEmbedding_le n p)))
  change ‖iteratedFDeriv ℝ j (T i ∘ f ∘ primitiveParameterSlice c) w‖ ≤ _
  rw [he]
  apply hbound'.trans
  dsimp only [g]
  rw [iteratedFDeriv_comp_add_right]
  exact hex.2.2 i j hj _

end JanetCartan.ResponseTransfer.GradedPrimitives
