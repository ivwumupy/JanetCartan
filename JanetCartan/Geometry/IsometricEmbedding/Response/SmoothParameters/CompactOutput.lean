module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.SupportedResponse
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compact restrictions of the fixed smooth response

For the parameter paragraph of `app:ch_response:thm:response-literal-transfer`,
the finite Sobolev-to-uniform bound proves smooth parameter dependence in the
uniform output norm. Evaluation then gives exact commutation of every parameter
derivative with the same response. The output is the supplied representative,
restricted pointwise; no new representative or response is selected.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.ResponseSmoothParameters
open RetardedSobolev.Spaces

variable {d p : ℕ} {X G : Type*} [TopologicalSpace X]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {K : Set (ℝ × (Fin d → ℝ))} {L : Set X} [CompactSpace L]

/-- Restriction of the original physical response to the compact observation
set (`app:ch_response:prop:response-graded`). This linear map uses the original
values, including the original output cutoff and smooth representative. -/
def compactResponse
    (B : supportedTests K →ₗ[ℝ] (X → G))
    (hB : ∀ u, ContinuousOn (B u) L) : supportedTests K →ₗ[ℝ] C(L, G) where
  toFun u := ⟨fun x ↦ B u x, (hB u).comp_continuous continuous_subtype_val
    (fun x ↦ x.property)⟩
  map_add' u v := by ext x; exact congrFun (B.map_add u v) x
  map_smul' a u := by ext x; exact congrFun (B.map_smul a u) x

/-- The finite-order tame bound implies smoothness in the uniform norm on the
unchanged compact output set (`app:ch_response:prop:response-graded`). The
source order and constant precede the varying source and its parameters. -/
theorem contDiffAt_compactResponse
    {U : Set (Euclidean p)} (hU : IsOpen U) (hK : IsCompact K)
    (B : supportedTests K →ₗ[ℝ] (X → G)) (hBreg : ∀ u, ContinuousOn (B u) L)
    (s : ℕ) (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K, ∀ x ∈ L,
      ‖B u x‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ))
    (k : ℕ) {a : Euclidean p} (ha : a ∈ U) :
    ContDiffAt ℝ k (fun c ↦ compactResponse B hBreg (f c)) a := by
  apply contDiffAt_supportedResponse hU hK (compactResponse B hBreg) s _ f hf k ha
  obtain ⟨C, hC, hbound⟩ := hB
  refine ⟨C, hC, fun u ↦ (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).mpr ?_⟩
  exact fun x ↦ hbound u x x.property

/-- Every parameter derivative of the original representative is the same
response applied to the actual differentiated source, at every point of the
compact output set (`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_response_apply
    {U : Set (Euclidean p)} (hU : IsOpen U) (hK : IsCompact K)
    (B : supportedTests K →ₗ[ℝ] (X → G)) (hBreg : ∀ u, ContinuousOn (B u) L)
    (s : ℕ) (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K, ∀ x ∈ L,
      ‖B u x‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ))
    (k : ℕ) (v : Fin k → Euclidean p) {a : Euclidean p} (ha : a ∈ U)
    {x : X} (hx : x ∈ L) :
    iteratedFDeriv ℝ k (fun c ↦ B (f c) x) a v =
      B (supportedParameterTest hU hK f hf k v a ha) x := by
  have hnorm : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K,
      ‖compactResponse B hBreg u‖ ≤ C * ‖ofTest s volume u.val‖ := by
    obtain ⟨C, hC, hbound⟩ := hB
    refine ⟨C, hC, fun u ↦ (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).mpr ?_⟩
    exact fun y ↦ hbound u y y.property
  have he := congrArg (fun m ↦ m v)
    ((ContinuousMap.evalCLM ℝ (⟨x, hx⟩ : L) (M := G)).iteratedFDeriv_comp_left
      (contDiffAt_compactResponse hU hK B hBreg s hB f hf k ha) le_rfl)
  change iteratedFDeriv ℝ k (fun c ↦ B (f c) x) a v =
    (iteratedFDeriv ℝ k (fun c ↦ compactResponse B hBreg (f c)) a v) ⟨x, hx⟩ at he
  rw [iteratedFDeriv_supportedResponse hU hK (compactResponse B hBreg) s hnorm
    f hf k v ha] at he
  exact he

/-- Smooth source dependence in the uniform norm gives joint continuity of
the actual output on the original parameter domain and compact observation set
(`app:ch_response:thm:response-literal-transfer`). -/
theorem continuousOn_joint_compactResponse
    {U : Set (Euclidean p)} (hU : IsOpen U) (hK : IsCompact K)
    (B : supportedTests K →ₗ[ℝ] (X → G)) (hBreg : ∀ u, ContinuousOn (B u) L)
    (s : ℕ) (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K, ∀ x ∈ L,
      ‖B u x‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ)) :
    ContinuousOn (fun z : Euclidean p × L ↦ B (f z.1) z.2) (U ×ˢ univ) := by
  have hc : ContinuousOn (fun c ↦ compactResponse B hBreg (f c)) U :=
    fun a ha ↦ (contDiffAt_compactResponse hU hK B hBreg s hB f hf 0 ha).continuousAt.continuousWithinAt
  exact continuous_eval.comp_continuousOn
    ((hc.comp continuousOn_fst (fun _ hz ↦ hz.1)).prodMk continuousOn_snd)

end JanetCartan.ResponseSmoothParameters
