module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.HilbertLift
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization
public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Local

/-!
# Parameter derivatives of a fixed response on supported sources

The source derivatives are the actual derivatives furnished by
`Retarded.ParameterRealization`, for `app:ch_response:thm:response-literal-transfer`.
Only the fixed response's finite-order norm bound is an analytic producer input.
The support, source measure, response, and derivative source are unchanged.
This is the norm-valued step toward joint output regularity in CorrectedAtoms.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.ResponseSmoothParameters
open RetardedSobolev.Spaces ResponseTransfer.ParameterRealization

variable {d p : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G]

/-- The finite Hilbert product of the original Lebesgue jets, used only for
the extension step of `app:ch_response:thm:response-literal-transfer`. -/
private abbrev JetHilbert (d s : ℕ) :=
  PiLp 2 (fun _ : JetIndex d s ↦ Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ)))

/-- Include the existing Sobolev completion in the equivalent Hilbert product
without changing any jet (`app:ch_response:thm:response-literal-transfer`). -/
private def jetHilbertInclusion (s : ℕ) :
    Sobolev s (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℝ] JetHilbert d s :=
  (((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap).comp
    (sobolevSubmodule s volume).subtypeL).restrictScalars ℝ

/-- The finite Hilbert norm controls the original product norm, so the
producer's bound transfers (`app:ch_response:prop:response-graded`). -/
private theorem norm_le_jetHilbertInclusion (s : ℕ)
    (u : Sobolev s (volume : Measure ((Fin d → ℝ) × ℝ))) :
    ‖u‖ ≤ ‖jetHilbertInclusion s u‖ := by
  change ‖u.val‖ ≤ _
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun i ↦ PiLp.norm_apply_le (jetHilbertInclusion s u) i)

/-- The actual parameter derivative remains in the SAME supported test space
(`app:ch_response:thm:response-literal-transfer`). This uses the classical
support theorem, rather than an assumed derivative-source admission. -/
def supportedParameterTest
    {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ))
    (k : ℕ) (v : Fin k → Euclidean p) (a : Euclidean p) (ha : a ∈ U) :
    supportedTests K :=
  ⟨parameterTest hU hK (fun c ↦ (f c).val.val) hf
      (fun c _ ↦ (f c).property) k v a ha,
    tsupport_parameterField_subset hU hK.isClosed (fun c _ ↦ (f c).property) k v ha⟩

/-- A jointly smooth supported source family becomes smooth after the SAME
fixed response, in any Banach output norm controlled by a finite Sobolev source
norm (`app:ch_response:prop:response-graded`). In particular the output may be
the uniform norm of a spatial jet on a fixed compact observation set. -/
theorem contDiffAt_supportedResponse
    {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (B : supportedTests K →ₗ[ℝ] G) (s : ℕ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K,
      ‖B u‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ))
    (k : ℕ) {a : Euclidean p} (ha : a ∈ U) :
    ContDiffAt ℝ k (fun c ↦ B (f c)) a := by
  let j : supportedTests K →ₗ[ℝ] JetHilbert d s :=
    (jetHilbertInclusion s).toLinearMap.comp
      (((ofTest s volume).comp (supportedTests K).subtype).restrictScalars ℝ)
  refine contDiffAt_response_of_hilbert_bound j B ?_ (f := f) (k := k) ?_
  · obtain ⟨C, hC, hCbound⟩ := hB
    exact ⟨C, fun u ↦ (hCbound u).trans
      (mul_le_mul_of_nonneg_left (norm_le_jetHilbertInclusion s _) hC)⟩
  · exact (jetHilbertInclusion s).contDiff.contDiffAt.comp a
      (contDiffAt_ofTest_of_commonCompactSupport hU hK (fun c ↦ (f c).val) hf
        (fun c _ ↦ (f c).property) s k ha)

/-- All evaluated parameter derivatives commute with the fixed response.
The right hand side uses its actual classical parameter derivative, with the
same compact source support and Lebesgue measure
(`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_supportedResponse
    {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (B : supportedTests K →ₗ[ℝ] G) (s : ℕ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K,
      ‖B u‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ))
    (k : ℕ) (v : Fin k → Euclidean p) {a : Euclidean p} (ha : a ∈ U) :
    iteratedFDeriv ℝ k (fun c ↦ B (f c)) a v =
      B (supportedParameterTest hU hK f hf k v a ha) := by
  let j : supportedTests K →ₗ[ℝ] JetHilbert d s :=
    (jetHilbertInclusion s).toLinearMap.comp
      (((ofTest s volume).comp (supportedTests K).subtype).restrictScalars ℝ)
  have hsource := contDiffAt_ofTest_of_commonCompactSupport hU hK
    (fun c ↦ (f c).val) hf (fun c _ ↦ (f c).property) s k ha
  refine iteratedFDeriv_response_eq_of_hilbert_bound j B ?_ k v
    (supportedParameterTest hU hK f hf k v a ha) ?_ ?_
  · obtain ⟨C, hC, hCbound⟩ := hB
    exact ⟨C, fun u ↦ (hCbound u).trans
      (mul_le_mul_of_nonneg_left (norm_le_jetHilbertInclusion s _) hC)⟩
  · exact (jetHilbertInclusion s).contDiff.contDiffAt.comp a hsource
  · have he := congrArg (fun m ↦ m v)
      ((jetHilbertInclusion s).iteratedFDeriv_comp_left hsource le_rfl)
    change iteratedFDeriv ℝ k (fun c ↦ j (f c)) a v =
      jetHilbertInclusion s (iteratedFDeriv ℝ k
        (fun c ↦ ofTest s volume (f c).val) a v) at he
    rw [iteratedFDeriv_ofTest_eq_ofTest_parameterTest hU hK
      (fun c ↦ (f c).val) hf (fun c _ ↦ (f c).property) s k v a ha] at he
    exact he

end JanetCartan.ResponseSmoothParameters
