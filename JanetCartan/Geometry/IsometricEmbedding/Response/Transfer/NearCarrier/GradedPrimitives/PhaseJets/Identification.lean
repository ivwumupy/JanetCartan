module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.PhaseJets.Contractions

/-!
# Identifying the actual partial phase Hessians locally

The two contractions below recover the literal phase derivatives used in
`app:ch_response:eq:direct-envelope-profile`. All differentiations take
place in the open buffered chart; the phase need not extend smoothly across
the zero covector. These identities supply `PhaseJets` and hence the mixed
inverse and parameter-coefficient deductions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives

variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {X D : Set (Euclidean n)}

/-- The actual mixed phase matrix is a fixed contraction of the joint
Hessian on the annular chart (`app:ch_response:eq:direct-envelope-profile`). -/
theorem mixedPhaseMatrix_eq_jointHessian_contraction
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    FourierIntegral.mixedPhaseMatrix S q.1 q.2 =
      mixedHessianContraction n (fderiv ℝ (fderiv ℝ (Function.uncurry S)) q) := by
  have h := hS.contDiffAt ((hX.prod hD).mem_nhds hq)
  have hd := (h.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  ext i j
  have he : (fun η ↦ partialDeriv (fun x ↦ S x η) q.1 i) =ᶠ[𝓝 q.2]
      (fun η ↦ fderiv ℝ (Function.uncurry S) (q.1, η) (EuclideanSpace.single i 1, 0)) := by
    filter_upwards [hD.mem_nhds hq.2] with η hη
    have hi := (((hS.contDiffAt (x := (q.1, η)) ((hX.prod hD).mem_nhds ⟨hq.1, hη⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 η)).fderiv
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hi
  have hi := ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ), (0 : Euclidean n))).hasFDerivAt.comp
    q.2 (hd.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2))).fderiv
  change (fderiv ℝ (fun η ↦ partialDeriv (fun x ↦ S x η) q.1 i) q.2)
    (EuclideanSpace.single j 1) = _
  rw [he.fderiv_eq]
  exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single j 1)) hi

/-- The literal covector Hessian is the restriction of both slots of the
joint Hessian (`app:ch_response:eq:direct-envelope-profile`). -/
theorem covectorHessian_eq_jointHessian_contraction
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    fderiv ℝ (fderiv ℝ (S q.1)) q.2 =
      covectorHessianContraction n (fderiv ℝ (fderiv ℝ (Function.uncurry S)) q) := by
  let R : ((Euclidean n × Euclidean n) →L[ℝ] ℝ) →L[ℝ] (Euclidean n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n × Euclidean n) ℝ).flip
      (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n))
  have h := hS.contDiffAt ((hX.prod hD).mem_nhds hq)
  have hd := (h.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : fderiv ℝ (S q.1) =ᶠ[𝓝 q.2]
      (fun η ↦ R (fderiv ℝ (Function.uncurry S) (q.1, η))) := by
    filter_upwards [hD.mem_nhds hq.2] with η hη
    exact (((hS.contDiffAt (x := (q.1, η)) ((hX.prod hD).mem_nhds ⟨hq.1, hη⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp η (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 η)).fderiv
  rw [he.fderiv_eq]
  exact (R.hasFDerivAt.comp q.2
    (hd.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2))).fderiv

end JanetCartan.ResponseTransfer.GradedPrimitives
