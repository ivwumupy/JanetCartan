module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.ConicZeroTimeHessian

/-!
# Initial data for the uniform retained stationary branch

Both literal orientations use the same retained conic chart. Its original
projection and initial condition give the stationary diagonal and its explicit
inverse Hessian, on the normalized domain without a raw-frequency restriction.
Consumer: the uniform stationary construction for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ResponseTransfer.RetainedFactors
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open DirectEvolution EvolutionIntegral.KernelIdentification

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "W" => CarrierVariables (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- The original retained phase is stationary at the primary diagonal at
zero elapsed time, in either literal orientation. The identity uses only
the same chart's projection, source and flow initial condition
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_conic_zeroTime_stationary
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    (φ : E → Euclidean 3 → ℝ) (q : E × Euclidean 3)
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y q.2) q.1)
    (hgraph : elapsedChartPoint 0 q.1 (gradient (fun y ↦ φ y q.2) q.1) ∈
      domain ℓ C.target) :
    gradient (fun w ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((0, q), w))
      (WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) = 0 := by
  let w : W := WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)
  have he := retained_conic_zeroTime_orientations_eventuallyEq adj ℓ hC hsource hi φ q
    (w := w) hgraph (by simpa [carrierGraphPoint, w, elapsedChartPoint] using hgraph)
  have hp : Continuous (fun v : W ↦ (((0 : ℝ), q), v)) :=
    continuous_const.prodMk continuous_id
  have hm := ((contDiff_carrierGraphPoint false).continuous.comp hp).continuousAt
    (x := w) |>.preimage_mem_nhds
    ((isOpen_domain ℓ C.open_target).mem_nhds hgraph)
  have he' : elapsedCarrierPhase (curriedPhase ℓ C) 0 φ q =ᶠ[𝓝 w]
      carrierPhase (fun x θ : E ↦ inner ℝ x θ) φ q := by
    filter_upwards [hm] with v hv
    exact congrArg (fun r ↦ r - inner ℝ v.fst v.snd + φ v.fst q.2 - φ q.1 q.2)
      (retained_conic_elapsedPhase_zero ℓ hC hsource hi hv)
  rw [he.gradient_eq, he'.gradient_eq]
  have hz := (WithLp.fstL 2 ℝ E E).hasFDerivAt (x := w)
  have hθ := (WithLp.sndL 2 ℝ E E).hasFDerivAt (x := w)
  have hd := (((((hasFDerivAt_const (𝕜 := ℝ) q.1 w).inner ℝ hθ).sub
    (hz.inner ℝ hθ)).add (hφ.hasFDerivAt.comp w hz)).sub_const (φ q.1 q.2))
  have hg : HasGradientAt (carrierPhase (fun x θ : E ↦ inner ℝ x θ) φ q) 0 w := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [map_zero, zero_apply, add_apply, sub_apply,
      ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, inner_zero_left, add_zero,
      WithLp.fstL_apply, WithLp.sndL_apply, ← inner_gradient_left]
    change 0 = inner ℝ q.1 v.snd -
      (inner ℝ q.1 v.snd + inner ℝ v.fst (gradient (fun y ↦ φ y q.2) q.1)) +
        inner ℝ (gradient (fun y ↦ φ y q.2) q.1) v.fst
    rw [real_inner_comm v.fst]
    ring
  exact hg.gradient

/-- Both literal zero-time Hessians are the same explicit invertible block
on their original normalized domains. This is the initial linearization of
the uniform stationary branch (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_conic_zeroTime_hessian_orientation
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    (q : E × Euclidean 3) {w : W} (hw : (w.fst, q.2) ∈ Ω)
    (hout : carrierGraphPoint false ((0, q), w) ∈ domain ℓ C.target)
    (hsrc : carrierGraphPoint true ((0, q), w) ∈ domain ℓ C.target) :
    fderiv ℝ (gradient (fun v ↦
      jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((0, q), v))) w =
      (retainedDiagonalHessianEquiv
        (fderiv ℝ (gradient (fun y ↦ φ y q.2)) w.fst)).toContinuousLinearMap := by
  rw [(retained_conic_zeroTime_orientations_eventuallyEq adj ℓ hC hsource hi φ q
    hout hsrc).gradient.fderiv_eq]
  exact retained_conic_zeroTime_hessian_of_normalized_domain ℓ hC hsource hi hΩ hφ hw hout

/-- The primary second-jet budget gives an explicit inverse bound at the
stationary diagonal. The budget can be fixed before the primary phase and
retained chart by `HistoryPrimaryPhaseJets`; it is not an inverse assumption
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_conic_zeroTime_stationary_inverse_bound
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {q : E × Euclidean 3} (hq : q ∈ Ω) {B : ℝ}
    (hB : ‖iteratedFDeriv ℝ 2 (Function.uncurry φ) q‖ ≤ B)
    (hgraph : elapsedChartPoint 0 q.1 (gradient (fun y ↦ φ y q.2) q.1) ∈
      domain ℓ C.target) :
    let w : W := WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)
    let H := fderiv ℝ (gradient (fun v ↦
      jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((0, q), v))) w
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    IsUnit H ∧ ‖Ring.inverse H‖ ≤
      ‖e.symm.toContinuousLinearMap‖ * (1 + B) * ‖e.toContinuousLinearMap‖ := by
  dsimp only
  rw [retained_conic_zeroTime_hessian_orientation adj ℓ hC hsource hi hΩ hφ q
    (w := WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) hq hgraph
    (by simpa [carrierGraphPoint, elapsedChartPoint] using hgraph)]
  refine ⟨(retainedDiagonalHessianEquiv _).toUnit.isUnit,
    (norm_inverse_retainedDiagonalHessian_le _).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((norm_primary_spatialHessian_le_joint hΩ hφ hq).trans hB))
        (norm_nonneg _)) (norm_nonneg _)

end JanetCartan.ResponseTransfer.RetainedFactors
