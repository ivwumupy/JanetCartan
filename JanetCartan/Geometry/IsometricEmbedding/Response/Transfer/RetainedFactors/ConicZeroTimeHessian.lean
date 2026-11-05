module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.ZeroTimeOrientation
/-!
# Zero-time Hessians on the full normalized conic domain

The full annular selector need not have its RAW covectors near the section
centre. The same retained flow still gives the exact diagonal Hessian on its
NORMALIZED conic domain. This removes the artificial raw-overlap restriction
from the averaged inverse bound, retaining the original Hilbert norms.
Consumer: `app:ch_response:eq:direct-envelope-profile` on `AnnularCarriers`.
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
/-- The exact Hilbert gradient of the zero-time carrier polynomial
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem gradient_diagonalCarrierPhase (φ : E → Euclidean 3 → ℝ) (x : E) (c : Euclidean 3) (w : W)
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y c) w.fst) :
    gradient (carrierPhase (fun x θ : E ↦ inner ℝ x θ) φ (x, c)) w =
      WithLp.toLp 2 (gradient (fun y ↦ φ y c) w.fst - w.snd, x - w.fst) := by
  have hz := (WithLp.fstL 2 ℝ E E).hasFDerivAt (x := w)
  have hθ := (WithLp.sndL 2 ℝ E E).hasFDerivAt (x := w)
  have hd := (((((hasFDerivAt_const (𝕜 := ℝ) x w).inner ℝ hθ).sub
    (hz.inner ℝ hθ)).add (hφ.hasFDerivAt.comp w hz)).sub_const (φ x c))
  have hg : HasGradientAt (carrierPhase (fun x θ : E ↦ inner ℝ x θ) φ (x, c))
      (WithLp.toLp 2 (gradient (fun y ↦ φ y c) w.fst - w.snd, x - w.fst)) w := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro v
    change inner ℝ (WithLp.toLp 2
      (gradient (fun y ↦ φ y c) w.fst - w.snd, x - w.fst)) v = _
    rw [WithLp.prod_inner_apply]
    change inner ℝ (gradient (fun y ↦ φ y c) w.fst - w.snd) v.fst +
      inner ℝ (x - w.fst) v.snd = _
    simp only [inner_sub_left, add_apply, sub_apply,
      ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, zero_apply,
      inner_zero_left, add_zero,
      WithLp.fstL_apply, WithLp.sndL_apply, ← inner_gradient_left]
    rw [real_inner_comm w.snd v.fst]
    ring
  exact hg.gradient

/-- At every normalized conic covector the SAME retained phase has the
explicit diagonal Hessian. Raw covectors may traverse the entire annular
radial range; only their actual conic chart membership is required
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_conic_zeroTime_hessian_of_normalized_domain
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {x : E} {c : Euclidean 3} {w : W} (hw : (w.fst, c) ∈ Ω)
    (hgraph : elapsedChartPoint 0 x w.snd ∈ domain ℓ C.target) :
    fderiv ℝ (gradient (elapsedCarrierPhase (curriedPhase ℓ C) 0 φ (x, c))) w =
      (retainedDiagonalHessianEquiv
        (fderiv ℝ (gradient (fun y ↦ φ y c)) w.fst)).toContinuousLinearMap := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  have hpath : Continuous (fun v : W ↦ (((0 : ℝ), (x, c)), v)) :=
    continuous_const.prodMk continuous_id
  have hmem := ((contDiff_carrierGraphPoint false).continuous.comp hpath).continuousAt.preimage_mem_nhds
    ((isOpen_domain ℓ C.open_target).mem_nhds hgraph)
  have he : elapsedCarrierPhase (curriedPhase ℓ C) 0 φ (x, c) =ᶠ[𝓝 w]
      carrierPhase (fun x θ : E ↦ inner ℝ x θ) φ (x, c) := by
    filter_upwards [hmem] with v hv
    exact congrArg (fun r ↦ r - inner ℝ v.fst v.snd + φ v.fst c - φ x c)
      (retained_conic_elapsedPhase_zero ℓ hC hsource hi hv)
  have hsrc : Continuous (fun v : W ↦ (v.fst, c)) := by fun_prop
  have hg : gradient (carrierPhase (fun x θ : E ↦ inner ℝ x θ) φ (x, c)) =ᶠ[𝓝 w]
      fun v ↦ e.symm (gradient (fun y ↦ φ y c) v.fst - v.snd, x - v.fst) := by
    filter_upwards [hsrc.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hw)] with v hv
    exact gradient_diagonalCarrierPhase φ x c v
      (((hφ.contDiffAt (hΩ.mem_nhds hv)).comp v.fst
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have hdiff : DifferentiableAt ℝ (gradient (fun y ↦ φ y c)) w.fst :=
    (((contDiffOn_joint_primaryGradient hΩ hφ).contDiffAt (hΩ.mem_nhds hw)).comp
      w.fst (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hd := e.symm.hasFDerivAt.comp w
    (((hdiff.hasFDerivAt.comp w (WithLp.fstL 2 ℝ E E).hasFDerivAt).sub
      (WithLp.sndL 2 ℝ E E).hasFDerivAt).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) x w).sub (WithLp.fstL 2 ℝ E E).hasFDerivAt))
  rw [he.gradient.fderiv_eq, (hd.congr_of_eventuallyEq hg).fderiv]
  ext v
  simp [retainedDiagonalHessianEquiv, stationaryDiagonalEquiv, e]

/-- The exact averaged inverse bound holds on the entire normalized conic
carrier, including the full radial range of the retained annular multiplier.
The original primary second jet controls the bound; no inverse or Hessian
smallness is assumed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_conic_zeroTime_averagedHessian_bound_of_normalized_domain
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ w ∈ ball z a, Φ (w, 0) = w)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {KP : Set (E × Euclidean 3)} (hKP : IsCompact KP) (hKPΩ : KP ⊆ Ω)
    (κ : E × Euclidean 3 → W) (x : E) (c : Euclidean 3) (w : W)
    (hprimary : ∀ t ∈ Icc (0 : ℝ) 1,
      ((κ (x, c) + t • (w - κ (x, c))).fst, c) ∈ KP)
    (hbase : ∀ t ∈ Icc (0 : ℝ) 1,
      elapsedChartPoint 0 x (κ (x, c) + t • (w - κ (x, c))).snd ∈
        domain ℓ C.target) :
    let H := averagedPhaseHessian (elapsedCarrierPhase (curriedPhase ℓ C) 0 φ) κ (x, c) w
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    IsUnit H ∧ ‖Ring.inverse H‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      (1 + cNorm KP 2 (Function.uncurry φ)) * ‖e.toContinuousLinearMap‖ := by
  let seg := fun t : ℝ ↦ κ (x, c) + t • (w - κ (x, c))
  let A := fun t : ℝ ↦ fderiv ℝ (gradient (fun y ↦ φ y c)) (seg t).fst
  have hseg : Continuous (fun t : ℝ ↦ (seg t).fst) := by
    dsimp [seg]
    fun_prop
  have hAs : ContinuousOn A (uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hg : ContDiffAt ℝ ∞ (gradient (fun y ↦ φ y c)) (seg t).fst :=
      ((contDiffOn_joint_primaryGradient hΩ hφ).contDiffAt
        (hΩ.mem_nhds (hKPΩ (hprimary t ht')))).comp
          (f := fun y : E ↦ (y, c)) (seg t).fst (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hg.fderiv_right (m := ∞) (by simp)).continuousAt.comp
      (x := t) hseg.continuousAt).continuousWithinAt
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 1 := hAs.intervalIntegrable
  have heq : averagedPhaseHessian (elapsedCarrierPhase (curriedPhase ℓ C) 0 φ) κ (x, c) w =
      (retainedDiagonalHessianEquiv (∫ t in (0 : ℝ)..1, A t)).toContinuousLinearMap := by
    rw [← integral_retainedDiagonalHessian A hAi]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact retained_conic_zeroTime_hessian_of_normalized_domain ℓ hC hsource hi hΩ hφ
      (hKPΩ (hprimary t ht')) (hbase t ht')
  have hbound : ‖∫ t in (0 : ℝ)..1, A t‖ ≤ cNorm KP 2 (Function.uncurry φ) := by
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (fun t ht ↦ (norm_primary_spatialHessian_le_joint hΩ hφ
          (hKPΩ (hprimary t (by simpa using (uIoc_subset_uIcc ht))))).trans
            (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKP
              (fun q hq ↦ (hφ.contDiffAt (hΩ.mem_nhds (hKPΩ hq))).of_le (by norm_num))
              (hprimary t (by simpa using (uIoc_subset_uIcc ht))) le_rfl))
  dsimp only
  rw [heq]
  refine ⟨(retainedDiagonalHessianEquiv _).toUnit.isUnit,
    (norm_inverse_retainedDiagonalHessian_le _).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hbound) (norm_nonneg _)) (norm_nonneg _)


end JanetCartan.ResponseTransfer.RetainedFactors
