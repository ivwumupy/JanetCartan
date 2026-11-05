module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.ZeroTime
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.KernelIdentity

/-!
# Diagonal PDO geometry for the original full source

The complete elliptic solver and residual have full physical covectors. Their
forward and literal-adjoint carrier phases are the same diagonal phase. Its
critical point, zero value and full segment-averaged inverse bound follow from
the original primary phase, without a characteristic chart or an added cap.
The generic full-amplitude branch calculus consumes these geometric facts.
Actual reserved symbol grades and the operator application remain separate.

Sources: `app:ch_response:eq:response-exact-phase`,
`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open DirectEvolution DirectEvolution.CompactTransfer RetainedFactors CompatibleResponse
open FullSourceStationary
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)

/-- The forward and literal-adjoint PDO carrier phases coincide, with the
original full source parameters fixed (`app:ch_response:eq:response-exact-phase`). -/
theorem diagonal_adjointCarrierPhase_eq (φ : E → Param → ℝ) :
    adjointCarrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ =
      carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ := by
  rfl

private theorem gradient_diagonal_fullSourcePhase (φ : E → Param → ℝ)
    (q : E × Param) (w : W)
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y q.2) w.fst) :
    gradient (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ q) w =
      WithLp.toLp 2 (gradient (fun y ↦ φ y q.2) w.fst - w.snd, q.1 - w.fst) := by
  have hz := (WithLp.fstL 2 ℝ E E).hasFDerivAt (x := w)
  have hθ := (WithLp.sndL 2 ℝ E E).hasFDerivAt (x := w)
  have hd := (((((hasFDerivAt_const (𝕜 := ℝ) q.1 w).inner ℝ hθ).sub
    (hz.inner ℝ hθ)).add (hφ.hasFDerivAt.comp w hz)).sub_const (φ q.1 q.2))
  have hg : HasGradientAt (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ q)
      (WithLp.toLp 2 (gradient (fun y ↦ φ y q.2) w.fst - w.snd, q.1 - w.fst)) w := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro v
    change inner ℝ (WithLp.toLp 2
      (gradient (fun y ↦ φ y q.2) w.fst - w.snd, q.1 - w.fst)) v = _
    rw [WithLp.prod_inner_apply]
    change inner ℝ (gradient (fun y ↦ φ y q.2) w.fst - w.snd) v.fst +
      inner ℝ (q.1 - w.fst) v.snd = _
    simp only [inner_sub_left, add_apply, sub_apply,
      ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, zero_apply, inner_zero_left, add_zero,
      WithLp.fstL_apply, WithLp.sndL_apply, ← inner_gradient_left]
    rw [real_inner_comm w.snd v.fst]
    ring
  exact hg.gradient

/-- The full-frequency diagonal PDO phase has its actual stationary point
and zero critical value at the original source gradient. No characteristic
chart or extra source cap is used (`app:ch_response:eq:direct-envelope-profile`). -/
theorem diagonal_fullSourcePhase_stationary_value
    (φ : E → Param → ℝ) (q : E × Param)
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y q.2) q.1) :
    let κ : W := WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)
    gradient (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ q) κ = 0 ∧
      carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ q κ = 0 := by
  dsimp only
  constructor
  · rw [gradient_diagonal_fullSourcePhase φ q
      (WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) hφ]
    simp
  · simp [carrierPhase]

/-- The full-frequency PDO carrier Hessian is the retained explicit block at
every source position in the original phase domain. All components of the
independent full source parameter and covector remain unchanged
(`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`). -/
theorem diagonal_fullSourcePhase_hessian
    {φ : E → Param → ℝ} {Ω : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    (q : E × Param) {w : W} (hw : (w.fst, q.2) ∈ Ω) :
    fderiv ℝ (gradient (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ q)) w =
      (retainedDiagonalHessianEquiv
        (fderiv ℝ (gradient (fun y ↦ φ y q.2)) w.fst)).toContinuousLinearMap := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  have hsrc : Continuous (fun v : W ↦ (v.fst, q.2)) := by fun_prop
  have hg : gradient (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ q) =ᶠ[𝓝 w]
      fun v ↦ e.symm (gradient (fun y ↦ φ y q.2) v.fst - v.snd, q.1 - v.fst) := by
    filter_upwards [hsrc.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hw)] with v hv
    exact gradient_diagonal_fullSourcePhase φ q v
      (((hφ.contDiffAt (hΩ.mem_nhds hv)).comp v.fst
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have hdiff : DifferentiableAt ℝ (gradient (fun y ↦ φ y q.2)) w.fst :=
    (((contDiffOn_full_source_gradient hΩ hφ).contDiffAt (hΩ.mem_nhds hw)).comp
      w.fst (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hd := e.symm.hasFDerivAt.comp w
    (((hdiff.hasFDerivAt.comp w (WithLp.fstL 2 ℝ E E).hasFDerivAt).sub
      (WithLp.sndL 2 ℝ E E).hasFDerivAt).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) q.1 w).sub (WithLp.fstL 2 ℝ E E).hasFDerivAt))
  rw [(hd.congr_of_eventuallyEq hg).fderiv]
  ext v
  simp [retainedDiagonalHessianEquiv, stationaryDiagonalEquiv, e]

/-- Segment averaging preserves the explicit invertible PDO block. The same
joint second jet bounds its inverse over the whole original segment, including
all frequency shoulders. This discharges the inverse-gap input of the full
amplitude elliptic envelope; symbol grades remain a separate input
(`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`). -/
theorem diagonal_fullSourcePhase_averagedHessian_bound
    {φ : E → Param → ℝ} {Ω KP : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    (hKP : IsCompact KP) (hKPΩ : KP ⊆ Ω)
    (κ : E × Param → W) (q : E × Param) (w : W)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1,
      ((κ q + t • (w - κ q)).fst, q.2) ∈ KP) :
    let H := averagedPhaseHessian (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ) κ q w
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    IsUnit H ∧ ‖Ring.inverse H‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      (1 + cNorm KP 2 (Function.uncurry φ)) * ‖e.toContinuousLinearMap‖ := by
  let seg := fun t : ℝ ↦ κ q + t • (w - κ q)
  let A := fun t : ℝ ↦ fderiv ℝ (gradient (fun y ↦ φ y q.2)) (seg t).fst
  have hseg : Continuous (fun t : ℝ ↦ (seg t).fst) := by
    dsimp [seg]
    fun_prop
  have hAs : ContinuousOn A (uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hg : ContDiffAt ℝ ∞ (gradient (fun y ↦ φ y q.2)) (seg t).fst :=
      ((contDiffOn_full_source_gradient hΩ hφ).contDiffAt
        (hΩ.mem_nhds (hKPΩ (hsegment t ht')))).comp
          (f := fun y : E ↦ (y, q.2)) (seg t).fst (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hg.fderiv_right (m := ∞) (by simp)).continuousAt.comp
      (x := t) hseg.continuousAt).continuousWithinAt
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 1 := hAs.intervalIntegrable
  have heq : averagedPhaseHessian (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ) κ q w =
      (retainedDiagonalHessianEquiv (∫ t in (0 : ℝ)..1, A t)).toContinuousLinearMap := by
    rw [← integral_retainedDiagonalHessian A hAi]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact diagonal_fullSourcePhase_hessian hΩ hφ q (hKPΩ (hsegment t ht'))
  have hbound : ‖∫ t in (0 : ℝ)..1, A t‖ ≤ cNorm KP 2 (Function.uncurry φ) := by
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (fun t ht ↦ (norm_full_source_spatialHessian_le_joint hΩ hφ
          (hKPΩ (hsegment t (by simpa using (uIoc_subset_uIcc ht))))).trans
            (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKP
              (fun q hq ↦ (hφ.contDiffAt (hΩ.mem_nhds (hKPΩ hq))).of_le (by norm_num))
              (hsegment t (by simpa using (uIoc_subset_uIcc ht))) le_rfl))
  dsimp only
  rw [heq]
  refine ⟨(retainedDiagonalHessianEquiv _).toUnit.isUnit,
    (norm_inverse_retainedDiagonalHessian_le _).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hbound) (norm_nonneg _)) (norm_nonneg _)

end JanetCartan.ResponseTransfer.DiagonalPdo
