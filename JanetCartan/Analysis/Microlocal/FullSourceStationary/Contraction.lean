module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationarySystem
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.StationaryBranch.Quantitative

/-!
# Quantitative contraction with independent full-source parameters

The primitive full joint second and third phase jets imply the normalized
contraction gap. The existing quantitative inverse theorem then constructs the
stationary point in the prescribed ball. No stationary-map hypothesis is used.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.FullSourceStationary
open ResponseTransfer.DirectEvolution ResponseTransfer.RetainedFactors
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "W" => CarrierVariables (d + 1)

/-- Original second and third phase jets give the normalized derivative gap
and residual estimate on the full supplied buffered cylinder. The zero-time
linearization is supplied by `full_source_conic_zeroTime_hessian`;
the fixed inverse bound comes from the primary second jet. No positive-time
Hessian smallness is an input (`app:ch_response:eq:direct-envelope-profile`). -/
theorem full_source_stationary_normalized_estimates
    {f : FullSourcePoint d → ℝ} {V : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (q : E × (Euclidean 3 × Euclidean d)) (a : W) (A : W ≃L[ℝ] W)
    {T r M B₂ B₃ t : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (hM : 0 ≤ M) (_hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hA : fderiv ℝ (gradient (fun w ↦ f ((0, q), w))) a = A.toContinuousLinearMap)
    (hAi : ‖A.symm.toContinuousLinearMap‖ ≤ M)
    (hzero : gradient (fun w ↦ f ((0, q), w)) a = 0)
    (hbuf : (Icc (-T) T ×ˢ {q}) ×ˢ closedBall a (2 * r) ⊆ V)
    (hjet₂ : ∀ p ∈ (Icc (-T) T ×ˢ {q}) ×ˢ closedBall a (2 * r),
      ‖iteratedFDeriv ℝ 2 f p‖ ≤ B₂)
    (hjet₃ : ∀ p ∈ (Icc (-T) T ×ˢ {q}) ×ˢ closedBall a (2 * r),
      ‖iteratedFDeriv ℝ 3 f p‖ ≤ B₃)
    (htT : |t| ≤ T) (htr : |t| ≤ 2 * r) :
    (∀ w ∈ closedBall a (2 * r),
      ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (gradient (fun v ↦ f ((t, q), v))) w) -
          ContinuousLinearMap.id ℝ W‖ ≤ M * B₃ * (2 * r)) ∧
    ‖A.symm (gradient (fun w ↦ f ((t, q), w)) a)‖ ≤ M * B₂ * |t| := by
  let S := (Icc (-T) T ×ˢ {q}) ×ˢ closedBall a (2 * r)
  have hS : Convex ℝ S := ((convex_Icc (-T) T).prod (convex_singleton q)).prod
    (convex_closedBall a (2 * r))
  have ha : a ∈ closedBall a (2 * r) := mem_closedBall_self (by positivity)
  have h0 : ((0, q), a) ∈ S := ⟨⟨⟨by linarith, hT⟩, rfl⟩, ha⟩
  have ht (w : W) (hw : w ∈ closedBall a (2 * r)) : ((t, q), w) ∈ S :=
    ⟨⟨abs_le.mp htT, rfl⟩, hw⟩
  constructor
  · intro w hw
    have hdiff := norm_full_source_stationaryHessian_sub_le hV hf hS hbuf hjet₃ h0 (ht w hw)
    have hdist : ‖((t, q), w) - ((0, q), a)‖ ≤ 2 * r := by
      simpa only [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_def, norm_zero,
        Real.norm_eq_abs, max_eq_left (abs_nonneg t), max_le_iff] using
        And.intro htr (show ‖w - a‖ ≤ 2 * r by simpa [mem_closedBall, dist_eq_norm] using hw)
    have he : A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (gradient (fun v ↦ f ((t, q), v))) w) - ContinuousLinearMap.id ℝ W =
        A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (gradient (fun v ↦ f ((t, q), v))) w - A.toContinuousLinearMap) := by
      ext v; simp
    rw [he]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    calc
      _ ≤ M * (B₃ * (2 * r)) := mul_le_mul hAi
        (by rw [← hA]; exact hdiff.trans (mul_le_mul_of_nonneg_left hdist hB₃))
          (norm_nonneg _) hM
      _ = _ := by ring
  · have hb := norm_full_source_stationarySystem_sub_le hV hf hS hbuf hjet₂ h0 (ht a ha)
    rw [hzero, sub_zero] at hb
    have hd : ‖((t, q), a) - ((0, q), a)‖ = |t| := by simp [Prod.norm_def]
    rw [hd] at hb
    exact (A.symm.toContinuousLinearMap.le_opNorm _).trans
      ((mul_le_mul hAi hb (norm_nonneg _) hM).trans_eq (by ring))

/-- Contraction constructs a stationary point within the half-radius ball,
and proves uniqueness on the larger buffered ball. Every positive-time bound
is derived above from primitive jets; the radius inequalities are supplied by
`exists_retained_stationary_radii`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_source_stationary_point_of_low_jets
    {f : FullSourcePoint d → ℝ} {V : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (q : E × (Euclidean 3 × Euclidean d)) (a : W) (A : W ≃L[ℝ] W)
    {T r M B₂ B₃ t : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (hM : 0 ≤ M) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hA : fderiv ℝ (gradient (fun w ↦ f ((0, q), w))) a = A.toContinuousLinearMap)
    (hAi : ‖A.symm.toContinuousLinearMap‖ ≤ M)
    (hzero : gradient (fun w ↦ f ((0, q), w)) a = 0)
    (hbuf : (Icc (-T) T ×ˢ {q}) ×ˢ closedBall a (2 * r) ⊆ V)
    (hjet₂ : ∀ p ∈ (Icc (-T) T ×ˢ {q}) ×ˢ closedBall a (2 * r),
      ‖iteratedFDeriv ℝ 2 f p‖ ≤ B₂)
    (hjet₃ : ∀ p ∈ (Icc (-T) T ×ˢ {q}) ×ˢ closedBall a (2 * r),
      ‖iteratedFDeriv ℝ 3 f p‖ ≤ B₃)
    (htT : |t| ≤ T) (htr : |t| ≤ 2 * r)
    (hsmall₃ : M * B₃ * (2 * r) ≤ 1 / 2)
    (hsmall₂ : M * B₂ * |t| ≤ r / 4) :
    InjOn (gradient (fun w ↦ f ((t, q), w))) (closedBall a (2 * r)) ∧
      ∃ w ∈ closedBall a (r / 2), gradient (fun v ↦ f ((t, q), v)) w = 0 := by
  obtain ⟨hgap, hres⟩ := full_source_stationary_normalized_estimates hV hf q a A
    hT hr.le hM hB₂ hB₃ hA hAi hzero hbuf hjet₂ hjet₃ htT htr
  have hg w (hw : w ∈ closedBall a (2 * r)) :
      DifferentiableAt ℝ (gradient (fun v ↦ f ((t, q), v))) w := by
    have hm : ((t, q), w) ∈ V := hbuf ⟨⟨abs_le.mp htT, rfl⟩, hw⟩
    exact (((full_source_stationarySystem_local_jet hV hf hm).1).comp w
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hgap' w (hw : w ∈ closedBall a (2 * r)) := (hgap w hw).trans hsmall₃
  refine ⟨injOn_of_normalized_derivative_gap (convex_closedBall a (2 * r)) A hg hgap', ?_⟩
  have hz : (0 : W) ∈ (gradient (fun w ↦ f ((t, q), w))) '' closedBall a (r / 2) := by
    apply mem_image_closedBall_of_normalized_derivative_gap (convex_closedBall a (2 * r))
      A hg hgap' (by positivity) (closedBall_subset_closedBall (by linarith))
    simpa only [zero_sub, map_neg, norm_neg, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hres.trans hsmall₂
  exact hz

end JanetCartan.FullSourceStationary
