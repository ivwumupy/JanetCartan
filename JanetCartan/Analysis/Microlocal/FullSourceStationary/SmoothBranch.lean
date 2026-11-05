module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.Contraction
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Joint smoothness for the full-source stationary branch

Uniqueness of the contracted roots identifies them with the local implicit
functions in all independent source parameters. The IFT proves regularity on
the already fixed interval; it does not choose another field-dependent radius.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.FullSourceStationary
open ResponseTransfer.DirectEvolution ResponseTransfer.RetainedFactors
variable {d : ℕ}
local notation "W" => CarrierVariables (d + 1)
local notation "P" => ℝ × (Euclidean (d + 1) × (Euclidean 3 × Euclidean d))

private theorem stationary_derivative_isInvertible
    (A : W ≃L[ℝ] W) (H : W →L[ℝ] W)
    (h : ‖A.symm.toContinuousLinearMap.comp H - ContinuousLinearMap.id ℝ W‖ ≤ 1 / 2) :
    H.IsInvertible := by
  have hn : ‖1 - A.symm.toContinuousLinearMap.comp H‖ < 1 := by
    rw [norm_sub_rev]
    exact lt_of_le_of_lt h (by norm_num)
  have hu : IsUnit (A.symm.toContinuousLinearMap.comp H) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  obtain ⟨u, hu⟩ := hu
  have hi : (A.symm.toContinuousLinearMap.comp H).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ W u, ?_⟩
    exact hu
  exact ContinuousLinearMap.isInvertible_equiv_comp.mp hi

/-- The uniformly constructed stationary roots form one jointly smooth
branch. The contraction data are produced by
`exists_full_source_stationary_point_of_low_jets` and
`full_source_stationary_normalized_estimates`; these intermediate inputs are
discharged by the retained branch assembly. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_smooth_full_source_stationary_branch_of_contraction
    {f : FullSourcePoint d → ℝ} {V : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {U : Set P} (hU : IsOpen U) (a : P → W) (ha : ContinuousOn a U)
    (A : P → W ≃L[ℝ] W) {r : ℝ} (hr : 0 < r)
    (hbuf : ∀ p ∈ U, ∀ w ∈ closedBall (a p) (2 * r), (p, w) ∈ V)
    (hgap : ∀ p ∈ U, ∀ w ∈ closedBall (a p) (2 * r),
      ‖(A p).symm.toContinuousLinearMap.comp
        (fderiv ℝ (gradient (fun v ↦ f (p, v))) w) - ContinuousLinearMap.id ℝ W‖ ≤ 1 / 2)
    (hroot : ∀ p ∈ U, ∃ w ∈ closedBall (a p) (r / 2),
      gradient (fun v ↦ f (p, v)) w = 0) :
    ∃ κ : P → W, ContDiffOn ℝ ∞ κ U ∧
      (∀ p ∈ U, κ p ∈ closedBall (a p) (r / 2) ∧
        gradient (fun v ↦ f (p, v)) (κ p) = 0) ∧
      ∀ p ∈ U, ∀ w ∈ closedBall (a p) (2 * r),
        gradient (fun v ↦ f (p, v)) w = 0 ↔ κ p = w := by
  classical
  let κ : P → W := fun p ↦ if hp : p ∈ U then (hroot p hp).choose else a p
  have hk p (hp : p ∈ U) : κ p ∈ closedBall (a p) (r / 2) ∧
      gradient (fun v ↦ f (p, v)) (κ p) = 0 := by
    simpa only [κ, dite_eq_left hp] using (hroot p hp).choose_spec
  have hkbig p (hp : p ∈ U) : κ p ∈ closedBall (a p) (2 * r) :=
    closedBall_subset_closedBall (by linarith) (hk p hp).1
  let F : FullSourcePoint d → W := fun p ↦ gradient (fun w ↦ f (p.1, w)) p.2
  have hdiff p (hp : p ∈ U) w (hw : w ∈ closedBall (a p) (2 * r)) :
      ContDiffAt ℝ ∞ F (p, w) :=
    (full_source_stationarySystem_local_jet (f := f) hV hf (hbuf p hp w hw)).1
  have hunique p (hp : p ∈ U) :
      InjOn (gradient (fun v ↦ f (p, v))) (closedBall (a p) (2 * r)) :=
    injOn_of_normalized_derivative_gap (convex_closedBall (a p) (2 * r)) (A p)
      (fun w hw ↦ ((hdiff p hp w hw).comp w
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) (hgap p hp)
  have heq p (hp : p ∈ U) w (hw : w ∈ closedBall (a p) (2 * r)) :
      gradient (fun v ↦ f (p, v)) w = 0 ↔ κ p = w := by
    constructor
    · intro hw0
      exact hunique p hp (hkbig p hp) hw ((hk p hp).2.trans hw0.symm)
    · rintro rfl
      exact (hk p hp).2
  refine ⟨κ, ?_, hk, heq⟩
  intro p hp
  have hF := hdiff p hp (κ p) (hkbig p hp)
  have hpartial : fderiv ℝ (gradient (fun w ↦ f (p, w))) (κ p) =
      (fderiv ℝ F (p, κ p)).comp (ContinuousLinearMap.inr ℝ P W) :=
    ((hF.differentiableAt (by simp)).hasFDerivAt.comp (κ p)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p (κ p))).fderiv
  have hinv : ((fderiv ℝ F (p, κ p)).comp (ContinuousLinearMap.inr ℝ P W)).IsInvertible := by
    rw [← hpartial]
    exact stationary_derivative_isInvertible (A p) _ (hgap p hp _ (hkbig p hp))
  let k := hF.implicitFunction (by simp) hinv
  have hks : ContDiffAt ℝ ∞ k p := hF.contDiffAt_implicitFunction (by simp) hinv
  have hk0 : k p = κ p := hF.implicitFunction_apply_self (by simp) hinv
  have hdist : dist (k p) (a p) < 2 * r := by
    rw [hk0]
    exact lt_of_le_of_lt (hk p hp).1 (by linarith)
  have hnear : ∀ᶠ v in 𝓝 p, k v ∈ closedBall (a v) (2 * r) := by
    have hc := hks.continuousAt.dist (ha.continuousAt (hU.mem_nhds hp))
    filter_upwards [hc.eventually (gt_mem_nhds hdist)] with v hv
    exact hv.le
  have hkeq : κ =ᶠ[𝓝 p] k := by
    filter_upwards [hU.mem_nhds hp, hnear,
      hF.eventually_apply_implicitFunction (by simp) hinv] with v hv hkv hFv
    exact (heq v hv (k v) hkv).mp (hFv.trans (hk p hp).2)
  exact (hks.congr_of_eventuallyEq hkeq).contDiffWithinAt

end JanetCartan.FullSourceStationary
