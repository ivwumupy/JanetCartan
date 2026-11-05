module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Characteristics
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SmoothBufferedChart
/-!
# Local inverse footpoint charts

The initial identity and the actual characteristic velocity make the forward
space-time derivative an invertible shear. The inverse function theorem then
constructs the smooth footpoint map and both inverse identities on a product
source (`app:ch_waves:thm:leading`). The neighborhood chosen here is qualitative;
a uniform choice from low bounds remains a separate quantitative obligation.
-/

open Set Metric Filter
open scoped Topology ContDiff
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.NullTransport.ActualFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
/-- The initial derivative of the characteristic space-time map
(`app:ch_waves:thm:leading`). -/
def initialShear (v : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun q ↦ (q.1, q.1 • v + q.2)
    invFun := fun q ↦ (q.1, q.2 - q.1 • v)
    map_add' := by intro p q; ext <;> simp [add_smul]; abel
    map_smul' := by intro s q; ext <;> simp [smul_add, smul_smul]
    left_inv := by intro q; ext <;> simp
    right_inv := by intro q; ext <;> simp }

/-- The initial identity and time ODE determine the entire forward derivative;
invertibility is proved, not assumed (`app:ch_waves:thm:leading`). -/
theorem hasFDerivAt_initial_characteristic
    {Φ : ℝ × E → E} {S : Set E} (hS : IsOpen S) {p₀ : E} (hp₀ : p₀ ∈ S)
    (hΦ : DifferentiableAt ℝ Φ (0, p₀))
    (hinit : ∀ p ∈ S, Φ (0, p) = p) {v : E}
    (hdt : HasDerivAt (fun t ↦ Φ (t, p₀)) v 0) :
    HasFDerivAt (fun q ↦ (q.1, Φ q)) (initialShear v).toContinuousLinearMap (0, p₀) := by
  have ht : fderiv ℝ Φ (0, p₀) (1, 0) = v :=
    (hΦ.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 p₀))).unique hdt
  have hs : (fderiv ℝ Φ (0, p₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      ContinuousLinearMap.id ℝ E := by
    apply (hΦ.hasFDerivAt.comp p₀ (hasFDerivAt_prodMk_right 0 p₀)).unique
    apply (hasFDerivAt_id p₀).congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hp₀] with p hp using hinit p hp
  convert! (hasFDerivAt_fst.prodMk hΦ.hasFDerivAt) using 1
  apply ContinuousLinearMap.ext
  rintro ⟨t, p⟩
  refine Prod.ext rfl ?_
  change t • v + p = fderiv ℝ Φ (0, p₀) (t, p)
  have hpair : (t, p) = t • ((1 : ℝ), (0 : E)) + (0, p) := by simp
  rw [hpair, map_add, map_smul, ht]
  exact congrArg (fun A : E →L[ℝ] E ↦ t • v + A p) hs.symm



/-- Construct a smooth inverse on an actual open flow tube, with a two-sided
product source. This supplies both MapsTo and inverse identities used by
`PositiveTransport.FlowSolution` (`app:ch_waves:thm:leading`). The consumer
`exists_actual_local_flow_chart` constructs and supplies the forward flow. -/
theorem exists_local_footpoint_chart
    {Φ : ℝ × E → E} {I : Set ℝ} {S : Set E} (hI : IsOpen I) (hS : IsOpen S)
    (h0 : 0 ∈ I) {p₀ : E} (hp₀ : p₀ ∈ S)
    (hΦ : ContDiffOn ℝ ∞ Φ (I ×ˢ S)) (hinit : ∀ p ∈ S, Φ (0, p) = p)
    {v : E} (hdt : HasDerivAt (fun t ↦ Φ (t, p₀)) v 0) :
    ∃ δ > (0 : ℝ), ∃ D : Set (ℝ × E), ∃ Y : ℝ × E → E,
      Ioo (-δ) δ ×ˢ ball p₀ δ ⊆ I ×ˢ S ∧ IsOpen D ∧
      D = (fun q ↦ (q.1, Φ q)) '' (Ioo (-δ) δ ×ˢ ball p₀ δ) ∧
      ContDiffOn ℝ ∞ Y D ∧
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-δ) δ ×ˢ ball p₀ δ) D ∧
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-δ) δ ×ˢ ball p₀ δ) ∧
      (∀ p ∈ ball p₀ δ, ∀ t ∈ Ioo (-δ) δ, Y (t, Φ (t, p)) = p) ∧
      (∀ q ∈ D, Φ (q.1, Y q) = q.2) := by
  let G : ℝ × E → ℝ × E := fun q ↦ (q.1, Φ q)
  let A := initialShear v
  have hG : ContDiffOn ℝ ∞ G (I ×ˢ S) := contDiffOn_fst.prodMk hΦ
  have hG₀ : ContDiffAt ℝ ∞ G (0, p₀) := hG.contDiffAt ((hI.prod hS).mem_nhds ⟨h0, hp₀⟩)
  have hA : HasFDerivAt G A.toContinuousLinearMap (0, p₀) :=
    hasFDerivAt_initial_characteristic hS hp₀
      ((hΦ.contDiffAt ((hI.prod hS).mem_nhds ⟨h0, hp₀⟩)).differentiableAt (by simp))
      hinit hdt
  have hgap₀ : ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ G (0, p₀)) -
      ContinuousLinearMap.id ℝ (ℝ × E)‖ = 0 := by
    rw [hA.fderiv]
    simp
  have hgap : ∀ᶠ q in 𝓝 ((0 : ℝ), p₀),
      ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ G q) -
        ContinuousLinearMap.id ℝ (ℝ × E)‖ < 1 / 2 := by
    have hc : ContinuousAt (fun q ↦ ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ G q) -
        ContinuousLinearMap.id ℝ (ℝ × E)‖) (0, p₀) := ((continuousAt_const.clm_comp
      (hG₀.continuousAt_fderiv (by simp))).sub continuousAt_const).norm
    apply hc.eventually (gt_mem_nhds _)
    change ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ G (0, p₀)) -
      ContinuousLinearMap.id ℝ (ℝ × E)‖ < 1 / 2
    rw [hgap₀]
    norm_num
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (hgap.and ((hI.prod hS).mem_nhds ⟨h0, hp₀⟩))
  have hbox : Ioo (-δ) δ ×ˢ ball p₀ δ ⊆ ball ((0 : ℝ), p₀) δ := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa only [Real.dist_eq, sub_zero] using abs_lt.mpr ht, hp⟩
  have hsub : Ioo (-δ) δ ×ˢ ball p₀ δ ⊆ I ×ˢ S := fun q hq ↦ (hb (hbox hq)).2
  obtain ⟨e, he, hs, htarget, hi⟩ := HamiltonPhase.exists_smoothInverse_of_normalized_half_gap
    (isOpen_Ioo.prod isOpen_ball) ((convex_Ioo _ _).prod (convex_ball p₀ δ)) A G
    (hG.mono hsub) (fun q hq ↦ (hb (hbox hq)).1.le)
  let Y : ℝ × E → E := fun q ↦ (e.symm q).2
  have htime (q) (hq : q ∈ e.target) : (e.symm q).1 = q.1 := by
    have h := congrArg Prod.fst (e.right_inv hq)
    simpa only [he, G] using h
  refine ⟨δ, hδ, e.target, Y, hsub, e.open_target, htarget, hi.snd, ?_, ?_, ?_, ?_⟩
  · intro q hq
    change G q ∈ e.target
    rw [← he]
    exact e.map_source (hs.symm ▸ hq)
  · intro q hq
    have h := e.map_target hq
    rw [hs] at h
    simpa only [← htime q hq] using h
  · intro p hp t ht
    have h := congrArg Prod.snd (e.left_inv (hs.symm ▸ (show (t, p) ∈
      Ioo (-δ) δ ×ˢ ball p₀ δ from ⟨ht, hp⟩)))
    simpa only [he, G] using h
  · intro q hq
    have h := congrArg Prod.snd (e.right_inv hq)
    have heq : (q.1, Y q) = e.symm q := Prod.ext (htime q hq).symm rfl
    rw [heq]
    simpa only [he, G] using h

end JanetCartan.NullTransport.ActualFlow
