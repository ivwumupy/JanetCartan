module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.RowPullback.TimeShift
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilTransport

/-!
# Primitive coordinates for the row pullback

For `app:ch_regular_base:lem:characteristic-kernel`, derive the forward chart
from the autonomous flow at elapsed time and extract the initial label from
the inverse chart. The consumer is `exists_twoTimeRowTransport_cNorm_bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback

open FullPhaseCharts.InverseEstimates NullTransport.AmplitudeTame

variable {E A B F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed linear map evaluating the autonomous flow at `t-s`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def elapsedInputLinear : TwoTimePoint E →L[ℝ] RootState E × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ (RootState E)).prod
    (ContinuousLinearMap.fst ℝ ℝ (RootState E) -
      (ContinuousLinearMap.fst ℝ ℝ (E × E)).comp
        (ContinuousLinearMap.snd ℝ ℝ (RootState E)))

/-- The unchanged coordinates of the two-time projection
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def projectionBaseLinear : TwoTimePoint E →L[ℝ] TwoTimePoint E :=
  (ContinuousLinearMap.fst ℝ ℝ (RootState E)).prod
    (((ContinuousLinearMap.fst ℝ ℝ (E × E)).comp
      (ContinuousLinearMap.snd ℝ ℝ (RootState E))).prod
      ((0 : TwoTimePoint E →L[ℝ] E).prod
        ((ContinuousLinearMap.snd ℝ E E).comp
          ((ContinuousLinearMap.snd ℝ ℝ (E × E)).comp
            (ContinuousLinearMap.snd ℝ ℝ (RootState E))))))

/-- Insert the transported position into the two-time projection
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def projectionFlowLinear : RootState E →L[ℝ] TwoTimePoint E :=
  (0 : RootState E →L[ℝ] ℝ).prod ((0 : RootState E →L[ℝ] ℝ).prod
    (((ContinuousLinearMap.fst ℝ E E).comp
      (ContinuousLinearMap.snd ℝ ℝ (E × E))).prod (0 : RootState E →L[ℝ] E)))

/-- Extract the actual initial label from the inverse chart
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def initialLabelLinear : TwoTimePoint E →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ ℝ (E × E)).comp
    (ContinuousLinearMap.snd ℝ ℝ (RootState E))

private theorem cNorm_postcomp_linear_le (L : B →L[ℝ] F)
    {K : Set A} (hK : IsCompact K) {f : A → B} (m : ℕ)
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f x) :
    cNorm K m (L ∘ f) ≤ ‖L‖ * cNorm K m f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg K j f))
  intro j hj x hx
  apply (L.norm_iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hj)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hf hj)
      (mem_image_of_mem _ hx)) (norm_nonneg _)

omit [FiniteDimensional ℝ E] in
/-- The elapsed-time input sends the fixed characteristic compact ball into
the fixed doubled flow ball (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem elapsedInputLinear_mapsTo_closedBall (t₀ : ℝ) (p : E × E) {r : ℝ}
    (hr : 0 ≤ r) : MapsTo (elapsedInputLinear (E := E))
      (closedBall (t₀, (t₀, p)) r) (closedBall ((t₀, p), 0) (2 * r)) := by
  intro q hq
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hq
  change max (dist q.2 (t₀, p)) (dist (q.1 - q.2.1) 0) ≤ 2 * r
  apply max_le
  · have hh : dist q.2 (t₀, p) ≤ r := by
      simpa only [Prod.dist_eq, max_le_iff] using hq.2
    exact hh.trans (by linarith)
  · rw [Real.dist_eq, sub_zero, ← Real.dist_eq]
    exact (dist_triangle q.1 t₀ q.2.1).trans (by
      rw [dist_comm t₀ q.2.1]
      linarith [hq.2.1])

omit [FiniteDimensional ℝ E] in
/-- The same elapsed-time image containment on the open margin
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem elapsedInputLinear_mapsTo_ball (t₀ : ℝ) (p : E × E) {r : ℝ}
    (hr : 0 < r) : MapsTo (elapsedInputLinear (E := E))
      (ball (t₀, (t₀, p)) r) (ball ((t₀, p), 0) (2 * r)) := by
  intro q hq
  simp only [mem_ball, Prod.dist_eq, max_lt_iff] at hq
  change max (dist q.2 (t₀, p)) (dist (q.1 - q.2.1) 0) < 2 * r
  apply max_lt
  · have hh : dist q.2 (t₀, p) < r := by
      simpa only [Prod.dist_eq, max_lt_iff] using hq.2
    exact hh.trans (by linarith)
  · rw [Real.dist_eq, sub_zero, ← Real.dist_eq]
    exact (dist_triangle q.1 t₀ q.2.1).trans_lt (by
      rw [dist_comm t₀ q.2.1]
      linarith [hq.2.1])

omit [FiniteDimensional ℝ E] in
/-- The literal forward chart splits into fixed linear coordinates and the
actual flow, with no forward-chart derivative premise
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeProjection_linear_formula (Φ : RootState E × ℝ → RootState E) :
    twoTimeProjection Φ = fun q ↦ projectionBaseLinear q +
      projectionFlowLinear (Φ (elapsedInputLinear q)) := by
  funext q
  simp [twoTimeProjection, twoTimeState, projectionBaseLinear,
    projectionFlowLinear, elapsedInputLinear]

omit [FiniteDimensional ℝ E] in
/-- Forward-chart smoothness follows from the autonomous flow on the fixed
elapsed-time ball (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_twoTimeProjection_ball (t₀ : ℝ) (p : E × E) {R : ℝ}
    (hR : 0 < R) {Φ : RootState E × ℝ → RootState E}
    (hΦ : ContDiffOn ℝ ∞ Φ (ball ((t₀, p), 0) (2 * R))) :
    ContDiffOn ℝ ∞ (twoTimeProjection Φ) (ball (t₀, (t₀, p)) R) := by
  rw [twoTimeProjection_linear_formula]
  exact (projectionBaseLinear (E := E)).contDiff.contDiffOn.add
    ((projectionFlowLinear (E := E)).contDiff.comp_contDiffOn
      (hΦ.comp (elapsedInputLinear (E := E)).contDiff.contDiffOn
        (elapsedInputLinear_mapsTo_ball t₀ p hR)))

/-- The forward chart has a linear bound in the flow norm on fixed balls.
Its cost depends only on coordinates and order, never on the flow or chart
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem cNorm_twoTimeProjection_le (t₀ : ℝ) (p : E × E) {σ R : ℝ}
    (hσ : 0 < σ) (hσR : σ < R) {Φ : RootState E × ℝ → RootState E}
    (hΦ : ContDiffOn ℝ ∞ Φ (ball ((t₀, p), 0) (2 * R))) (m : ℕ) :
    cNorm (closedBall (t₀, (t₀, p)) σ) m (twoTimeProjection Φ) ≤
      cNorm (closedBall (t₀, (t₀, p)) σ) m (projectionBaseLinear (E := E)) +
        (‖projectionFlowLinear (E := E)‖ * linearNormCost (elapsedInputLinear (E := E)) m) *
          cNorm (closedBall ((t₀, p), 0) (2 * σ)) m Φ := by
  let K := closedBall (t₀, (t₀, p)) σ
  let f : TwoTimePoint E → RootState E := Φ ∘ elapsedInputLinear
  let g : TwoTimePoint E → TwoTimePoint E := projectionFlowLinear ∘ f
  have hs : ContDiffOn ℝ ∞ f (ball (t₀, (t₀, p)) R) :=
    hΦ.comp (elapsedInputLinear (E := E)).contDiff.contDiffOn
      (elapsedInputLinear_mapsTo_ball t₀ p (hσ.trans hσR))
  have ha : ∀ q ∈ K, ContDiffAt ℝ m f q :=
    fun q hq ↦ (hs.contDiffAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball hσR hq))).of_le (by simp)
  have hg : ∀ q ∈ K, ContDiffAt ℝ m g q :=
    fun q hq ↦ (projectionFlowLinear (E := E)).contDiff.contDiffAt.comp q (ha q hq)
  have hadd := cNorm_add_le_of_contDiffAt (f := (projectionBaseLinear (E := E)))
    (g := g) (isCompact_closedBall (t₀, (t₀, p)) σ)
    (fun _ _ ↦ (projectionBaseLinear (E := E)).contDiff.contDiffAt) hg
  have hpost := cNorm_postcomp_linear_le (projectionFlowLinear (E := E))
    (f := f) (isCompact_closedBall (t₀, (t₀, p)) σ) m ha
  have hpre := cNorm_comp_linear_le (elapsedInputLinear (E := E))
    (S := K) (isCompact_closedBall ((t₀, p), (0 : ℝ)) (2 * σ)) isOpen_ball
    (closedBall_subset_ball (show 2 * σ < 2 * R by linarith)) hΦ
    (elapsedInputLinear_mapsTo_closedBall t₀ p hσ.le) m
  rw [twoTimeProjection_linear_formula]
  apply hadd.trans
  apply add_le_add le_rfl
  exact hpost.trans ((mul_le_mul_of_nonneg_left hpre (norm_nonneg _)).trans_eq (by ring))

/-- The actual inverse-label norm is bounded by the inverse-chart norm,
without assuming any separate derivative bound for that label
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem cNorm_twoTimeInitialLabel_le (z : TwoTimePoint E) {ρ R : ℝ}
    (hρR : ρ < R) {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : ContDiffOn ℝ ∞ (C.symm : TwoTimePoint E → TwoTimePoint E) (ball z R)) (m : ℕ) :
    cNorm (closedBall z ρ) m (twoTimeInitialLabel C) ≤
      ‖initialLabelLinear (E := E)‖ *
        cNorm (closedBall z ρ) m (C.symm : TwoTimePoint E → TwoTimePoint E) :=
  cNorm_postcomp_linear_le (initialLabelLinear (E := E))
    (f := (C.symm : TwoTimePoint E → TwoTimePoint E)) (isCompact_closedBall z ρ) m
    (fun q hq ↦ (hC.contDiffAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball hρR hq))).of_le (by simp))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Both oriented time segments stay in the same characteristic ball.
The forward image is therefore in the exact physical coefficient ball
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem chart_timeSegment_mem {t₀ : ℝ} {p x : E × E} {σ τ : ℝ}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hmap : MapsTo C (closedBall (t₀, (t₀, p)) σ) (closedBall (t₀, (t₀, x)) τ))
    {q : TwoTimePoint E} (hq : q ∈ closedBall (t₀, (t₀, p)) σ)
    {u : ℝ} (hu : u ∈ uIcc q.2.1 q.1) :
    (u, q.2) ∈ closedBall (t₀, (t₀, p)) σ ∧
      C (u, q.2) ∈ closedBall (t₀, (t₀, x)) τ := by
  have hs : (u, q.2) ∈ closedBall (t₀, (t₀, p)) σ := by
    rw [← closedBall_prod_same, ← closedBall_prod_same] at hq ⊢
    exact ⟨(convex_closedBall t₀ σ).ordConnected.uIcc_subset hq.2.1 hq.1 hu, hq.2⟩
  exact ⟨hs, hmap hs⟩

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback
