module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RowTransport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Reparametrization

/-!
# Joint estimates for the variable-source-time integral

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, the
coefficient is evaluated on the actual two-time characteristic. Subtracting
two evaluations of its fixed-zero primitive gives the integral from `s` to
`t`, including both orientations and the diagonal. The estimates below use
only coefficient jets on one fixed ball and lose no derivatives. They are
consumed by the signed row estimates for `W₀` and the complete residual
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicTransport.RowBounds

open NullTransport.AmplitudeTame FullPhaseCharts.InverseEstimates

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- Source-time evaluation of the fixed primitive in
`app:ch_regular_base:lem:characteristic-kernel`. -/
def sourceTimeMap : (ℝ × (ℝ × P)) →L[ℝ] ℝ × (ℝ × P) :=
  ((ContinuousLinearMap.fst ℝ ℝ P).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × P))).prod
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × P))

omit [FiniteDimensional ℝ P] in
/-- Source-time evaluation preserves every centered coefficient ball
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem sourceTimeMap_mapsTo_closedBall (p : P) (σ : ℝ) :
    MapsTo (sourceTimeMap (P := P)) (closedBall (0, (0, p)) σ)
      (closedBall (0, (0, p)) σ) := by
  intro q hq
  simp only [mem_closedBall, Prod.dist_eq, Real.dist_eq, sub_zero] at hq ⊢
  change max |q.2.1| (max |q.2.1| (dist q.2.2 p)) ≤ σ
  exact max_le ((le_max_left _ _).trans ((le_max_right _ _).trans hq))
    ((le_max_right _ _).trans hq)

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Every actual segment between source and output time stays in the fixed
coefficient ball. This discharges the domain condition for the literal
integral and `norm_rowTransport_le`, in both time orientations
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem row_timeSegment_mem_closedBall {p : P} {σ : ℝ}
    {q : ℝ × (ℝ × P)} (hq : q ∈ closedBall (0, (0, p)) σ)
    {u : ℝ} (hu : u ∈ uIcc q.2.1 q.1) :
    (u, q.2) ∈ closedBall (0, (0, p)) σ := by
  rw [← closedBall_prod_same, ← closedBall_prod_same] at hq ⊢
  exact ⟨(convex_closedBall (0 : ℝ) σ).ordConnected.uIcc_subset hq.2.1 hq.1 hu, hq.2⟩

/-- The actual oriented integral in the signed characteristic row
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def rowIntegral (c : ℝ × (ℝ × P) → ℝ) (q : ℝ × (ℝ × P)) : ℝ :=
  ∫ u in q.2.1..q.1, c (u, q.2)

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Both time orientations, including `t = s`, are given by the difference
of two fixed-zero primitives (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rowIntegral_eq_fixed_primitive {p : P} {R : ℝ} (hR : 0 < R)
    {c : ℝ × (ℝ × P) → ℝ} (hc : ContinuousOn c (ball (0, (0, p)) R))
    {q : ℝ × (ℝ × P)} (hq : q ∈ ball (0, (0, p)) R) :
    rowIntegral c q = (∫ u in (0 : ℝ)..q.1, c (u, q.2)) -
      ∫ u in (0 : ℝ)..q.2.1, c (u, q.2) := by
  rw [← ball_prod_same, ← ball_prod_same] at hc hq
  have hct : ContinuousOn (fun u ↦ c (u, q.2)) (ball (0 : ℝ) R) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu ↦ ⟨hu, hq.2⟩)
  have hI : OrdConnected (ball (0 : ℝ) R) := (convex_ball (0 : ℝ) R).ordConnected
  have hzero : (0 : ℝ) ∈ ball (0 : ℝ) R := mem_ball_self hR
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hct.mono (hI.uIcc_subset hzero hq.2.1)).intervalIntegrable
    (hct.mono (hI.uIcc_subset hq.2.1 hq.1)).intervalIntegrable
  dsimp [rowIntegral]
  linarith

/-- Joint smoothness of the actual integral on the open buffered ball,
including derivatives in the initial time and every characteristic label
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_rowIntegral {p : P} {R : ℝ} (hR : 0 < R)
    {c : ℝ × (ℝ × P) → ℝ} (hc : ContDiffOn ℝ ∞ c (ball (0, (0, p)) R)) :
    ContDiffOn ℝ ∞ (rowIntegral c) (ball (0, (0, p)) R) := by
  have hc' := hc
  rw [← ball_prod_same, ← ball_prod_same] at hc'
  have hi := contDiffOn_parametricIntervalIntegral isOpen_ball
    (convex_ball (0 : ℝ) R).ordConnected (isOpen_ball.prod isOpen_ball)
    hc' (mem_ball_self hR)
  rw [ball_prod_same, ball_prod_same] at hi
  have his : ContDiffOn ℝ ∞
      (fun q : ℝ × (ℝ × P) ↦ ∫ u in (0 : ℝ)..q.2.1, c (u, q.2))
      (ball (0, (0, p)) R) := by
    apply hi.comp (sourceTimeMap (P := P)).contDiff.contDiffOn
    intro q hq
    simp only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero] at hq ⊢
    change max |q.2.1| (max |q.2.1| (dist q.2.2 p)) < R
    exact max_lt (lt_of_le_of_lt (le_max_left _ _) ((max_lt_iff.mp hq).2))
      (max_lt_iff.mp hq).2
  exact (hi.sub his).congr (fun q hq ↦ rowIntegral_eq_fixed_primitive hR hc.continuousOn hq)

/-- Linear joint bound for the actual variable-lower-end integral on a fixed
ball. The constant precedes the coefficient and its open enlargement; no
integral derivative bounds are assumed. Consumer: the row exponential in
`app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_cNorm_rowIntegral_le (p : P) {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), σ < R →
      ∀ c : ℝ × (ℝ × P) → ℝ,
      ContDiffOn ℝ ∞ c (ball (0, (0, p)) R) →
      cNorm (closedBall (0, (0, p)) σ) m (rowIntegral c) ≤
        C * cNorm (closedBall (0, (0, p)) σ) m c := by
  obtain ⟨A, hA, hbound⟩ := exists_cNorm_timeIntegral_le_same_ball ((0 : ℝ), p) hσ m
  let L := sourceTimeMap (P := P)
  let D := linearNormCost L m
  have hD : 0 < D := linearNormCost_pos _ _
  refine ⟨(1 + D) * A, mul_pos (by linarith) hA, ?_⟩
  intro R hσR c hc
  let K := closedBall ((0 : ℝ), ((0 : ℝ), p)) σ
  let f := fun q : ℝ × (ℝ × P) ↦ ∫ u in (0 : ℝ)..q.1, c (u, q.2)
  obtain ⟨W, hW, hKW, hf⟩ := exists_timeIntegral_smooth_near_ball ((0 : ℝ), p) hσ
    isOpen_ball (closedBall_subset_ball hσR) hc
  have hlin := cNorm_comp_linear_le L (isCompact_closedBall (0, (0, p)) σ)
    hW hKW hf (sourceTimeMap_mapsTo_closedBall p σ) m
  have he : ∀ q ∈ K, rowIntegral c =ᶠ[𝓝 q] f - f ∘ L := by
    intro q hq
    filter_upwards [isOpen_ball.mem_nhds (closedBall_subset_ball hσR hq)] with z hz
    exact rowIntegral_eq_fixed_primitive (hσ.trans hσR) hc.continuousOn hz
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq he m]
  have hsum := cNorm_add_le_of_contDiffAt (f := f) (g := -(f ∘ L)) (isCompact_closedBall (0, (0, p)) σ)
    (fun q hq ↦ (hf.contDiffAt (hW.mem_nhds (hKW hq))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    (fun q hq ↦ (((hf.contDiffAt (hW.mem_nhds
      (hKW (sourceTimeMap_mapsTo_closedBall p σ hq)))).comp q
        L.contDiff.contDiffAt).neg).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  have hsub : cNorm K m (f - f ∘ L) ≤ cNorm K m f + cNorm K m (f ∘ L) := by
    simpa only [sub_eq_add_neg, cNorm_neg] using hsum
  have hb := hbound (ball (0, (0, p)) R) isOpen_ball (closedBall_subset_ball hσR) c hc
  calc
    _ ≤ cNorm K m f + cNorm K m (f ∘ L) := hsub
    _ ≤ (1 + D) * cNorm K m f := by change cNorm K m (f ∘ L) ≤ D * cNorm K m f at hlin; nlinarith
    _ ≤ (1 + D) * (A * cNorm K m c) :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    _ = _ := by ring

/-- Joint one-high estimate for the literal two-time exponential. Its low
budget is on the primitive coefficient alone, and there is no derivative loss
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_cNorm_rowFactor_le (p : P) {σ : ℝ} (hσ : 0 < σ)
    (m : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), σ < R →
      ∀ c : ℝ × (ℝ × P) → ℝ,
      ContDiffOn ℝ ∞ c (ball (0, (0, p)) R) →
      cNorm (closedBall (0, (0, p)) σ) 0 c ≤ M →
      cNorm (closedBall (0, (0, p)) σ) m
        (fun q : ℝ × (ℝ × P) ↦ transportFactor (fun u ↦ c (u, q.2)) q.2.1 q.1) ≤
        C * (1 + cNorm (closedBall (0, (0, p)) σ) m c) := by
  obtain ⟨A₀, hA₀, hi₀⟩ := exists_cNorm_rowIntegral_le p hσ 0
  obtain ⟨A, hA, hi⟩ := exists_cNorm_rowIntegral_le p hσ m
  obtain ⟨B, hB, he⟩ := exists_cNorm_exp_neg_le_joint_tame_closedBall
    ((0 : ℝ), ((0 : ℝ), p)) hσ m (A₀ * M)
  refine ⟨B * (1 + A), mul_pos hB (by linarith), ?_⟩
  intro R hσR c hc hlow
  have hl := (hi₀ R hσR c hc).trans (mul_le_mul_of_nonneg_left hlow hA₀.le)
  have hh := he (ball (0, (0, p)) R) isOpen_ball (closedBall_subset_ball hσR)
    (rowIntegral c) (contDiffOn_rowIntegral (hσ.trans hσR) hc) hl
  apply hh.trans
  have hn := cNorm_nonneg (closedBall (0, (0, p)) σ) m c
  have hb := hi R hσR c hc
  have hb' : 1 + cNorm (closedBall (0, (0, p)) σ) m (rowIntegral c) ≤
      (1 + A) * (1 + cNorm (closedBall (0, (0, p)) σ) m c) := by nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb' hB.le

end JanetCartan.CharacteristicTransport.RowBounds
