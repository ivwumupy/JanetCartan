module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.ChartComparison
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.AveragedGradient

/-!
# Phases on common buffered targets

Assemble the smooth scalar-symbol perturbation construction with the phase
identities of `app:lem:common-hamilton-phase`. The same target and source buffers
work for every sufficiently `C³`-close symbol. Inverse-coordinate and phase
comparison estimates follow from the actual projection gap. This is a local
construction; conic extension and arbitrary-order estimates are separate.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]

/-- Common smooth phases for a scalar `C³` neighborhood of a transverse symbol
(`app:lem:common-hamilton-phase`, `app:ch_regular_base:eq:actual-eikonal`).
The root, flow, inverse chart and phase are constructed. The full differential,
eikonal and section identities hold on the common target, with a quantitative
comparison to a fixed reference phase. No flow-closeness or inverse-chart
premise is supplied. Conic extension, a common mixed-Hessian gap across symbols,
and higher-order estimates are not asserted by this local result. -/
theorem exists_commonBufferedHamiltonPhases
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀)
      (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
      (r b δ K ρ : ℝ) (V : Set (E × (ℝ × U))),
      0 < r ∧ 0 < b ∧ 0 < δ ∧ 0 < K ∧ 0 < ρ ∧
      IsOpen V ∧ IsCompact (closure V) ∧ (j s₀.1, s₀.2) ∈ V ∧
      closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * ρ) ⊆ V ∧
      C₀.target = V ∧ ContDiffOn ℝ ∞ (phase C₀.coordinates) V ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          C.target = V ∧
          C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧ ContDiffOn ℝ ∞ (phase C.coordinates) V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
                ≤ 1 / 2) ∧
          (∀ z ∈ V,
            HasFDerivAt (phase C.coordinates)
              (phaseDifferential (Φ.momentum (chartLift C.coordinates z)) (C.coordinates z)) z ∧
            H.h (z.1, gradient (fun x ↦ phase C.coordinates (x, z.2)) z.1) = z.2.1 ∧
            HasFDerivAt (fun η ↦ phase C.coordinates (z.1, η))
              (canonicalCovector (C.coordinates z)) z.2 ∧
            ‖C.coordinates z - C₀.coordinates z‖ ≤
              K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) ∧
            ‖phase C.coordinates z - phase C₀.coordinates z‖ ≤
              (|z.2.1| + ‖z.2.2‖) * K *
                cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)) ∧
          (∀ u η, (0, (u, η)) ∈ C.source →
            phase C.coordinates (j u, η) = ⟪u, η.2⟫_ℝ) ∧
          (∀ s ∈ ball s₀ (min r ρ), (0, s) ∈ C.source ∧
            phase C.coordinates (j s.1, s.2) = ⟪s.1, s.2.2⟫_ℝ) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨Ψ₀, A, r, b, δ, B, V, hr, hb, hδ, hB, hV, hVc, hzV, hadm, hfamily⟩ :=
    exists_common_buffered_symbol_charts H₀ hD hDH₀ hH₀ j ν horth hspan
      hR hRD henergy htrans
  have hzero : cNorm (closedBall z₀ R) 3 (fun z ↦ H₀.h z - H₀.h z) = 0 := by
    simp only [sub_self]
    exact cNorm_zero _ _
  obtain ⟨Φ₀, C₀, ht₀, hp₀, _, _, _, _, hC₀t, hC₀s, _, hC₀,
    _, _, _, _, hclose₀⟩ := hfamily H₀ hDH₀ hH₀ (by rw [hzero]; exact hδ.le)
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  let K := 2 * (N + 1) * B
  have hN : 0 ≤ N := by
    exact norm_nonneg (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))
  have hK : 0 < K := by dsimp [K]; positivity
  have heq₀ : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      Φ₀.augmentedProjection q = Ψ₀.augmentedProjection q := by
    intro q hq
    have hh := (hclose₀ q hq).1
    rw [hzero, mul_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV _ hzV
  have hbox : closedBall (j s₀.1) (3 * (ε / 4)) ×ˢ
      closedBall s₀.2 (3 * (ε / 4)) ⊆ V := by
    intro z hz
    apply hεV
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hz.1).trans_lt (by linarith),
      (mem_closedBall.mp hz.2).trans_lt (by linarith)⟩
  refine ⟨Φ₀, C₀, A, r, b, δ, K, ε / 4, V, hr, hb, hδ, hK, by positivity,
    hV, hVc, hzV, hbox, hC₀t, ?_, ?_⟩
  · exact hC₀t ▸ C₀.contDiffOn_phase (hC₀t.symm ▸ hC₀)
  intro H hDH hH hsmall
  obtain ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hCbuffer, hC,
    hinner, houter, hpre, hgap, hclose⟩ := hfamily H hDH hH hsmall
  have hadm' : closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters := by
    simpa only [ht, hp] using hadm
  have hclose' : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤
        B * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) := by
    intro q hq
    rw [heq₀ q hq]
    exact (hclose q hq).1
  refine ⟨Φ, C, ht.trans ht₀.symm, hp.trans hp₀.symm, hj, hx, hξ, hrange,
    hCt, hCs, hCbuffer, hadm', hC, hCt ▸ C.contDiffOn_phase (hCt.symm ▸ hC),
    hinner, houter, hpre, hgap, ?_, ?_, ?_⟩
  · intro z hz
    have hzC : z ∈ C.target := hCt.symm ▸ hz
    have hzC₀ : z ∈ C₀.target := hC₀t.symm ▸ hz
    have hlift : chartLift C.coordinates z ∈ ball ((0 : ℝ), s₀) (3 * r) := by
      have hh := C.maps_to_source z hzC
      rw [hCs] at hh
      exact hh.1
    have hlift₀ : chartLift C₀.coordinates z ∈ ball ((0 : ℝ), s₀) (3 * r) := by
      have hh := C₀.maps_to_source z hzC₀
      rw [hC₀s] at hh
      exact hh.1
    have hc := C.norm_coordinates_sub_le_of_projection_close C₀ (convex_ball _ _) A
      (subset_closure.trans hadm') hgap hclose' hzC hzC₀ hlift hlift₀
    have hc' : ‖C.coordinates z - C₀.coordinates z‖ ≤
        K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) := by
      have hn := CompositionBounds.cNorm_nonneg (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)
      change _ ≤ 2 * N * (B * _) at hc
      dsimp [K]
      nlinarith [mul_nonneg hB.le hn]
    refine ⟨C.hasFDerivAt_phase hzC, C.eikonal hzC,
      C.hasFDerivAt_phase_canonical hzC, hc', ?_⟩
    calc
      _ ≤ (|z.2.1| + ‖z.2.2‖) * ‖C.coordinates z - C₀.coordinates z‖ :=
        C.norm_phase_sub_le C₀ z
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hc' (by positivity)
  · intro u η hs
    simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using C.initial_value hs

  · intro s hs
    have hsball : (0, s) ∈ ball ((0 : ℝ), s₀) (3 * r) := by
      rw [mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
      exact ⟨by positivity, (mem_ball.mp hs).trans_le
        ((min_le_left _ _).trans (by linarith))⟩
    have hsadm := (hadm' (subset_closure hsball)).2
    have htarget : (j s.1, s.2) ∈ V := by
      apply hbox
      have hdist := (mem_ball.mp hs).trans_le (min_le_right _ _)
      rw [Prod.dist_eq, max_lt_iff] at hdist
      constructor
      · rw [mem_closedBall, j.dist_map]
        linarith [hdist.1]
      · rw [mem_closedBall]
        linarith [hdist.2]
    have hsource : (0, s) ∈ C.source := by
      rw [hCs]
      refine ⟨hsball, ?_⟩
      simpa [HamiltonFlow.augmentedProjection, Φ.initial_position s hsadm, hj] using htarget
    exact ⟨hsource, by simpa [hj] using C.initial_value hsource⟩

end JanetCartan.HamiltonPhase
