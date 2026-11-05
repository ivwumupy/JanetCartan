module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.Symbol
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability

/-!
# Retaining the frozen chart and its low-order perturbation family

The zero-error specialization of `app:lem:common-hamilton-phase` is selected
once. The same state ball, source buffers, target, central equivalence and
positive scalar C³ threshold are retained with that exact reference chart.
This is a construction from transverse initial data, not an assumption of a
reference phase or of any momentum comparison estimate.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase

/-- The precise low-order chart output retained in the frozen construction
(`app:lem:common-hamilton-phase`). The producer constructs each field; the
comparison here is for augmented projections, not for full phase gradients. -/
structure BufferedChartControl {n : ℕ}
    (j : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n)
    (s₀ : InitialData (Euclidean (n - 1))) (z₀ : Euclidean n × Euclidean n)
    (R r b K : ℝ) (V : Set (Euclidean n × (ℝ × Euclidean (n - 1))))
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1))))
    (Φ₀ : HamiltonFlow (frozenSymbol n) (Euclidean (n - 1)))
    {H : HomogeneousSymbol (Euclidean n)}
    (Φ : HamiltonFlow H (Euclidean (n - 1))) (χ : ProjectionChart Φ) : Prop where
  time_eq : Φ.time = Φ₀.time
  parameters_eq : Φ.parameters = Φ₀.parameters
  section_eq : Φ.sectionMap = j.toContinuousLinearMap
  position_smooth : ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters)
  momentum_smooth : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters)
  state_mem : ∀ q ∈ Φ.time ×ˢ Φ.parameters,
    (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R
  target_eq : χ.target = V
  source_eq : χ.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V
  source_subset : χ.source ⊆ ball ((0 : ℝ), s₀) (2 * r)
  source_admissible : closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters
  coordinates_smooth : ContDiffOn ℝ ∞ χ.coordinates V
  inner_buffer : cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V
  outer_buffer : cthickening b (closure V) ⊆
    Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r)
  preimage_buffer : Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
    ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r)
  derivative_gap : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
    ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ Φ.augmentedProjection q) -
      ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2
  projection_comparison : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
    ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤
      K * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - (frozenSymbol n).h z) ∧
    ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤
      K * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - (frozenSymbol n).h z)

/-- Output sidecar for a fixed frozen chart. In particular `reference_control`
uses the very same flow and chart as the zero-error witness
(`app:lem:common-hamilton-phase`, `app:ch_seed:prop:seed-actual-menu`, Step 1).
Neither the affine identity nor a full-phase comparison is a field here. -/
structure FrozenHamiltonFamily {n : ℕ}
    (j : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n) (ν : Euclidean n)
    (s₀ : InitialData (Euclidean (n - 1))) (τ₀ : ℝ)
    (D : Set (Euclidean n × Euclidean n)) (R : ℝ) where
  flow : HamiltonFlow (frozenSymbol n) (Euclidean (n - 1))
  chart : ProjectionChart flow
  equivalence : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
    (Euclidean n × (ℝ × Euclidean (n - 1)))
  sourceRadius : ℝ
  buffer : ℝ
  threshold : ℝ
  coefficient : ℝ
  target : Set (Euclidean n × (ℝ × Euclidean (n - 1)))
  sourceRadius_pos : 0 < sourceRadius
  buffer_pos : 0 < buffer
  threshold_pos : 0 < threshold
  coefficient_pos : 0 < coefficient
  target_open : IsOpen target
  target_compact_closure : IsCompact (closure target)
  base_mem : (j s₀.1, s₀.2) ∈ target
  reference_control : BufferedChartControl j s₀ (transverseSectionState j ν (s₀, τ₀))
    R sourceRadius buffer coefficient target equivalence flow flow chart
  perturbations : ∀ H : HomogeneousSymbol (Euclidean n), D ⊆ H.domain →
    ContDiffOn ℝ ∞ H.h D →
    cNorm (closedBall (transverseSectionState j ν (s₀, τ₀)) R) 3
      (fun z ↦ H.h z - (frozenSymbol n).h z) ≤ threshold →
    ∃ (Φ : HamiltonFlow H (Euclidean (n - 1))) (χ : ProjectionChart Φ),
      BufferedChartControl j s₀ (transverseSectionState j ν (s₀, τ₀))
        R sourceRadius buffer coefficient target equivalence flow Φ χ

/-- Construct the low-order sidecar from actual transverse section data. The
only conditional inputs are the open state buffer, its contained closed ball,
energy and transverse derivative, and the orthogonal spanning section; the
reference and all perturbation charts are outputs
(`app:lem:common-hamilton-phase`). -/
theorem exists_frozenHamiltonFamily {n : ℕ}
    {D : Set (Euclidean n × Euclidean n)} (hD : IsOpen D)
    (hDH : D ⊆ (frozenSymbol n).domain)
    (j : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n) (ν : Euclidean n)
    (horth : ∀ v, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x, ⟪ν, x⟫_ℝ = 0 → ∃ u, j u = x)
    {s₀ : InitialData (Euclidean (n - 1))} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : (frozenSymbol n).h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪(frozenSymbol n).hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    Nonempty (FrozenHamiltonFamily j ν s₀ τ₀ D R) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  have hH := (frozenSymbol_smooth n).mono hDH
  obtain ⟨Ψ, A, r, b, δ, K, V, hr, hb, hδ, hK, hV, hVc, hbase, hadm, hfamily⟩ :=
    exists_common_buffered_symbol_charts (frozenSymbol n) hD hDH hH
      j ν horth hspan hR hRD henergy htrans
  have hzero : cNorm (closedBall z₀ R) 3
      (fun z ↦ (frozenSymbol n).h z - (frozenSymbol n).h z) = 0 := by
    simp only [sub_self]
    exact cNorm_zero _ _
  obtain ⟨Φ₀, χ₀, ht₀, hp₀, hj₀, hx₀, hm₀, hs₀, hχt₀, hχs₀, hχb₀, hc₀,
    hi₀, ho₀, hpre₀, hg₀, hclose₀⟩ :=
    hfamily (frozenSymbol n) hDH hH (by rw [hzero]; exact hδ.le)
  have heq (q) (hq : q ∈ ball ((0 : ℝ), s₀) (3 * r)) :
      Φ₀.augmentedProjection q = Ψ.augmentedProjection q ∧
      fderiv ℝ Φ₀.augmentedProjection q = fderiv ℝ Ψ.augmentedProjection q := by
    have hh := hclose₀ q hq
    rw [hzero, mul_zero] at hh
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh.1 (norm_nonneg _))),
      sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh.2 (norm_nonneg _)))⟩
  refine ⟨⟨Φ₀, χ₀, A, r, b, δ, K, V, hr, hb, hδ, hK, hV, hVc, hbase, ?_, ?_⟩⟩
  · refine ⟨rfl, rfl, hj₀, hx₀, hm₀, hs₀, hχt₀, hχs₀, hχb₀, ?_, hc₀,
      hi₀, ho₀, hpre₀, hg₀, ?_⟩
    · simpa only [ht₀, hp₀] using hadm
    · intro q _
      rw [show cNorm (closedBall (transverseSectionState j ν (s₀, τ₀)) R) 3
        (fun z ↦ (frozenSymbol n).h z - (frozenSymbol n).h z) = 0 from hzero]
      simp
  · intro H hdom hsm hsmall
    obtain ⟨Φ, χ, ht, hp, hj, hx, hm, hs, hχt, hχs, hχb, hc,
      hi, ho, hpre, hg, hclose⟩ := hfamily H hdom hsm hsmall
    refine ⟨Φ, χ, ht.trans ht₀.symm, hp.trans hp₀.symm, hj, hx, hm, hs,
      hχt, hχs, hχb, ?_, hc, hi, ho, hpre, hg, ?_⟩
    · simpa only [ht, hp] using hadm
    · intro q hq
      rw [(heq q hq).1, (heq q hq).2]
      exact hclose q hq

/-- Any zero-error specialization of the retained family has exactly the
reference inverse coordinates on the common target. This follows from the
proved projection comparison and the reference chart's inverse identities,
not from a fresh existential chart (`app:lem:common-hamilton-phase`). -/
theorem FrozenHamiltonFamily.zero_error_coordinates_eq {n : ℕ}
    {j : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n} {ν : Euclidean n}
    {s₀ : InitialData (Euclidean (n - 1))} {τ₀ R : ℝ}
    {D : Set (Euclidean n × Euclidean n)} (F : FrozenHamiltonFamily j ν s₀ τ₀ D R)
    {Φ : HamiltonFlow (frozenSymbol n) (Euclidean (n - 1))} {χ : ProjectionChart Φ}
    (hχ : BufferedChartControl j s₀ (transverseSectionState j ν (s₀, τ₀))
      R F.sourceRadius F.buffer F.coefficient F.target F.equivalence F.flow Φ χ)
    {z : Euclidean n × (ℝ × Euclidean (n - 1))} (hz : z ∈ F.target) :
    χ.coordinates z = F.chart.coordinates z := by
  have hzχ : z ∈ χ.target := hχ.target_eq.symm ▸ hz
  have hs := χ.maps_to_source z hzχ
  rw [hχ.source_eq] at hs
  have hc := (hχ.projection_comparison _ hs.1).1
  have hzero : cNorm (closedBall (transverseSectionState j ν (s₀, τ₀)) R) 3
      (fun z ↦ (frozenSymbol n).h z - (frozenSymbol n).h z) = 0 := by
    simp only [sub_self]
    exact cNorm_zero _ _
  rw [hzero, mul_zero] at hc
  have heq := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hc (norm_nonneg _)))
  have hproj : F.flow.augmentedProjection (chartLift χ.coordinates z) = z := by
    rw [← heq]
    exact Prod.ext (χ.right_inverse z hzχ) rfl
  have hs₀ : chartLift χ.coordinates z ∈ F.chart.source := by
    rw [F.reference_control.source_eq]
    exact ⟨hs.1, by change F.flow.augmentedProjection _ ∈ F.target; rw [hproj]; exact hz⟩
  have hi := F.chart.left_inverse _ hs₀
  change F.chart.coordinates (F.flow.position (chartLift χ.coordinates z), z.2) =
    χ.coordinates z at hi
  have hx : F.flow.position (chartLift χ.coordinates z) = z.1 := congrArg Prod.fst hproj
  rw [hx] at hi
  exact hi.symm

end JanetCartan.ActualCarriers.FrozenPhaseReference
