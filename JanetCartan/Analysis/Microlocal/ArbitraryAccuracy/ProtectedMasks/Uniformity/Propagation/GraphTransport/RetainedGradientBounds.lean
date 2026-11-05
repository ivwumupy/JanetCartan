module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.LocalConstruction

/-!
# Uniform physical derivatives of the retained comparison gradients

The local construction in `app:ch_regular:thm:no-return`, retaining the order-two
phase estimate of `app:lem:common-hamilton-phase` on the very same charts. The
constant precedes the varying symbol and uses only its fixed C³ neighborhood.
The consumers are `physicalDirectRelation_comparison_graph_error_le` and
`comparisonChart_gradient_dist_le_of_derivative_bound`, via the chart-selection
equality of `exists_finite_comparison_cover_with_selection`.

This local producer does not identify arbitrary previously chosen existential
families. Finite selection and its instantiation in the initialized signed
no-return construction remain with the consuming construction.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section PhysicalHessian

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ (E × P) := Prod.normedSpace

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the phase Hessian to physical directions without increasing its
norm (`app:lem:common-hamilton-phase`). This supplies the derivative estimate
in `exists_localComparisonFamily_with_gradient_derivative_bound`. -/
private theorem norm_fderiv_physicalGradient_le
    {f : E × P → ℝ} {x : E} {η : P} (hf : ContDiffAt ℝ 2 f (x, η)) :
    ‖fderiv ℝ (gradient (fun y ↦ f (y, η))) x‖ ≤
      ‖iteratedFDeriv ℝ 2 f (x, η)‖ := by
  let i := ContinuousLinearMap.inl ℝ E P
  let R := (ContinuousLinearMap.compL ℝ E (E × P) ℝ).flip i
  have hi : ‖i‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ E P
  have hR : ‖R‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    exact (A.opNorm_comp_le i).trans (by nlinarith [norm_nonneg A])
  have he : fderiv ℝ (fun y ↦ f (y, η)) =ᶠ[𝓝 x]
      (fun y ↦ R (fderiv ℝ f (y, η))) := by
    have hnear := (continuousAt_id.prodMk continuousAt_const).tendsto.eventually
      (hf.eventually (by norm_num))
    filter_upwards [hnear] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y η) |>.fderiv
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := R.hasFDerivAt.comp x
    (hd.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x η))
  change ‖fderiv ℝ ((InnerProductSpace.toDual ℝ E).symm ∘
    fderiv ℝ (fun y ↦ f (y, η))) x‖ ≤ _
  rw [← norm_iteratedFDeriv_one,
    (InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left,
    norm_iteratedFDeriv_one, he.fderiv_eq]
  rw [show fderiv ℝ (fun y ↦ R (fderiv ℝ f (y, η))) x = _ from hc.fderiv]
  calc
    _ ≤ ‖R‖ * ‖(fderiv ℝ (fderiv ℝ f) (x, η)).comp i‖ := R.opNorm_comp_le _
    _ ≤ ‖(fderiv ℝ (fderiv ℝ f) (x, η)).comp i‖ :=
      mul_le_of_le_one_left (norm_nonneg ((fderiv ℝ (fderiv ℝ f) (x, η)).comp i)) hR
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (x, η)‖ * ‖i‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (x, η)‖ :=
      mul_le_of_le_one_right (norm_nonneg (fderiv ℝ (fderiv ℝ f) (x, η))) hi
    _ = _ := by rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

end PhysicalHessian

set_option maxHeartbeats 2000000 in
/-- Strengthen the actual local comparison producer with one uniform physical
gradient-derivative bound (`app:ch_regular:thm:no-return`). The hypotheses are
exactly those of `exists_localComparisonFamily`. All its geometry, flows,
inverse charts, buffers, quantitative comparisons, regular bounds and coverage
are constructed from the same retained common-phase witness. Its order-two
phase estimate costs scalar-symbol order three, bounded by the fixed reference
symbol and the existing perturbation threshold.

The bound is literally for `F.charts`, so the selection equality in
`exists_finite_comparison_cover_with_selection` transfers it to the finite
cover used by the graph-error estimates of `app:ch_regular:lem:finite-chain`.
The parent construction must still select and instantiate this strengthened
producer in its initialized signed no-return family. -/
theorem exists_localComparisonFamily_with_gradient_derivative_bound
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (hhom : H₀.ConicHomogeneous) {ξ : E} (hξ : ξ ≠ 0) (hz : (0, ξ) ∈ D)
    (he : H₀.h (0, ξ) = 0) (hν : H₀.hp (0, ξ) ≠ 0)
    {G M : Set E} (hG : IsOpen G) (hM : IsClosed M)
    (hreg : normalizedCovector ξ ∈ G \ M) :
    ∃ (F : LocalComparisonFamily H₀ D G M ξ) (Lx : ℝ), 0 ≤ Lx ∧
      ∀ H, ∀ η ∈ F.geometry.parameters,
        ∀ x ∈ closedBall 0 (2 * F.geometry.radius),
          ‖fderiv ℝ ((F.charts H).gradientMap η) x‖ ≤ Lx := by
  let ν := H₀.hp (0, ξ)
  let T : Submodule ℝ E := (ℝ ∙ ν)ᗮ
  let j : T →ₗᵢ[ℝ] E := T.subtypeₗᵢ
  have horth (v : T) : ⟪ν, j v⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property
  have hspan (x : E) (hx : ⟪ν, x⟫_ℝ = 0) : ∃ u : T, j u = x :=
    ⟨⟨x, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx⟩, rfl⟩
  have hξT : ξ ∈ T := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    ((H₀.euler (hDH₀ hz)).trans he)
  let ξT : T := ⟨ξ, hξT⟩
  let s₀ : InitialData T := (0, (0, ξT))
  have hj0 : j s₀.1 = 0 := map_zero j
  have hz₀ : transverseSectionState j ν (s₀, 0) = (0, ξ) := by
    simp [transverseSectionState, s₀, ξT, j]
  obtain ⟨R, angular, hR, hangular, hRD, hgap, hregular⟩ :=
    exists_regular_transverse_stateBall H₀ hD hDH₀ hξ hz hν hG hM hreg
  have henergy : H₀.h (transverseSectionState j ν (s₀, 0)) = s₀.2.1 := by
    simpa only [hz₀] using he
  have htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, 0)), ν⟫_ℝ ≠ 0 := by
    simpa only [hz₀] using inner_self_ne_zero.mpr hν
  obtain ⟨R₁, δg, c, hR₁, hR₁R, hδg, hc, hR₁D, hgapH⟩ :=
    exists_uniform_transverse_stateBall H₀ hD hDH₀ hH₀ hR hRD ν
      (inner_self_ne_zero.mpr hν)
  have haux := exists_commonBufferedHamiltonPhases H₀ hD hDH₀ hH₀
    j ν horth hspan (s₀ := s₀) (τ₀ := 0) hR₁ (hz₀.symm ▸ hR₁D) henergy htrans
  rw [hz₀] at haux
  obtain ⟨Ψ₀, B₀, Aaux, ra, ba, δa, Ka, ρa, Va,
    hra, _hba, hδa, hKa, hρa, _hVa, _hVac, _hcenterVa, hboxa,
    _hB₀target, _hB₀smooth, haux⟩ := haux
  let R₂ := min R₁ (min ra ρa) / 2
  have hR₂ : 0 < R₂ := by dsimp [R₂]; positivity
  have hR₂R₁ : R₂ < R₁ := by have := min_le_left R₁ (min ra ρa); dsimp [R₂]; linarith
  have hR₂ra : R₂ < ra := by
    have := (min_le_right R₁ (min ra ρa)).trans (min_le_left ra ρa)
    dsimp [R₂]; linarith
  have hR₂ρa : R₂ < ρa := by
    have := (min_le_right R₁ (min ra ρa)).trans (min_le_right ra ρa)
    dsimp [R₂]; linarith
  have hR₂D : closedBall ((0 : E), ξ) R₂ ⊆ D :=
    (closedBall_subset_closedBall hR₂R₁.le).trans hR₁D
  have hfamily := exists_commonTameContinuousConicHamiltonPhases H₀ hD hDH₀ hH₀
    j ν horth hspan (s₀ := s₀) (τ₀ := 0) hR₂ (hz₀.symm ▸ hR₂D)
    henergy htrans (by simpa only [hz₀] using hξ)
  rw [hz₀] at hfamily
  obtain ⟨ℓ, A, r, b, ρ, σ, a, δc, ε, β, t, bounds, V, W, Φ₀, C₀,
    hr, hb, hρ, hσ, _ha, hδc, _hε, hβ, _ht, hbounds, _hℓ, _hV, _hVc,
    hW, _hWc, _hΩ, _hQ, _hbuf, hnormal, hBP, hcone, Fc, Cc, hcprops, _hcont⟩ := hfamily
  let δ := min δg (min δa δc)
  have hδ : 0 < δ := lt_min hδg (lt_min hδa hδc)
  let S := {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
    H.ConicHomogeneous ∧ cNorm (closedBall (0, ξ) R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}
  have hmono (H : S) {R' : ℝ} (hR' : R' ≤ R) :
      cNorm (closedBall (0, ξ) R') 3 (fun z ↦ H.1.h z - H₀.h z) ≤
        cNorm (closedBall (0, ξ) R) 3 (fun z ↦ H.1.h z - H₀.h z) :=
    cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hR')
      (isCompact_closedBall _ _) (fun z hz ↦
        ((H.2.2.1.sub hH₀).contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp))
  let Hc (H : S) := (⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1,
    (hmono H (hR₂R₁.le.trans hR₁R.le)).trans (H.2.2.2.2.trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩ :
    {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
      H.ConicHomogeneous ∧ cNorm (closedBall (0, ξ) R₂) 3
        (fun z ↦ H.h z - H₀.h z) ≤ δc})
  let F (H : S) := Fc (Hc H)
  let C (H : S) := Cc (Hc H)
  have hprops (H : S) := hcprops (Hc H)
  have haex (H : S) := haux H.1 H.2.1 H.2.2.1
    ((hmono H hR₁R.le).trans (H.2.2.2.2.trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  let Fa (H : S) := (haex H).choose
  let Ca (H : S) := (haex H).choose_spec.choose
  have haprops (H : S) := (haex H).choose_spec.choose_spec
  let g : ComparisonGeometry E := {
    tangentSpace := T
    normalizer := ℓ
    center := s₀.2
    center_energy := rfl
    radius := ρ / 12
    radius_pos := by positivity
    parameterRadius := σ
    parameterRadius_pos := hσ }
  have hdomO : g.domain ⊆ ball (j s₀.1) ρ ×ˢ
      (ball s₀.2 (3 * a) ∩ canonicalCone ℓ (ball s₀.2 (3 * a))) := by
    intro z hz
    refine ⟨?_, hnormal (ball_subset_closedBall hz.2)⟩
    rw [hj0]
    exact ball_subset_ball (by dsimp [g]; linarith) hz.1
  have hdomV : g.domain ⊆ V := fun z hz ↦ hBP ⟨(hdomO hz).1, (hdomO hz).2.1⟩
  have hdomCone : g.domain ⊆ CharacteristicRoot.conicDomain ℓ V := by
    intro z hz
    have hx : z.1 ∈ closedBall (j s₀.1) (ρ / 2) := by
      rw [hj0]
      exact ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by dsimp [g]; linarith)) hz.1
    have hh := hcone ⟨hx, ball_subset_closedBall hz.2⟩
    exact ⟨hh.1, hBP hh.2⟩
  let charts (H : S) : ComparisonChart H.1 g := by
    have hp := hprops H
    have hCt := hp.2.2.2.2.2.2.2.2.1
    exact {
      homogeneous := H.2.2.2.1
      flow := F H
      chart := C H
      section_eq := hp.2.2.2.2.1
      momentum_smooth := hp.2.2.2.2.2.2.1
      coordinates_smooth := hCt.symm ▸ hp.2.2.2.2.2.2.2.2.2.2.2.2.1
      target_contains := hCt.symm ▸ hdomV
      conic_contains := hCt.symm ▸ hdomCone
      phase_eq := fun z hz ↦ hp.2.1 z (hdomO hz)
      sourceRadius := r
      sourceRadius_pos := hr
      buffer := b
      buffer_pos := hb
      source_eq := hCt.symm ▸ hp.2.2.2.2.2.2.2.2.2.1
      source_subset := hp.2.2.2.2.2.2.2.2.2.2.1
      source_admissible := hp.2.2.2.2.2.2.2.2.2.2.2.1
      source_target_buffer := hCt.symm ▸ hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      target_source_buffer := hCt.symm ▸ hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      preimage_buffer := hCt.symm ▸ hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 }
  have hzero : cNorm (closedBall ((0 : E), ξ) R) 3 (fun z ↦ H₀.h z - H₀.h z) = 0 := by
    simp only [sub_self]
    exact cNorm_zero _ _
  let Href : S := ⟨H₀, hDH₀, hH₀, hhom, by rw [hzero]; exact hδ.le⟩
  have hunit : ‖‖ξT‖⁻¹ • ξT‖ = 1 := by
    apply norm_smul_inv_norm
    intro heq
    apply hξ
    exact congrArg Subtype.val heq
  have hsourceRadius (H : S) : 3 * r ≤ R₂ :=
    sourceRadius_le_stateRadius (F H) j (hprops H).2.2.2.2.1
      (‖ξT‖⁻¹ • ξT) hunit s₀.2 hr (hprops H).2.2.2.2.2.2.2.2.2.2.2.1
        (hprops H).2.2.2.2.2.2.2.1
  have hstateEq (H : S) : EqOn
      (fun q ↦ ((F H).position q, (F H).momentum q))
      (fun q ↦ ((Fa H).position q, (Fa H).momentum q))
      (ball ((0 : ℝ), s₀) (3 * r)) := by
    obtain ⟨_ht, _hp, hj, _hx, _hm, hrange, _hCt, _hCs, _hbuf, hadm, _rest⟩ := haprops H
    apply (F H).state_eq_on_transverse_ball (Fa H) hD H.2.1 H.2.2.1 hR₁D
      (by positivity) j ν hν horth hspan (hprops H).2.2.2.2.1 hj
    · intro z hz
      exact abs_pos.mp (hc.trans_le (hgapH H.1 H.2.1 H.2.2.1
        (H.2.2.2.2.trans (min_le_left _ _)) z hz))
    · exact subset_closure.trans (hprops H).2.2.2.2.2.2.2.2.2.2.2.1
    · exact (ball_subset_ball (by linarith [hsourceRadius H])).trans
        (subset_closure.trans hadm)
    · intro q hq
      exact closedBall_subset_closedBall hR₂R₁.le ((hprops H).2.2.2.2.2.2.2.1 q hq)
    · exact hrange
  have hdomVa (H : S) : g.domain ⊆ Va := by
    intro z hz
    have ht := (charts H).target_contains hz
    have hs := (charts H).chart.maps_to_source z ht
    have ha := (charts H).chart.source_admissible _ hs
    have hb := (hprops H).2.2.2.2.2.2.2.1 _ ha
    have hx : dist z.1 0 ≤ R₂ := by
      have hh := (le_max_left _ _).trans (mem_closedBall.mp hb)
      rwa [(charts H).chart.right_inverse z ht] at hh
    have hη : dist z.2 s₀.2 < 2 * r := by
      have hh := mem_ball.mp ((charts H).source_subset hs)
      exact (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hh)
    apply hboxa
    rw [hj0]
    exact ⟨mem_closedBall.mpr (by linarith), mem_closedBall.mpr (by
      linarith [hsourceRadius H])⟩
  have hcoordsEq (H : S) : EqOn (C H).coordinates (Ca H).coordinates g.domain := by
    intro z hz
    obtain ⟨_ht, _hp, _hj, _hx, _hm, _hrange, hCt, hCs, _rest⟩ := haprops H
    have ht := (charts H).target_contains hz
    have hs := (charts H).chart.maps_to_source z ht
    have hq : chartLift (C H).coordinates z ∈ ball ((0 : ℝ), s₀) (3 * r) :=
      ball_subset_ball (by linarith) ((charts H).source_subset hs)
    have hx : (Fa H).position (chartLift (C H).coordinates z) = z.1 :=
      (congrArg Prod.fst (hstateEq H hq)).symm.trans ((C H).right_inverse z ht)
    have hqa : chartLift (C H).coordinates z ∈ (Ca H).source := by
      rw [hCs]
      refine ⟨ball_subset_ball (by linarith [hsourceRadius H]) hq, ?_⟩
      change ((Fa H).position (chartLift (C H).coordinates z), z.2) ∈ Va
      rw [hx]
      exact hdomVa H hz
    have hh := (Ca H).left_inverse _ hqa
    rw [hx] at hh
    exact hh.symm
  have hrefCoords : EqOn (C Href).coordinates B₀.coordinates g.domain := by
    intro z hz
    rw [hcoordsEq Href hz]
    have hh := ((haprops Href).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 z
      (hdomVa Href hz)).2.2.2.1
    have hzero' : cNorm (closedBall ((0 : E), ξ) R₁) 3
        (fun z ↦ H₀.h z - H₀.h z) = 0 := by
      simp only [sub_self]; exact cNorm_zero _ _
    change ‖(Ca Href).coordinates z - B₀.coordinates z‖ ≤
      Ka * cNorm (closedBall (0, ξ) R₁) 3 (fun z ↦ H₀.h z - H₀.h z) at hh
    have hh0 : ‖(Ca Href).coordinates z - B₀.coordinates z‖ ≤ 0 := by
      simpa only [hzero', mul_zero] using hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh0 (norm_nonneg _)))
  have hcenterW : ξ ∈ W := by
    obtain ⟨_hest, _heq, _hsec, _hdiff, hj, _hpos, _hmom, hstate,
      hCt, hCs, _hsource, hadm, _hcoord, _hinner, _houter, _hpre, _hscale, _hchart,
      _hsmooth, _hhomogeneous, _hagreement, _heik, _hsection, havg⟩ := hprops Href
    change (F Href).sectionMap = j.toContinuousLinearMap at hj
    have hq : ((0 : ℝ), s₀) ∈ closure (ball ((0 : ℝ), s₀) (3 * r)) :=
      subset_closure (mem_ball_self (by positivity))
    have hs : s₀ ∈ (F Href).parameters := (hadm hq).2
    have hx : (F Href).position (0, s₀) = 0 := by
      simpa only [hj, LinearIsometry.coe_toContinuousLinearMap, hj0] using
        (F Href).initial_position s₀ hs
    have hp : (F Href).momentum (0, s₀) = ξ :=
      initial_momentum_eq_of_transverse_patch (F Href) (convex_closedBall _ _)
        (hRD.trans hDH₀) j ν hν horth hspan hj hgap hs
        ((closedBall_subset_closedBall (hR₂R₁.le.trans hR₁R.le)) (hstate _ (hadm hq)))
        (by simpa [s₀, ξT, j] using
          (mem_closedBall_self hR.le : ((0 : E), ξ) ∈ closedBall (0, ξ) R))
        (by simpa [Href, s₀, ξT, j] using he)
    have hzV : ((0 : E), s₀.2) ∈ V := by
      apply hBP
      exact ⟨hj0 ▸ mem_ball_self hρ, (hnormal (mem_closedBall_self (by positivity))).1⟩
    have hqsource : ((0 : ℝ), s₀) ∈ (C Href).source := by
      rw [hCs]
      exact ⟨mem_ball_self (by positivity), by
        change ((F Href).position (0, s₀), s₀.2) ∈ V
        simpa only [hx] using hzV⟩
    have hc : (C Href).coordinates (0, s₀.2) = (0, s₀.1) := by
      have hh : (C Href).coordinates ((F Href).position (0, s₀), s₀.2) =
          (0, s₀.1) := (C Href).left_inverse _ hqsource
      simpa only [hx] using hh
    have hg : gradient (fun x ↦ phase (C Href).coordinates (x, s₀.2)) 0 = ξ := by
      rw [(C Href).gradient_phase_eq_chartMomentum (z := (0, s₀.2)) (hCt.symm ▸ hzV)]
      simpa only [ProjectionChart.chartMomentum, chartLift, hc] using hp
    have h0B : (0 : E) ∈ ball (j s₀.1) ρ := hj0 ▸ mem_ball_self hρ
    have hinnerW := (havg 0 h0B 0 h0B).2.2.2.1
    apply hinnerW
    apply self_subset_cthickening
    refine ⟨s₀.2, mem_closedBall_self hσ.le, ?_⟩
    simpa only [averagedPhaseGradient_self] using hg
  let family : LocalComparisonFamily H₀ D G M ξ := by
    refine {
      geometry := g
      covectors := W
      covectors_open := hW
      center_mem := hcenterW
      stateRadius := R
      stateRadius_pos := hR
      state_subset := hRD
      threshold := δ
      threshold_pos := hδ
      lower := ‖ξ‖ / 2
      lower_pos := half_pos (norm_pos_iff.mpr hξ)
      upper := ‖ξ‖ + R
      angularBuffer := angular
      angularBuffer_pos := hangular
      charts := charts
      reference := charts Href
      sourceRadius := r
      sourceRadius_pos := hr
      sourceRadius_eq := fun _ ↦ rfl
      buffer := b
      buffer_pos := hb
      buffer_eq := fun _ ↦ rfl
      flowBound := 2 * ‖(Aaux : (ℝ × InitialData T) →L[ℝ] (E × (ℝ × T)))‖ + 1
      flowBound_pos := by positivity
      position_dist_le := ?_
      coordinateBound := Ka
      coordinateBound_pos := hKa
      coordinates_dist_le := ?_
      regular := ?_
      covers := ?_ }
    · intro H q hq w hw
      change dist ((F H).position q) ((F H).position w) ≤ _
      have heq : (F H).position q = (Fa H).position q := congrArg Prod.fst (hstateEq H hq)
      have hew : (F H).position w = (Fa H).position w := congrArg Prod.fst (hstateEq H hw)
      rw [heq, hew]
      have hsub : ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (3 * ra) :=
        ball_subset_ball (by linarith [hsourceRadius H])
      obtain ⟨_ht, _hp, _hj, _hx, _hm, _hrange, _hCt, _hCs, _hbuf, hadm,
        _hC, _hS, _hinner, _houter, _hpre, hhalf, _rest⟩ := haprops H
      have hh := position_dist_le_of_projection_gap (Fa H) (convex_ball _ _)
        (subset_closure.trans hadm) Aaux hhalf (hsub hq) (hsub hw)
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
    · intro H z hz
      change dist ((C H).coordinates z) ((C Href).coordinates z) ≤ _
      rw [hcoordsEq H hz, hrefCoords hz, dist_eq_norm]
      have hh := ((haprops H).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 z
        (hdomVa H hz)).2.2.2.1
      exact hh.trans (mul_le_mul_of_nonneg_left (hmono H hR₁R.le) hKa.le)
    · intro H x hx η hη
      obtain ⟨_hest, _heq, _hsec, _hdiff, _hj, _hpos, _hmom, hstate, _hrest⟩ := hprops H
      have hzdom := g.outer_product_subset_domain (a := (x, η)) ⟨hx, hη⟩
      have hztarget := (charts H).target_contains hzdom
      have hq := (C H).source_admissible _ ((C H).maps_to_source _ hztarget)
      have hbound := hregular _ ((closedBall_subset_closedBall
        (hR₂R₁.le.trans hR₁R.le)) (hstate _ hq))
      rw [(charts H).gradient_eq_chartMomentum hzdom]
      exact hbound
    · intro H x hx p hp hchar
      obtain ⟨_hest, _heq, _hsec, _hdiff, _hj, _hpos, _hmom, _hstate,
        _hCt, _hCs, _hsource, _hadm, _hcoord, _hinner, _houter, _hpre, _hscale, _hchart,
        _hsmooth, _hhomogeneous, _hagreement, _heik, _hsection, havg⟩ := hprops H
      have hxB : x ∈ ball (j s₀.1) ρ := by
        rw [hj0]
        exact closedBall_subset_ball (by dsimp [g]; linarith) hx
      have hpW : p ∈ cthickening β (closure W) :=
        self_subset_cthickening _ (subset_closure hp)
      obtain ⟨η, hη, hηp⟩ := (havg x hxB x hxB).2.2.2.2.2.2.2.1 hpW
      have hgrad : p = (charts H).gradientMap η x := by
        simpa only [averagedPhaseGradient_self, ComparisonChart.gradientMap,
          ComparisonChart.phaseFunction] using hηp.symm
      have hzdom : (x, η) ∈ g.domain := by
        exact ⟨closedBall_subset_ball (by dsimp [g]; linarith [g.radius_pos]) hx,
          ball_subset_ball (by dsimp [g]; linarith) hη⟩
      have henergy := ((charts H).eikonal hzdom).2
      refine ⟨η, ⟨ball_subset_closedBall hη, ?_⟩, hgrad⟩
      rw [← hgrad, hchar] at henergy
      exact henergy.symm
  let Lx := bounds 2 * (1 + δ + cNorm (closedBall (0, ξ) R₂) 3 H₀.h)
  have hLx : 0 ≤ Lx := by
    dsimp [Lx]
    positivity [hbounds 2, cNorm_nonneg (closedBall (0, ξ) R₂) 3 H₀.h]
  refine ⟨family, Lx, hLx, ?_⟩
  intro H η hη x hx
  let K := closedBall (j s₀.1) (ρ / 2) ×ˢ closedBall s₀.2 (3 * σ)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hsmooth : ∀ z ∈ K, ContDiffAt ℝ 2 ((C H).conicPhase ℓ) z := by
    intro z hzK
    have hm : z ∈ CharacteristicRoot.conicDomain ℓ (C H).target := by
      rw [(hprops H).2.2.2.2.2.2.2.2.1]
      exact ⟨(hcone hzK).1, hBP (hcone hzK).2⟩
    exact (((C H).contDiffOn_conicPhase ℓ (charts H).coordinates_smooth).contDiffAt
      ((CharacteristicRoot.isOpen_conicDomain ℓ (C H).isOpen_target).mem_nhds hm)).of_le
        (by simp)
  have hpoint : (x, η) ∈ K := by
    change x ∈ closedBall 0 (2 * g.radius) at hx
    change η ∈ g.parameters at hη
    constructor
    · rw [hj0]
      exact closedBall_subset_closedBall (by dsimp [g]; linarith) hx
    · exact closedBall_subset_closedBall (by linarith) hη.1
  have hsymbol : cNorm (closedBall (0, ξ) R₂) 3 H.1.h ≤
      δ + cNorm (closedBall (0, ξ) R₂) 3 H₀.h := by
    have hadd := cNorm_add_le_of_contDiffAt (r := 3) (isCompact_closedBall (0, ξ) R₂)
      (fun z hz ↦ ((H.2.2.1.sub hH₀).contDiffAt
        (hD.mem_nhds (hR₂D hz))).of_le (by simp))
      (fun z hz ↦ (hH₀.contDiffAt (hD.mem_nhds (hR₂D hz))).of_le (by simp))
    have heq : (fun z ↦ H.1.h z - H₀.h z) + H₀.h = H.1.h := by
      funext z
      exact sub_add_cancel _ _
    rw [heq] at hadd
    have hsmall : cNorm (closedBall (0, ξ) R₂) 3 (fun z ↦ H.1.h z - H₀.h z) ≤ δ :=
      (hmono H (hR₂R₁.le.trans hR₁R.le)).trans H.2.2.2.2
    exact hadd.trans (add_le_add hsmall le_rfl)
  have hphase : cNorm K 2 ((C H).conicPhase ℓ) ≤
      bounds 2 * (1 + cNorm (closedBall (0, ξ) R₂) 3 H.1.h) := by
    have hbudget := (hprops H).1 2
    have hflow := cNorm_nonneg (closedBall s₀ t ×ˢ Icc (-t) t) 2
      (fun q ↦ ((F H).position (q.2, q.1), (F H).momentum (q.2, q.1)))
    have hcoord := cNorm_nonneg K 2 (C H).coordinates
    linarith only [hbudget, hflow, hcoord]
  change ‖fderiv ℝ (gradient (fun y ↦ (C H).conicPhase ℓ (y, η))) x‖ ≤ Lx
  apply (norm_fderiv_physicalGradient_le (hsmooth (x, η) hpoint)).trans
  apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hsmooth hpoint (le_refl 2)).trans
  apply hphase.trans
  dsimp only [Lx]
  exact mul_le_mul_of_nonneg_left (by linarith only [hsymbol]) (hbounds 2).le

end JanetCartan.ProtectedFlow.PhaseCover
