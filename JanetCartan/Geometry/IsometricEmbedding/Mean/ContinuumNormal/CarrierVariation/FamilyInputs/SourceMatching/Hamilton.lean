module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Hamilton
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.PatchFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TransverseCompatibility

/-!
# Source dilation and the retained Hamilton charts

The consumer is the positive-scale phase identification in
`FamilyInputs.SourceMatching`, for `app:ch_background:eq:bg-Nsigma` and
`paper-v2.tex`, `new:lem:scaling`. Both charts below belong to the SAME retained
patch family. Its source balls, unlike an arbitrary pair of inverse charts,
are preserved by contraction of time and section position. This allows the
inverse lifts to be compared without an additional inverse-gap hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers ActualCarriers.NormalizedSymbol CurrentFullPhase FrozenPhaseReference

private theorem norm_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (x : E) : ‖σ • x‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
  exact mul_le_of_le_one_left (norm_nonneg x) hσ1

private theorem dilation_mem_ball {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Z]
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) {r : ℝ} {z : Z} {p : E × Z}
    (hp : p ∈ ball (0, z) r) : (σ • p.1, p.2) ∈ ball (0, z) r := by
  simp only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] at hp ⊢
  exact ⟨(norm_smul_le hσ hσ1 p.1).trans_lt hp.1, hp.2⟩

private theorem dilation_mem_closedBall {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Z]
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) {r : ℝ} {z : Z} {p : E × Z}
    (hp : p ∈ closedBall (0, z) r) : (σ • p.1, p.2) ∈ closedBall (0, z) r := by
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right] at hp ⊢
  exact ⟨(norm_smul_le hσ hσ1 p.1).trans hp.1, hp.2⟩

/-- The retained source ball is invariant under positive source contraction.
This supplies the common admissible source for `app:ch_background:eq:bg-Nsigma`;
the radius is chosen by the patch producer before the scale. -/
theorem sourceFlowMap_mem_retained_ball {n : ℕ} {ξ : Euclidean n}
    (a : AdaptedSection ξ) {σ r : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {q : ℝ × InitialData (Euclidean (n - 1))}
    (hq : q ∈ ball ((0 : ℝ), a.baseData) r) :
    sourceFlowMap σ q ∈ ball ((0 : ℝ), a.baseData) r := by
  have hq' : ‖q.1‖ < r ∧ q.2 ∈ ball a.baseData r := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] using hq
  have hs := dilation_mem_ball hσ hσ1 hq'.2
  simp only [sourceFlowMap_apply, mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right]
  exact ⟨(norm_smul_le hσ hσ1 q.1).trans_lt hq'.1, by simpa only [AdaptedSection.baseData, mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] using hs⟩

private theorem transverse_momentum_eq {E V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (H : HomogeneousSymbol E) {K : Set (E × E)} (hK : Convex ℝ K)
    (hKH : K ⊆ H.domain) (j : V →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (horth : ∀ v, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x, ⟪ν, x⟫_ℝ = 0 → ∃ u, j u = x)
    (hgap : ∀ z ∈ K, ⟪H.hp z, ν⟫_ℝ ≠ 0)
    {x p p' : E} {η : V} (hpK : (x, p) ∈ K) (hpK' : (x, p') ∈ K)
    (hp : ∀ v, ⟪p, j v⟫_ℝ = ⟪η, v⟫_ℝ)
    (hp' : ∀ v, ⟪p', j v⟫_ℝ = ⟪η, v⟫_ℝ)
    (he : H.h (x, p) = H.h (x, p')) : p = p' := by
  let a := ⟪ν, p⟫_ℝ / ⟪ν, ν⟫_ℝ
  let a' := ⟪ν, p'⟫_ℝ / ⟪ν, ν⟫_ℝ
  have hpa : p = a • ν + j η :=
    sectionMomentum_eq_normal_add_tangent j ν p hν horth hspan η hp
  have hpa' : p' = a' • ν + j η :=
    sectionMomentum_eq_normal_add_tangent j ν p' hν horth hspan η hp'
  have hdiff : p' - p = (a' - a) • ν := by rw [hpa', hpa]; module
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (x, p + t • (p' - p)) ∈ K := by
    simpa using hK.add_smul_sub_mem hpK hpK' ht
  let f : ℝ → ℝ := fun t ↦ H.h (x, p + t • (p' - p))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt f ⟪H.hp (x, p + t • (p' - p)), p' - p⟫_ℝ t := by
    have hh := (H.hasFDerivAt_h _ (hKH (hmem t ht))).comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk
        ((hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const (p' - p))))
    simpa [f, Function.comp_def, hamiltonDifferential_apply] using hh
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope f
    (fun t ↦ ⟪H.hp (x, p + t • (p' - p)), p' - p⟫_ℝ) zero_lt_one
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hd t (Ioo_subset_Icc_self ht))
  have hend : f 1 = f 0 := by simpa [f] using he.symm
  rw [hend, sub_self, zero_div, hdiff, inner_smul_right] at heq
  have haa : a' - a = 0 := (mul_eq_zero.mp heq).resolve_right
    (by simpa only [← hdiff] using hgap _ (hmem t (Ioo_subset_Icc_self ht)))
  rw [sub_eq_zero.mp haa] at hpa'
  exact hpa.trans hpa'.symm

variable {n : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

set_option quotPrecheck false
local notation "H₀" => normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1
local notation "Hσ" => normalizedHomogeneousSymbol hU Qσ.1 Qσ.2.1
local notation "Φ₀" => T.family.flow Q₀
local notation "Φσ" => T.family.flow Qσ
local notation "stateBall" => closedBall (0, T.data.center) T.data.localReference.stateRadius

/-- Root and ODE uniqueness for the retained family under source dilation.
The three symbol equations are the literal scalar/gradient identities produced
by `SourceGeometry.Hamilton.Determinant`; they do not assert any phase or
trajectory equality. State ranges and common time/parameter domains are derived
from the retained family. Consumer: `current_coordinates_source_dilation`.
Source: `app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`. -/
theorem retained_state_source_dilation
    (hKU : stateBall ⊆ (H₀).domain)
    (htrans : ∀ z ∈ stateBall, ⟪(H₀).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (he : ∀ z ∈ stateBall, (Hσ).h z = (H₀).h (σ • z.1, z.2))
    (hp : ∀ z ∈ stateBall, (Hσ).hp z = (H₀).hp (σ • z.1, z.2))
    (hx : ∀ z ∈ stateBall, (Hσ).hx z = σ • (H₀).hx (σ • z.1, z.2))
    {q : ℝ × InitialData (Euclidean (n - 1))}
    (hq : q ∈ ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius)) :
    (σ • (Φσ).position q, (Φσ).momentum q) =
      ((Φ₀).position (sourceFlowMap σ q), (Φ₀).momentum (sourceFlowMap σ q)) := by
  let r := 3 * T.family.sourceRadius
  have hr : 0 < r := mul_pos (by norm_num) T.family.sourceRadius_pos
  have hq' : q.1 ∈ Ioo (-r) r ∧ q.2 ∈ ball T.data.adapted.baseData r := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo, r] using hq
  have hball (t : ℝ) (ht : t ∈ Ioo (-r) r) :
      (t, q.2) ∈ ball ((0 : ℝ), T.data.adapted.baseData) r := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using And.intro ht (mem_ball.mp hq'.2)
  have hadm (t : ℝ) (ht : t ∈ Ioo (-r) r) := T.family.source_admissible Qσ (hball t ht)
  have hadm₀ (t : ℝ) (ht : t ∈ Ioo (-r) r) := T.family.source_admissible Q₀
    (sourceFlowMap_mem_retained_ball T.data.adapted hσ.le hσ1 (hball t ht))
  let u : ℝ → Euclidean n × Euclidean n := fun t ↦
    (σ • (Φσ).position (t, q.2), (Φσ).momentum (t, q.2))
  let v : ℝ → Euclidean n × Euclidean n := fun t ↦
    ((Φ₀).position (sourceFlowMap σ (t, q.2)), (Φ₀).momentum (sourceFlowMap σ (t, q.2)))
  have huK (t : ℝ) (ht : t ∈ Ioo (-r) r) : u t ∈ stateBall :=
    dilation_mem_closedBall hσ.le hσ1 (T.family.state_mem Qσ _ (hadm t ht))
  have hvK (t : ℝ) (ht : t ∈ Ioo (-r) r) : v t ∈ stateBall :=
    T.family.state_mem Q₀ _ (hadm₀ t ht)
  have hzero : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  have hposition : (u 0).1 = (v 0).1 := by
    change σ • (Φσ).position (0, q.2) = (Φ₀).position (σ * 0, (σ • q.2.1, q.2.2))
    rw [mul_zero, (Φσ).initial_position _ (hadm 0 hzero).2,
      (Φ₀).initial_position (σ • q.2.1, q.2.2) (hadm₀ 0 hzero).2, T.family.section_eq, T.family.section_eq]
    exact (map_smul T.data.adapted.embedding.toContinuousLinearMap σ q.2.1).symm
  have hν : T.data.adapted.normal ≠ 0 := by
    intro hh
    have hu := T.data.adapted.normal_unit
    rw [hh, norm_zero] at hu
    norm_num at hu
  have hmomentum : (u 0).2 = (v 0).2 := by
    apply transverse_momentum_eq H₀ (convex_closedBall _ _) hKU
      T.data.adapted.embedding T.data.adapted.normal hν
      T.data.adapted.orthogonal T.data.adapted.spanning htrans (huK 0 hzero)
      (by change ((u 0).1, (v 0).2) ∈ stateBall; rw [hposition]; exact hvK 0 hzero)
    · intro w
      simpa only [u, T.family.section_eq, LinearIsometry.coe_toContinuousLinearMap]
        using (Φσ).initial_momentum q.2 (hadm 0 hzero).2 w
    · intro w
      simpa only [v, sourceFlowMap_apply, sourceDilationMap_apply, mul_zero, T.family.section_eq,
        LinearIsometry.coe_toContinuousLinearMap]
        using (Φ₀).initial_momentum (sourceDilationMap σ q.2) (hadm₀ 0 hzero).2 w
    · have henergy := he _ (T.family.state_mem Qσ _ (hadm 0 hzero))
      change (Hσ).h ((Φσ).position (0, q.2), (Φσ).momentum (0, q.2)) = (H₀).h (u 0) at henergy
      change (H₀).h (u 0) = (H₀).h ((u 0).1, (v 0).2)
      rw [← henergy, (Φσ).initial_energy _ (hadm 0 hzero).2, hposition]
      simpa only [v, sourceFlowMap_apply, sourceDilationMap_apply, mul_zero] using
        ((Φ₀).initial_energy (sourceDilationMap σ q.2) (hadm₀ 0 hzero).2).symm
  have hinit : u 0 = v 0 := Prod.ext hposition hmomentum
  let V : Euclidean n × Euclidean n → Euclidean n × Euclidean n :=
    fun z ↦ σ • (H₀).vectorField z
  have hV : ContDiffOn ℝ ∞ V (H₀).domain :=
    (contDiffOn_normalizedHomogeneousSymbol_vectorField hU Q₀.1 Q₀.2.1).const_smul σ
  let L : ℝ≥0 := ⟨cNorm stateBall 2 V, cNorm_nonneg _ _ _⟩
  have hlip := (ODE.field_and_fderiv_lipschitzOnWith_of_cNorm
    (K := L) (H₀).isOpen_domain hKU hV le_rfl).1
  have hdu (t : ℝ) (ht : t ∈ Ioo (-r) r) : HasDerivAt u (V (u t)) t := by
    have hrange := T.family.state_mem Qσ _ (hadm t ht)
    have hd := (((Φσ).position_hasDerivAt (hadm t ht).1 (hadm t ht).2).const_smul σ).prodMk
      ((Φσ).momentum_hasDerivAt (hadm t ht).1 (hadm t ht).2)
    rw [hp _ hrange, hx _ hrange] at hd
    simpa only [u, V, HomogeneousSymbol.vectorField, Prod.smul_mk, smul_neg, Pi.smul_apply] using hd
  have hdv (t : ℝ) (ht : t ∈ Ioo (-r) r) : HasDerivAt v (V (v t)) t := by
    have hd := (((Φ₀).position_hasDerivAt (hadm₀ t ht).1 (hadm₀ t ht).2).prodMk
      ((Φ₀).momentum_hasDerivAt (hadm₀ t ht).1 (hadm₀ t ht).2)).scomp t
        ((hasDerivAt_id t).const_mul σ)
    convert! hd using 1
    simp [v, V, sourceFlowMap_apply, HomogeneousSymbol.vectorField]
  have hseg : uIcc 0 q.1 ⊆ Ioo (-r) r := ordConnected_Ioo.uIcc_subset hzero hq'.1
  have heq := autonomousFlow_dist_le hlip
    (fun t ht ↦ hdu t (hseg ht)) (fun t ht ↦ hdv t (hseg ht))
    (fun t ht ↦ huK t (hseg ht)) (fun t ht ↦ hvK t (hseg ht))
  simpa only [hinit, dist_self, zero_mul, dist_le_zero] using heq

/-- The SAME retained current coordinates are the explicitly divided seed
coordinates. Common lift containment follows from `sourceFlowMap_mem_retained_ball`
and the retained source description; it is not a premise. The seed transverse
gap is the remaining root-branch input. Source: `app:ch_background:eq:bg-Nsigma`.
Consumer: phase and ambient transport-jet matching in `FamilyInputs`. -/
theorem current_coordinates_source_dilation
    (hKU : stateBall ⊆ (H₀).domain)
    (htrans : ∀ z ∈ stateBall, ⟪(H₀).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (he : ∀ z ∈ stateBall, (Hσ).h z = (H₀).h (σ • z.1, z.2))
    (hp : ∀ z ∈ stateBall, (Hσ).hp z = (H₀).hp (σ • z.1, z.2))
    (hx : ∀ z ∈ stateBall, (Hσ).hx z = σ • (H₀).hx (σ • z.1, z.2)) :
    EqOn (T.currentChart Qσ).coordinates
      (sourceCoordinates (T.currentChart Q₀).coordinates σ) T.target := by
  intro z hz
  have hlift := (T.currentChart Qσ).maps_to_source z hz
  rw [PatchQuantitativeFamily.currentChart,
    restrictChart_source_eq _ _ _ (T.family.source_eq Qσ)] at hlift
  have hstate := retained_state_source_dilation T Q₀ Qσ hKU htrans hσ hσ1
    he hp hx hlift.1
  have hpos : (Φ₀).position (sourceFlowMap σ (chartLift (T.currentChart Qσ).coordinates z)) =
      σ • z.1 := by
    have hh := congrArg Prod.fst hstate
    change σ • (Φσ).position (chartLift (T.currentChart Qσ).coordinates z) =
      (Φ₀).position (sourceFlowMap σ (chartLift (T.currentChart Qσ).coordinates z)) at hh
    rw [(T.currentChart Qσ).right_inverse z hz] at hh
    exact hh.symm
  have htarget : (σ • z.1, z.2) ∈ T.target := by
    have hz' : z ∈ ball (0, T.data.adapted.baseData.2) T.family.radius := by
      simpa only [PatchQuantitativeFamily.target, AdaptedSection.baseData, map_zero] using hz
    simpa only [PatchQuantitativeFamily.target, AdaptedSection.baseData, map_zero] using
      dilation_mem_ball hσ.le hσ1 hz'
  have hsource : sourceFlowMap σ (chartLift (T.currentChart Qσ).coordinates z) ∈
      (T.currentChart Q₀).source := by
    rw [PatchQuantitativeFamily.currentChart,
      restrictChart_source_eq _ _ _ (T.family.source_eq Q₀)]
    refine ⟨sourceFlowMap_mem_retained_ball T.data.adapted hσ.le hσ1 hlift.1, ?_⟩
    change ((Φ₀).position (sourceFlowMap σ (chartLift (T.currentChart Qσ).coordinates z)), z.2) ∈ T.target
    rw [hpos]
    exact htarget
  have hinv := (T.currentChart Q₀).left_inverse _ hsource
  rw [hpos] at hinv
  change (T.currentChart Q₀).coordinates (σ • z.1, z.2) =
    σ • (T.currentChart Qσ).coordinates z at hinv
  simp only [sourceCoordinates, hinv, smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]

/-- Full-energy phase equality on the fixed retained open target, stronger
than its zero-energy restriction used by the carrier row. No phase comparison
is assumed. Source: `app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`. -/
theorem current_phase_source_dilation
    (hKU : stateBall ⊆ (H₀).domain)
    (htrans : ∀ z ∈ stateBall, ⟪(H₀).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (he : ∀ z ∈ stateBall, (Hσ).h z = (H₀).h (σ • z.1, z.2))
    (hp : ∀ z ∈ stateBall, (Hσ).hp z = (H₀).hp (σ • z.1, z.2))
    (hx : ∀ z ∈ stateBall, (Hσ).hx z = σ • (H₀).hx (σ • z.1, z.2)) :
    EqOn (phase (T.currentChart Qσ).coordinates)
      (sourcePhase (phase (T.currentChart Q₀).coordinates) σ) T.target := by
  intro z hz
  rw [← phase_sourceCoordinates]
  simp only [phase, current_coordinates_source_dilation T Q₀ Qσ hKU htrans hσ hσ1 he hp hx hz]

/-- The retained frozen state ball is a punctured state buffer for every
current symbol on `U`. Only its physical containment is required; exclusion of
zero momentum is retained by `LocalFrozenReference`. Consumer: the source
matching uniqueness argument (`app:lem:common-hamilton-phase`). -/
theorem retained_stateBall_subset
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U) :
    stateBall ⊆ (H₀).domain := by
  intro z hz
  refine ⟨hphysical ?_, ?_⟩
  · exact (max_le_iff.mp (by simpa only [mem_closedBall, Prod.dist_eq] using hz)).1
  · apply (mem_frozenSymbol_domain z).mp
    apply T.data.localReference.state_subset
    apply T.data.localReference.stateBall_subset
    simpa only [T.data.adapted.baseState_eq] using hz

/-- Identify the actual projected-stress charts and every ambient phase jet.
All symbol-scaling premises of `current_coordinates_source_dilation` are
DISCHARGED using the full-rank source-geometry producer. The remaining seed
transverse hypothesis concerns a scalar determinant derivative, not a chart or
trajectory match. It is supplied by the fixed-reference transverse gap and a
primitive frame neighborhood. No flatness is needed for this Hamilton step.
Source: `app:ch_background:eq:bg-Nsigma`, `paper-v2.tex`, `new:lem:scaling`.
Consumer: canonical transport matching in `FamilyInputs.SourceMatching`. -/
theorem projected_current_chart_source_dilation {N : ℕ}
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ stateBall, ⟪(H₀).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ)) :
    EqOn (T.currentChart Qσ).coordinates
      (sourceCoordinates (T.currentChart Q₀).coordinates σ) T.target ∧
    EqOn (phase (T.currentChart Qσ).coordinates)
      (sourcePhase (phase (T.currentChart Q₀).coordinates) σ) T.target ∧
    ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (phase (T.currentChart Qσ).coordinates))
      (iteratedFDeriv ℝ m (sourcePhase (phase (T.currentChart Q₀).coordinates) σ)) T.target := by
  have hKU := retained_stateBall_subset T Q₀ hphysical
  have hQ : ContDiffOn ℝ ∞ (ProjectedStressFrame.projectedStress F) U := hseed ▸ Q₀.2.1
  have hscaled_mem (z) (hz : z ∈ stateBall) : (σ • z.1, z.2) ∈ (H₀).domain :=
    hKU (dilation_mem_closedBall hσ.le hσ1 hz)
  have he (z) (hz : z ∈ stateBall) : (Hσ).h z = (H₀).h (σ • z.1, z.2) := by
    change normalizedSymbol Qσ.1 z =
      normalizedSymbol Q₀.1 (σ • z.1, z.2)
    rw [hseed, hscaled]
    exact normalizedSymbol_sourceDilation hσ hF z.1 z.2 (hrank _ (hscaled_mem z hz).1)
  have hp (z) (hz : z ∈ stateBall) : (Hσ).hp z = (H₀).hp (σ • z.1, z.2) := by
    change covectorGradient (normalizedSymbol Qσ.1) z =
      covectorGradient (normalizedSymbol Q₀.1) (σ • z.1, z.2)
    rw [hseed, hscaled]
    exact covectorGradient_sourceNormalizedSymbol hU hF hrank hQ hσ (hscaled_mem z hz)
  have hx (z) (hz : z ∈ stateBall) : (Hσ).hx z = σ • (H₀).hx (σ • z.1, z.2) := by
    change physicalGradient (normalizedSymbol Qσ.1) z =
      σ • physicalGradient (normalizedSymbol Q₀.1) (σ • z.1, z.2)
    rw [hseed, hscaled]
    exact physicalGradient_sourceNormalizedSymbol hU hF hrank hQ hσ (hscaled_mem z hz)
  have hcoords := current_coordinates_source_dilation T Q₀ Qσ hKU htrans hσ hσ1 he hp hx
  have hphase := current_phase_source_dilation T Q₀ Qσ hKU htrans hσ hσ1 he hp hx
  refine ⟨hcoords, hphase, fun m z hz ↦ ?_⟩
  have heq : phase (T.currentChart Qσ).coordinates =ᶠ[𝓝 z]
      sourcePhase (phase (T.currentChart Q₀).coordinates) σ :=
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun w hw ↦ hphase hw)
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
