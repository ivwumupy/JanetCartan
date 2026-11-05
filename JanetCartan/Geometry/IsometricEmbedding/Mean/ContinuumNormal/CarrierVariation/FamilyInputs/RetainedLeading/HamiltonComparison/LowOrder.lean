module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.PatchComparison

/-!
# Comparison on the original retained Hamilton source

The order-zero root and trajectory estimates for `app:lem:common-hamilton-phase`
are proved on the entire original source ball. The flows are the retained
flows, and no auxiliary chart or new central radius occurs. The consumer is
the inverse comparison on the original coefficient compact needed by
`RetainedLeading.exists_originalScalar_primitives_sub_tolerance`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference

private theorem initial_state_sub_le
    {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ)
    (H H₀ : HomogeneousSymbol (Euclidean n))
    (Φ : HamiltonFlow H (Euclidean (n - 1)))
    (Φ₀ : HamiltonFlow H₀ (Euclidean (n - 1)))
    {K : Set (Euclidean n × Euclidean n)} (hK : Convex ℝ K)
    (hKH₀ : K ⊆ H₀.domain)
    (hj : Φ.sectionMap = a.embedding.toContinuousLinearMap)
    (hj₀ : Φ₀.sectionMap = a.embedding.toContinuousLinearMap)
    {c e : ℝ} (hc : 0 < c)
    (hgap : ∀ z ∈ K, c ≤ |⟪H₀.hp z, a.normal⟫_ℝ|)
    (hclose : ∀ z ∈ K, |H.h z - H₀.h z| ≤ e)
    {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ Φ.parameters) (hs₀ : s ∈ Φ₀.parameters)
    (hrange : (Φ.position (0, s), Φ.momentum (0, s)) ∈ K)
    (hrange₀ : (Φ₀.position (0, s), Φ₀.momentum (0, s)) ∈ K) :
    ‖(Φ.position (0, s), Φ.momentum (0, s)) -
      (Φ₀.position (0, s), Φ₀.momentum (0, s))‖ ≤ e / c := by
  have hν : a.normal ≠ 0 := by
    intro he
    have hh := a.normal_unit
    rw [he, norm_zero] at hh
    norm_num at hh
  let p := Φ.momentum (0, s)
  let p₀ := Φ₀.momentum (0, s)
  let b := ⟪a.normal, p⟫_ℝ / ⟪a.normal, a.normal⟫_ℝ
  let b₀ := ⟪a.normal, p₀⟫_ℝ / ⟪a.normal, a.normal⟫_ℝ
  have hx : Φ.position (0, s) = a.embedding s.1 := by
    simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_position s hs
  have hx₀ : Φ₀.position (0, s) = a.embedding s.1 := by
    simpa only [hj₀, LinearIsometry.coe_toContinuousLinearMap] using Φ₀.initial_position s hs₀
  have hp : p = b • a.normal + a.embedding s.2.2 :=
    sectionMomentum_eq_normal_add_tangent a.embedding a.normal p hν a.orthogonal
      a.spanning s.2.2 (by
        simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_momentum s hs)
  have hp₀ : p₀ = b₀ • a.normal + a.embedding s.2.2 :=
    sectionMomentum_eq_normal_add_tangent a.embedding a.normal p₀ hν a.orthogonal
      a.spanning s.2.2 (by
        simpa only [hj₀, LinearIsometry.coe_toContinuousLinearMap] using Φ₀.initial_momentum s hs₀)
  have hdiff : p - p₀ = (b - b₀) • a.normal := by rw [hp, hp₀]; module
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (a.embedding s.1, p₀ + t • (p - p₀)) ∈ K := by
    have hh := hK.add_smul_sub_mem hrange₀ hrange ht
    simpa [hx, hx₀, p, p₀, Prod.mk_add_mk, Prod.mk_sub_mk] using hh
  let f : ℝ → ℝ := fun t ↦ H₀.h (a.embedding s.1, p₀ + t • (p - p₀))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt f ⟪H₀.hp (a.embedding s.1, p₀ + t • (p - p₀)), p - p₀⟫_ℝ t := by
    have hh := (H₀.hasFDerivAt_h _ (hKH₀ (hmem t ht))).comp_hasDerivAt t
      ((hasDerivAt_const t (a.embedding s.1)).prodMk
        ((hasDerivAt_const t p₀).add ((hasDerivAt_id t).smul_const (p - p₀))))
    simpa [f, Function.comp_def, hamiltonDifferential_apply] using hh
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f
    (fun t ↦ ⟪H₀.hp (a.embedding s.1, p₀ + t • (p - p₀)), p - p₀⟫_ℝ)
    zero_lt_one (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hd t (Ioo_subset_Icc_self ht))
  have hf₀ : f 0 = s.2.1 := by
    simpa [f, p₀, hx₀] using Φ₀.initial_energy s hs₀
  have hf₁ : f 1 = H₀.h (Φ.position (0, s), Φ.momentum (0, s)) := by simp [f, p, hx]
  have he' := congrArg abs he
  rw [hf₁, hf₀, ← Φ.initial_energy s hs] at he'
  simp only [sub_zero, div_one, hdiff, inner_smul_right, abs_mul] at he'
  have hb : |b - b₀| * c ≤ e := by
    calc
      _ ≤ |b - b₀| * |⟪H₀.hp (a.embedding s.1, p₀ + t • (p - p₀)), a.normal⟫_ℝ| :=
        mul_le_mul_of_nonneg_left (hgap _ (hmem t (Ioo_subset_Icc_self ht))) (abs_nonneg _)
      _ = |H₀.h (Φ.position (0, s), Φ.momentum (0, s)) -
          H.h (Φ.position (0, s), Φ.momentum (0, s))| := by simpa only [hdiff] using he'
      _ ≤ e := by rw [abs_sub_comm]; exact hclose _ hrange
  have hn : ‖(Φ.position (0, s), Φ.momentum (0, s)) -
      (Φ₀.position (0, s), Φ₀.momentum (0, s))‖ = |b - b₀| := by
    simp only [Prod.mk_sub_mk, hx, hx₀, sub_self, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)]
    change ‖p - p₀‖ = _
    rw [hdiff, norm_smul, a.normal_unit, mul_one, Real.norm_eq_abs]
  rw [hn]
  exact (le_div_iff₀ hc).mpr hb

/-- The SAME retained trajectories are Lipschitz in the order-one scalar
symbol seminorm on the whole original source ball. Only the reference
transverse gap is used; the admitted varying flows already have their original
state range. This is the root/ODE base case for the original-compact inverse
comparison in `app:lem:common-hamilton-phase`. -/
theorem exists_retained_state_sub_le_symbol {n : ℕ} {ξ : Euclidean n}
    {a : AdaptedSection ξ} {N : LocalFrozenReference a}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (hdomain : ∀ z ∈ N.stateDomain, z.1 ∈ U)
    (L : LocalQuantitativeFamily N U hU) {R : ℝ} (hR : 0 < R)
    (hRN : R < N.stateRadius)
    (hrange : ∀ Q, ∀ q ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters,
      ((L.flow Q).position q, (L.flow Q).momentum q) ∈ closedBall (0, ξ) R)
    (Q₀ : _)
    (hgap₀ : ∀ z ∈ closedBall (0, ξ) R,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, a.normal⟫_ℝ ≠ 0) :
    ∃ B > (0 : ℝ), ∀ Q, ∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius),
      ‖((L.flow Q).position q, (L.flow Q).momentum q) -
        ((L.flow Q₀).position q, (L.flow Q₀).momentum q)‖ ≤
      B * cNorm (closedBall (0, ξ) N.stateRadius) 1
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) := by
  let H (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < L.threshold}) :=
    normalizedHomogeneousSymbol hU Q.1 Q.2.1
  have hND : closedBall (0, ξ) N.stateRadius ⊆ N.stateDomain := by
    simpa only [a.baseState_eq] using N.stateBall_subset
  have hRD : closedBall (0, ξ) R ⊆ N.stateDomain :=
    (closedBall_subset_closedBall hRN.le).trans hND
  have hDH (Q : _) : N.stateDomain ⊆ (H Q).domain := fun z hz ↦
    ⟨hdomain z hz, (mem_frozenSymbol_domain z).mp (N.state_subset hz)⟩
  have hH (Q : _) : ContDiffOn ℝ ∞ (H Q).h N.stateDomain :=
    (contDiffOn_normalizedSymbol hU Q.2.1).mono (hDH Q)
  have hV (Q : _) : ContDiffOn ℝ ∞ (H Q).vectorField N.stateDomain :=
    (H Q).contDiffOn_vectorField_of_subset N.state_open (hDH Q) (by simpa using hH Q)
  have hc : ContinuousOn (fun z ↦ |⟪(H Q₀).hp z, a.normal⟫_ℝ|) (closedBall (0, ξ) R) :=
    fun z hz ↦ (((H Q₀).hasFDerivAt_hp z (hDH Q₀ (hRD hz))).continuousAt.inner
      continuousAt_const).abs.continuousWithinAt
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall (0, ξ) R).exists_isMinOn
    ⟨(0, ξ), mem_closedBall_self hR.le⟩ hc
  let c := |⟪(H Q₀).hp z, a.normal⟫_ℝ|
  have hcpos : 0 < c := abs_pos.mpr (hgap₀ z hz)
  let k : ℝ≥0 := ⟨cNorm (closedBall (0, ξ) R) 2 (H Q₀).vectorField, cNorm_nonneg _ _ _⟩
  have hlip := (ODE.field_and_fderiv_lipschitzOnWith_of_cNorm
    (K := k) N.state_open hRD (hV Q₀) le_rfl).1
  let B := gronwallBound c⁻¹ k 1 (3 * L.sourceRadius)
  have htime : 0 < 3 * L.sourceRadius := mul_pos (by norm_num) L.sourceRadius_pos
  have hB : 0 ≤ B := gronwallBound_nonneg (inv_nonneg.mpr hcpos.le)
    k.coe_nonneg zero_le_one htime.le
  refine ⟨B + 1, by positivity, ?_⟩
  intro Q q hq
  let e := cNorm (closedBall (0, ξ) N.stateRadius) 1
    (normalizedSymbol Q.1 - normalizedSymbol Q₀.1)
  have he : 0 ≤ e := cNorm_nonneg _ _ _
  have hscalar (z) (hz : z ∈ closedBall (0, ξ) R) : |(H Q).h z - (H Q₀).h z| ≤ e := by
    have hh := norm_symbol_jet_sub_le_cNorm (H Q) (H Q₀) N.state_open
        ((hH Q).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) ((hH Q₀).of_le (by simp))
        (isCompact_closedBall _ _) hND (by omega : 0 ≤ 1)
        (closedBall_subset_closedBall hRN.le hz)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hh
    exact hh
  have hfield (z) (hz : z ∈ closedBall (0, ξ) R) :
      ‖(H Q).vectorField z - (H Q₀).vectorField z‖ ≤ e := by
    have hb := norm_iteratedFDeriv_vectorField_sub_le (H Q) (H Q₀) N.state_open
      (hDH Q) (hDH Q₀) ((hH Q).of_le (by simp : (0 + 1 : ℕ∞ω) ≤ ∞))
      ((hH Q₀).of_le (by simp)) (hRD hz)
    rw [norm_iteratedFDeriv_zero] at hb
    exact hb.trans (norm_symbol_jet_sub_le_cNorm (H Q) (H Q₀) N.state_open
      ((hH Q).of_le (by simp)) ((hH Q₀).of_le (by simp))
      (isCompact_closedBall _ _) hND (le_refl 1)
      (closedBall_subset_closedBall hRN.le hz))
  have hqs : q.1 ∈ Ioo (-(3 * L.sourceRadius)) (3 * L.sourceRadius) ∧
      q.2 ∈ ball a.baseData (3 * L.sourceRadius) := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using hq
  have hsource (t : ℝ) (ht : t ∈ Ioo (-(3 * L.sourceRadius)) (3 * L.sourceRadius)) :
      (t, q.2) ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius) := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using And.intro ht hqs.2
  have hzero : (0 : ℝ) ∈ Ioo (-(3 * L.sourceRadius)) (3 * L.sourceRadius) :=
    ⟨by linarith, htime⟩
  let u (t : ℝ) := ((L.flow Q).position (t, q.2), (L.flow Q).momentum (t, q.2))
  let u₀ (t : ℝ) := ((L.flow Q₀).position (t, q.2), (L.flow Q₀).momentum (t, q.2))
  have hi : ‖u 0 - u₀ 0‖ ≤ e / c := initial_state_sub_le a (H Q) (H Q₀)
    (L.flow Q) (L.flow Q₀) (convex_closedBall _ _) (hRD.trans (hDH Q₀))
    (L.section_eq Q) (L.section_eq Q₀) hcpos (fun z hz ↦ hmin hz) hscalar
    (L.source_admissible Q (hsource 0 hzero)).2
    (L.source_admissible Q₀ (hsource 0 hzero)).2
    (hrange Q _ (L.source_admissible Q (hsource 0 hzero)))
    (hrange Q₀ _ (L.source_admissible Q₀ (hsource 0 hzero)))
  have hode (Q : _) (t : ℝ)
      (ht : t ∈ Ioo (-(3 * L.sourceRadius)) (3 * L.sourceRadius)) :
      HasDerivAt (fun t ↦ ((L.flow Q).position (t, q.2), (L.flow Q).momentum (t, q.2)))
        ((H Q).vectorField ((L.flow Q).position (t, q.2), (L.flow Q).momentum (t, q.2))) t := by
    have ha := L.source_admissible Q (hsource t ht)
    exact ((L.flow Q).position_hasDerivAt ha.1 ha.2).prodMk
      ((L.flow Q).momentum_hasDerivAt ha.1 ha.2)
  have hsub : uIcc 0 q.1 ⊆ Ioo (-(3 * L.sourceRadius)) (3 * L.sourceRadius) :=
    ordConnected_Ioo.uIcc_subset hzero hqs.1
  have hg := ODE.norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun t ↦ u t - u₀ t)
    (R' := fun t ↦ (H Q).vectorField (u t) - (H Q₀).vectorField (u₀ t))
    (fun t ht ↦ (hode Q t (hsub ht)).sub (hode Q₀ t (hsub ht))) hi
    (L := k) (ε := e) (fun t ht ↦ by
      have hu := hrange Q _ (L.source_admissible Q (hsource t (hsub ht)))
      have hu₀ := hrange Q₀ _ (L.source_admissible Q₀ (hsource t (hsub ht)))
      calc
        _ ≤ ‖(H Q).vectorField (u t) - (H Q₀).vectorField (u t)‖ +
            ‖(H Q₀).vectorField (u t) - (H Q₀).vectorField (u₀ t)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ e + (k : ℝ) * ‖u t - u₀ t‖ := add_le_add (hfield _ hu) (hlip.norm_sub_le hu hu₀)
        _ = _ := add_comm _ _)
  have ht : |q.1 - 0| ≤ 3 * L.sourceRadius := by simpa using (abs_lt.mpr hqs.1).le
  have hb : ‖u q.1 - u₀ q.1‖ ≤ B * e := by
    apply (hg.trans (gronwallBound_mono (div_nonneg he hcpos.le) he k.coe_nonneg ht)).trans_eq
    simpa only [div_eq_mul_inv, mul_comm e c⁻¹, one_mul] using
      gronwallBound_mul c⁻¹ k 1 e (3 * L.sourceRadius)
  exact hb.trans (by nlinarith)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
