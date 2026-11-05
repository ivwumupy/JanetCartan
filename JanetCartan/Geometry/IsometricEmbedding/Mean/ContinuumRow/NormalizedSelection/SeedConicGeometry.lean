module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.CommonConicGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.SourcePhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.IncidenceScaling

/-!
# Retained Hamilton seeds with a common full conic inverse domain

The original Hamilton phase proves the joint forward smoothness and frozen
central differential. The common conic construction then chooses its masks
and inverse domains together before the varying source scale. The chosen
input buffer remains available for the original coefficient and density
charts; there is no analytic inverse premise.
-/

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormalReduction.TransportSymbol
open ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase ActualComparison
open CanonicalConic ContinuumNormal.FrozenModel

/-- Instantiate the full common conic construction on the actual retained
Hamilton phase. Seed smoothness and its central differential follow from the
retained covector producer. A primitive threshold precedes the seed, and all
masks, domains, inverse maps and Jacobian bounds precede its varying scale.
The inverse-frequency constant is four on the original quarter-radius shell.
Consumer: the same-family `NormalizedNormalLimit` inputs, before finite
selection (`app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-full-complex-amplitude`). -/
theorem exists_retained_seed_conic_geometry_on_buffer
    {n : ℕ} (hn : 0 < n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : ‖k‖ = 1 / 4) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) :
    ∃ δ > (0 : ℝ), ∀ Q₀ : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q₀.1 - fun _ ↦ cubeStress n) < δ → Q₀.1 0 = cubeStress n →
    let Y := normalizedTransportPosition T Q₀
    let A := augmentedReferenceEquiv T hP hz₀ hinc hd
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∀ O : Set (InputVariables n), IsOpen O → p₀ ∈ O →
    ∀ {rmax amax : ℝ}, 0 < rmax → 0 < amax →
    ∃ K W : Set (InputVariables n),
      IsCompact K ∧ Convex ℝ K ∧ IsOpen W ∧ K ⊆ W ∧
      K ⊆ O ∧ W ⊆ radialInputDomain O ∧ p₀ ∈ interior K ∧
      (∀ p ∈ K, ‖ηb‖ / 2 ≤ ‖p.2.2‖) ∧
      (∀ p ∈ W, p.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ p, scaleInput t p ∈ W ↔ p ∈ W) ∧
    ∃ Q Ω : Set (Variables n × Euclidean 2),
      IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient (Y 0) p₀ ∈ Q ∧
      (∀ q ∈ Q, ‖q.1.2.2‖ = (1 / 4 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω) ∧
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ a > (0 : ℝ), a ≤ amax ∧ a ≤ r ∧ 4 * a < 1 / 2 ∧
    ∃ e > (0 : ℝ), ∃ gap > (0 : ℝ),
    ∃ u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
        augmentedTransportGradient (Y q.1) q.2) (Ioo (-e) e ×ˢ W) ∧
      ∀ σ ∈ Ioo (-e) e,
        ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
        MapsTo (inverseCoordinates (u σ)) Ω W ∧
        (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
        (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ K, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) p) ∧
        ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ)) W ∧
        (∀ p ∈ W, 0 < transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) p) ∧
        (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ 4 * ‖p.1.2.2‖) ∧
        (∀ t : ℝ, 0 < t → ∀ q,
          u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
        (∀ p ∈ W, ∀ t : ℝ, 0 < t →
          transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) (scaleInput t p) =
            t * transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) p) ∧
        (∀ p ∈ conicMaskSupport z₀ ηb r a,
          p ∈ W ∧ transportAveragedGradient (Y σ) p ≠ 0 ∧
          normalizeOutputRadius (1 / 4) (augmentedTransportGradient (Y σ) p) ∈ Q ∧
          inverseCoordinates (u σ) (augmentedTransportGradient (Y σ) p) = p) ∧
        (closure (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a) ∩
          {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
        (∀ q ∈ closure (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a),
          ‖q.1.2.2‖ = (1 / 4 : ℝ) → q ∈ Q) := by
  obtain ⟨Vseed, hVseed, hzVseed, hVbuffer, δ, hδ, hseed⟩ :=
    exists_retained_seed_covector_buffer T hP hz₀
  refine ⟨δ, hδ, ?_⟩
  intro Q₀ hsmall hzero Y A p₀ ηb O hO hpO rmax amax hrmax hamax
  obtain ⟨hS, hcov⟩ := hseed Q₀ hsmall hzero
  obtain ⟨K₀, W₀, _, _, hW₀, hKW₀, hpK₀, _, _, _, _, _, _,
    e₀, he₀, _, _, _, hjoint, _⟩ :=
    exists_source_common_local_charts T hP hz₀ hinc hd isOpen_ball hVseed
      (mem_ball_self T.physicalRadius_pos) hS hVbuffer hcov hzVseed
  have hA : fderiv ℝ (augmentedTransportGradient (Y 0)) p₀ = A.toContinuousLinearMap :=
    fderiv_sourceAugmentedTransport_zero_center T hP hz₀ hinc hd
      isOpen_ball hVseed (mem_ball_self T.physicalRadius_pos) hS hVbuffer hcov hzVseed
  have hcenter : augmentedTransportGradient (Y 0) p₀ = ((0, 0, k), spectatorCenter z₀) :=
    (sourceAugmentedTransport_zero_eq_frozen T isOpen_ball hVseed
      (mem_ball_self T.physicalRadius_pos) hS hVbuffer hcov p₀ hzVseed).trans
        (frozenAugmentedChart_center T hP hz₀ hinc)
  have hb : ‖transportAveragedGradient (Y 0) p₀‖ = 1 / 4 :=
    (congrArg (fun q : Variables n × Euclidean 2 ↦ ‖q.1.2.2‖) hcenter).trans hk
  change ‖transportAveragedGradient (Y 0) ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)‖ = 1 / 4 at hb
  have hkne : k ≠ 0 := norm_pos_iff.mp (hk ▸ (by norm_num : (0 : ℝ) < 1 / 4))
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hkne hinc
  have hηsmall : ‖ηb‖ < 1 := by
    have hadj : ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact T.data.adapted.embedding.norm_toContinuousLinearMap_le
    have hh := T.data.adapted.embedding.toContinuousLinearMap.adjoint.le_opNorm k
    have hm := mul_le_mul_of_nonneg_right hadj (norm_nonneg k)
    change ‖ηb‖ ≤ _ at hh
    rw [one_mul, hk] at hm
    rw [hk] at hh
    linarith
  let O' := (W₀ ∩ O) ∩ {p : InputVariables n | ‖ηb‖ / 2 < ‖p.2.2‖ ∧ ‖p.2.2‖ < 1}
  have hO' : IsOpen O' := (hW₀.inter hO).inter
    ((isOpen_lt continuous_const continuous_snd.snd.norm).inter
      (isOpen_lt continuous_snd.snd.norm continuous_const))
  have hpO' : p₀ ∈ O' := ⟨⟨hKW₀ (interior_subset hpK₀), hpO⟩,
    half_lt_self (norm_pos_iff.mpr hηb), hηsmall⟩
  have hF : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (Ioo (-e₀) e₀ ×ˢ O') :=
    hjoint.mono (prod_mono Subset.rfl (fun _ hp ↦ hp.1.1))
  have hfreq : ∀ p ∈ O', p.2.2 ≠ 0 ∧ ‖p.2.2‖ ≤ 1 := by
    intro p hp
    exact ⟨norm_pos_iff.mp ((half_pos (norm_pos_iff.mpr hηb)).trans hp.2.1), hp.2.2.le⟩
  obtain ⟨_, K, W, hK, hconv, hW, hKW, hKO', hWO', hpK, hWfreq, hWcone,
    Q, Ω, hQ, hΩ, hQΩ, hcenterQ, hQfreq, hcone, r, hr, hrr, a, ha, haa, har, hcell,
    e, he, _, gap, hgap, u, hJ, hfamily⟩ :=
    exists_source_conic_geometry_with_radial_input hn (adaptedSliceCoordinates T)
      hηb isOpen_Ioo hO' ⟨neg_neg_of_pos he₀, he₀⟩ hpO' hfreq hF A hA hrmax hamax
  have hWO : W ⊆ radialInputDomain O := by
    intro p hp
    obtain ⟨t, ht, htp⟩ := hWO' hp
    exact ⟨t, ht, htp.1.2⟩
  refine ⟨K, W, hK, hconv, hW, hKW, fun p hp ↦ (hKO' hp).1.2, hWO, hpK,
    fun p hp ↦ (hKO' hp).2.1.le, hWfreq, hWcone,
    Q, Ω, hQ, hΩ, hQΩ, hcenterQ, ?_, hcone, r, hr, hrr, a, ha, haa, har, hcell,
    e, he, gap, hgap, u, hJ, ?_⟩
  · simpa only [hb] using hQfreq
  · intro σ hσ
    simpa only [hb, one_div, inv_inv, inv_div, div_one] using hfamily σ hσ

end JanetCartan.ContinuumRow.NormalizedSelection
