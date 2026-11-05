module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Coordinates

/-!
# Full conic geometry of the selected primary phase

This constructs the geometric inputs to the complete-complement argument in
`app:ch_response:thm:response-literal-transfer`, using the same current chart,
carrier, and section as `exists_constructed_carrier_phases`. The consumer is
the compatible response construction and its application of
`ResponseTransfer.reverseSource_gap_uniform`.

All domains, angular cutoffs, and positive low thresholds precede the current
frame, frequencies, and samples. Canonical covectors retain the product maximum
norm on `ℝ × Euclidean (n - 1)`; physical covectors and the Fourier convention
are unchanged. The global inverse bound is proved through the frozen
energy/tangential inverse and the full derivative comparison on the convex cone.
No pointwise mixed gap is substituted for global injectivity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

set_option maxHeartbeats 1200000 in
/-- Conic geometry of the entire selected primary family, with one primitive
threshold for the annular and global inverse bounds on both signed cones.
The angular source gaps concern the full closed supports, including shoulders.
Every analytic conclusion is proved for the literal selected phase, and every
geometric premise of the helper constructions is discharged here
(`app:ch_response:thm:response-compatible-choice` and the complete-complement
paragraph of `app:ch_response:thm:response-literal-transfer`). -/
theorem exists_selected_primary_conic_geometry {c C : ℝ} (hP : P.IsValid c C) :
    ∃ (r ρ m M L δ d : ℝ) (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ)
      (V : Set (ℝ × Euclidean (n - 1))) (a : (ℝ × Euclidean (n - 1)) → ℝ),
      0 < r ∧ r < min T.family.radius (3 * T.family.sourceRadius) ∧
      0 < ρ ∧ 0 < m ∧ 0 < M ∧ 0 < L ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧ 0 < d ∧
      closedBall (0 : Euclidean n) (2 * ρ) ⊆ ball 0 T.physicalRadius ∧
      IsOpen V ∧ IsCompact (closure V) ∧ T.primaryCanonicalCompact ⊆ V ∧
      closure V ⊆ T.sectionEnergyDomain ∩ T.sectionEnergyCone ℓ r ∧
      IsOpen (T.sectionEnergyCone ℓ r) ∧ Convex ℝ (T.sectionEnergyCone ℓ r) ∧
      Disjoint (T.sectionEnergyCone ℓ r) (Neg.neg ⁻¹' T.sectionEnergyCone ℓ r) ∧
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ (antipodalCutoff a) ∧
      (∀ η, a η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport a ∧
      tsupport a ⊆ T.sectionEnergyCone ℓ r ∧
      T.normalizedPrimaryCanonicalCompact ℓ ⊆ interior {η | a η = 1} ∧
      Disjoint (tsupport a) (tsupport (antipodalCutoff a)) ∧
      (∀ ζ ∈ T.normalizedPrimaryCanonicalCompact ℓ,
        ∀ η ∈ tsupport (antipodalCutoff a) ∪ tsupport (fun η ↦ a η - 1),
          d < dist ζ η) ∧
      (∀ ζ ∈ Neg.neg ⁻¹' T.normalizedPrimaryCanonicalCompact ℓ,
        ∀ η ∈ tsupport a ∪ tsupport (fun η ↦ antipodalCutoff a η - 1),
          d < dist ζ η) ∧
      (∀ η, 0 < ℓ η → (ℓ η)⁻¹ • η ∈ tsupport a → η ∈ T.sectionEnergyCone ℓ r) ∧
      (∀ η, 0 < -ℓ η → (-ℓ η)⁻¹ • η ∈ tsupport (antipodalCutoff a) →
        -η ∈ T.sectionEnergyCone ℓ r) ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
        ContDiffOn ℝ ∞ (fun q : Euclidean n × (ℝ × Euclidean (n - 1)) ↦
          T.conicSectionEnergyPhase ℓ Q q.1 q.2)
          (ball 0 T.physicalRadius ×ˢ T.sectionEnergyCone ℓ r) ∧
        ContDiffOn ℝ ∞ (fun q : Euclidean n × (ℝ × Euclidean (n - 1)) ↦
          T.conjugateConicSectionEnergyPhase ℓ Q q.1 q.2)
          (ball 0 T.physicalRadius ×ˢ (Neg.neg ⁻¹' T.sectionEnergyCone ℓ r)) ∧
        ∀ x ∈ closedBall (0 : Euclidean n) (2 * ρ),
          (∀ η ∈ closure V,
            T.conicSectionEnergyPhase ℓ Q x η = T.sectionEnergyPhase Q x η) ∧
          (∀ z ∈ parameterCube P.radius,
            T.conicSectionEnergyPhase ℓ Q x (T.primaryCanonical z) = T.carrier Q x z ∧
            gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y (T.primaryCanonical z)) x =
              T.carrierGradient Q x z ∧
            T.conjugateConicSectionEnergyPhase ℓ Q x (-T.primaryCanonical z) = -T.carrier Q x z ∧
            gradient (fun y ↦ T.conjugateConicSectionEnergyPhase ℓ Q y (-T.primaryCanonical z)) x =
              -T.carrierGradient Q x z) ∧
          (∀ η ∈ T.sectionEnergyCone ℓ r,
            m * ‖η‖ ≤ ‖gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x‖ ∧
            ‖gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x‖ ≤ M * ‖η‖ ∧
            normalizedSymbol Q.1 (x, gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x) = η.1) ∧
          (∀ η ∈ T.sectionEnergyCone ℓ r, ∀ θ ∈ T.sectionEnergyCone ℓ r,
            ‖η - θ‖ ≤ L * ‖gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x -
              gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y θ) x‖) ∧
          (∀ η, -η ∈ T.sectionEnergyCone ℓ r →
            m * ‖η‖ ≤ ‖gradient (fun y ↦ T.conjugateConicSectionEnergyPhase ℓ Q y η) x‖ ∧
            ‖gradient (fun y ↦ T.conjugateConicSectionEnergyPhase ℓ Q y η) x‖ ≤ M * ‖η‖) ∧
          (∀ η, -η ∈ T.sectionEnergyCone ℓ r → ∀ θ, -θ ∈ T.sectionEnergyCone ℓ r →
            ‖η - θ‖ ≤ L * ‖gradient (fun y ↦ T.conjugateConicSectionEnergyPhase ℓ Q y η) x -
              gradient (fun y ↦ T.conjugateConicSectionEnergyPhase ℓ Q y θ) x‖) := by
  obtain ⟨r, ℓ, V, hr, hrR, hV, hcV, hKV, hVD, hDo, hDc, hmatch⟩ :=
    T.exists_conicSectionEnergyPhase_primary hP
  have hKD : T.primaryCanonicalCompact ⊆ T.sectionEnergyCone ℓ r :=
    fun η hη ↦ (hVD (subset_closure (hKV hη))).2
  obtain ⟨Vin, Vout, a, d, _hi, _ho, _hKi, _hio, hoD, _hci, _hco,
    hd, ha, han, harange, hac, has, hap, had, hgap, hgapn, hlift, hliftn⟩ :=
    T.exists_normalized_primary_cutoffs hP ℓ hKD
  obtain ⟨ρ, hρ, m, hm, M, hM, δa, hδa, hball, hann⟩ :=
    T.exists_conicSectionEnergyPhase_annular_bounds ℓ hr hrR
  obtain ⟨L, hL, δi, hδi, hinv⟩ := T.exists_conicSectionEnergyPhase_inverse_bound ℓ hrR.le
  let δ := min T.family.threshold (min δa δi)
  have hδ : 0 < δ := lt_min T.family.threshold_pos (lt_min hδa hδi)
  refine ⟨r, ρ, m, M, L, δ, d, ℓ, V, a, hr, hrR, hρ, hm, hM, hL, hδ,
    min_le_left _ _, hd, hball, hV, hcV, hKV, hVD, hDo, hDc,
    T.sectionEnergyCone_disjoint_antipode ℓ r, ha, han, harange, hac,
    has.trans (subset_closure.trans hoD), hap, had, hgap, hgapn, hlift, hliftn, ?_⟩
  intro Q hQ
  have hQa := hQ.trans_le ((min_le_right _ _).trans (min_le_left δa δi))
  have hQi := hQ.trans_le ((min_le_right _ _).trans (min_le_right δa δi))
  refine ⟨T.conicSectionEnergyPhase_smooth ℓ hrR.le Q,
    T.conjugateConicSectionEnergyPhase_smooth ℓ hrR.le Q, ?_⟩
  intro x hx
  have hm' := hmatch Q x (hball hx)
  refine ⟨hm'.1, ?_, ?_, hinv Q hQi x (hball hx), ?_, ?_⟩
  · intro z hz
    have hh := hm'.2 z hz
    refine ⟨hh.1, hh.2, ?_, ?_⟩
    · simpa only [conjugateConicSectionEnergyPhase, neg_neg] using congrArg Neg.neg hh.1
    · rw [T.conjugateConicSectionEnergyPhase_gradient, neg_neg, hh.2]
  · intro η hη
    have hh := hann Q hQa x hx η hη
    exact ⟨hh.1, hh.2, (T.conicSectionEnergyPhase_eikonal ℓ hrR.le Q (hball hx) hη).2⟩
  · intro η hη
    simpa only [T.conjugateConicSectionEnergyPhase_gradient, norm_neg] using
      hann Q hQa x hx (-η) hη
  · intro η hη θ hθ
    simpa only [T.conjugateConicSectionEnergyPhase_gradient, neg_sub_neg, norm_sub_rev] using
      hinv Q hQi x (hball hx) (-η) hη (-θ) hθ

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
