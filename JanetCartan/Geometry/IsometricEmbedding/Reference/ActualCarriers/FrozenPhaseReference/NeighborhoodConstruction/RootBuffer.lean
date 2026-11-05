module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction.FlowIdentities

/-!
# A frozen state buffer with unique energy roots

For `app:lem:common-hamilton-phase` and Step 1 of
`app:ch_seed:prop:seed-actual-menu`, scalar-root uniqueness gives injectivity of
the energy/tangential-momentum coordinates on a small closed momentum ball.
This discharges the injectivity input of
`FrozenHamiltonFamily.phase_eq_canonicalMomentum` and
`FrozenHamiltonFamily.canonicalMomentum_eq_of_characteristic`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase

/-- A bounded open state buffer and an interior closed ball on which energy
and tangential momentum determine the whole covector
(`app:lem:common-hamilton-phase`, `app:ch_seed:prop:seed-actual-menu`, Step 1).
The state buffer is constructed as an open ball in the punctured symbol domain;
the momentum radius also keeps both root coordinates in the uniqueness patch. -/
theorem exists_frozenRootBuffer {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ) :
    ∃ (D : Set (Euclidean n × Euclidean n)) (R : ℝ),
      IsOpen D ∧ D ⊆ (frozenSymbol n).domain ∧ 0 < R ∧
      closedBall (0, ξ) R ⊆ D ∧
      Set.InjOn (fun p : Euclidean n ↦
        ((frozenSymbol n).h (0, p), a.embedding.toContinuousLinearMap.adjoint p))
        (closedBall ξ R) := by
  let f := sectionEnergyEquation (frozenSymbol n) a.embedding a.normal
  let S := transverseSectionState a.embedding a.normal ⁻¹' (frozenSymbol n).domain
  have hS : IsOpen S := (frozenSymbol n).isOpen_domain.preimage
    (contDiff_transverseSectionState a.embedding a.normal).continuous
  have hf : ContDiffOn ℝ ∞ f S :=
    ((frozenSymbol_smooth n).comp
      (contDiff_transverseSectionState a.embedding a.normal).contDiffOn
      (fun _ hw ↦ hw)).sub contDiff_fst.snd.fst.contDiffOn
  have hbase : (a.baseData, ⟪a.normal, ξ⟫_ℝ) ∈ S := by
    change transverseSectionState a.embedding a.normal _ ∈ (frozenSymbol n).domain
    simpa only [a.baseState_eq, mem_frozenSymbol_domain] using hξ
  have hz : f (a.baseData, ⟪a.normal, ξ⟫_ℝ) = 0 := by
    dsimp only [f, sectionEnergyEquation]
    rw [a.baseState_eq, frozenSymbol_h, hchar]
    simp [AdaptedSection.baseData]
  have hd : CharacteristicRoot.scalarDerivative f (a.baseData, ⟪a.normal, ξ⟫_ℝ) ≠ 0 := by
    rw [scalarDerivative_sectionEnergyEquation (frozenSymbol n) a.embedding a.normal hbase,
      a.baseState_eq]
    exact (frozenSymbol_transverse_pos hξ hchar a.determinant_positive).ne'
  obtain ⟨U, V, c, hU, hbaseU, hV, hbaseV, _, _, _, huniq⟩ :=
    CharacteristicRoot.exists_localRoot_patch hS hf hbase hz hd
  let datum (p : Euclidean n) : InitialData (Euclidean (n - 1)) :=
    (0, ((frozenSymbol n).h (0, p), a.embedding.toContinuousLinearMap.adjoint p))
  have hdatum : datum ξ = a.baseData := by
    simp [datum, AdaptedSection.baseData, frozenSymbol_h, hchar]
  have henergy : ContinuousAt (fun p : Euclidean n ↦ (frozenSymbol n).h (0, p)) ξ :=
    ((frozenSymbol_smooth n).continuousOn.continuousAt
      ((frozenSymbol n).isOpen_domain.mem_nhds
        ((mem_frozenSymbol_domain (0, ξ)).mpr hξ))).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hcoordinates : ContinuousAt
      (fun p : Euclidean n ↦ (datum p, ⟪a.normal, p⟫_ℝ)) ξ :=
    (continuousAt_const.prodMk
      (henergy.prodMk a.embedding.toContinuousLinearMap.adjoint.continuous.continuousAt)).prodMk
      (continuousAt_const.inner continuousAt_id)
  have hpatch : (fun p : Euclidean n ↦ (datum p, ⟪a.normal, p⟫_ℝ)) ⁻¹' (U ×ˢ V) ∈
      nhds ξ := by
    apply hcoordinates.preimage_mem_nhds
    exact (hU.prod hV).mem_nhds ⟨hdatum ▸ hbaseU, hbaseV⟩
  obtain ⟨ε, hε, hεpatch⟩ := Metric.mem_nhds_iff.mp hpatch
  obtain ⟨δ, hδ, hδdomain⟩ := Metric.isOpen_iff.mp (frozenSymbol n).isOpen_domain
    (0, ξ) ((mem_frozenSymbol_domain (0, ξ)).mpr hξ)
  let R := min (δ / 2) (ε / 2)
  have hR : 0 < R := lt_min (half_pos hδ) (half_pos hε)
  have hRδ : R < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hRε : R < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  have hmem {p : Euclidean n} (hp : p ∈ closedBall ξ R) :
      datum p ∈ U ∧ ⟪a.normal, p⟫_ℝ ∈ V :=
    hεpatch ((mem_closedBall.mp hp).trans_lt hRε)
  have hroot (p : Euclidean n) : f (datum p, ⟪a.normal, p⟫_ℝ) = 0 := by
    simp [f, sectionEnergyEquation, transverseSectionState, datum, a.covector_decomposition]
  refine ⟨ball (0, ξ) δ, R, isOpen_ball, hδdomain, hR,
    closedBall_subset_ball hRδ, ?_⟩
  intro p hp q hq heq
  have hdata : datum p = datum q := congrArg (fun η ↦ (0, η)) heq
  have hadjoint : a.embedding.toContinuousLinearMap.adjoint p =
      a.embedding.toContinuousLinearMap.adjoint q := congrArg Prod.snd heq
  have hnormal : ⟪a.normal, p⟫_ℝ = ⟪a.normal, q⟫_ℝ := by
    have hpRoot := (huniq (datum p) (hmem hp).1 _ (hmem hp).2).mp (hroot p)
    have hqRoot := (huniq (datum q) (hmem hq).1 _ (hmem hq).2).mp (hroot q)
    rw [hdata] at hpRoot
    exact hpRoot.symm.trans hqRoot
  calc
    p = ⟪a.normal, p⟫_ℝ • a.normal +
        a.embedding (a.embedding.toContinuousLinearMap.adjoint p) :=
      (a.covector_decomposition p).symm
    _ = ⟪a.normal, q⟫_ℝ • a.normal +
        a.embedding (a.embedding.toContinuousLinearMap.adjoint q) := by
      rw [hnormal, hadjoint]
    _ = q := a.covector_decomposition q

end JanetCartan.ActualCarriers.FrozenPhaseReference
