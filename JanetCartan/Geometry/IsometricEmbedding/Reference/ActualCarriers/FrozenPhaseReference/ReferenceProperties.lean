module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

/-!
# Properties retained by the constructed frozen references

The consumers of `app:ch_seed:prop:seed-actual-menu`, Steps 1–2, and
`app:lem:common-hamilton-phase` use the literal normalized cube symbol and the
same chart as the retained perturbation family. These consequences of
`FrozenPatchData` expose those identifications and the doubled closed cube
containments. The main `FrozenPhaseReference` module constructs the data from
the dimension hypothesis alone.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open FrozenMenu HamiltonPhase

/-- Every retained reference uses the literal normalized determinant of the
constant cube frame (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem FrozenPatchData.reference_symbol_eq {n : ℕ} {P : Patch n} (d : FrozenPatchData P) :
    d.reference.symbol = normalizedHomogeneousSymbol isOpen_univ
      (fun _ : Euclidean n ↦ cubeStress n) contDiffOn_const := rfl

/-- The reference symbol is defined on precisely the nonzero covectors
(`app:lem:common-hamilton-phase`). -/
theorem FrozenPatchData.mem_reference_symbol_domain {n : ℕ} {P : Patch n}
    (d : FrozenPatchData P) (q : Euclidean n × Euclidean n) :
    q ∈ d.reference.symbol.domain ↔ q.2 ≠ 0 := mem_frozenSymbol_domain q

/-- Nonvanishing on the doubled closed parameter cube follows from the final
covector-neighborhood refinement (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem FrozenPatchData.buffered_nonzero {n : ℕ} {P : Patch n} (d : FrozenPatchData P)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius)) : P.toFun z ≠ 0 :=
  d.localReference.covectorSet_nonzero _ (d.buffered_mem z hz)

/-- The characteristic inverse identity holds also on the boundary of the
doubled closed cube (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem FrozenPatchData.reference_patch_covector_closed {n : ℕ} {P : Patch n}
    (d : FrozenPatchData P) {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) :
    d.reference.covector (0, d.reference.spatialPatch z) = P.toFun z :=
  d.localReference.covector_inverse _ (d.buffered_mem z hz)
    (d.buffered_characteristic z hz)

/-- The target contains the entire doubled closed patch over the chosen
physical ball (`app:lem:common-hamilton-phase`). -/
theorem FrozenPatchData.reference_target_contains_closed {n : ℕ} {P : Patch n}
    (d : FrozenPatchData P) {x : Euclidean n} (hx : x ∈ ball 0 d.reference.radius)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius)) :
    (x, (0, d.reference.spatialPatch z)) ∈ d.reference.chart.target :=
  d.localReference.target_contains x hx _ (d.buffered_mem z hz)

/-- The frozen zero-energy carrier has exactly the positive affine sign on
the doubled closed patch (`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem FrozenPatchData.reference_carrierPhase_eq {n : ℕ} {P : Patch n}
    (d : FrozenPatchData P) {x : Euclidean n} (hx : x ∈ ball 0 d.reference.radius)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius)) :
    carrierPhase d.reference.chart d.reference.spatialPatch x z = ⟪P.toFun z, x⟫_ℝ := by
  change phase d.reference.chart.coordinates (x, (0, d.reference.spatialPatch z)) = _
  rw [d.reference.phase_linear _ (d.reference_target_contains_closed hx hz),
    d.reference_patch_covector_closed hz]

/-- The retained low-order perturbation witness has exactly the reference
target and section, with its original state ball, source buffers, central
equivalence and quantitative projection control
(`app:lem:common-hamilton-phase`). These are scalar C³ hypotheses on a current
symbol, not assumptions needed for frozen-reference existence. Full momentum
comparison and all-order phase estimates remain separate analytic tasks. -/
theorem FrozenPatchData.exists_reference_perturbation {n : ℕ} {P : Patch n}
    (d : FrozenPatchData P) (H : HomogeneousSymbol (Euclidean n))
    (hdom : d.localReference.stateDomain ⊆ H.domain)
    (hsm : ContDiffOn ℝ ∞ H.h d.localReference.stateDomain)
    (hsmall : cNorm (closedBall
      (transverseSectionState d.adapted.embedding d.adapted.normal
        (d.adapted.baseData, ⟪d.adapted.normal, d.center⟫_ℝ))
      d.localReference.stateRadius) 3 (fun z ↦ H.h z - d.reference.symbol.h z) ≤
        d.localReference.family.threshold) :
    ∃ (Φ : HamiltonFlow H (Euclidean (n - 1))) (χ : ProjectionChart Φ),
      χ.target = d.reference.chart.target ∧
      Φ.sectionMap = d.reference.sectionEmbedding.toContinuousLinearMap ∧
      BufferedChartControl d.adapted.embedding d.adapted.baseData
        (transverseSectionState d.adapted.embedding d.adapted.normal
          (d.adapted.baseData, ⟪d.adapted.normal, d.center⟫_ℝ))
        d.localReference.stateRadius d.localReference.family.sourceRadius
        d.localReference.family.buffer d.localReference.family.coefficient
        d.localReference.family.target d.localReference.family.equivalence
        d.reference.flow Φ χ := by
  obtain ⟨Φ, χ, hχ⟩ := d.localReference.family.perturbations H hdom hsm hsmall
  exact ⟨Φ, χ, hχ.target_eq.trans d.localReference.family.reference_control.target_eq.symm,
    hχ.section_eq, hχ⟩

/-- Finite minima give one physical radius, positive lower annular and
determinant bounds, a scalar C³ threshold, and an upper annular bound for all
literal patches. The existing finite-buffer lemma includes a default entry,
so empty patch lists require no extra assumption
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_common_frozenReference_bounds {n : ℕ} (D : CoverData n)
    (d : (a : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      FrozenPatchData (D.patches a.1 a.2)) :
    ∃ r c C : ℝ, 0 < r ∧ 3 * r < 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ a, 3 * r < (d a).reference.radius ∧
        c ≤ (d a).localReference.family.threshold ∧
        ∀ z ∈ parameterCube (2 * (D.patches a.1 a.2).radius),
          c ≤ ‖(D.patches a.1 a.2).toFun z‖ ∧
          ‖(D.patches a.1 a.2).toFun z‖ ≤ C ∧
          c ≤ fderiv ℝ cubeDeterminant ((D.patches a.1 a.2).toFun z)
            (d a).adapted.normal := by
  obtain ⟨r, c, C, hr, hr1, hc, hC, hcommon⟩ := exists_common_phase_buffers
    (fun a ↦ (d a).reference.radius)
    (fun a ↦ min (d a).lower
      (min (d a).localReference.determinantGap (d a).localReference.family.threshold))
    (fun a ↦ (d a).upper) (fun a ↦ (d a).reference.radius_pos)
    (fun a ↦ lt_min (d a).lower_pos
      (lt_min (d a).localReference.determinantGap_pos
        (d a).localReference.family.threshold_pos))
  refine ⟨r, c, C, hr, hr1, hc, hC, fun a ↦ ?_⟩
  have hca := le_min_iff.mp (hcommon a).2.1
  have hgap := le_min_iff.mp hca.2
  refine ⟨(hcommon a).1, hgap.2, fun z hz ↦ ?_⟩
  exact ⟨hca.1.trans ((d a).buffered_annulus z hz).1,
    ((d a).buffered_annulus z hz).2.trans (hcommon a).2.2,
    hgap.1.trans ((d a).localReference.determinant_gap _ ((d a).buffered_mem z hz))⟩

end JanetCartan.ActualCarriers.FrozenPhaseReference
