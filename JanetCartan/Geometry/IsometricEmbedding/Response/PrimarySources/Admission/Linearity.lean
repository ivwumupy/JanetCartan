module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Linearity.Span
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Linearity.Atoms

/-!
# Real linearity of the actual primary strain source in the initial scalar

The consumer is `exists_finite_retained_raw_primary_family_with_source_admission`
in `Admission.Family`. Its SAME retained outputs supply the open chart, its
spatial and phase containment, the smooth full-rank immersion, nonzero selected
nullvectors, and scalar-amplitude smoothness for every primitive initial scalar.

This deduction supplies actual linear maps on the span of those original scalars,
with literal values on the entire original source support. The parent must
instantiate these inputs from its one retained family. No response estimate or
new derivative reserve is required, and no existence of a new family is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PrimarySourceAdmission
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSourceExtension InitialScalarCalculus

/-- Actual complex, real, and imaginary source maps, real-linear in the ORIGINAL
initial scalar on the span of its original primitive class. All correction terms
are retained. Generator smoothness is produced by
`RawPrimary.exists_finite_retained_raw_primary_family`; the consumer
`exists_finite_retained_raw_primary_family_with_source_admission` must instantiate
it and the geometric hypotheses on the SAME family.
Sources: `app:ch_response:cor:current-atoms`, `app:ch_waves:eq:WKB-W`. -/
theorem exists_fullPrimarySourceLinearMaps
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hα : ∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (τ : ℝ) (z : Euclidean 3) (ξ : Euclidean (n - 1))
    (chiSrc : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ chiSrc)
    (hc : HasCompactSupport chiSrc)
    (hs : ∀ x ∈ tsupport chiSrc, (x, (z, ξ)) ∈ Ω) :
    ∃ L : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
        (Euclidean n → Matrix (Fin n) (Fin n) ℂ),
    ∃ Lre Lim : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
        compactSmoothSources (tsupport chiSrc),
    ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
      L r = (fun x ↦ chiSrc x • WKB.complexLinearizedMetric F
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x) ∧
      (Lre r : MetricField n) = tensorFieldRealPart (fun x ↦ chiSrc x •
        WKB.complexLinearizedMetric F
          (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x) ∧
      (Lim r : MetricField n) = tensorFieldImagPart (fun x ↦ chiSrc x •
        WKB.complexLinearizedMetric F
          (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x) ∧
      MemLp (tensorFieldRealPart (fun x ↦ chiSrc x • WKB.complexLinearizedMetric F
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x)) 2 volume ∧
      MemLp (tensorFieldImagPart (fun x ↦ chiSrc x • WKB.complexLinearizedMetric F
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x)) 2 volume := by
  have hαspan (r : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα r.property
  have hatom (r : initialScalarSpan (n := n) z₀ R Mᵣ m) : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2)) Ω :=
    contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
      hΩ hspace hphase hF hi hrank (hαspan r) hnonzero
  let O : Set (Euclidean n) := {x | (x, (z, ξ)) ∈ Ω}
  have ho : IsOpen O := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hd (r : initialScalarSpan (n := n) z₀ R Mᵣ m) {x : Euclidean n} (hx : x ∈ O) :
      DifferentiableAt ℝ (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x := by
    have h := ((hatom r).contDiffAt (hΩ.mem_nhds hx)).comp x
      (f := fun y : Euclidean n ↦ (y, (z, ξ)))
      (contDiffAt_id.prodMk contDiffAt_const)
    exact h.differentiableAt (by simp)
  let L : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
      (Euclidean n → Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun r x ↦ chiSrc x • WKB.complexLinearizedMetric F
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x
      map_add' := by
        intro r s
        funext x
        by_cases hx : x ∈ tsupport chiSrc
        · have he : (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ
              ((r + s : initialScalarSpan (n := n) z₀ R Mᵣ m) : Euclidean (n - 1) × Euclidean 3 → ℝ)
              z (y, ξ)) =ᶠ[𝓝 x]
              ((fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) +
               (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ s z (y, ξ))) := by
            filter_upwards [ho.mem_nhds (hs x hx)] with y hy
            exact fullPrimaryAtom_initial_add T Q F row col Φ Y hΩ hspace hphase
              hF hi hnonzero τ (r := r) (s := s) (hαspan r) (hαspan s)
              (w := (y, (z, ξ))) hy
          rw [(complexLinearizedMetric_eventuallyEq F he).self_of_nhds,
            complexLinearizedMetric_add F (hd r (hs x hx)) (hd s (hs x hx)), smul_add]
          rfl
        · simp only [image_eq_zero_of_notMem_tsupport hx, zero_smul, Pi.add_apply, add_zero]
      map_smul' := by
        intro c r
        funext x
        by_cases hx : x ∈ tsupport chiSrc
        · have he : (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ
              ((c • r : initialScalarSpan (n := n) z₀ R Mᵣ m) : Euclidean (n - 1) × Euclidean 3 → ℝ)
              z (y, ξ)) =ᶠ[𝓝 x]
              c • (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) := by
            filter_upwards [ho.mem_nhds (hs x hx)] with y hy
            exact fullPrimaryAtom_initial_smul T Q F row col Φ Y hΩ hspace hphase
              hF hi hnonzero τ (r := r) (hαspan r) c (w := (y, (z, ξ))) hy
          rw [(complexLinearizedMetric_eventuallyEq F he).self_of_nhds,
            complexLinearizedMetric_real_smul F (hd r (hs x hx)) c]
          exact smul_comm _ _ _
        · simp only [image_eq_zero_of_notMem_tsupport hx, zero_smul, Pi.smul_apply,
            smul_zero] }
  have hmem (r : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      tensorFieldRealPart (L r) ∈ compactSmoothSources (tsupport chiSrc) ∧
      tensorFieldImagPart (L r) ∈ compactSmoothSources (tsupport chiSrc) :=
    fullPrimaryAtom_source_mem T Q F row col Φ Y r hΩ hspace hF τ
      (hatom r) z ξ chiSrc hχ hc hs
  let Lre := (tensorFieldRealPart.comp L).codRestrict
    (compactSmoothSources (tsupport chiSrc)) (fun r ↦ (hmem r).1)
  let Lim := (tensorFieldImagPart.comp L).codRestrict
    (compactSmoothSources (tsupport chiSrc)) (fun r ↦ (hmem r).2)
  exact ⟨L, Lre, Lim, fun r ↦ ⟨rfl, rfl, rfl,
    memLp_of_mem_compactSmoothSources (hmem r).1,
    memLp_of_mem_compactSmoothSources (hmem r).2⟩⟩

end JanetCartan.PrimarySourceAdmission
