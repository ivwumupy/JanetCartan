module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ComplexFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Linearity

/-!
# Correcting the literal retained primary family

The consumer is the corrected family in `PreparedHistory`, `Current`, and the
actual `UniformHistoryCorrection` construction. We retain the supplied
`T,Q,F,row,col,Φ,Y`, original initial scalars and source cutoff. One supplied
response is used at every scalar, carrier and frequency. The regularity deduction
instantiates source admission on the full actual strain; the reduced solver's
regularity remains an input produced by `both-fixed-inverse`.

These are consequences for the retained family, not a construction of that
inverse or its uniform history estimates. No reference, flow or cutoff is chosen
in this module.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSourceExtension PrimarySourceAdmission

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))

/-- The correction of the SAME full raw atom, using the complete cutoff source
and the one fixed real response (`app:ch_response:cor:current-atoms`). -/
def fullPrimaryResponse (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  complexifyResponse B (complexAtomicSource F χ
    (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x, c.2)))

/-- The literal retained corrected atom; the response has no accuracy, scalar
or carrier parameter (`app:ch_response:cor:current-atoms`). -/
def fullCorrectedPrimaryAtom (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  complexCorrectedAtom F χ B
    (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x, c.2))

/-- The complete source, including the algebraic and Christoffel corrections,
is exactly the one passed to the response
(`app:ch_waves:eq:WKB-residual`, `app:ch_response:cor:current-atoms`). -/
theorem fullPrimaryResponse_eq_remodulated (τ : ℝ)
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) :
    fullPrimaryResponse T Q F row col Φ Y χ B τ r c =
      complexifyResponse B (fun x ↦ χ x •
        (Complex.exp (Complex.I * (phase T Q x c.2 : ℂ) / (τ : ℂ)) •
          fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x, c))) := by
  unfold fullPrimaryResponse complexAtomicSource
  rw [fullPrimaryAtom_source_eq_remodulated]

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)

include hΩ hspace hphase hF hi hrank hnonzero

/-- The source maps already proved on the span of the ORIGINAL primitive
scalars give both a globally linear response family and a locally linear
corrected family. The atom's local linearity is proved from the actual transport
and algebraic correction, not assumed. The same `B` works throughout
(`app:ch_response:cor:current-atoms`, `app:ch_response:eq:current-density-lipschitz`). -/
theorem exists_fullCorrectedPrimaryLinearMaps
    {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    (hα : ∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (τ : ℝ) (c : Euclidean 3 × Euclidean (n - 1))
    (hs : ∀ x ∈ tsupport χ, (x, c) ∈ Ω) :
    ∃ V : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
        (Euclidean n → EuclideanSpace ℂ (Fin N)),
    ∃ W : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
        ({x : Euclidean n | (x, c) ∈ Ω} → EuclideanSpace ℂ (Fin N)),
      (∀ r, V r = fullPrimaryResponse T Q F row col Φ Y χ B τ r c) ∧
      (∀ r x, W r x = fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r c x) := by
  obtain ⟨L, _Lre, _Lim, hL⟩ := exists_fullPrimarySourceLinearMaps T Q F row col Φ Y
    hΩ hspace hphase hF hi hrank hnonzero hα τ c.1 c.2 χ hχ hc hs
  have hαspan (r : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα r.property
  let V := ((complexifyResponse B).restrictScalars ℝ).comp L
  have hV (r : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      V r = fullPrimaryResponse T Q F row col Φ Y χ B τ r c := by
    change complexifyResponse B (L r) = _
    rw [(hL r).1]
    rfl
  let W₀ : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
      ({x : Euclidean n | (x, c) ∈ Ω} → EuclideanSpace ℂ (Fin N)) :=
    { toFun r x := fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x, c.2)
      map_add' r s := by
        funext x
        exact fullPrimaryAtom_initial_add T Q F row col Φ Y hΩ hspace hphase
          hF hi hnonzero τ (r := r) (s := s) (hαspan r) (hαspan s)
          (w := (x, c)) x.property
      map_smul' a r := by
        funext x
        exact fullPrimaryAtom_initial_smul T Q F row col Φ Y hΩ hspace hphase
          hF hi hnonzero τ (r := r) (hαspan r) a (w := (x, c)) x.property }
  let res : (Euclidean n → EuclideanSpace ℂ (Fin N)) →ₗ[ℝ]
      ({x : Euclidean n | (x, c) ∈ Ω} → EuclideanSpace ℂ (Fin N)) :=
    { toFun f x := f x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine ⟨V, W₀ - res.comp V, hV, ?_⟩
  intro r x
  change fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x, c.2) - V r x = _
  rw [hV]
  rfl

/-- Subtraction preserves smoothness on the original physical chart. The
primary regularity is an output of the retained raw construction; the response
regularity comes from its fixed solver (`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_fullCorrectedPrimaryAtom (τ : ℝ)
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (c : Euclidean 3 × Euclidean (n - 1))
    (hB : ContDiffOn ℝ ∞ (fullPrimaryResponse T Q F row col Φ Y χ B τ r c)
      {x : Euclidean n | (x, c) ∈ Ω}) :
    ContDiffOn ℝ ∞ (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r c)
      {x : Euclidean n | (x, c) ∈ Ω} := by
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  exact (hw.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ hx)).sub hB

/-- Local smoothness of the actual raw atom supplies its differentiability in
the exact cancellation identity. Only the response regularity remains to be
instantiated by its producer (`app:ch_response:cor:current-atoms`). -/
theorem fullCorrectedPrimaryAtom_strain (τ : ℝ)
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (c : Euclidean 3 × Euclidean (n - 1)) {x : Euclidean n}
    (hx : (x, c) ∈ Ω) (hχ : χ x = 1)
    (hB : DifferentiableAt ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r c) x) :
    WKB.complexLinearizedMetric F (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r c) x =
      -complexAtomicResidual F B (complexAtomicSource F χ
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2))) x := by
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  exact complexCorrectedAtom_strain F χ B _ hχ
    (((hw.contDiffAt (hΩ.mem_nhds hx)).comp x
      (f := fun y : Euclidean n ↦ (y, c))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)) hB

section Ambient

variable {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
    (η : Euclidean n → ℝ)
    (Tresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Fin n → ℝ))
    (Sresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hS : ∀ h : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
      DifferentiableAt ℝ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) x)
    (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (c : Euclidean 3 × Euclidean (n - 1))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : ∀ x ∈ tsupport χ, (x, c) ∈ Ω)

include hα hχ hc hs

/-- The response of the literal raw atom agrees in germ with BOTH actual
ambient quadratures. Source membership is discharged from the retained raw
construction; no source is dropped or replaced
(`app:ch_response:eq:response-full-map`, `app:ch_response:cor:current-atoms`). -/
theorem fullPrimaryResponse_ambientExtension_eventuallyEq
    {x : Euclidean n} (hx : x ∈ core) :
    fullPrimaryResponse T Q F row col Φ Y χ
      (ambientExtension F Q.1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
      τ r c =ᶠ[𝓝 x]
      (fun y ↦ euclideanComplexInclusion (AmbientResponse.ambientResponse F Q.1 η Tresp Sresp
        (tensorFieldRealPart (complexAtomicSource F χ
          (fun z ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (z, c.2)))) y) +
        Complex.I • euclideanComplexInclusion (AmbientResponse.ambientResponse F Q.1 η Tresp Sresp
          (tensorFieldImagPart (complexAtomicSource F χ
            (fun z ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (z, c.2)))) y)) := by
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  obtain ⟨hr, hi⟩ := fullPrimaryAtom_source_mem T Q F row col Φ Y r hΩ hspace hF
    τ hw c.1 c.2 χ hχ hc hs
  exact complexify_ambientExtension_eventuallyEq F Q.1 η Tresp Sresp
    (compactSmoothSources (tsupport χ)) Ξ hS _ hr hi hx

variable (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (hSsmooth : ∀ h : compactSmoothSources (tsupport χ),
      ContDiffOn ℝ ∞ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) chart)

include hchart hchartU hSsmooth

/-- Smoothness of the response to the SAME complete raw source follows from
actual source admission and the reduced inverse's existing chart regularity.
`both-fixed-inverse` must produce `hSsmooth` for its fixed `Sresp,Tresp`;
it is not a conclusion assumed about corrected atoms
(`app:ch_response:prop:response-ambient`, `app:ch_response:cor:current-atoms`). -/
theorem contDiff_fullPrimaryResponse_ambientExtension :
    ContDiff ℝ ∞ (fullPrimaryResponse T Q F row col Φ Y χ
      (ambientExtension F Q.1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
      τ r c) := by
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  obtain ⟨hr, him⟩ := fullPrimaryAtom_source_mem T Q F row col Φ Y r hΩ hspace hF
    τ hw c.1 c.2 χ hχ hc hs
  exact contDiff_complexify_ambientExtension F Q.1 η Tresp Sresp
    (compactSmoothSources (tsupport χ)) Ξ hS _ hr him hchart (hF.mono hchartU)
    hr.1.contDiffOn him.1.contDiffOn (fun x hx ↦ hi x (hchartU hx))
    (fun x hx ↦ hrank x (hchartU hx)) (hSsmooth ⟨_, hr⟩) (hSsmooth ⟨_, him⟩)

/-- The actual ambient extension closes the response-differentiability premise
of the full strain identity on this retained atom. Its analytic residual bounds
remain those of the SAME fixed inverse, to be supplied by `both-response-transfer`
(`app:ch_response:cor:current-atoms`). -/
theorem fullCorrectedPrimaryAtom_strain_ambientExtension
    {x : Euclidean n} (hx : (x, c) ∈ Ω) (hplateau : χ x = 1) :
    let B₀ := ambientExtension F Q.1 η Tresp Sresp
      (compactSmoothSources (tsupport χ)) Ξ hS
    WKB.complexLinearizedMetric F
      (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B₀ τ r c) x =
      -complexAtomicResidual F B₀ (complexAtomicSource F χ
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2))) x := by
  apply fullCorrectedPrimaryAtom_strain T Q F row col Φ Y χ _ hΩ hspace hphase
    hF hi hrank hnonzero τ r hα c hx hplateau
  exact (contDiff_fullPrimaryResponse_ambientExtension T Q F row col Φ Y χ
    hΩ hspace hphase hF hi hrank hnonzero Ξ η Tresp Sresp hS τ r hα c hχ hc hs
    hchart hchartU hSsmooth).differentiable (by simp) x

end Ambient

end JanetCartan.CorrectedAtoms
