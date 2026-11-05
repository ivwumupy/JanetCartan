module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.RetainedCompact
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.FullSourceAdmission

/-!
# The initial error on the admitted original primary source

Identify the two actual smooth solver data with the retained reduced source,
then apply the proved right-localizer estimate. The same source compact, first
mask, stress row, full independent covector and both cutoffs are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.InitialSourceLocalization
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame ResponsePrimarySources
open ResponseSourceExtension Sampling.BackgroundModulation ResponseTransfer ResponseTransfer.SourceNegative
open FiniteChain.Graph LocalSobolev ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic.RetardedLocalization
open CompatibleResponse CorrectedAtoms PrimarySourceAdmission FixedDomainInverse
variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp CV 2 (volume : Measure E)

/-- Both actual `cutoffStressSmoothSource` data of the original primary atom
have arbitrary initial localization accuracy with the full cubic amplitude
budget. Their identities are proved from `fullPrimary_cutoffStressSmoothSource_quadratures`;
no equality between independently selected source constructions is assumed.
The current full-phase graph is constructed from the fixed frozen geometry,
and all constants precede the frame, scalar, free covector, frequency and mask
(`app:ch_regular:eq:source-tail`, `app:ch_response:eq:response-actual-solver-formula`). -/
theorem exists_retained_admittedSource_initial_accuracy_on_source_compact
    (hn : 5 ≤ d+1) (T : PatchQuantitativeFamily P U hU)
    (center : E × Par) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : MapsTo Prod.fst (closedBall center ρ) K)
    (hstate : closedBall (0 : E) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hΓ : ∀ j, 0 ≤ Γ j)
    {core chart : Set E} (χenv : OutputCutoff core chart) (hchart : IsOpen chart)
    (χsrc ηred : E → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc)
    (hcχsrc : HasCompactSupport χsrc) (hηred : ContDiff ℝ ∞ ηred)
    (hcore : tsupport χsrc ⊆ core)
    {V : Set Par} (hV : IsOpen V) (hproduct : chart ×ˢ V ⊆ closedBall center ρ)
    {Cpar : Set Par} (hCpar : IsCompact Cpar) (hCV : Cpar ⊆ V)
    (hsource : tsupport χsrc ×ˢ Cpar ⊆ domain T)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1)
    (χ₂ : E → ℝ) (hχ₂source : tsupport χsrc ⊆ tsupport χ₂)
    {Ωsource : Set E} (hΩsym : ∀ ξ ∈ Ωsource, -ξ ∈ Ωsource)
    (hfrozen : ∀ w ∈ tsupport χsrc ×ˢ Cpar,
      ProtectedFlow.normalizedCovector (T.reference.chart.chartMomentum (w.1,(0,w.2.2))) ∈
        interior Ωsource) :
    ∃ Ksource : Set E, IsCompact Ksource ∧
      (∀ ξ ∈ Ksource, -ξ ∈ Ksource) ∧
      (∀ ξ ∈ Ksource, ξ ≠ 0 ∧ ProtectedFlow.normalizedCovector ξ ∈ Ωsource) ∧
    ∀ (δmask : ℝ), 0 < δmask → ∀ (Dmask : ℕ → ℝ), (∀ j, 0 ≤ Dmask j) →
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ q : ℕ → ℝ → ℕ, ∃ Binitial : ℕ → ℝ → ℝ,
      (∀ s accuracy, 0 ≤ Binitial s accuracy) ∧
      ∀ (F : E → Euclidean (embeddingDimension (d+1)))
        (Q : {Q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
        (row col : Fin (d+1)) (Φ Y : ℝ × (Euclidean d × Par) → Euclidean d × Par)
        (r : Euclidean d × Euclidean 3 → ℝ) (Kr : Set (Euclidean d × Euclidean 3))
        (Ω : Set (E × Par)),
        Q.1 = projectedStress F →
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
        IsOpen Ω → closedBall center ρ ⊆ Ω → MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x, κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress (d+1) i) <
          ambientStrainFrameThreshold hn) →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
          (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x,w.2) •
            nullvector T Q col (x,w.2)) w.1 = 0) →
        (∀ j, cNorm (closedBall center ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ j * (1 + cNorm K (j+14) F + cNorm Kr (j+14) r)) →
        ∀ (RF Rr : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 16 ≤ RF → 16 ≤ Rr → ∀ τ : ℝ, 0 < τ →
          L ≤ τ⁻¹ ^ (1-ν) → ∀ c ∈ Cpar,
          let atom := complexAtomicSource F χsrc
            (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y,c.2))
          ∃ (hSU : tsupport χsrc ⊆ U)
            (hre : tensorFieldRealPart atom ∈ compactSmoothSources (tsupport χsrc))
            (him : tensorFieldImagPart atom ∈ compactSmoothSources (tsupport χsrc)),
          ∀ (s : ℕ) (accuracy : ℝ),
          ∀ (m : LocalizerSymbol (d+1)), ContDiff ℝ ∞ m → HasCompactSupport m →
          (∀ j, j ≤ q s accuracy → ∀ p, ‖iteratedFDeriv ℝ j m p‖ ≤ Dmask j) →
          (∀ y ξ, m (y,-ξ) = m (y,ξ)) →
          cthickening δmask (tsupport χ₂ ×ˢ Ksource) ⊆ interior {p | m p = 1} →
          ∀ (Mloc : H →L[ℂ] H),
          (∀ v : H, Mloc v =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (rightLocalizer τ⁻¹ m (fun y ↦ (v y).ofLp) x)) →
          ∀ (W : Set E) (hW : MeasurableSet W), tsupport χsrc ⊆ W →
          let admit := cutoffStressSmoothSource (W := W) Q.1 ηred hU
            (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hηred hSU
          ∀ imaginary : Bool,
          let h := if imaginary then (admit ⟨_,him⟩ : LocalL2 W E)
            else (admit ⟨_,hre⟩ : LocalL2 W E)
          let e := h - localRealCompression hW W Mloc h
          e ∈ (restrictionSobolevScale W RV hW).level s ∧
            (restrictionSobolevScale W RV hW).gradeNorm s e ≤
              Binitial s accuracy * τ^3 * (τ⁻¹)^(-accuracy) := by
  obtain ⟨Ksource,hKsource,hsym,hfreq,hlocalize⟩ :=
    exists_retained_reducedSource_initial_accuracy_on_source_compact
      hn T center hρ hK hKU hball hstate M hκmet hκnormal AF Ar Γ hAF hAr hΓ
      χenv hchart χsrc ηred hχsrc hcχsrc hηred hV hproduct hCpar hCV hsource hν hν1
      χ₂ hχ₂source hΩsym hfrozen
  refine ⟨Ksource,hKsource,hsym,hfreq,?_⟩
  intro δmask hδmask Dmask hDmask
  obtain ⟨δ,hδ,hδT,q,B,hB,hestimate⟩ := hlocalize δmask hδmask Dmask hDmask
  refine ⟨δ,hδ,hδT,q,B,hB,?_⟩
  intro F Q row col Φ Y r Kr Ω hQ hclose hΩ hballΩ hΩK hphase hF hi hrank hFM
    hmet hnormal hframe hscalar hnull htransport hcorrection RF Rr L hpF hpr hL hRF hRr
    τ hτ hscale c hc atom
  have hΩc (x : E) (hx : x ∈ tsupport χsrc) : (x,c) ∈ Ω := by
    have hp : χenv.toFun x = 1 := interior_subset (s := {x | χenv.toFun x = 1})
      (χenv.plateau (hcore hx))
    have hxenv : x ∈ tsupport χenv.toFun := subset_tsupport _ (by
      change χenv.toFun x ≠ 0
      rw [hp]
      exact one_ne_zero)
    exact hballΩ (hproduct ⟨χenv.support_chart hxenv,hCV hc⟩)
  have hspace (w) (hw : w ∈ Ω) : w.1 ∈ U := hKU (hΩK hw)
  have hSU : tsupport χsrc ⊆ U := fun x hx ↦ hspace (x,c) (hΩc x hx)
  obtain ⟨hre,him,hm,hidentify⟩ := fullPrimary_cutoffStressSmoothSource_quadratures
    T Q F row col Φ Y r hΩ hspace hphase hF hi hrank hscalar hnull
    χenv χsrc ηred hχsrc hcχsrc hηred hcore τ c hΩc
  obtain ⟨hm',hbound⟩ := hestimate F Q row col Φ Y r Kr Ω hQ hclose hΩ hballΩ hΩK
    hphase hF hi hrank hFM hmet hnormal hframe hscalar hnull htransport hcorrection
    RF Rr L hpF hpr hL hRF hRr τ hτ hscale c hc
  refine ⟨hSU,hre,him,?_⟩
  intro s accuracy m hms hmc hmjet heven hplateau Mloc hMloc W hW hχW admit imaginary h e
  have hb := hbound s accuracy m hms hmc hmjet heven hplateau Mloc hMloc W hW hχW
  have hid := hidentify W
  dsimp only [e,h]
  cases imaginary <;> simp only [Bool.false_eq_true,↓reduceIte]
  · rw [hid.1]
    simpa only [one_smul] using hb 1 (by simp)
  · rw [hid.2]
    exact hb (-Complex.I) (by simp)

end JanetCartan.InitialSourceLocalization
