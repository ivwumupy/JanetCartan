module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Retained
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.FullPhaseCompact

/-!
# The retained source estimate on its constructed common compact

The frozen full-phase geometry constructs a common compact for every admitted
current source before the first mask is selected. The actual source jets and
nonstationary estimate then control the original local identity subtraction.
The current source graph and every analytic source bound are proved internally.
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
variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp CV 2 (volume : Measure E)

/-- Construct the SAME original full-source graph compact, then prove the
initial localizer error for every supplied first even right mask with that
compact's plateau. No varying source graph inclusion or source decay is a
premise. Constants precede frames, full covectors, frequencies and masks;
both quadratures retain the original cubic amplitude budget and both cutoffs
(`app:ch_regular:eq:source-tail`, `app:ch_response:eq:response-graded-reduced`). -/
theorem exists_retained_reducedSource_initial_accuracy_on_source_compact
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
          let datum := fun x ↦ ηred x • ((1/2 : ℝ) • complexStressContraction (Q.1 x)
            (fullStrainEnvelope T Q F row col Φ Y r χenv τ c x))
          let source := modulatedSource χsrc (fun x ↦ phase T Q x c.2) datum τ⁻¹
          ∃ hm : MemLp source 2 volume, ∀ (s : ℕ) (accuracy : ℝ),
          ∀ (m : LocalizerSymbol (d+1)), ContDiff ℝ ∞ m → HasCompactSupport m →
          (∀ j, j ≤ q s accuracy → ∀ p, ‖iteratedFDeriv ℝ j m p‖ ≤ Dmask j) →
          (∀ y ξ, m (y,-ξ) = m (y,ξ)) →
          cthickening δmask (tsupport χ₂ ×ˢ Ksource) ⊆ interior {p | m p = 1} →
          ∀ (Mloc : H →L[ℂ] H),
          (∀ v : H, Mloc v =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (rightLocalizer τ⁻¹ m (fun y ↦ (v y).ofLp) x)) →
          ∀ (W : Set E) (hW : MeasurableSet W), tsupport χsrc ⊆ W →
          ∀ ζ : ℂ, ‖ζ‖ = 1 →
          let h := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hm.toLp source))
          let e := h - localRealCompression hW W Mloc h
          e ∈ (restrictionSobolevScale W RV hW).level s ∧
            (restrictionSobolevScale W RV hW).gradeNorm s e ≤
              Binitial s accuracy * τ^3 * (τ⁻¹)^(-accuracy) := by
  obtain ⟨δgraph,hδgraph,hδgraphT,Ksource,hKsource,hsym,hfreq,hgraph⟩ :=
    exists_retained_fullPhase_source_frequency_compact T hcχsrc hCpar hsource hΩsym hfrozen
  refine ⟨Ksource,hKsource,hsym,hfreq,?_⟩
  intro δmask hδmask Dmask hDmask
  obtain ⟨δanalytic,hδanalytic,hδanalyticT,q,B,hB,hloc⟩ :=
    exists_retained_reducedSource_initial_accuracy_constants hn T center hρ hK hKU
      hball hstate M hκmet hκnormal AF Ar Γ hAF hAr hΓ χenv hchart χsrc ηred
      hχsrc hcχsrc hηred hV hproduct hCpar hCV hsource hν hν1 δmask hδmask Dmask hDmask
  refine ⟨min δgraph δanalytic,lt_min hδgraph hδanalytic,
    (min_le_left _ _).trans hδgraphT,q,B,hB,?_⟩
  intro F Q row col Φ Y r Kr Ω hQ hclose hΩ hballΩ hΩK hphase hF hi hrank hFM
    hmet hnormal hframe hscalar hnull htransport hcorrection RF Rr L hpF hpr hL hRF hRr
    τ hτ hscale c hc datum source
  obtain ⟨hm,hbound⟩ := hloc F Q row col Φ Y r Kr Ω hQ
    (hclose.trans_le (min_le_right _ _)) hΩ hballΩ hΩK hphase hF hi hrank hFM hmet
    hnormal hframe hscalar hnull htransport hcorrection RF Rr L hpF hpr hL hRF hRr
    τ hτ hscale c hc
  refine ⟨hm,?_⟩
  intro s accuracy m hms hmc hmjet heven hplateau Mloc hMloc W hW hχW ζ hζ
  exact hbound s accuracy m hms hmc hmjet heven (tsupport χ₂ ×ˢ Ksource) hplateau
    (fun x hx ↦ ⟨hχ₂source hx,(hgraph Q (hclose.trans_le (min_le_left _ _)) x hx c hc).2⟩)
    Mloc hMloc W hW hχW ζ hζ

end JanetCartan.InitialSourceLocalization
