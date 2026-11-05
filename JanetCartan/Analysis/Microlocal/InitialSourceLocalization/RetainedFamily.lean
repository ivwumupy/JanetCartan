module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.RetainedAdmission
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations

/-!
# The original admitted family in the finite-chain source slot

The first member of the selected proof-mask chain has the source plateau at
depth zero. Apply its actual right quantization to the original smooth solver
data. The resulting family satisfies exactly the initial `RapidDecayAt`
premise, with its original cubic amplitude budget and physical measure.
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
open ArbitraryAccuracy ArbitraryAccuracy.ProtectedMasks
variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp CV 2 (volume : Measure E)

/-- The depth-zero plateau of the SAME selected chain is the source
plateau used by the initial oscillatory estimate
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:source-tail`). -/
theorem first_proofMask_source_plateau {N : ℕ}
    (R : (E × E) → (E × E) → Prop) (S : Set (E × E)) (δ : ℝ)
    (m : Fin (N+1) → LocalizerSymbol (d+1))
    (hplateau : ∀ k, cthickening δ (reachableAt R S k.val) ⊆
      interior {p | m k p = 1}) :
    cthickening δ S ⊆ interior {p | m 0 p = 1} := by
  have hzero : reachableAt R S 0 = S := by
    ext q
    constructor
    · rintro ⟨p,hp,hchain⟩
      cases hchain
      exact hp
    · exact fun hq ↦ ⟨q,hq,.refl q⟩
  simpa only [Fin.val_zero,hzero] using hplateau 0

/-- The original admitted real and imaginary source families satisfy the
exact `finiteChain_observation_rapidDecayAt.hsource` signature under the SAME
selected first masks. The original cubic budget is `τ^3`, the true source
frequency is `τ⁻¹`, and every mask realization keeps the literal right integral.
The fixed frozen source geometry and initializer outputs remain explicit;
current graph inclusion and all source estimates are proved, not assumed
(`app:ch_regular:eq:source-tail`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_retained_admittedSource_firstMask_rapidDecayAt
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
    ∀ {ι : Type*}
      (F : ι → E → Euclidean (embeddingDimension (d+1)))
      (Q : ι → {Q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
      (row col : ι → Fin (d+1))
      (Φ Y : ι → ℝ × (Euclidean d × Par) → Euclidean d × Par)
      (r : ι → Euclidean d × Euclidean 3 → ℝ)
      (Kr : ι → Set (Euclidean d × Euclidean 3)) (Ω : ι → Set (E × Par)),
      (∀ i, (Q i).1 = projectedStress (F i)) →
      (∀ i, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        ((Q i).1 - fun _ ↦ cubeStress (d+1)) < δ) →
      (∀ i, IsOpen (Ω i)) → (∀ i, closedBall center ρ ⊆ Ω i) →
      (∀ i, MapsTo Prod.fst (Ω i) K) →
      (∀ i w, w ∈ Ω i → (w.1,w.2.2) ∈ phaseDomain T) →
      (∀ i, ContDiffOn ℝ ∞ (F i) U) → (∀ i, IsImmersionOn (F i) U) →
      (∀ i, HasFullNormalRankOn (F i) U) → (∀ i, cNorm K 14 (F i) ≤ M) →
      (∀ i x, x ∈ K → ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ (F i) x v‖^2) →
      (∀ i x, x ∈ K → ∀ v ∈ normalSpace (F i) x,
        κnormal * ‖v‖ ≤ ‖normalPairing (F i) (fun _ ↦ v) x‖) →
      (∀ i j, cNorm K 6 (fun x ↦ projectedStress (F i) x j - cubeStress (d+1) j) <
        ambientStrainFrameThreshold hn) →
      (∀ i, ContDiffOn ℝ ∞
        (scalarAmplitude T (Q i) (F i) (row i) (col i) (Φ i) (Y i) (r i)) (Ω i)) →
      (∀ i w, w ∈ Ω i → nullvector T (Q i) (col i) w ≠ 0 ∧
        conullvector T (Q i) (row i) w ≠ 0) →
      (∀ i w, w ∈ Ω i → conullvector T (Q i) (row i) w ⬝ᵥ
        reducedOperator (F i) (Q i).1
          (fun x ↦ scalarAmplitude T (Q i) (F i) (row i) (col i) (Φ i) (Y i) (r i)
            (x,w.2) • nullvector T (Q i) (col i) (x,w.2)) w.1 = 0) →
      (∀ i j, cNorm (closedBall center ρ) j
        (fullCorrectionCovector T (Q i) (F i) (row i) (col i) (Φ i) (Y i) (r i)) ≤
          Γ j * (1 + cNorm K (j+14) (F i) + cNorm (Kr i) (j+14) (r i))) →
      ∀ (RF Rr : ι → ℕ) (L τ : ι → ℝ),
      (∀ i, HasDerivativeProfile K (F i) (RF i) (L i) AF) →
      (∀ i, HasDerivativeProfile (Kr i) (r i) (Rr i) (L i) Ar) →
      (∀ i, 1 ≤ L i) → (∀ i, 16 ≤ RF i) → (∀ i, 16 ≤ Rr i) →
      (∀ i, 0 < τ i) → (∀ i, L i ≤ (τ i)⁻¹ ^ (1-ν)) →
      ∀ c : ι → Par, (∀ i, c i ∈ Cpar) →
      let atom := fun i ↦ complexAtomicSource (F i) χsrc
        (fun y ↦ fullPrimaryAtom T (Q i) (F i) (row i) (col i) (Φ i) (Y i)
          (τ i) (r i) (c i).1 (y,(c i).2))
      ∃ (hSU : ∀ _i : ι, tsupport χsrc ⊆ U)
        (hre : ∀ i, tensorFieldRealPart (atom i) ∈ compactSmoothSources (tsupport χsrc))
        (him : ∀ i, tensorFieldImagPart (atom i) ∈ compactSmoothSources (tsupport χsrc)),
      ∀ (N : ℕ) (Rproof : ι → (E × E) → (E × E) → Prop)
        (Vproof : ι → Set (E × E)) (m : ι → Fin (N+1) → LocalizerSymbol (d+1)),
      (∀ i, IsBufferedLocalizer (m i 0) (tsupport χ₂ ×ˢ Ksource) (Vproof i)) →
      (∀ i y ξ, m i 0 (y,-ξ) = m i 0 (y,ξ)) →
      (∀ i k, cthickening δmask (reachableAt (Rproof i) (tsupport χ₂ ×ˢ Ksource) k.val) ⊆
        interior {p | m i k p = 1}) →
      (∀ i j p, ‖iteratedFDeriv ℝ j (m i 0) p‖ ≤ Dmask j) →
      ∀ Mloc : ι → H →L[ℂ] H,
      (∀ i (v : H), Mloc i v =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer (τ i)⁻¹ (m i 0) (fun y ↦ (v y).ofLp) x)) →
      ∀ (W : Set E) (hW : MeasurableSet W), tsupport χsrc ⊆ W →
      ∀ imaginary : ι → Bool,
      let admit := fun i ↦ cutoffStressSmoothSource (W := W) (Q i).1 ηred hU
        (fun j ↦ contDiffOn_pi.mp (Q i).property.1 j) hηred (hSU i)
      let h := fun i ↦ if imaginary i then (admit i ⟨_,him i⟩ : LocalL2 W E)
        else (admit i ⟨_,hre i⟩ : LocalL2 W E)
      ∀ s, RapidDecayAt (restrictionSobolevScale W RV hW) s
        (fun i ↦ (τ i)⁻¹) (fun i ↦ (τ i)^3)
        (fun i ↦ h i - localRealCompression hW W (Mloc i) (h i)) := by
  obtain ⟨Ksource,hKsource,hsym,hfreq,hlocalize⟩ :=
    exists_retained_admittedSource_initial_accuracy_on_source_compact
      hn T center hρ hK hKU hball hstate M hκmet hκnormal AF Ar Γ hAF hAr hΓ
      χenv hchart χsrc ηred hχsrc hcχsrc hηred hcore hV hproduct hCpar hCV hsource
      hν hν1 χ₂ hχ₂source hΩsym hfrozen
  refine ⟨Ksource,hKsource,hsym,hfreq,?_⟩
  intro δmask hδmask Dmask hDmask
  obtain ⟨δ,hδ,hδT,q,B,hB,hestimate⟩ := hlocalize δmask hδmask Dmask hDmask
  refine ⟨δ,hδ,hδT,?_⟩
  intro ι F Q row col Φ Y r Kr Ω hQ hclose hΩ hballΩ hΩK hphase hF hi hrank hFM
    hmet hnormal hframe hscalar hnull htransport hcorrection RF Rr L τ hpF hpr hL hRF hRr
    hτ hscale c hc atom
  choose hSU hre him hbound using fun i ↦
    hestimate (F i) (Q i) (row i) (col i) (Φ i) (Y i) (r i) (Kr i) (Ω i)
      (hQ i) (hclose i) (hΩ i) (hballΩ i) (hΩK i) (hphase i) (hF i) (hi i) (hrank i)
      (hFM i) (hmet i) (hnormal i) (hframe i) (hscalar i) (hnull i) (htransport i)
      (hcorrection i) (RF i) (Rr i) (L i) (hpF i) (hpr i) (hL i) (hRF i) (hRr i)
      (τ i) (hτ i) (hscale i) (c i) (hc i)
  refine ⟨hSU,hre,him,?_⟩
  intro N Rproof Vproof m hm heven hplateau hmjet Mloc hMloc W hW hχW imaginary admit h s accuracy
  refine ⟨B s accuracy,hB s accuracy,?_⟩
  intro i
  exact hbound i s accuracy (m i 0) (hm i).smooth (hm i).compactSupport
    (fun j _ p ↦ hmjet i j p) (heven i)
    (first_proofMask_source_plateau (Rproof i) (tsupport χ₂ ×ˢ Ksource) δmask
      (m i) (hplateau i)) (Mloc i) (hMloc i) W hW hχW (imaginary i)

end JanetCartan.InitialSourceLocalization
