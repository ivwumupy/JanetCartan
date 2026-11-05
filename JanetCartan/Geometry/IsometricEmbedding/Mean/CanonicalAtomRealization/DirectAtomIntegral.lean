module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.Identification
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverJointRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.UniformCanonicalSlice

/-!
# Physical derivative of the direct solver's canonical wave

On the original source cutoff, the classical solver estimate gives the
component Sobolev bounds needed to move the response through the integral.
Differentiate this identity on the observation chart, which can be smaller
than the source-validity chart. Both constructions retain the original
Lebesgue measure in the adapted coordinates of the same raw slice.

Sources: `app:ch_response:cor:current-atoms`, `app:ch_waves:eq:individual-representation`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open RawPrimary RawInputPartition CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension
open CurrentMean AmplitudeBound FixedDomainInverse LocalSobolev RetardedSobolev.Spaces
open ResponseSmoothParameters LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open FourierIntegral FiniteChain.Graph.KernelLimits

/-- The part of the original raw parameter chart on which the entire fixed
source cutoff is admitted and the physical observation is interior to `L`.
The cutoff itself is unchanged (`app:ch_response:cor:current-atoms`). -/
def sourceObservationDomain {n : ℕ}
    (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) (S L : Set (Euclidean n)) :=
  Ω ∩ (interior L ×ˢ {c | ∀ y ∈ S, (y, c) ∈ Ω})

/-- Compactness of the original source support supplies an open joint chart
for the same response (`app:ch_response:cor:current-atoms`). -/
theorem isOpen_sourceObservationDomain {n : ℕ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hΩ : IsOpen Ω)
    {S : Set (Euclidean n)} (hS : IsCompact S) (L : Set (Euclidean n)) :
    IsOpen (sourceObservationDomain Ω S L) := by
  apply hΩ.inter
  apply isOpen_interior.prod
  rw [isOpen_iff_mem_nhds]
  intro c hc
  have hsub : S ×ˢ ({c} : Set (Euclidean 3 × Euclidean (n - 1))) ⊆ Ω := by
    rintro ⟨y, c'⟩ ⟨hy, hc'⟩
    change c' = c at hc'
    subst c'
    exact hc y hy
  obtain ⟨A, V, _, hV, hSA, hcV, hAV⟩ := generalized_tube_lemma hS isCompact_singleton hΩ hsub
  exact mem_of_superset (hV.mem_nhds (hcV (mem_singleton c))) (fun c' hc' y hy ↦ hAV ⟨hSA hy, hc'⟩)

variable {d N : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (F : Euclidean (d + 1) → Euclidean N) (row col : Fin (d + 1))
    (Φ Y : ℝ × (Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) →
      Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))
    (r : Euclidean ((d + 1) - 1) × Euclidean 3 → ℝ)
    (χ η : Euclidean (d + 1) → ℝ) (hη : ContDiff ℝ ∞ η) (hχU : tsupport χ ⊆ U)
    {W core chart : Set (Euclidean (d + 1))}
    (solver : smoothSource W (Euclidean (d + 1)) →ₗ[ℝ]
      (Euclidean (d + 1) → Euclidean (d + 1)))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (x₀ : Euclidean (d + 1)) (Rout : ℝ) (hcore : closedBall x₀ Rout ⊆ core)
    (D a : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m) (ha : ∀ m, 0 ≤ a m) (β : ℕ)
    (hbound : ∀ (h : smoothSource W (Euclidean (d + 1))) (m : ℕ),
      cNorm (closedBall x₀ Rout) m (solver h) ≤ D m *
        (restrictionSobolevNorm W (m + (d + 2)) (h : LocalL2 W (Euclidean (d + 1))) +
          (1 + a (m + (d + 2) + β)) * ‖(h : LocalL2 W (Euclidean (d + 1)))‖))
    {Ω : Set (Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (τ : ℝ)

set_option quotPrecheck false in
local notation "Bfixed" => fixedSmoothSolverAmbientExtension F (Subtype.val Q) η hU
  (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ
local notation "Lobs" => closedBall x₀ Rout
local notation "Ojoint" => sourceObservationDomain Ω (tsupport χ) Lobs

/-- Use the SAME retained adapted coordinates as `UniformCanonicalSlice` for
the source Sobolev inclusion (`app:ch_waves:eq:individual-raw-slice`). -/
private def adaptedSourceCoordinates {d : ℕ} {ξ : Euclidean (d + 1)}
    (sec : FrozenPhaseReference.AdaptedSection ξ) :
    (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm).trans
      (NullTransport.ActualFlow.adaptedCoordinates sec).symm

/-- The actual slice coordinates preserve the original Lebesgue source
measure after the Sobolev jet's coordinate swap (`app:ch_waves:eq:individual-raw-slice`). -/
private theorem adaptedSourceCoordinates_measurePreserving {d : ℕ} {ξ : Euclidean (d + 1)}
    (sec : FrozenPhaseReference.AdaptedSection ξ) :
    MeasurePreserving (graphInputCoordinates (adaptedSourceCoordinates sec)) volume volume :=
  (SliceBounds.adaptedPhysicalCoordinates_measurePreserving sec).comp
    (((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin d))).comp
      Measure.measurePreserving_swap)

include hchart hchartU hcore hD ha hbound hΩ hspace hphase hF hi hrank hα hnonzero hχ hc

/-- The direct classical solver estimate gives joint regularity on the actual
observation chart, using the existing adapted coordinates and unshrunk source
cutoff (`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_directSolverResponse_sourceObservationDomain :
    ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ Bfixed τ r w.2 w.1) Ojoint :=
  contDiffOn_fullPrimaryResponse_fixedSmoothSolver_of_classical_bound T Q F row col Φ Y χ η
    hη hχU solver hsolver Ξ hchart hchartU x₀ Rout hcore D a hD ha β hbound
    (adaptedSourceCoordinates T.data.adapted) (adaptedSourceCoordinates_measurePreserving _)
    hΩ hspace hphase hF hi hrank hnonzero (isOpen_sourceObservationDomain hΩ hc _)
    (fun _ hw ↦ hw.2.1) (fun _ hw ↦ hw.2.2) hχ hc τ r hα

variable {J : ℕ} (z : Euclidean 3) {X : Set (Euclidean (d + 1))} {V : Set (Euclidean ((d + 1) - 1))}
    (hshift : ∀ p ∈ X ×ˢ V, (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈ Ω)
    (hX : IsOpen X) (hV : IsOpen V) (hceil : closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    (hsrc : tsupport χ ⊆ X) {mask : Euclidean ((d + 1) - 1) → ℂ} {M : ℝ}
    (hd : Measurable mask) (hM : 0 ≤ M) (hb : ∀ ξ, ‖mask ξ‖ ≤ M)

include hshift hX hV hceil hsrc hd hM hb

/-- The whole-source direct solution and the atomwise corrected field have
identical physical derivatives and the literal integral representation on the
observation ball. The bound is used only there, never on the whole source
support (`app:ch_lag:eq:lag-recurrence`, `app:ch_waves:eq:individual-representation`). -/
theorem directSolver_wholeSourceDerivative_eq_corrected_and_integral (hτ : τ ≠ 0)
    (v : WideInput (d + 1) J) {x : Euclidean (d + 1)} (hx : x ∈ X) (hxL : x ∈ interior Lobs) :
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ Bfixed τ z mask v x =
        correctedWideDerivative T Q F row col Φ Y χ Bfixed τ r z (T.reference.spatialPatch z) mask v x ∧
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ Bfixed τ z mask v x =
        rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
          (fun y ξ ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ Bfixed r τ (y, (z, ξ)))
          (T.reference.spatialPatch z) τ volume (weightedWideDensity mask v) x := by
  let e := adaptedSourceCoordinates T.data.adapted
  have hB := exists_fixedSmoothSolver_tensorComponent_bounds e (adaptedSourceCoordinates_measurePreserving _)
    F Q.val η hc hU (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ
    hchart (hF.mono hchartU) (fun y hy ↦ hi y (hchartU hy)) (fun y hy ↦ hrank y (hchartU hy))
    x₀ Rout hcore D a hD ha β hbound
  have hzero (i j : Fin (d + 1)) := hB i j 0
  simp only [norm_iteratedFDeriv_zero] at hzero
  have hopen := isOpen_sourceObservationDomain hΩ hc Lobs
  have hresp := contDiffOn_directSolverResponse_sourceObservationDomain T Q F row col Φ Y r χ η
    hη hχU solver hsolver Ξ hchart hchartU x₀ Rout hcore D a hD ha β hbound hΩ hspace hphase
    hF hi hrank hα hnonzero hχ hc τ
  have hshift' (p : Euclidean (d + 1) × Euclidean ((d + 1) - 1)) (hp : p ∈ (X ∩ interior Lobs) ×ˢ V) :
      (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈ Ojoint :=
    ⟨hshift p ⟨hp.1.1, hp.2⟩, hp.1.2, fun y hy ↦ hshift (y, p.2) ⟨hsrc hy, hp.2⟩⟩
  have hw (y : Euclidean (d + 1)) (hy : y ∈ X ∩ interior Lobs) :
      wholeSourceCorrectedWave T Q F row col Φ Y r χ Bfixed τ z mask v y =
        correctedWideWave T Q F row col Φ Y χ Bfixed τ r z (T.reference.spatialPatch z) mask v y := by
    rw [correctedWideWave_eq_canonical_sub_responseIntegral T Q F row col Φ Y χ Bfixed τ r z
      (T.reference.spatialPatch z) hopen (fun w hw ↦ hspace w hw.1) (fun w hw ↦ hphase w hw.1)
      hF hi hrank (hα.mono inter_subset_left) (fun w hw ↦ hnonzero w hw.1) hresp hshift' hceil hd hM hb v hy]
    change fullPrimaryWave T Q F row col Φ Y τ r z mask v y - complexifyResponse Bfixed
      (complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z mask v)) y = _
    rw [fullPrimaryWave_response_eq_integral_on_observation T Q F row col Φ Y r hΩ hspace hphase hF
      hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc hχ hc e Bfixed hzero v
      (interior_subset hy.2)]
    rfl
  have hh : wholeSourceCorrectedWave T Q F row col Φ Y r χ Bfixed τ z mask v =ᶠ[𝓝 x]
      correctedWideWave T Q F row col Φ Y χ Bfixed τ r z (T.reference.spatialPatch z) mask v := by
    filter_upwards [(hX.inter isOpen_interior).mem_nhds (show x ∈ X ∩ interior Lobs from ⟨hx, hxL⟩)]
      with y hy using hw y hy
  have hder : wholeSourceCorrectedDerivative T Q F row col Φ Y r χ Bfixed τ z mask v x =
      correctedWideDerivative T Q F row col Φ Y χ Bfixed τ r z (T.reference.spatialPatch z) mask v x := by
    unfold wholeSourceCorrectedDerivative correctedWideDerivative
    rw [hh.fderiv_eq, phase_on_carrier]
  exact ⟨hder, hder.trans (correctedWideDerivative_eq_integral T Q F row col Φ Y χ Bfixed τ r z
    (T.reference.spatialPatch z) hopen (fun w hw ↦ hspace w hw.1) (fun w hw ↦ hphase w hw.1)
    hF hi hrank (hα.mono inter_subset_left) (fun w hw ↦ hnonzero w hw.1) hresp hshift'
    hτ (hX.inter isOpen_interior) hV hceil hd hM hb v ⟨hx, hxL⟩)⟩

end JanetCartan.CanonicalAtomRealization
