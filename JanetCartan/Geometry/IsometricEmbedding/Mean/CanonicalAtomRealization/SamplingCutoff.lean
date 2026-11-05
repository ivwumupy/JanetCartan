module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.DirectAtomIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Extension

/-!
# A common smooth sampling extension of the actual corrected amplitude

A fixed compact tube in the original observation chart has one cutoff for
every inverse frequency and Fourier band. Joint regularity is obtained from
the same direct solution, and multiplication by this cutoff extends it off
the tube (`app:ch_waves:eq:sampling-operator-bounds`).
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
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)

set_option quotPrecheck false in
local notation "Bfixed" => fixedSmoothSolverAmbientExtension F (Subtype.val Q) η hU
  (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ
local notation "Lobs" => closedBall x₀ Rout
local notation "Ojoint" => sourceObservationDomain Ω (tsupport χ) Lobs

include hchart hchartU hcore hD ha hbound hΩ hspace hphase hF hi hrank hα hnonzero hχ hc

/-- The original supplied sampling cutoff makes the SAME direct-solver
amplitude globally smooth. The all-source classical estimate supplies the
joint regularity on its support; no replacement cutoff or amplitude is chosen
(`app:ch_waves:eq:sampling-operator-bounds`, `app:ch_response:cor:current-atoms`). -/
theorem contDiff_directSolver_cutoffAmplitude
    (κ : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hs : tsupport κ ⊆ Ojoint) {τ : ℝ} (hτ : τ ≠ 0) :
    ContDiff ℝ ∞ (fun w ↦
      κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ Bfixed r τ w) := by
  have hopen := isOpen_sourceObservationDomain hΩ hc Lobs
  have hresp := contDiffOn_directSolverResponse_sourceObservationDomain T Q F row col Φ Y r χ η
    hη hχU solver hsolver Ξ hchart hchartU x₀ Rout hcore D a hD ha β hbound hΩ hspace
    hphase hF hi hrank hα hnonzero hχ hc τ
  exact ResponseTransfer.GradedPrimitives.contDiff_cutoffExtension hopen hκ hs
    (contDiffOn_fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ Bfixed r
      hopen (fun w hw ↦ hspace w hw.1) (fun w hw ↦ hphase w hw.1) hF hi hrank
      (hα.mono inter_subset_left) (fun w hw ↦ hnonzero w hw.1) hτ hresp)

/-- A single extension of the corrected sampling amplitude on a supplied
compact retained tube. The cutoff is fixed before the inverse frequencies
and band cutoffs. It is one throughout a neighborhood of the tube and zero
off the original observation chart
(`app:ch_waves:eq:sampling-operator-bounds`, `app:ch_response:cor:current-atoms`). -/
theorem exists_directSolver_samplingAmplitudeCutoff
    (Kobs : Set (Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))))
    (hK : IsCompact Kobs) (hKO : Kobs ⊆ Ojoint) :
    ∃ κ : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)) → ℝ,
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ Ojoint ∧
      Kobs ⊆ interior {w | κ w = 1} ∧
      ∀ τ : ℝ, τ ≠ 0 → ContDiff ℝ ∞ (fun w ↦
        κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ Bfixed r τ w) := by
  have hopen := isOpen_sourceObservationDomain hΩ hc Lobs
  obtain ⟨κ, hκ, _, hκc, hs, hone⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hK hopen hKO
  refine ⟨κ, hκ, hκc, hs, hone, fun τ hτ ↦ ?_⟩
  exact contDiff_directSolver_cutoffAmplitude T Q F row col Φ Y r χ η hη hχU
    solver hsolver Ξ hchart hchartU x₀ Rout hcore D a hD ha β hbound hΩ hspace hphase
    hF hi hrank hα hnonzero hχ hc κ hκ hs hτ

/-- Construct the sampling plateau on one retained slice before every node,
inverse frequency and band ceiling in its window. The compact tube uses the
original slice cutoff, full original source admission, and the returned
radii; neither input mask nor source support is shrunk
(`app:ch_waves:eq:individual-raw-slice`, `app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retainedSlice_directSolver_samplingCutoff
    (z₀ : Euclidean 3) (ζ₀ : Euclidean ((d + 1) - 1)) {σ aSlice bSlice e : ℝ}
    (haSlice : 4 * aSlice ≤ σ / 2) (hbSlice : bSlice ≤ σ / 4)
    (he : 0 < e) (heb : 16 * e < bSlice)
    (hraw : closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ ⊆ Ω)
    (hsource : ∀ w ∈ closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ,
      ∀ y ∈ tsupport χ, (y, w.2) ∈ Ω)
    (ψ : Euclidean (d + 1) → ℝ) (hψsmall : tsupport ψ ⊆ closedBall 0 (aSlice / 4))
    (hψL : tsupport ψ ⊆ interior Lobs) :
    ∃ κ : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)) → ℝ,
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ Ojoint ∧
      (∀ τ : ℝ, τ ≠ 0 → ContDiff ℝ ∞ (fun w ↦ κ w •
        fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ Bfixed r τ w)) ∧
      ∀ z : Euclidean 3, (z, T.reference.spatialPatch z) ∈ ball (z₀, ζ₀) (σ / 4) →
      ∀ K τ : ℝ, 1 ≤ K → 0 ≤ τ → 2 * (τ * K) ≤ e →
      ∀ y ∈ tsupport ψ, ∀ θ ∈ closedBall 0 ((2 : ℝ) ^ cutoffCount K),
        κ (y, (z, T.reference.spatialPatch z + τ • θ)) = 1 := by
  let Ct := tsupport ψ ×ˢ closedBall (z₀, ζ₀) (σ / 2)
  have hψc := (isCompact_closedBall (0 : Euclidean (d + 1)) _).of_isClosed_subset
    (isClosed_tsupport ψ) hψsmall
  have hct : IsCompact Ct := hψc.prod (isCompact_closedBall _ _)
  have hobs : Ct ⊆ Ojoint := by
    rintro ⟨y, c⟩ ⟨hy, hc⟩
    have hyc : (y, c) ∈ closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ := by
      rw [mem_closedBall, Prod.dist_eq, max_le_iff]
      exact ⟨(mem_closedBall.mp (hψsmall hy)).trans (by linarith), (mem_closedBall.mp hc).trans (by linarith)⟩
    exact ⟨hraw hyc, hψL hy, hsource _ hyc⟩
  obtain ⟨κ, hκ, hκc, hs, hone, hA⟩ := exists_directSolver_samplingAmplitudeCutoff T Q F row col Φ Y r χ η
    hη hχU solver hsolver Ξ hchart hchartU x₀ Rout hcore D a hD ha β hbound hΩ hspace
    hphase hF hi hrank hα hnonzero hχ hc Ct hct hobs
  refine ⟨κ, hκ, hκc, hs, hA, ?_⟩
  intro z hz K τ hK hτ hw y hy θ hθ
  apply interior_subset (hone ?_)
  refine ⟨hy, ?_⟩
  have hfreq := (rawSlice_window_containments T z (a := aSlice) he heb hK hτ hw).2.2.2 θ
    (closedBall_subset_closedBall (cutoffCount_ceiling hK) hθ)
  have hz' := mem_ball.mp hz
  rw [Prod.dist_eq, max_lt_iff] at hz'
  rw [mem_closedBall, Prod.dist_eq, max_le_iff]
  exact ⟨hz'.1.le.trans (by linarith),
    (dist_triangle _ (T.reference.spatialPatch z) ζ₀).trans (by linarith [mem_ball.mp hfreq, hz'.2])⟩

end JanetCartan.CanonicalAtomRealization
