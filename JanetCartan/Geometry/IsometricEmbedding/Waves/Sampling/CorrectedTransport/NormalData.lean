module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.CrossJets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.Support
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.InputJets

/-!
# Actual corrected transport normal data on the retained phase geometry

Every amplitude field is proved from the original primitive coefficient,
response and measurement jets along the fixed-frequency algebraic path. The phase, domains and buffers are inherited from the same
phase-only construction supplied by `FullNormalGeometry`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CorrectedAtoms RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open FullNormalGeometry FullNormalGeometry.PhaseJets MeasuredAmplitude
open NormalComparison ContinuumRow

/-- Insert the actual corrected product into the SAME supplied phase geometry.
Every amplitude field, including the epsilon derivative at the homotopy's
zero endpoint, follows from the five raw profiles and same-response jets.
The required reserve is exactly `20*(n+1)+1`. The physical response rate stays
positive and fixed while the path reaches the common leading endpoint. Constants
precede the varying real measurement as well as the raw fields and history. The phase-only input is the output of
`FullNormalGeometry.exists_uniform_literalFullPhaseNormalData`, and its actual
instantiation remains an obligation of the final mean application
(`app:ch_osc:setup:osc-normal`, `app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_correctedTransportNormalData_of_profiles
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hκK : tsupport κ ⊆ K)
    (Cjet A₀ A₁ B₀ B₁ Cresp Cmeas : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    (hCmeas : ∀ j, 0 ≤ Cmeas j)
    (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {S : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hS : IsCompact S) (hSM : S ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1)
    (G : UniformNormalGeometry (m + 1) (m + 1)) (Cphase : ℕ → ℝ)
    (V : Set (Euclidean 2))
    (hGS : ∀ v ∈ V, ∀ w ∈ closure G.X ×ˢ closure G.D, (v, w) ∈ S)
    (hGe : G.ε₀ ≤ e)
    {ηb : Euclidean (m + 1 - 1)} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈
      CanonicalConic.closedDirections (n := m + 1) ηb radius)
    (hκX : Prod.fst '' Function.support κ ⊆ G.X₀)
    (hψs : ∀ v ∈ V, ∀ s, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      s ∈ closedBall (z₀ 0) radius)
    (hD₀ : G.D₀ = radialSamplingSupport T z₀ ηb radius amin amax) :
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
        Euclidean (m + 1)), ContDiff ℝ ∞ C →
      ∀ (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
        ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
        (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
          Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
        (χ : Euclidean (m + 1) → ℝ)
        (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
        (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ),
      (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
      ∀ (τ L : ℝ) (rpar : ℕ), 0 < τ → τ ≤ 1 → 1 ≤ L →
      (∀ k, ∀ x ∈ Prod.fst '' K,
        ‖iteratedFDeriv ℝ k C x‖ ≤ Cmeas k * L ^ (k - rpar)) →
      HasDerivativeProfile K (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
      HasDerivativeProfile K (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
      HasDerivativeProfile K (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (rpar + 1) L A₁ →
      HasDerivativeProfile K (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
      HasDerivativeProfile K (fullCorrectionReconstruction T Q F row col Φ Y r)
        (rpar + 1) L B₁ →
      ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω →
      (∀ j, ∀ w ∈ K,
        ‖iteratedFDeriv ℝ j (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
          τ * Cresp j * L ^ (j - rpar)) →
      20 * ((m + 1) + 1) + 1 ≤ rpar →
      ∀ v ∈ V, ∀ j,
      ∀ N₀ : UniformNormalData G Cphase,
      N₀.extensionDomain = fullPhaseExtensionDomain T v M →
      ∃ Ndata : UniformNormalData G (fun k ↦ Cphase k + D k),
        Ndata.phase = N₀.phase ∧ Ndata.parameterDomain = N₀.parameterDomain ∧
        Ndata.extensionDomain = N₀.extensionDomain ∧
        Ndata.amplitude = (fun ε x u ↦
          (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
            angular highPass ψ j v ε x u).ofLp) := by
  obtain ⟨A, hA, hactual⟩ := exists_correctedTransportNormalAmplitude_budgets_of_profiles (N := N)
    T hP z₀ hρ hcarrier hK hΩ hKΩ κ hκ hκK Cjet A₀ A₁ B₀ B₁ Cresp Cmeas
    hCjet hA₀ hA₁ hB₀ hB₁ hCresp hCmeas M he hS hSM ψ hψ angular highPass ha hah hhigh hhigh₁
  let D := fun k ↦ 1 + ‖measuredOutputCoordinates (m + 1)‖ * (A k + A (k + 1))
  have hD (k) : 0 < D k := by
    have := hA k
    have := hA (k + 1)
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro C hC Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁ τ L rpar hτ hτ₁ hL
    hCpoint hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets hreserve v hv j N₀ hW
  obtain ⟨hs, _, hj⟩ := hactual C hC Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁
    τ L rpar hτ hτ₁ hL hCpoint hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets j
  let amp := correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
    angular highPass ψ j v
  have hampSmooth : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
        (amp q.1 q.2.1 q.2.2).ofLp) (N₀.parameterDomain ×ˢ N₀.extensionDomain) := by
    apply PiLp.contDiff_ofLp.comp_contDiffOn
    apply hs.comp (f := fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
      (q.1, v, q.2)) (by fun_prop)
    intro q hq
    exact ⟨mem_univ _, by simpa only [hW, tripleDomain, mem_ofPred_eq] using hq.2⟩
  have hampSupport (ε : ℝ) :
      Function.support (Function.uncurry (fun x u ↦ (amp ε x u).ofLp)) ⊆ G.X₀ ×ˢ G.D₀ := by
    have hh := support_correctedTransportNormalAmplitude_subset T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ hah hηb hradius hlo hhi hangle hκX v (hψs v hv) j ε
    rw [hD₀]
    intro w hw
    apply hh
    intro hz
    apply hw
    change (amp ε w.1 w.2).ofLp = 0
    change amp ε w.1 w.2 = 0 at hz
    rw [hz]
    rfl
  have hampJets (ε : ℝ) (hε : ε ∈ Icc 0 G.ε₀)
      (w : Euclidean (m + 1) × Euclidean (m + 1)) (hw : w ∈ G.X ×ˢ G.D)
      (k : ℕ) (hk : k ≤ 20 * ((m + 1) + 1)) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦ (amp ε x u).ofLp)) w‖ +
        ‖deriv (fun t ↦ iteratedFDeriv ℝ k
          (Function.uncurry (fun x u ↦ (amp t x u).ofLp)) w) ε‖ ≤ D k := by
    have hwc : w ∈ closure G.X ×ˢ closure G.D :=
      ⟨subset_closure hw.1, subset_closure hw.2⟩
    have he' : ε ∈ Icc (-e) e :=
      ⟨by linarith [G.ε₀_pos, hε.1], hε.2.trans hGe⟩
    have hS' : (ε, v, w) ∈ Icc (-e) e ×ˢ S := ⟨he', hGS v hv w hwc⟩
    have hw' : w ∈ fullPhaseExtensionDomain T v M := by
      simpa only [hW] using N₀.spatial_subset hwc
    have hb := (measured_inputJets_le_joint T hs ε hw' k).trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (hj (ε, v, w) hS' k (by omega)) (hj (ε, v, w) hS' (k + 1) (by omega)))
        (norm_nonneg _))
    exact hb.trans (le_add_of_nonneg_left zero_le_one)
  let Ndata : UniformNormalData G (fun k ↦ Cphase k + D k) := {
    N₀ with
    amplitude := fun ε x u ↦ (amp ε x u).ofLp
    amplitude_smooth := hampSmooth
    amplitude_support := fun ε _ ↦ hampSupport ε
    input_jets := by
      intro ε hε w hw k hk
      have hp := N₀.input_jets ε hε w hw k hk
      have ha' := hampJets ε hε w hw k hk
      have hz₁ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (N₀.amplitude ε)) w)
      have hz₂ := norm_nonneg (deriv (fun t ↦
        iteratedFDeriv ℝ k (Function.uncurry (N₀.amplitude t)) w) ε)
      linarith }
  exact ⟨Ndata, rfl, rfl, rfl, rfl⟩

end JanetCartan.Sampling.CorrectedTransport
