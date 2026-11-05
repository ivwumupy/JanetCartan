module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.PrimitiveFields

/-!
# Scalar selected primitives constructed from the raw coefficient profile

This instantiates the raw phase/amplitude producer, its fixed buffered cutoff,
and all concrete scalar extractions. The result supplies the smooth primitive
fields, total reserve, literal coefficients, exact selected amplitude and
initial support required by `SpatialEstimate` and `ParameterEstimate`.
No inverse jets or graph bounds are hypotheses. Actual geometric data and
annular Jacobian/transport jets remain the response construction's inputs.
Source: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NearCarrierAssembly
open FourierIntegral GradedPrimitives NormalizedTransfer NearCarrierParameter
local instance rawFieldsRealMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace
local instance rawFieldsComplexMatrixTopology (r : ℕ) :
    TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Raw primitive phase and full-amplitude profiles produce the concrete scalar
family used in both transfer inductions, with the original matrix amplitude
recovered exactly. The cutoff and profile precede scale and frequency.
The selected support includes all cutoff shoulders and compact parameters.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_selectedPrimitiveFields_of_raw_profiles {n r p m : ℕ}
    (w : Fin m → Euclidean p)
    {X V : Set (Euclidean n)} {C : Set (Euclidean p)}
    (hX : IsOpen X) (hV : IsOpen V) (hC : IsOpen C)
    {Ksel : Set (ParameterAmplitudePoint n (Euclidean p))}
    (hKsel : IsCompact Ksel) (hKU : Ksel ⊆ (X ×ˢ X ×ˢ V) ×ˢ C)
    (A P Q : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hP : ∀ j, 0 ≤ P j)
    (hQ : ∀ j, 0 ≤ Q j) (Z M : ℝ) (hZ : 0 ≤ Z) :
    ∃ (χ : ParameterAmplitudePoint n (Euclidean p) → ℝ)
      (Ω : Set (ParameterAmplitudePoint n (Euclidean p))) (G : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      IsOpen Ω ∧ Ksel ⊆ Ω ∧ Ω ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      EqOn χ (fun _ ↦ 1) Ω ∧ (∀ j, 0 ≤ G j) ∧
      ∀ (L ρ : ℝ) (N Rstar : ℕ), 1 ≤ L → ρ ≠ 0 → 2 ≤ Rstar →
      ∀ (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n)
        (a : FullAmplitude n r) (q : Euclidean p × Euclidean n → ℂ)
        (D : Set (Euclidean n)),
      IsOpen D → Convex ℝ D →
      (∀ c ∈ C, ζ c ∈ D) → (∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) → ContDiffOn ℝ ∞ ζ C →
      ContDiffOn ℝ ∞ (normalizedFullAmplitude a ρ) (X ×ˢ X ×ˢ D) →
      ContDiffOn ℝ ∞ q (C ×ˢ V) →
      ∀ (b K : ℝ), 0 < b → (∀ c ∈ C, Metric.closedBall (ζ c) b ⊆ D) →
      (∀ x ∈ X, ∀ c ∈ C, IsUnit (mixedPhaseOperator S x (ζ c))) →
      (∀ x ∈ X, ∀ c ∈ C, ‖Ring.inverse (mixedPhaseOperator S x (ζ c))‖ ≤ M) →
      0 ≤ K → (∀ x ∈ X, ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K) →
      (∀ ε ∈ V, ‖ε‖ ≤ averagedMixedSelectorRadius b M K) →
      (∀ j ≤ N + 2, ∀ w ∈ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry S) w‖ ≤ A j * L ^ (j - Rstar)) →
      (∀ j ≤ N, ∀ w ∈ X ×ˢ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (normalizedFullAmplitude a ρ) w‖ ≤ P j * L ^ (j - (Rstar - 2))) →
      (∀ j ≤ N, ∀ w ∈ C ×ˢ V, ‖iteratedFDeriv ℝ j q w‖ ≤ Q j) →
      (∀ j, 1 ≤ j → j ≤ N + 1 → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z) →
      tsupport (normalizedParameterAmplitude a q ζ ρ) ⊆ Ksel →
      let f := cutoffExtension χ (selectedPrimitives a q S ζ ρ)
      let fields := selectedPrimitiveFields w f
      (∀ i, ContDiff ℝ ∞ (fields i)) ∧
      (∀ (i : SelectedPrimitiveEntry n r m) j, 0 ≤ ‖selectedPrimitiveExtraction w i‖ * G j) ∧
      (∀ i j, j ≤ N → ∀ z, ‖iteratedFDeriv ℝ j (fields i) z‖ ≤
        (‖selectedPrimitiveExtraction w i‖ * G j) * L ^ (j + 2 - Rstar)) ∧
      (∀ c i j, scalarPhysicalAmplitude (r := 1) ρ (frozenField c (fields (.amplitude i j))) =
        fun x y δ _ _ ↦ forwardSelectedAmplitude a (ζ c) ρ
          (fun δ ↦ q (c, ρ⁻¹ • δ)) x y δ i j) ∧
      (∀ i j z, jointPrimitivePointMap z ∈ Ksel →
        fields (.forwardSpatial i j) z =
          (averagedMixedMatrix S (ζ z.1.1) 1 z.1.2.1 z.2 i j : ℂ)) ∧
      (∀ i j z, jointPrimitivePointMap z ∈ Ksel →
        fields (.reverseSpatial i j) z =
          ((averagedMixedMatrix S (ζ z.1.1) 1 z.1.2.2 z.2)⁻¹ i j : ℂ)) ∧
      (∀ i j z, jointPrimitivePointMap z ∈ Ksel →
        fields (.forwardParameter i j) z =
          (phaseCoefficient S ζ ρ z.1.1 (w i) z.1.2.1 (ρ • z.2) j : ℂ)) ∧
      (∀ i j z, jointPrimitivePointMap z ∈ Ksel →
        fields (.reverseParameter i j) z =
          reverseParameterRow S ζ ρ
            (fun y δ ↦ (averagedMixedMatrix S (ζ z.1.1) 1 y (ρ⁻¹ • δ))⁻¹)
            z.1.1 (w i) z.1.2.2 (ρ • z.2) j) ∧
      ∀ {Xout Xsrc F : Set (Euclidean n)} (_hXout : IsCompact Xout) (_hXsrc : IsCompact Xsrc),
        (∀ z ∈ Ksel, z.1.1 ∈ Xout ∧ z.1.2.1 ∈ Xsrc ∧ z.1.2.2 ∈ F) →
        ∀ i j, SupportedJointAmplitude C Xout Xsrc F (jointPrimitivePointMap ⁻¹' Ksel)
          (fields (.amplitude i j)) := by
  obtain ⟨χ, Ω, G, hχ, hc, hs, hΩ, hKΩ, hΩU, hp, hG, hbuild⟩ :=
    exists_global_selected_primitives (r := r) hX hV hC hKsel hKU A P Q hA hP hQ Z M hZ
  refine ⟨χ, Ω, G, hχ, hc, hs, hΩ, hKΩ, hΩU, hp, hG, ?_⟩
  intro L ρ N Rstar hL hρ hR S ζ a q D hD hcD hζD hbuffer hS hζ ha hq
    b K hb hball hu hM hK hd hε hSjet hajet hqjet hζjet hsupport
  obtain ⟨hf, _, _, _, hfirst, he, _, hj⟩ := hbuild L ρ N Rstar hL hR S ζ a q D
    hD hcD hζD hbuffer hS hζ ha hq b K hb hball hu hM hK hd hε
    hSjet hajet hqjet hζjet hsupport
  have hfields := selectedPrimitiveFields_smooth_and_jets w hf hG hj
  have hmaps : MapsTo (jointPrimitivePointMap (n := n) (p := p))
      (jointPrimitivePointMap ⁻¹' Ksel) Ω := fun _ hz ↦ hKΩ hz
  refine ⟨hfields.1, hfields.2.1, hfields.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c i j
    exact scalarPhysicalAmplitude_selectedPrimitiveFields w a q ζ hρ hfirst c i j
  · intro i j z hz
    exact selectedPrimitiveFields_forwardSpatial w a q S ζ ρ hmaps he i j hz
  · intro i j z hz
    exact selectedPrimitiveFields_reverseSpatial w a q S ζ ρ hmaps he i j hz
  · intro i j z hz
    exact selectedPrimitiveFields_forwardParameter w a q S ζ hρ hmaps he i j hz
  · intro i j z hz
    exact selectedPrimitiveFields_reverseParameter w a q S ζ hρ hmaps he i j hz
  · intro Xout Xsrc F hXout hXsrc hpositions i j
    exact selectedPrimitiveFields_amplitude_supported w hf a q ζ ρ hfirst hsupport
      hXout hXsrc hpositions i j

end JanetCartan.ResponseTransfer.NearCarrierAssembly
