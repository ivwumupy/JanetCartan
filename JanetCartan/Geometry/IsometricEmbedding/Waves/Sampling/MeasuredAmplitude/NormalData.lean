module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.InputJets

/-!
# Inserting the actual measured amplitude into the full phase geometry

The phase-only data are produced by
`FullNormalGeometry.exists_uniform_literalFullPhaseNormalData`. This module
replaces their zero reference amplitude by the SAME retained measured WKB
polynomial and proves all amplitude fields from the retained reconstruction
outputs. No normalized jet bound or normal-operator estimate is assumed.
The original geometric witnesses, phase, domains and epsilon interval remain
identical. The parent still has to choose these fixed supports and primitive
budgets on one initialized family and apply the mean and sample endpoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial RawKernel
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer
open FullNormalGeometry FullNormalGeometry.PhaseJets
open ContinuumRow.CanonicalConic ContinuumRow FullPhaseCharts

/-- Construct the nonzero measured normal data on the prescribed full phase
geometry, with every amplitude field proved from the actual retained raw
polynomial. The common amplitude budget precedes the immersion, scalar,
history scale, bands, spectators and phase data. In particular the epsilon
jet spends exactly one joint order and uses the original high profiles.
The final equality identifies the full measured amplitude on all inputs,
including epsilon zero (`app:ch_waves:setup:oscillatory`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retained_measuredNormalData
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C) (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {S : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hS : IsCompact S) (hSM : S ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean ((m + 1) - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean (m + 1) → ℝ)
    (measurement : Euclidean (m + 1) → Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ measurement U)
    (G : NormalComparison.UniformNormalGeometry (m + 1) (m + 1))
    (Cphase : ℕ → ℝ) (V : Set (Euclidean 2))
    (hGS : ∀ v ∈ V, ∀ w ∈ closure G.X ×ˢ closure G.D, (v, w) ∈ S)
    (hGe : G.ε₀ ≤ e) (hGρ : G.ε₀ ≤ ρ / 8)
    (hχplateau : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψgraph : ∀ s v, ψ (ContinuumRow.carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    {z₀ : Euclidean 3} {ηb : Euclidean (m + 1 - 1)} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈
      ContinuumRow.CanonicalConic.closedDirections (n := m + 1) ηb radius)
    (hχX : Function.support χ ⊆ G.X₀)
    (hψs : ∀ v ∈ V, ∀ s, ψ (ContinuumRow.carrierSamplingEquiv (s, v)) ≠ 0 →
      s ∈ closedBall (z₀ 0) radius)
    (hD₀ : G.D₀ = radialSamplingSupport T z₀ ηb radius amin amax) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
          Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
        (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      20 * ((m + 1) + 1) + 1 ≤ rpar →
      ∀ v ∈ V, ∀ j,
      ∀ N₀ : NormalComparison.UniformNormalData G Cphase,
      N₀.extensionDomain = fullPhaseExtensionDomain T v M →
      ∃ N : NormalComparison.UniformNormalData G (fun k ↦ Cphase k + A k),
        N.phase = N₀.phase ∧ N.parameterDomain = N₀.parameterDomain ∧
        N.extensionDomain = N₀.extensionDomain ∧
        N.amplitude = (fun ε x u ↦
          (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
            angular highPass ψ j v ε x u).ofLp) ∧
        ∀ ε ∈ Icc 0 G.ε₀, ∀ x u,
          N.amplitude ε x u =
            (fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
              (RawPrimary.MaskProfiles.detectorMask (n := m + 1) angular highPass)
              ψ j v ε x (canonicalInputCoordinates T u)).ofLp := by
  obtain ⟨A, hA, hactual⟩ := exists_retained_normalizedAmplitude_budgets (N := N) T
    hP M he hS hSM ψ hψ angular highPass ha hah hhigh hhigh₁ a hρ
    hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ χ measurement hχ hm
  let B := fun k ↦ 1 + ‖measuredOutputCoordinates (m + 1)‖ * (A k + A (k + 1))
  have hB (k) : 0 < B k := by
    have := hA k
    have := hA (k + 1)
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr hreserve v hv j N₀ hW
  obtain ⟨hs, _, hj⟩ := hactual F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr j
  let amp := supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
    angular highPass ψ j v
  have habs (ε : ℝ) (hε : ε ∈ Icc 0 G.ε₀) : |ε| ≤ ρ / 8 := by
    rw [abs_of_nonneg hε.1]
    exact hε.2.trans hGρ
  have hampSmooth : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
        (amp q.1 q.2.1 q.2.2).ofLp) (N₀.parameterDomain ×ˢ N₀.extensionDomain) := by
    apply PiLp.contDiff_ofLp.comp_contDiffOn
    apply hs.comp (f := fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
      (q.1, v, q.2)) (by fun_prop)
    intro q hq
    exact ⟨mem_univ _, by simpa only [hW, tripleDomain, mem_ofPred_eq] using hq.2⟩
  have hampSupport (ε : ℝ) (hε : ε ∈ Icc 0 G.ε₀) :
      Function.support (Function.uncurry (fun x u ↦ (amp ε x u).ofLp)) ⊆ G.X₀ ×ˢ G.D₀ := by
    have hh := support_supportedMeasuredNormalAmplitude_subset T Q F row col Φ Y r measurement
      χ a hρ angular highPass ψ hχplateau hψgraph hah hηb hradius hlo hhi hangle hχX
      v (hψs v hv) j (habs ε hε)
    rw [hD₀]
    intro w hw
    apply hh
    change amp ε w.1 w.2 ≠ 0
    intro hz
    apply hw
    change (amp ε w.1 w.2).ofLp = 0
    rw [hz]
    rfl
  have hampJets (ε : ℝ) (hε : ε ∈ Icc 0 G.ε₀)
      (w : Euclidean (m + 1) × Euclidean (m + 1)) (hw : w ∈ G.X ×ˢ G.D)
      (k : ℕ) (hk : k ≤ 20 * ((m + 1) + 1)) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦ (amp ε x u).ofLp)) w‖ +
        ‖deriv (fun t ↦ iteratedFDeriv ℝ k
          (Function.uncurry (fun x u ↦ (amp t x u).ofLp)) w) ε‖ ≤ B k := by
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
  let N : NormalComparison.UniformNormalData G (fun k ↦ Cphase k + B k) := {
    N₀ with
    amplitude := fun ε x u ↦ (amp ε x u).ofLp
    amplitude_smooth := hampSmooth
    amplitude_support := hampSupport
    input_jets := by
      intro ε hε w hw k hk
      have hp := N₀.input_jets ε hε w hw k hk
      have ha := hampJets ε hε w hw k hk
      have hz₁ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (N₀.amplitude ε)) w)
      have hz₂ := norm_nonneg (deriv (fun t ↦
        iteratedFDeriv ℝ k (Function.uncurry (N₀.amplitude t)) w) ε)
      linarith }
  refine ⟨N, rfl, rfl, rfl, rfl, ?_⟩
  intro ε hε x u
  exact congrArg WithLp.ofLp
    (supportedMeasuredNormalAmplitude_eq T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ hχplateau hψgraph j v (habs ε hε) x u)

end JanetCartan.Sampling.MeasuredAmplitude
