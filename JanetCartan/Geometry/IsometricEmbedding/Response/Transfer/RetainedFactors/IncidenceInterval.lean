module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IncidenceCriticalSlice
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedKernels

/-!
# The original incidence retains the full elapsed phase agreement

The stationary segments on a nonempty original incidence imply the needed radius
comparison. Apply that comparison to the existing supported-phase identities for
both complete physical factors. The time interval, masks and literal cancellation
phase are retained (`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral UniformEvolution
open FullSourceStationary DirectEvolution EvolutionIntegral.KernelIdentification
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)

/-- On a nonempty original source incidence, the selector's full segment
certificate itself proves that its stationary radius is no larger than the
carrier radius. No extra cap or independently chosen radius is needed.
Consumer: full elapsed supported-phase agreement in
`app:ch_response:eq:fixed-factor-transfer`. -/
theorem full_source_stationary_radius_le_carrier_of_nonempty
    (z : RootState (Euclidean d)) {ε τ : ℝ} (hε : 0 < ε)
    {V : Set Par} (hV : V.Nonempty) (O : Set E)
    (κ : (ℝ × (E × Par)) → CW) :
    let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ V
    let D := retainedOpenIntegrationDomain z ε O
    let Z := Ioo (-2 * τ) (2 * τ) ×ˢ U₀
    MapsTo κ Z D →
    (∀ p ∈ Z, ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ a ∈ Icc (0 : ℝ) 1,
      ((u, p.2), κ p + a • (w - κ p)) ∈ fullSourceSignedCarrier z ε (closure V) O) →
    τ ≤ ε := by
  intro U₀ D Z hκ hsegments
  by_contra! hτε
  obtain ⟨c, hc⟩ := hV
  let x := timeSpacePoint z.1 z.2.1
  have hx : x ∈ elapsedPhysicalBox z (ε / 2) := by
    simp only [x, elapsedPhysicalBox, timeSpacePoint_time, spatialPart_timeSpacePoint,
      mem_ofPred_eq]
    exact ⟨mem_ball_self (half_pos hε), mem_ball_self (half_pos hε)⟩
  let p : ℝ × (E × Par) := (τ + ε, (x, c))
  have hp : p ∈ Z := ⟨⟨by dsimp [p]; linarith, by dsimp [p]; linarith⟩, hx, hc⟩
  have h := hsegments p hp (κ p) (subset_closure (hκ hp)) p.1 right_mem_uIcc
    0 ⟨le_rfl, zero_le_one⟩
  have ht : τ + ε ≤ 2 * ε := h.1.1.2
  linarith

/-- The original full-source stationary segments discharge the source-radius
comparison for both complete physical factors. Thus the original cancellation
phase agrees on their nonzero amplitudes over the WHOLE source interval, with
unchanged masks and complete `PW₁`. Only the original supported cancellation
germs are used. The input critical map and its segments are the outputs retained
by `exists_full_source_stationary_smooth_fixed_inverse`
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem full_source_incidence_solver_residual_phase_agreement
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε τ src aperture : ℝ} (hε : 0 < ε) (hsrcτ : src ≤ τ)
    {V : Set Par} (hV : V.Nonempty) (O : Set E)
    (κ : (ℝ × (E × Par)) → CW)
    (hκ : MapsTo κ (Ioo (-2 * τ) (2 * τ) ×ˢ (elapsedPhysicalBox z (ε / 2) ×ˢ V))
      (retainedOpenIntegrationDomain z ε O))
    (hsegments : ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ (elapsedPhysicalBox z (ε / 2) ×ˢ V),
      ∀ w ∈ closure (retainedOpenIntegrationDomain z ε O),
      ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ a ∈ Icc (0 : ℝ) 1,
      ((u, p.2), κ p + a • (w - κ p)) ∈ fullSourceSignedCarrier z ε (closure V) O)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {χphase : TwoTimePoint (Euclidean d) → ℝ}
    (hχ : ∀ p ∈ closedBall (z.1, z) (4 * ε), χphase =ᶠ[𝓝 p] (fun _ ↦ 1))
    {q : ℕ} (W₀ W₁ PW₁ : TwoTimePoint (Euclidean d) → Matrix (Fin q) (Fin q) ℂ)
    (G : TwoTimePoint (Euclidean d) → ℝ) (κtime : ℝ → ℝ)
    (hGsolver : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (hGres : ∀ p : TwoTimePoint (Euclidean d), κtime =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
      PW₁ p ≠ 0 → G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (hplateau : ∀ x, χout x ≠ 0 → κtime =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (hβ : tsupport β ⊆ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) :
    let Ψactual := fun t s y ξ ↦ G (t, (s, (y, ξ)))
    let Ψ := SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase (twoTimePhase C)
    (∀ t ∈ Icc (0 : ℝ) (3 * src / 4), ∀ x y ξ,
      elapsedAmplitude (AmplitudeBounds.curryCharacteristicMatrix W₀ +
        AmplitudeBounds.curryCharacteristicMatrix W₁) χout χsource β t x y ξ ≠ 0 →
      elapsedPhase Ψactual t x ξ = elapsedPhase Ψ t x ξ) ∧
    (∀ t ∈ Icc (0 : ℝ) (3 * src / 4), ∀ x y ξ,
      elapsedAmplitude (AmplitudeBounds.curryCharacteristicMatrix PW₁)
        χout χsource β t x y ξ ≠ 0 →
      elapsedPhase Ψactual t x ξ = elapsedPhase Ψ t x ξ) := by
  intro Ψactual Ψ
  have hsrcε := hsrcτ.trans
    (full_source_stationary_radius_le_carrier_of_nonempty z hε hV O κ hκ hsegments)
  exact ⟨fun _ ht x y ξ hA ↦ capped_solver_phase_eq_representative_on_amplitude
    ℓ z hε hsrcε C hδ hδhalf hχ W₀ W₁ G hGsolver χout χsource β hout hβ ht x y ξ hA,
    fun _ ht x y ξ hA ↦ capped_residual_phase_eq_representative_on_amplitude
    ℓ z hε hsrcε C hδ hδhalf hχ PW₁ G κtime hGres χout χsource β hout hplateau hβ ht x y ξ hA⟩

end JanetCartan.ResponseTransfer.RetainedFactors
