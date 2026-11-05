module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.NormalizedJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Carrier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Kernels

/-!
# One smooth representative for the same retained conic kernels

`exists_common_smooth_representative` selects the normalized localizer and
the small-frequency transition from the common buffers before the chart,
coefficients, frequency, histories or carrier parameters. The representative
is the explicit localized radial extension with that transition. Its global
smoothness supplies `hSPhase` and `hΨcont`; exact radial scaling on the compact
annular frequency carrier supplies the literal `hΘ` of both orientations of
`DirectEvolution.IntegratedEnvelope.Assembly`.

`Carrier` places the actual closed normalized-annular amplitude support in
that carrier and preserves the supported diagonal endpoint. `Jets` and
`NormalizedJets` derive quantitative costs from original phase jets with
derivative shift zero; no uniformity is inferred from smoothness alone.
`Kernels` identifies the same forward graphs, compact-frequency
regularizations, literal adjoints and elapsed integrals. In particular its
retained solver and full residual results use the existing `W₀+W₁` and `PW₁`
construction, retaining the residual's output time plateau.

The common-buffer containments and the two positive spatial-frequency lower
bounds are geometric inputs of the parent retained-factor application. The
parent must instantiate these on the SAME charts and masks from
`UniformAmplitudes.ConicConstruction` and `UniformEvolution.Assembly`.
In the retained-radius producer the fixed outer ball of radius `b` lies in
every target, while `ρ ≤ b` permits the inner closed ball of radius `ρ / 2`;
these supply `U` and `K` without choosing a cutoff after the coefficients.
This construction asserts no envelope estimate or response existence.
Sources: `app:ch_response:eq:direct-envelope-profile` and
`app:ch_response:eq:fixed-factor-transfer` in `paper.tex`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
open RegularSector.Characteristic ConicPhase EvolutionIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- Choose the common localizer and transition ONCE, before the varying chart
phase. The two primitive positive lower bounds concern, respectively, the
original physical multiplier and the normalized annular carrier. Their
minimum is used for the explicit smoothing; neither original mask changes.

For every supplied chart containing the common open buffer, this constructs
global smoothness, both consumer regularity signatures, supported joint germ
agreement, the exact literal annular radial identity, and quantitative
original-phase bounds with derivative shift zero. The final common-buffer
and mask instantiation remains the parent construction's obligation.
Sources: `app:ch_response:eq:direct-envelope-profile` and
`app:ch_response:eq:fixed-factor-transfer`. -/
theorem exists_common_smooth_representative
    (ℓ : Euclidean d →L[ℝ] ℝ) {K U : Set T}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {δphysical δannular : ℝ} (hphysical : 0 < δphysical) (hannular : 0 < δannular) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, δ ≤ δphysical ∧ δ ≤ δannular ∧
    ∃ χ : T → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1)) ∧
      ∀ C : OpenPartialHomeomorph T T, U ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        let G := representative ℓ δ hδ χ (twoTimePhase C)
        let Ψ := curriedRepresentative ℓ δ hδ χ (twoTimePhase C)
        ContDiff ℝ ∞ G ∧
        (∀ t, ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t))) ∧
        Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
          Ψ p.1.1 p.1.2 p.2.1 p.2.2) ∧
        (∀ p ∈ domain ℓ K, δ ≤ ‖p.2.2.2‖ → G =ᶠ[𝓝 p] phase ℓ C) ∧
        (∀ lam : ℝ, 1 ≤ lam → ∀ R t : ℝ, ∀ x θ : E,
          lam • θ ∈ annularFrequencyCarrier δ R lam →
          elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ) ∧
        (∀ J : Set T, IsCompact J → (∀ p ∈ J, 0 < ℓ p.2.2.2) →
          MapsTo (normalize ℓ) J K → (∀ p ∈ J, δ ≤ ‖p.2.2.2‖) → ∀ n : ℕ,
          cNorm J n G ≤ jetBoundConstant ℓ J n * cNorm K n (twoTimePhase C)) := by
  let δ := min δphysical δannular
  have hδ : 0 < δ := lt_min hphysical hannular
  obtain ⟨χ, hχ, hc, hs, he⟩ := exists_common_phase_localizer hK hU hKU
  refine ⟨δ, hδ, min_le_left _ _, min_le_right _ _, χ, hχ, hc, hs, he, ?_⟩
  intro C hUC hC G Ψ
  refine ⟨contDiff_representative ℓ hδ hχ hc hU hs (hC.mono hUC),
    fun t ↦ contDiff_elapsed_representative ℓ hδ hχ hc hU hs (hC.mono hUC) t,
    continuous_regrouped_representative ℓ hδ hχ hc hU hs (hC.mono hUC),
    fun p hp hf ↦ representative_eventuallyEq_phase ℓ C hδ he hp hf,
    fun lam hlam R t x θ hθ ↦
      elapsed_representative_smul_on_carrier ℓ hδ χ (twoTimePhase C) R hlam t x θ hθ,
    fun J hJ hpos hmap hfreq n ↦
      cNorm_representative_le ℓ C hδ he hK (hKU.trans hUC) hJ hC hpos hmap hfreq n⟩

end JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
