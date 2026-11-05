module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.SignedCarriers
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.JointPhaseJets

/-!
# One smooth phase on the entire retained signed carrier

The open frequency buffer has a strictly positive linear conic coordinate.
Its closure therefore has a quantitative spatial-frequency gap. The signed
normalization estimate puts the whole carrier in a closed chart ball strictly
inside the original target buffer. These facts instantiate the common smooth
representative before histories or masks and give exact phase germs in both
orientations. Consumer: the actual capped construction's smooth phase inputs
in `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral DirectEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- A positive spatial-frequency gap on the COMPLETE signed carrier, including
its frequency boundary and both annular shoulders. This is derived from the
actual linear conic gap, not from a compactness argument after choosing the
history (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedSignedCarrier_frequency_lower_bound
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε aperture gap radius : ℝ}
    (hgap : 0 < gap) {Par : Set (Euclidean 3)}
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOc : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOK : IsCompact (closure
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))) :
    0 < gap / (1 + ‖ℓ‖) ∧ ∀ v ∈ retainedSignedCarrier z ε Par
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius),
        gap / (1 + ‖ℓ‖) ≤ ‖spatialPart v.2.snd‖ := by
  have hden : 0 < 1 + ‖ℓ‖ := by positivity
  refine ⟨div_pos hgap hden, ?_⟩
  intro v hv
  have hfreq := (retainedOpenIntegrationDomain_geometry z ε hO hOc hOK).2.2.2 _ hv.2
  have hgap' : gap ≤ ℓ (spatialPart v.2.snd) := by
    apply closure_minimal (s := retainedOpenAnnularFrequencyCarrier ℓ z.2.2
      (ε / 2) aperture gap radius) (t := {θ : E | gap ≤ ℓ (spatialPart θ)})
      (fun θ hθ ↦ (show gap < ℓ (spatialPart θ) from hθ.2.2).le)
      (isClosed_le continuous_const (ℓ.continuous.comp spatialPartCLM.continuous)) hfreq.2
  apply (div_le_iff₀ hden).mpr
  have hb := ℓ.le_opNorm (spatialPart v.2.snd)
  rw [Real.norm_eq_abs] at hb
  calc
    gap ≤ |ℓ (spatialPart v.2.snd)| := hgap'.trans (le_abs_self _)
    _ ≤ ‖ℓ‖ * ‖spatialPart v.2.snd‖ := hb
    _ ≤ ‖spatialPart v.2.snd‖ * (1 + ‖ℓ‖) := by nlinarith [norm_nonneg (spatialPart v.2.snd)]

/-- Select one smooth representative on the actual enlarged signed carrier.
The capped constructor proves `8*ε ≤ b`, hence the strict buffer required here.
The single transition is below both the original physical frequency gap and
the just-proved annular gap. All choices precede the varying chart and phase.
Both literal carrier-phase germs agree on the ENTIRE signed carrier; every
joint derivative and critical/Hessian identity can be transported there.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_signed_carrier_smooth_representative
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε b aperture gap radius : ℝ}
    (hε : 0 < ε) (hεb : 4 * ε < b) (hAp : 0 < aperture) (hgap : 0 < gap)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOc : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOK : IsCompact (closure
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius)))
    {δphysical : ℝ} (hphysical : 0 < δphysical) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, δ ≤ δphysical ∧ δ ≤ gap / (1 + ‖ℓ‖) ∧
    ∃ χ : TC → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ ball (z.1, z) b ∧
      (∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1)) ∧
    ∀ C : OpenPartialHomeomorph TC TC, closedBall (z.1, z) b ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      let Ψ := SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)
      ContDiff ℝ ∞ (SmoothRepresentative.representative ℓ δ hδ χ (twoTimePhase C)) ∧
      (∀ t, ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t))) ∧
      Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ∧
      (∀ lam : ℝ, 1 ≤ lam → ∀ R t : ℝ, ∀ x θ : E,
        lam • θ ∈ SmoothRepresentative.annularFrequencyCarrier δ R lam →
        elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ) ∧
      ∀ (Par : Set (Euclidean 3)) (φ : E → Euclidean 3 → ℝ) (adj : Bool),
        ∀ v ∈ retainedSignedCarrier z ε Par
          (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius),
          jointRetainedCarrierPhase adj Ψ φ =ᶠ[𝓝 v]
            jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ := by
  have hden : 0 < gap / (1 + ‖ℓ‖) := div_pos hgap (by positivity)
  obtain ⟨δ, hδ, hδp, hδa, χ, hχ, hcχ, hsχ, heχ, hrep⟩ :=
    SmoothRepresentative.exists_common_smooth_representative ℓ
      (isCompact_closedBall (z.1, z) (4 * ε)) isOpen_ball
      (closedBall_subset_ball hεb) hphysical hden
  refine ⟨δ, hδ, hδp, hδa, χ, hχ, hcχ, hsχ, heχ, ?_⟩
  intro C hbuffer hC Ψ
  have hr := hrep C (ball_subset_closedBall.trans hbuffer) hC
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.1, ?_⟩
  intro Par φ adj v hv
  have hnorm := retainedSignedCarrier_normalizes ℓ z hε hAp hgap hO hOc hOK adj hv
  have hfreq := (retainedSignedCarrier_frequency_lower_bound ℓ z hgap hO hOc hOK).2 v hv
  exact jointRetainedCarrierPhase_representative_eventuallyEq adj ℓ C hδ heχ φ
    ⟨by simpa only [carrierGraphPoint] using hnorm.1, hnorm.2⟩ (hδa.trans hfreq)

end JanetCartan.ResponseTransfer.RetainedFactors
