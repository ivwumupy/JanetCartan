module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.ContinuousExtension.Regularity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhaseExtension

/-!
# Supported replacement of the conic phase in the elapsed graph

Joint germ agreement on the normalized buffer pulls back through the exact
elapsed-time substitution. The existing full graph phase-congruence theorem
then identifies the operators with both physical masks and the Fourier
multiplier retained. The geometric producer supplies only containment of
the normalized support in the compact buffer; no angular or jet hypotheses
are introduced here.

Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral
variable {d m : ℕ}

/-- The auxiliary and original conic elapsed phases have the same joint
germ, including the elapsed-time variable, whenever the spatial frequency
normalizes into the buffer. Consumer: all supported phase jets in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedPhase_joint_eventuallyEq_of_conic_extension
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {G : TwoTimePoint (Euclidean d) → ℝ} {K : Set (TwoTimePoint (Euclidean d))}
    (he : ∀ q ∈ domain ℓ K, G =ᶠ[𝓝 q] phase ℓ C)
    {r : ℝ} {x ξ : Euclidean (d + 1)}
    (hq : (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K) :
    (fun p : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) ↦
      elapsedPhase (fun t s y η ↦ G (t, (s, (y, η)))) p.1 p.2.1 p.2.2) =ᶠ[𝓝 (r, (x, ξ))]
    (fun p ↦ elapsedPhase (fun t s y η ↦ phase ℓ C (t, (s, (y, η)))) p.1 p.2.1 p.2.2) := by
  have hc : Continuous (fun p : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) ↦
      (p.2.1 0, (p.2.1 0 - p.1, (spatialPart p.2.1, spatialPart p.2.2)))) := by
    change Continuous (fun p : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) ↦
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.1,
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.1 - p.1,
          (spatialPartCLM p.2.1, spatialPartCLM p.2.2))))
    fun_prop
  filter_upwards [(he _ hq).comp_tendsto (hc.tendsto (r, (x, ξ)))] with p hp
  exact congrArg (fun a ↦ (p.2.1 0 - p.1) * p.2.2 0 + a) hp

/-- Fixed-elapsed-time joint agreement in output and frequency preserves
the supported phase derivatives used by the full graph construction.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedPhase_eventuallyEq_of_conic_extension
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {G : TwoTimePoint (Euclidean d) → ℝ} {K : Set (TwoTimePoint (Euclidean d))}
    (he : ∀ q ∈ domain ℓ K, G =ᶠ[𝓝 q] phase ℓ C)
    {r : ℝ} {x ξ : Euclidean (d + 1)}
    (hq : (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K) :
    Function.uncurry (elapsedPhase (fun t s y η ↦ G (t, (s, (y, η)))) r) =ᶠ[𝓝 (x, ξ)]
      Function.uncurry (elapsedPhase (fun t s y η ↦ phase ℓ C (t, (s, (y, η)))) r) :=
  (elapsedPhase_joint_eventuallyEq_of_conic_extension ℓ C he hq).comp_tendsto
    (continuous_const.prodMk continuous_id).continuousAt

/-- The literal elapsed graphs coincide when the full amplitude's support
normalizes into the buffer. Both physical masks, the source position and
the original Fourier normalization are retained. This proves equality of
the existing operators, without asserting an operator estimate.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_eq_of_conic_extension
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {G : TwoTimePoint (Euclidean d) → ℝ} {K : Set (TwoTimePoint (Euclidean d))}
    (he : ∀ q ∈ domain ℓ K, G =ᶠ[𝓝 q] phase ℓ C)
    (b : TwoTimeAmplitude d m) (χout χsource β : Euclidean (d + 1) → ℂ) (r : ℝ)
    (hsupp : ∀ x z ξ, elapsedAmplitude b χout χsource β r x z ξ ≠ 0 →
      (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K) :
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η)))) b χout χsource β r =
      elapsedGraph (fun t s y η ↦ phase ℓ C (t, (s, (y, η)))) b χout χsource β r := by
  apply FullLowBounds.fullGraphOperator_phase_congr
  intro x z ξ hA
  exact (elapsedPhase_eventuallyEq_of_conic_extension ℓ C he (hsupp x z ξ hA)).eq_of_nhds

/-- Output-mask and multiplier support containment suffices for the graph
identity, with no condition on the source mask. The parent conic geometry
supplies these two support inclusions into its actual compact buffer.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_eq_of_conic_extension_on_masks
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {G : TwoTimePoint (Euclidean d) → ℝ} {K : Set (TwoTimePoint (Euclidean d))}
    (he : ∀ q ∈ domain ℓ K, G =ᶠ[𝓝 q] phase ℓ C)
    (b : TwoTimeAmplitude d m) (χout χsource β : Euclidean (d + 1) → ℂ) (r : ℝ)
    (hsupp : ∀ x ξ, χout x ≠ 0 → β ξ ≠ 0 →
      (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K) :
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η)))) b χout χsource β r =
      elapsedGraph (fun t s y η ↦ phase ℓ C (t, (s, (y, η)))) b χout χsource β r := by
  apply elapsedGraph_eq_of_conic_extension ℓ C he b χout χsource β r
  intro x z ξ hA
  exact hsupp x ξ
    (fun hx ↦ hA (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x z ξ (Or.inl hx)))
    (fun hξ ↦ hA (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x z ξ
      (Or.inr (Or.inr hξ))))

end JanetCartan.RegularSector.Characteristic.ConicPhase
