module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Elapsed
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.ConicLimits.Support

/-!
# The same retained kernels with the constructed smooth representative

Only supported phase congruence is used. The full amplitude, its high-pass
transition, both physical masks and the elapsed integration endpoints are
unchanged. The residual identification retains its original output plateau.
Consumer: `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
open RegularSector.Characteristic ConicPhase EvolutionIntegral FourierIntegral
open UniformEvolution AmplitudeBounds
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The original multiplier support bound removes the smoothing transition
from every nonzero full amplitude, including its original high-pass shoulder
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem elapsed_representative_eq_on_amplitude
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (t : ℝ)
    (hfreq : ∀ ξ, β ξ ≠ 0 → δ ≤ ‖spatialPart ξ‖)
    (hbuffer : ∀ x z ξ, elapsedAmplitude b χout χsource β t x z ξ ≠ 0 →
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K)
    (x z ξ : E) (hA : elapsedAmplitude b χout χsource β t x z ξ ≠ 0) :
    elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t x ξ =
      elapsedPhase (curriedPhase ℓ C) t x ξ := by
  have hβ : β ξ ≠ 0 := fun h ↦ hA
    (elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z ξ (Or.inr (Or.inr h)))
  exact (elapsed_representative_eventuallyEq ℓ C hδ he
    (hbuffer x z ξ hA) (hfreq ξ hβ)).eq_of_nhds

/-- Equality of the literal bounded graph operators, with the original
amplitude and all original masks (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem elapsedGraph_representative_eq_conic
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (t : ℝ)
    (hfreq : ∀ ξ, β ξ ≠ 0 → δ ≤ ‖spatialPart ξ‖)
    (hbuffer : ∀ x z ξ, elapsedAmplitude b χout χsource β t x z ξ ≠ 0 →
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K) :
    elapsedGraph (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) b χout χsource β t =
      elapsedGraph (curriedPhase ℓ C) b χout χsource β t := by
  apply FullLowBounds.fullGraphOperator_phase_congr
  exact elapsed_representative_eq_on_amplitude ℓ C hδ he b χout χsource β t hfreq hbuffer

/-- Every compact-frequency regularization is unchanged in BOTH literal
orientations. The regularizing cutoff is arbitrary and the actual multiplier
is retained (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem regularized_representative_eq_conic
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (t : ℝ)
    (hfreq : ∀ ξ, β ξ ≠ 0 → δ ≤ ‖spatialPart ξ‖)
    (hbuffer : ∀ x z ξ, elapsedAmplitude b χout χsource β t x z ξ ≠ 0 →
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K)
    (backward : Bool) (cut : E → ℝ) (f : E → Fin q → ℂ) :
    (if backward then reverseGraphOperator else graphOperator)
        (elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t)
        (fun x z ξ ↦ (cut ξ : ℂ) • elapsedAmplitude b χout χsource β t x z ξ) f =
      (if backward then reverseGraphOperator else graphOperator)
        (elapsedPhase (curriedPhase ℓ C) t)
        (fun x z ξ ↦ (cut ξ : ℂ) • elapsedAmplitude b χout χsource β t x z ξ) f := by
  apply FiniteChain.Graph.ConicLimits.regularized_orientedGraph_phase_congr
  intro x z ξ hA _
  exact elapsed_representative_eq_on_amplitude ℓ C hδ he b χout χsource β t
    hfreq hbuffer x z ξ hA

/-- The elapsed integral and its literal integral of Hilbert adjoints keep
the original interval `Icc 0 Δ` (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem elapsed_integrals_representative_eq_conic
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (Δ : ℝ)
    (hfreq : ∀ ξ, β ξ ≠ 0 → δ ≤ ‖spatialPart ξ‖)
    (hbuffer : ∀ t ∈ Icc 0 Δ, ∀ x z ξ,
      elapsedAmplitude b χout χsource β t x z ξ ≠ 0 →
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K)
    (u : SpacetimeL2 d q) :
    elapsedGraphIntegral Δ (curriedRepresentative ℓ δ hδ χ (twoTimePhase C))
        b χout χsource β u =
      elapsedGraphIntegral Δ (curriedPhase ℓ C) b χout χsource β u ∧
    (∫ t in Icc 0 Δ, (elapsedGraph
        (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) b χout χsource β t).adjoint u) =
      ∫ t in Icc 0 Δ, (elapsedGraph (curriedPhase ℓ C) b χout χsource β t).adjoint u := by
  constructor
  · apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [elapsedGraph_representative_eq_conic ℓ C hδ he b χout χsource β t hfreq (hbuffer t ht)]
  · apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [elapsedGraph_representative_eq_conic ℓ C hδ he b χout χsource β t hfreq (hbuffer t ht)]

/-- The SAME retained `W₀+W₁` solver acts by the constructed representative,
in both orientations. The only operator input is the already produced
`RetainedSignedRetardedBounds` (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_solver_actions_eq_representative
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (Δ a₀ A₀ : ℝ) (A : ℕ → ℝ)
    (Solver : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hSolver : RetainedSignedRetardedBounds KQ Q B Δ a₀
      (fun t s y η ↦ G (t, (s, (y, η))))
      (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
      χout χsource β hs 0 A₀ A Solver)
    (hfreq : ∀ ξ, β ξ ≠ 0 → δ ≤ ‖spatialPart ξ‖)
    (hbuffer : ∀ t ∈ Icc 0 Δ, ∀ x z ξ,
      elapsedAmplitude (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
        χout χsource β t x z ξ ≠ 0 →
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K) :
    (∀ u, Solver u = elapsedGraphIntegral Δ
      (curriedRepresentative ℓ δ hδ χ (twoTimePhase C))
      (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β u) ∧
    (∀ u, Solver.adjoint u = ∫ t in Icc 0 Δ,
      (elapsedGraph (curriedRepresentative ℓ δ hδ χ (twoTimePhase C))
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
        χout χsource β t).adjoint u) := by
  obtain ⟨hf, ha⟩ := retained_solver_actions_eq_conic KQ Q B ℓ C W₀ W₁ G hG
    χout χsource β hs Δ a₀ A₀ A Solver hSolver
  have h := elapsed_integrals_representative_eq_conic ℓ C hδ he
    (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
    χout χsource β Δ hfreq hbuffer
  exact ⟨fun u ↦ (hf u).trans (h u).1.symm, fun u ↦ (ha u).trans (h u).2.symm⟩

/-- The SAME full residual, including the zeroth-order term and the actual
output plateau, acts by the representative in both orientations. `W` is the
producer's full `PW₁`; no branch is removed (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_residual_actions_eq_representative
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W : T → Mat) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (Δ a₀ A₀ : ℝ) (A : ℕ → ℝ)
    (Residual : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hResidual : RetainedSignedRetardedBounds KQ Q B Δ a₀
      (fun t s y η ↦ G (t, (s, (y, η)))) (curryCharacteristicMatrix W)
      χout χsource β hs 1 A₀ A Residual)
    (hfreq : ∀ ξ, β ξ ≠ 0 → δ ≤ ‖spatialPart ξ‖)
    (hbuffer : ∀ t ∈ Icc 0 Δ, ∀ x z ξ,
      elapsedAmplitude (curryCharacteristicMatrix W) χout χsource β t x z ξ ≠ 0 →
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K) :
    (∀ u, Residual u = elapsedGraphIntegral Δ
      (curriedRepresentative ℓ δ hδ χ (twoTimePhase C))
      (curryCharacteristicMatrix W) χout χsource β u) ∧
    (∀ u, Residual.adjoint u = ∫ t in Icc 0 Δ,
      (elapsedGraph (curriedRepresentative ℓ δ hδ χ (twoTimePhase C))
        (curryCharacteristicMatrix W) χout χsource β t).adjoint u) := by
  obtain ⟨hf, ha⟩ := retained_residual_actions_eq_conic KQ Q B ℓ C W G κ hG
    χout χsource β hs hout Δ a₀ A₀ A Residual hResidual
  have h := elapsed_integrals_representative_eq_conic ℓ C hδ he
    (curryCharacteristicMatrix W) χout χsource β Δ hfreq hbuffer
  exact ⟨fun u ↦ (hf u).trans (h u).1.symm, fun u ↦ (ha u).trans (h u).2.symm⟩

end JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
