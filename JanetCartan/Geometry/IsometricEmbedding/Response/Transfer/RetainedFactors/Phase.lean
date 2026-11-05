module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Basic

/-!
# Identification of the retained factors with the conic elapsed kernels

These are same-object connections for `app:ch_response:eq:fixed-factor-transfer`.
The hypotheses are literal outputs of `UniformAmplitudes.ConicConstruction` and
`UniformEvolution.exists_retained_local_solver_and_residual`. In particular the
residual keeps its output time plateau. Neither an envelope estimate nor a new
solver is assumed or constructed here. The conic representative has the exact
radial identity required by the annular calculation; its smooth extension and
common primary critical geometry remain separate obligations.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.UniformEvolution
open AmplitudeBounds ConicPhase DirectEvolution

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The same continued chart has exact degree one in the FULL spacetime
covector. This includes the time pairing, not only the spatial phase
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_elapsedPhase_smul
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (t : ℝ) (x ξ : E) {lam : ℝ} (hlam : 0 < lam) :
    elapsedPhase (curriedPhase ℓ C) t x (lam • ξ) =
      lam * elapsedPhase (curriedPhase ℓ C) t x ξ := by
  have h := extend_smul ℓ (twoTimePhase C)
    (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) hlam
  simp only [elapsedPhase, curriedPhase, SymbolBudgets.spatialPart_smul]
  change (x 0 - t) * (lam * ξ 0) + _ = _
  rw [show phase ℓ C (x 0, (x 0 - t, (spatialPart x, lam • spatialPart ξ))) =
    lam * phase ℓ C (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) from h]
  ring

/-- Both actions of the constructed solver are the SAME conic elapsed
kernels, with `W₀+W₁`, both physical masks and the original right multiplier.
Equality of these functions also preserves every carrier-parameter derivative
at fixed operator (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_solver_actions_eq_conic
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (Δ a₀ A₀ : ℝ) (A : ℕ → ℝ)
    (Solver : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hSolver : RetainedSignedRetardedBounds KQ Q B Δ a₀
      (fun t s y η ↦ G (t, (s, (y, η))))
      (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
      χout χsource β hs 0 A₀ A Solver) :
    (∀ u, Solver u = elapsedGraphIntegral Δ (curriedPhase ℓ C)
      (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β u) ∧
    (∀ u, Solver.adjoint u = ∫ t in Icc 0 Δ,
      (elapsedGraph (curriedPhase ℓ C)
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
        χout χsource β t).adjoint u) := by
  constructor
  · intro u
    exact (hSolver.2.1 u).trans
      (solver_elapsedGraphIntegral_eq_supported ℓ C W₀ W₁ G hG χout χsource β Δ u)
  · intro u
    rw [hSolver.2.2.1 u]
    simp_rw [solver_elapsedGraph_eq_supported ℓ C W₀ W₁ G hG]

/-- The complete residual's SAME forward and literal-adjoint actions use
the conic representative only after the actual output time plateau is retained.
Here `W` is the producer's third collared matrix, identified with the full
`twoTimePhysicalApply W₁`, including `B`, by
`retained_residual_eq_twoTimePhysicalApply`. No residual branch is discarded
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_residual_actions_eq_conic
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W : T → Mat) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (Δ a₀ A₀ : ℝ) (A : ℕ → ℝ)
    (Residual : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hResidual : RetainedSignedRetardedBounds KQ Q B Δ a₀
      (fun t s y η ↦ G (t, (s, (y, η)))) (curryCharacteristicMatrix W)
      χout χsource β hs 1 A₀ A Residual) :
    (∀ u, Residual u = elapsedGraphIntegral Δ (curriedPhase ℓ C)
      (curryCharacteristicMatrix W) χout χsource β u) ∧
    (∀ u, Residual.adjoint u = ∫ t in Icc 0 Δ,
      (elapsedGraph (curriedPhase ℓ C) (curryCharacteristicMatrix W)
        χout χsource β t).adjoint u) := by
  constructor
  · intro u
    exact (hResidual.2.1 u).trans
      (residual_elapsedGraphIntegral_eq_supported ℓ C W G κ hG χout χsource β hout Δ u)
  · intro u
    rw [hResidual.2.2.1 u]
    simp_rw [residual_elapsedGraph_eq_supported ℓ C W G κ hG χout χsource β hout]

end JanetCartan.ResponseTransfer.RetainedFactors
