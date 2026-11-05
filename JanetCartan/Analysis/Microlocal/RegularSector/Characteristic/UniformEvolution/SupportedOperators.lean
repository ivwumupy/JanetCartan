module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.RetardedOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhaseAgreement

/-!
# The constructed operators retain the supported auxiliary phase

The phase germs are the literal outputs of `UniformAmplitudes.ConicConstruction`.
Both bounded operators stay unchanged. Only their integral descriptions are
rewritten, including the original source mask and reversed triangle.
Consumer: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open AmplitudeBounds ConicPhase FourierIntegral EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- The solver's actual support germs transfer every integral identity of
the SAME constructed operator to the producer's smooth phase. The signed
coefficient bounds remain unchanged (`retarded-kernel`). -/
theorem retained_solver_bounds_supported_phase
    (KQ : Set E) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Matrix (Fin q) (Fin q) ℂ) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (Δ a₀ A₀ : ℝ) (A : ℕ → ℝ) (Op : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hOp : RetainedSignedRetardedBounds KQ Q B Δ a₀ (curriedPhase ℓ C)
      (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
      χout χsource β hs 0 A₀ A Op) :
    RetainedSignedRetardedBounds KQ Q B Δ a₀ (fun t s y η ↦ G (t, (s, (y, η))))
      (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁)
      χout χsource β hs 0 A₀ A Op := by
  simpa only [RetainedSignedRetardedBounds,
    solver_elapsedGraphIntegral_eq_supported ℓ C W₀ W₁ G hG,
    solver_elapsedGraph_eq_supported ℓ C W₀ W₁ G hG,
    solver_retardedPhysicalIntegral_eq_supported ℓ C W₀ W₁ G hG,
    solver_reverseRetardedFrequency_eq_supported ℓ C W₀ W₁ G hG] using hOp

/-- The physical residual's germ is needed only on the original output time
plateau. That precise weaker producer conclusion suffices for the SAME
bounded residual and its literal adjoint (`energy-complete-residual`). -/
theorem retained_residual_bounds_supported_phase
    (KQ : Set E) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W : T → Matrix (Fin q) (Fin q) ℂ) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (hs : ContDiff ℝ ∞ χsource)
    (Δ a₀ A₀ : ℝ) (A : ℕ → ℝ) (Op : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hOp : RetainedSignedRetardedBounds KQ Q B Δ a₀ (curriedPhase ℓ C)
      (curryCharacteristicMatrix W) χout χsource β hs 1 A₀ A Op) :
    RetainedSignedRetardedBounds KQ Q B Δ a₀ (fun t s y η ↦ G (t, (s, (y, η))))
      (curryCharacteristicMatrix W) χout χsource β hs 1 A₀ A Op := by
  simpa only [RetainedSignedRetardedBounds,
    residual_elapsedGraphIntegral_eq_supported ℓ C W G κ hG χout χsource β hout,
    residual_elapsedGraph_eq_supported ℓ C W G κ hG χout χsource β hout,
    residual_retardedPhysicalIntegral_eq_supported ℓ C W G κ hG χout χsource β hout,
    residual_reverseRetardedFrequency_eq_supported ℓ C W G κ hG χout β hout] using hOp

end JanetCartan.RegularSector.Characteristic.UniformEvolution
