module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactEstimate
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Extension
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CutoffGeometry

/-!
# Pure graph construction from uniform original cutoff jets

For `app:ch_regular_base:thm:actual-calculus`, Step 1, this assembles the actual
compact graphs, their proved normal identity, the primitive quadratic budget,
and the unique Fatou/density extension. All operator and transformed-symbol
premises are discharged. The remaining regularization obligation is explicit:
`jets` concerns the original amplitudes `χ_j A` and must be produced
uniformly from the uncut primitive symbol and the fixed cutoff profile.
The fixed uncut geometry is transported to every cutoff by `CutoffGeometry`.
This theorem does not yet discharge that cutoff-jet obligation.

Hamilton/compatible geometry supplies the actual averaged-gradient chart,
buffered inverse geometry, forward continuity and Jacobian jets; inverse
coefficients supplies the normalized inverse jets. The parent supplies the
original symbol, output/covector supports, and the uniform cutoff jets. The
constant depends only on dimension, fiber dimension, box and low geometry
budgets, never on amplitude size, cutoff index, or output Sobolev order.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Construct the unique graph and its literal adjoint with a linear amplitude
bound, conditional only on original geometry, support, polynomial domination
and uniform finite jets of the actual cutoff amplitudes. The transformed-symbol
bounds and operator identities are proved internally. Cutoff instantiation is
still required before claiming the uncut primitive low theorem. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem exists_graphL2_of_primitive_cutoffs (hn : 0 < n) (R M L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (X D : Set E) (S : E → E → ℝ) (A : E → E → Mat)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n))
      (a : ℝ), 0 ≤ a → AveragedGradientChart S X D η J δ →
      PrimitiveNormalGeometry X D S A A η J W K →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ j l, PrimitiveNormalShellInputs (cutAmplitude A j) (cutAmplitude A j)
        η J ((2 : ℝ)^l) (primitiveNormalReserve n) M L δ a a
        (normalDyadicShell (bufferedNormalDomain X D S) l) (V l)) →
      ∀ (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
        (Kout : Set E) (hKout : IsCompact Kout)
        (hsA : ∀ x η, x ∉ Kout → A x η = 0),
      (∀ x u, x ∉ X ∨ u ∉ D → A x u = 0) →
      ContinuousOn (normalForwardCoordinates S) (jointNormalCarrier A A) →
      ∀ (P : ℝ) (k : ℕ), (∀ x η, ‖A x η‖ ≤ P * (1 + ‖η‖ ^ k)) →
      ∃ T : H →L[ℂ] H, ‖T‖ ≤ C * a ∧ ‖T.adjoint‖ ≤ C * a ∧
        (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
            (graphTestToSchwartz u) x)) ∧
        (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) ∧
        (∀ f : H, Tendsto (fun j ↦ compactVectorGraph hS
          (cutAmplitude_entry_continuous hA j)
          (cutAmplitude_entry_hasCompactSupport hKout hsA j) f) atTop (𝓝 (T f))) ∧
        (∀ f : H, Tendsto (fun j ↦ (compactVectorGraph hS
          (cutAmplitude_entry_continuous hA j)
          (cutAmplitude_entry_hasCompactSupport hKout hsA j)).adjoint f)
          atTop (𝓝 (T.adjoint f))) ∧
        ∀ U : H →L[ℂ] H, (∀ u : graphTestSpace n r, U (graphTestToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
            (graphTestToSchwartz u) x)) → U = T := by
  obtain ⟨C, hC, hcompact⟩ := exists_compactVectorGraph_bound (n := n) (r := r) hn R M L hδ
  refine ⟨C, hC, ?_⟩
  intro X D S A η J W K V a ha chart geometry hR jets hS hA Kout hKout hsA
    hcarrier hforward P k hpolynomial
  apply exists_graphL2_of_cutoff_bound hS hA hKout hsA P k hpolynomial (mul_nonneg hC.le ha)
  intro j
  exact hcompact X D S (cutAmplitude A j) η J W K V a ha chart
    (geometry.cutAmplitude j j) hR (jets j) hS (cutAmplitude_entry_continuous hA j)
    (cutAmplitude_hasCompactSupport hKout hsA j)
    (fun x u hxu ↦ by simp [cutAmplitude, hcarrier x u hxu]) (hforward.mono (jointNormalCarrier_cutAmplitude_subset A A j j))

end JanetCartan.FourierIntegral.LowBounds
