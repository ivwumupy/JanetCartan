module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactPDO
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds

/-!
# The compact graph bound from original primitive jets

Actual-calculus Step 1 (`app:ch_regular_base:thm:actual-calculus`): the exact
compact normal identity and the primitive quadratic symbol budget yield a
linear amplitude bound. No transformed amplitude estimate, operator identity,
or operator norm is an input. The consumer is the uniform frequency-cutoff
construction; it must instantiate these original jets for every cutoff.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Uniform compact-graph bound from the actual chart and original finite jets.
The constant is chosen before the amplitude and its size, so the same constant
works at size zero and for every frequency regularization. The only derivative
reserve is `primitiveNormalReserve n = 2 * (n + 1)`. The Hamilton and compatible
geometry producers must supply `chart`, `geometry` and forward continuity;
inverse coefficients supply the inverse jets. The parent supplies amplitude
support and jets. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_compactVectorGraph_bound (hn : 0 < n) (R M L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (X D : Set E) (S : E → E → ℝ) (A : E → E → Mat)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n)) (a : ℝ),
      0 ≤ a → AveragedGradientChart S X D η J δ →
      PrimitiveNormalGeometry X D S A A η J W K →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ j, PrimitiveNormalShellInputs A A η J ((2 : ℝ)^j)
        (primitiveNormalReserve n) M L δ a a
        (normalDyadicShell (bufferedNormalDomain X D S) j) (V j)) →
      ∀ (hS : Continuous (Function.uncurry S))
        (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
        (hsA : HasCompactSupport (Function.uncurry A)),
      (∀ x u, x ∉ X ∨ u ∉ D → A x u = 0) →
      ContinuousOn (normalForwardCoordinates S) (jointNormalCarrier A A) →
      ‖compactVectorGraph hS hA
        (fun i k ↦ hsA.comp_left (g := fun Q : Mat ↦ Q i k) (by simp))‖ ≤ C * a := by
  obtain ⟨B, hB, hbudget⟩ := exists_cycleSelfNormalSymbol_bounds (n := n) (r := r) M L hδ
  let F := (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * B)
  have hF : 0 ≤ F := mul_nonneg (by positivity)
    (mul_nonneg (fixedBoxAmplitudeConstant_nonneg n R) hB.le)
  refine ⟨Real.sqrt F + 1, by positivity, ?_⟩
  intro X D S A η J W K V a ha chart geometry hR hj hS hA hsA hcarrier hforward
  have hnormal := hbudget X D S A η J W K V R a ha geometry hR hj
  have hcompact := geometry.hasCompactSupport_cycleSymbol hsA hsA hforward
  have hb := norm_compactVectorGraph_le_of_normalSymbol chart hS hA
    (fun i k ↦ hsA.comp_left (g := fun Q : Mat ↦ Q i k) (by simp)) hcarrier hn R _ hnormal hcompact
  have he : (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * (B * a^2)) = F * a^2 := by
    dsimp [F]
    ring
  rw [he, Real.sqrt_mul hF, Real.sqrt_sq ha] at hb
  exact hb.trans (by nlinarith)

end JanetCartan.FourierIntegral.LowBounds
