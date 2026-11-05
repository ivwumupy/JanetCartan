module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.Shells
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.CompactSupport
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Normal

/-!
# The primitive bilinear budget for the exact cycle normal symbol

This closes the amplitude-bound input to the uniform compact graph estimate
in actual-calculus Step 1, `app:ch_regular_base:eq:actual-normal-amplitude`.
The parent still instantiates the primitive geometry and cutoff jets and
identifies the compact graph normal with the bounded PDO.

Producer obligations (none is asserted to have been instantiated here):
* `jc-hamilton-phase` and `jc-compatible-phase-geometry` supply the buffered
  domain and range, `mapsTo`, `rightInverse`, the Jacobian component of
  `input_smooth`, `gap`, normalized `jacobianJets`, and forward continuity on
  `jointNormalCarrier`. Their inverse and buffer APIs live in `HamiltonPhase`
  and `FullPhaseCharts/InverseFamily`.
* `jc-normal-inverse-coefficients` supplies `inverse_smooth` and the positive
  normalized `inverseJets`; the checked finite composition API is
  `NormalComparison/InverseBounds/InverseAmplitude/Jets`.
* `jc-fio-source-independent-l2` supplies the amplitude components of
  `input_smooth`, the complete original cutoff jets `leftJets`/`rightJets`,
  `left_output`/`right_output`, `carrier`, `closed_image`, `buffer`, and the
  fixed physical box bound. The cutoffs and their shoulders are included in
  `A` and `B` before any inverse substitution. For compact-PDO identification
  it also supplies joint compactness of these original cutoff amplitudes.

The constants precede all those fields and their regularization parameter.
The finite reserve is `primitiveNormalReserve n = 2 * (n + 1)` and the sole
paired-coordinate multiplier is `normalPositionJetFactor n` at that reserve.
Cycle frequency changes no physical derivative order or budget.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The literal cycle cross-normal has budget `C * a * b`, with `C` chosen
before amplitudes, shell radii and regularizations. All quantitative hypotheses
bound original order-zero shell jets; the derivative reserve is exactly
`2 * (n + 1)`. Geometry is needed only on the buffered output box, and smoothness
and physical support are deduced from primitive inputs. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`, actual-calculus Step 1. -/
theorem exists_cycleCrossNormalSymbol_bounds (M L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (X D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n)) (R a b : ℝ),
      0 ≤ a → 0 ≤ b → PrimitiveNormalGeometry X D S A B η J W K →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ j, PrimitiveNormalShellInputs A B η J ((2 : ℝ)^j)
        (primitiveNormalReserve n) M L δ a b
        (normalDyadicShell (bufferedNormalDomain X D S) j) (V j)) →
      GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A B η J) R (C * a * b) := by
  obtain ⟨C, hC, hb⟩ := exists_extendedCrossNormalAmplitude_orderZero_bilinear_bound
    (n := n) (r := r) (primitiveNormalReserve n) M L hδ
  refine ⟨C * normalPositionJetFactor n (primitiveNormalReserve n),
    mul_pos hC (normalPositionJetFactor_pos _ _), ?_⟩
  intro X D S A B η J W K V R a b ha hb' G hR hshell
  refine ⟨G.contDiff_cycleSymbol,
    fun ξ i j ↦ cycleCrossNormalSymbol_supportedInCenteredBox G.left_output G.right_output hR ξ i j,
    ?_⟩
  intro ξ is hi z
  have hj := hb S A B η J _ W K V a b ha hb' hshell G.mapsTo G.rightInverse
    G.carrier G.closed_image G.buffer
  have he : cycleCrossNormalSymbol D S A B η J ξ =
      pairedNormalAmplitude (extendedCrossNormalAmplitude (bufferedNormalDomain X D S) A B η J)
        ((2 * Real.pi) • ξ) := by
    funext w
    exact cycleCrossNormalSymbol_eq_pairedBuffered X D S A B η J G.left_output G.right_output ξ w
  rw [he]
  apply (pairedNormalAmplitude_derivative_bound G.contDiff_extension hj _ is hi z).trans_eq
  ring

/-- The self-normal budget is exactly quadratic, also at `a = 0`; no
normalization by the amplitude size is used. This is the input to the compact
graph norm estimate in actual-calculus Step 1. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_cycleSelfNormalSymbol_bounds (M L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (X D : Set E) (S : E → E → ℝ) (A : E → E → Mat)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n)) (R a : ℝ),
      0 ≤ a → PrimitiveNormalGeometry X D S A A η J W K →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ j, PrimitiveNormalShellInputs A A η J ((2 : ℝ)^j)
        (primitiveNormalReserve n) M L δ a a
        (normalDyadicShell (bufferedNormalDomain X D S) j) (V j)) →
      GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A A η J) R (C * a^2) := by
  obtain ⟨C, hC, hb⟩ := exists_cycleCrossNormalSymbol_bounds (n := n) (r := r) M L hδ
  refine ⟨C, hC, ?_⟩
  intro X D S A η J W K V R a ha G hR hshell
  simpa only [pow_two, mul_assoc] using hb X D S A A η J W K V R a a ha ha G hR hshell

end JanetCartan.FourierIntegral.LowBounds
