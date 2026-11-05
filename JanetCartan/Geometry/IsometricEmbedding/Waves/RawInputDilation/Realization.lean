module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Operators

/-!
# Normalized realization of a raw annular channel

This bridge supplies the consumer of `app:ch_waves:thm:sampling` with the
normalized kernel on every unit-annulus input. Its input is the literal raw
kernel representation of an actual bounded operator. The raw-primary and
masked-normal producers must establish that representation and boundedness;
neither is assumed for the already normalized kernel.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputDilation
open RawInputRealization NormalComparison
variable {n r : ℕ} {K τ : ℝ}

/-- An actual raw operator with the literal half-derivative kernel has the
normalized kernel on *every* unit-annulus input (`app:ch_waves:eq:actual-T`).
This uses the constructed unitary, not a hypothesis asserting unitary equivalence.
The original kernel representation and boundedness remain producer obligations. -/
theorem dilatedRawPrimaryOperator_ae_integral (hn : 1 ≤ n) (hK : 0 < K) (hτ : τ ≠ 0)
    (S : Euclidean n → Euclidean (n - 1) → ℝ) (ζ : Euclidean (n - 1))
    (β : Euclidean (n - 1) → ℂ) (a : Euclidean n → Euclidean (n - 1) → Fin r → ℂ)
    (T : AnnularL2 n K →L[ℂ] NormalOutputL2 n r)
    (hT : ∀ (f : AnnularL2 n K) (i : Fin r), (T f) i =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        ∫ η, ((Real.sqrt ‖η‖ : ℂ) *
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) * β η) *
            f η) • a x η i ∂annularMeasure n K)
    (g : AnnularL2 n 1) (i : Fin r) :
    (dilatedOperator hK T g) i =ᵐ[volume] fun x ↦
      normalOperatorScale n K •
        ∫ θ, ((Real.sqrt ‖θ‖ : ℂ) *
          (oscillatoryFactor K (rawPrimaryPhaseDifference S ζ (τ * K) x θ) * β (K • θ)) *
            g θ) • a x (K • θ) i ∂annularMeasure n 1 := by
  apply (hT ((annularDilation n K hK).symm g) i).trans
  apply Filter.Eventually.of_forall
  intro x
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    normalized_rawPrimary_integral hn hK hτ S ζ x β (fun η ↦ a x η i)
      ((annularDilation n K hK).symm g)

end JanetCartan.RawInputDilation
