module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.KernelIdentity

/-!
# Normalized kernels of the literal elapsed-time factors

The fixed-time application of `paper-v2.tex`, `new:eq:carrier-ibp`. Here the
phase is literally `EvolutionIntegral.elapsedPhase Ψ t`, and all physical,
high-pass and annular masks appear in the displayed normalized amplitude.
The support-local homogeneity premise is supplied by the two-time phase
homogeneity through `EvolutionIntegral.elapsedPhase_smul`.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral

variable {d r : ℕ} {P : Type}

/-- Exact normalized kernel for the forward elapsed factor, retaining the
physical Fourier constant, the frequency Jacobian, both physical positions,
and every mask. Source: the localization preceding `new:eq:carrier-ibp`. -/
theorem demodulated_elapsedGraphOperator_eq_normalized
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ) (t : ℝ)
    (φ : Euclidean (d + 1) → P → ℝ) (a : Euclidean (d + 1) → Fin r → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (q : Euclidean (d + 1) × P)
    (hΘ : ∀ z θ,
      frequencyCutFullAmplitude (fun ξ => π (ρ⁻¹ • ξ))
        (elapsedAmplitude b χout χsource β t) q.1 z (ρ • θ) ≠ 0 →
      elapsedPhase Ψ t q.1 (ρ • θ) = ρ * elapsedPhase Ψ t q.1 θ) :
    carrier (-ρ) (fun x => φ x q.2) q.1 •
      graphOperator (elapsedPhase Ψ t)
        (frequencyCutFullAmplitude (fun ξ => π (ρ⁻¹ • ξ))
          (elapsedAmplitude b χout χsource β t))
        (fun z => carrier ρ (fun y => φ y q.2) z • a z) q.1 =
    ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • (ρ ^ (d + 1) •
      ∫ θ : Euclidean (d + 1), ∫ z : Euclidean (d + 1),
        oscillation (elapsedCarrierPhase Ψ t φ) ρ q (WithLp.toLp 2 (z, θ)) •
          ((π θ * (χout q.1 * χsource z * β (ρ • θ))) •
            b (q.1 0) (q.1 0 - t) (spatialPart q.1) (spatialPart (ρ • θ))).mulVec (a z)) := by
  rw [demodulated_graphOperator_eq_normalized _ _ _ _ hρ q hΘ]
  simp only [normalized_elapsedAmplitude_with_annular_mask b χout χsource β π hρ.ne']
  rfl

/-- The literal adjoint exchanges physical positions and conjugate-transposes
the full amplitude. Its reversed phase uses the original elapsed phase at the
integration position; no fixed-transverse retarded phase is substituted.
Source: the adjoint case of `new:eq:carrier-ibp`. -/
theorem demodulated_adjointElapsedGraphOperator_eq_normalized
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ) (t : ℝ)
    (φ : Euclidean (d + 1) → P → ℝ) (a : Euclidean (d + 1) → Fin r → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (q : Euclidean (d + 1) × P)
    (hΘ : ∀ z θ,
      frequencyCutFullAmplitude (fun ξ => π (ρ⁻¹ • ξ))
        (elapsedAmplitude b χout χsource β t) z q.1 (ρ • θ) ≠ 0 →
      elapsedPhase Ψ t z (ρ • θ) = ρ * elapsedPhase Ψ t z θ) :
    carrier (-ρ) (fun x => φ x q.2) q.1 •
      reverseGraphOperator (elapsedPhase Ψ t)
        (fun x z ξ => (frequencyCutFullAmplitude (fun ξ => π (ρ⁻¹ • ξ))
          (elapsedAmplitude b χout χsource β t) x z ξ).conjTranspose)
        (fun z => carrier ρ (fun y => φ y q.2) z • a z) q.1 =
    ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • (ρ ^ (d + 1) •
      ∫ θ : Euclidean (d + 1), ∫ z : Euclidean (d + 1),
        oscillation (adjointCarrierPhase (elapsedPhase Ψ t) φ) ρ q (WithLp.toLp 2 (z, θ)) •
          (star (π θ * (χout z * χsource q.1 * β (ρ • θ))) •
            (b (z 0) (z 0 - t) (spatialPart z) (spatialPart (ρ • θ))).conjTranspose).mulVec (a z)) := by
  rw [demodulated_reverseGraphOperator_eq_normalized _ _ _ _ hρ q hΘ]
  simp only [normalized_adjoint_elapsedAmplitude_with_annular_mask b χout χsource β π hρ.ne']

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
