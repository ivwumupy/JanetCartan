module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.ElapsedKernels

/-!
# The literal annular elapsed amplitude

These are the original objects in `app:ch_response:lem:energy-carrier-jets`.
The coefficient depends on the elapsed time and physical frequency, and is
independent of the carrier parameter. Both physical masks and beta/high-pass
remain inside it. The only new localization is the stated annular multiplier.
The initial compact branch restores exactly this amplitude, including its
order factor, for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral

variable {d r : ℕ} {P ι : Type}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The full fixed-time amplitude localized by the original annular
multiplier, before any carrier derivative (`new:eq:carrier-ibp`). -/
def annularElapsedAmplitude (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed lam : ℝ) : FullAmplitude (d + 1) r :=
  frequencyCutFullAmplitude (fun ξ => π (lam⁻¹ • ξ))
    (elapsedAmplitude a χout χsource β elapsed)

/-- The literal order-normalized amplitude in the joint compact integral.
The carrier parameter is deliberately unused: parameter differentiation fixes
the physical operator and frequency. Source: the annular normalization before
`new:eq:carrier-ibp`. -/
def normalizedAnnularElapsedAmplitude (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed lam : ℝ) (p : ℤ)
    (q : E × P) (w : CarrierVariables (d + 1)) : Mat :=
  (lam ^ p)⁻¹ • annularElapsedAmplitude a χout χsource β π elapsed lam
    q.1 w.fst (lam • w.snd)

/-- The displayed normalized integrand keeps every original mask and the
physical frequency `lam • θ`. Source: frequency localization in
`app:ch_response:lem:energy-carrier-jets`. -/
theorem normalizedAnnularElapsedAmplitude_apply
    (a : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (elapsed : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ)
    (q : E × P) (z θ : E) :
    normalizedAnnularElapsedAmplitude a χout χsource β π elapsed lam p
      q (WithLp.toLp 2 (z, θ)) =
      (lam ^ p)⁻¹ • ((π θ * (χout q.1 * χsource z * β (lam • θ))) •
        a (q.1 0) (q.1 0 - elapsed) (spatialPart q.1) (spatialPart (lam • θ))) := by
  simp only [normalizedAnnularElapsedAmplitude, annularElapsedAmplitude,
    normalized_elapsedAmplitude_with_annular_mask a χout χsource β π hlam]
  rfl

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]

/-- The initial branch is the SAME actual annular amplitude after restoration.
This identity closes the normalization obligation before applying the branch
operator construction; it assumes neither a new amplitude nor an operator
identification. Source: `new:eq:carrier-ibp`. -/
theorem modifiedAmplitude_initial_annular_eq
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (f : (E × P) → CarrierVariables (d + 1) → ℝ)
    (w₀ : E × P → CarrierVariables (d + 1))
    (a : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (elapsed : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ) (param : P) :
    modifiedAmplitude lam p (normalizedTermAmplitude basis f w₀
      (normalizedAnnularElapsedAmplitude a χout χsource β π elapsed lam p)
      initialJointTransferTerm param) =
      annularElapsedAmplitude a χout χsource β π elapsed lam := by
  funext x z ξ
  simp only [modifiedAmplitude, NearCarrierSymbol.physicalAmplitudeOfNormalized,
    Pi.smul_apply, normalizedTermAmplitude, matrixSlice, initialJointTransferTerm,
    IsometricEmbedding.Response.NearCarrier.AmplitudeExpression.evaluate,
    jointAmplitudeFields, normalizedSlice, normalizedAnnularElapsedAmplitude,
    smul_smul, mul_inv_cancel₀ (zpow_ne_zero p hlam), one_smul,
    WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, mul_inv_cancel₀ hlam]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
