module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Field
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.RootGeometry

/-!
# Global bounds retained for the actual characteristic root

These conclusions of the frozen-pencil constructor supply the finite protection
certificate export, then `SelectedSectorProtection.exists_selectedSector_nested_proof_masks`
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open ActualCarriers RootFamily
variable {d : ℕ}

/-- Global root-domain evidence for the same root used by the amplitudes.
The speed is that of the normalized physical determinant; the transverse
matrix derivative is also retained for the characteristic-kernel consumer.
Sources: `app:ch_regular:thm:no-return`, and `paper-v2.tex`,
`app:ch_regular_base:lem:characteristic-kernel`. -/
def RootProtectionBounds
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ)
    (U : Set (RootState (Euclidean d))) (ℓ : Euclidean d →L[ℝ] ℝ)
    (speedGap rootSize : ℝ) : Prop :=
  ∀ w ∈ U,
    w.2.2 ≠ 0 ∧ (rootPencil e Q h w).det = 0 ∧
    fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 ∧
    speedGap ≤ |JanetCartan.ArbitraryAccuracy.pencilRootSpeed Q e h w| ∧
    |h w| ≤ ℓ w.2.2 * rootSize

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
