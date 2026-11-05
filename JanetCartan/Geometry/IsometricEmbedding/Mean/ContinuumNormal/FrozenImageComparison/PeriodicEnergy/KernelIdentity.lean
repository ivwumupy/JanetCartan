module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Product
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Mixed

/-!
# Identifying the frozen periodic normal kernel

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, assemble the proved
identities for `B D*`, `D B*`, and `D D*` into the literal Bochner kernel
identity on every real L² input. Their absolutely integrable scalar sections
justify combining the three terms under one integral. Pairing with the input
then gives the double-integral energy identity, also on every real L² input.

The sole extra premise is continuity of the explicit scalar kernel entries.
Its producer is `contDiff_fixedNormalCorrectionKernelEntry` in the companion
`KernelRegularity` module. The parent frozen periodic energy comparison
retains its instantiation and application of the compact-kernel energy bound.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open JanetCartan.PeriodicLocalL2
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- All three actual frozen normal terms integrate the explicit correction
kernel, on every real L² input (`app:ch_background:prop:bg-frame`). The mixed
terms retain both source masks and leave the Bessel kernel undifferentiated;
their identification and the product's Fubini theorem are imported proofs.
The continuity premise is supplied by `contDiff_fixedNormalCorrectionKernelEntry`
when the parent periodic energy comparison applies this identity. -/
theorem fixedNormalCrossTerms_ae_integral (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hK : ∀ i j, Continuous (fixedNormalCorrectionKernelEntry hR A i j)) (u : R²) :
    normalCrossTerms (fixedEuclideanChannel hR A) (fixedLatticeOperator hR hcell A) u
      =ᵐ[volume] fun x ↦ ∫ y, fixedNormalCorrectionKernel hR A (x, y) (u y) := by
  let B := fixedEuclideanChannel hR A
  let D := fixedLatticeOperator hR hcell A
  filter_upwards [fixedEuclideanChannel_comp_latticeAdjoint_ae_integral hR hcell A u,
    fixedLatticeOperator_comp_euclideanAdjoint_ae_integral hR hcell A u,
    fixedLatticeOperator_normal_ae_integral hR hcell A u,
    Lp.coeFn_add (B (D.adjoint u) + D (B.adjoint u)) (D (D.adjoint u)),
    Lp.coeFn_add (B (D.adjoint u)) (D (B.adjoint u))] with x h₁ h₂ h₃ h₄ h₅
  change (B (D.adjoint u) + D (B.adjoint u) + D (D.adjoint u)) x = _
  simp only [Pi.add_apply] at h₄ h₅
  rw [h₄, h₅, h₁, h₂, h₃]
  ext i
  rw [integral_fixedNormalCorrectionKernel_apply_coordinate hR A hK u x i]
  change (∑ j, ∫ y, fixedMixedKernelEntry hR A i j (x, y) * u y j) +
    (∑ j, ∫ y, fixedMixedKernelEntry hR A j i (y, x) * u y j) +
    (∑ j, ∫ y, fixedLatticeProductKernelEntry hR A i j (x, y) * u y j) = _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hm := integrable_fixedMixedKernelEntry_mul_coordinate hR hcell A u i j x
  have ht := integrable_fixedMixedKernelEntry_swap_mul_coordinate hR hcell A u i j x
  have hp := integrable_fixedLatticeProductKernelEntry_mul_coordinate hR hcell A u i j x
  simp only [fixedNormalCorrectionKernelEntry, add_mul, Prod.swap_prod_mk]
  rw [← integral_add hm ht]
  exact (integral_add (hm.add ht) hp).symm

/-- The quadratic form of the full frozen normal correction equals its
literal double-kernel integral (`app:ch_background:prop:bg-frame`). This holds
on every real L² input, in particular on the integrable inputs used by
`exists_compactKernel_energy_bound` in the parent periodic energy comparison.
The parent supplies `hK` from `contDiff_fixedNormalCorrectionKernelEntry`. -/
theorem fixedNormalCrossTerms_inner_eq_integral (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hK : ∀ i j, Continuous (fixedNormalCorrectionKernelEntry hR A i j)) (u : R²) :
    inner ℝ u (normalCrossTerms (fixedEuclideanChannel hR A)
      (fixedLatticeOperator hR hcell A) u) =
        ∫ x, ∫ y, inner ℝ (u x) (fixedNormalCorrectionKernel hR A (x, y) (u y)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fixedNormalCrossTerms_ae_integral hR hcell A hK u] with x hx
  rw [hx]
  exact (integral_inner (integrable_fixedNormalCorrectionKernel_apply hR A hK u x)
    (u x)).symm

end JanetCartan.ContinuumNormal.FrozenImageComparison
