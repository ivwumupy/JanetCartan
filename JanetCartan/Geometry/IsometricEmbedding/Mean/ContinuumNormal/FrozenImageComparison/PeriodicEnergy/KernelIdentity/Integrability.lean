module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.Kernel

/-!
# Absolute convergence for the frozen normal kernel

The scalar sections and coordinate integrals below are used in the literal
three-term normal identity for `paper-v2.tex`, `app:ch_background:prop:bg-frame`.
Only the explicitly permitted continuity premise on the final entries is
needed for their vector-valued integral. Its producer is
`contDiff_fixedNormalCorrectionKernelEntry` in the companion regularity task.
This module does not identify that integral with the normal operator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

namespace KernelIdentity

/-- A compact scalar entry has compact input sections. This supplies the
absolute convergence needed by both mixed and product terms in
`app:ch_background:prop:bg-frame`. -/
theorem hasCompactSupport_entry_section {K : E × E → ℝ}
    (hs : HasCompactSupport K) (x : E) :
    HasCompactSupport (fun y ↦ K (x, y)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_snd)
  intro y hy
  exact ⟨(x, y), subset_tsupport K hy, rfl⟩

/-- Every real compact entry can be integrated against a coordinate of an
arbitrary L² input. Consumer: the finite sums in the full frozen normal
identity (`app:ch_background:prop:bg-frame`). -/
theorem integrable_entry_mul_coordinate {K : E × E → ℝ}
    (hc : Continuous K) (hs : HasCompactSupport K) (u : R²) (j : Fin n) (x : E) :
    Integrable (fun y ↦ K (x, y) * u y j) := by
  exact ((Lp.memLp u).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
    |>.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (hc.comp (continuous_const.prodMk continuous_id))
      (hasCompactSupport_entry_section hs x)

/-- The mixed-term candidate has compact support in both measurement
variables. Consumer: its Hilbert adjoint in the full normal identity
(`app:ch_background:prop:bg-frame`). -/
theorem hasCompactSupport_mixedEntry (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    HasCompactSupport (fixedMixedKernelEntry hR A i j) := by
  apply HasCompactSupport.intro
    ((JanetCartan.ContinuumRow.FixedCutoffs.physical hR 1).hasCompactSupport.isCompact.prod
      (JanetCartan.ContinuumRow.FixedCutoffs.physical hR 1).hasCompactSupport.isCompact)
  exact fun p hp ↦ fixedMixedKernelEntry_eq_zero_off_support hR A i j p hp

end KernelIdentity

/-- Absolute convergence of the final correction kernel on every L² input,
before operator identification (`app:ch_background:prop:bg-frame`). The
continuity premise is produced by the companion kernel regularity theorem. -/
theorem integrable_fixedNormalCorrectionKernel_apply (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hK : ∀ i j, Continuous (fixedNormalCorrectionKernelEntry hR A i j))
    (u : R²) (x : E) :
    Integrable (fun y ↦ fixedNormalCorrectionKernel hR A (x, y) (u y)) := by
  apply integrable_piLp_iff.mpr
  intro i
  change Integrable (fun y ↦ fixedNormalCorrectionKernel hR A (x, y) (u y) i)
  simp only [fixedNormalCorrectionKernel_apply]
  exact integrable_finsetSum Finset.univ fun j _ ↦
    KernelIdentity.integrable_entry_mul_coordinate (hK i j)
      (hasCompactSupport_fixedNormalCorrectionKernelEntry hR A i j) u j x

/-- The Bochner integral of the full correction agrees with its literal
matrix of scalar integrals. Consumer: assembly of the three normal terms in
`app:ch_background:prop:bg-frame`. -/
theorem integral_fixedNormalCorrectionKernel_apply_coordinate (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hK : ∀ i j, Continuous (fixedNormalCorrectionKernelEntry hR A i j))
    (u : R²) (x : E) (i : Fin n) :
    (∫ y, fixedNormalCorrectionKernel hR A (x, y) (u y)) i =
      ∑ j, ∫ y, fixedNormalCorrectionKernelEntry hR A i j (x, y) * u y j := by
  have he := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (integrable_fixedNormalCorrectionKernel_apply hR A hK u x)
  change (∫ y, fixedNormalCorrectionKernel hR A (x, y) (u y) i) =
    (∫ y, fixedNormalCorrectionKernel hR A (x, y) (u y)) i at he
  rw [← he]
  simp only [fixedNormalCorrectionKernel_apply]
  exact integral_finsetSum Finset.univ fun j _ ↦
    KernelIdentity.integrable_entry_mul_coordinate (hK i j)
      (hasCompactSupport_fixedNormalCorrectionKernelEntry hR A i j) u j x

end JanetCartan.ContinuumNormal.FrozenImageComparison
