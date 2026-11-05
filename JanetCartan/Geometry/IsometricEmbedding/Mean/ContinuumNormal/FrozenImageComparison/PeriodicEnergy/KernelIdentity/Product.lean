module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Integrability

/-!
# The literal lattice product in the frozen normal

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the actual product
`D D*` integrates `fixedLatticeProductKernelEntry`. The Fubini majorant uses
the original measurement support and a compact source section. It applies
to every L² input, with no L¹ or smooth-test hypothesis on that input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- Absolute convergence of the double integral before computing `D D*`.
This is the Fubini obligation in `app:ch_background:prop:bg-frame` for the
actual lattice kernels and an arbitrary real L² datum. -/
theorem integrable_fixedLatticeProduct_weight (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (i j k : Fin n) (x : E) :
    Integrable (fun p : E × E ↦ fixedLatticeKernel hR A i k (x, p.2) *
      fixedLatticeKernel hR A j k p * u p.1 j) (volume.prod volume) := by
  let S := tsupport (FixedCutoffs.physical (n := n) hR 1)
  have hS : IsCompact S := (FixedCutoffs.physical hR 1).hasCompactSupport
  have hu := (Lp.memLp u).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
  have huc : Integrable (S.indicator (fun y ↦ u y j)) :=
    (hu.locallyIntegrable (by norm_num)).integrableOn_isCompact hS
      |>.integrable_indicator hS.measurableSet
  have hc := (contDiff_fixedLatticeKernel hR hcell A i k).continuous
  have hd := (contDiff_fixedLatticeKernel hR hcell A j k).continuous
  have hr : Integrable (fun z ↦ fixedLatticeKernel hR A i k (x, z)) :=
    (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (KernelIdentity.hasCompactSupport_entry_section
        (hasCompactSupport_fixedLatticeKernel hR A i k) x)
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_fixedLatticeKernel hR A j k).exists_bound_of_continuous hd
  apply ((huc.norm.const_mul C).mul_prod hr.norm).mono'
  · exact ((hc.comp (continuous_const.prodMk continuous_snd)).aestronglyMeasurable.mul
      hd.aestronglyMeasurable).mul hu.aestronglyMeasurable.comp_fst
  · apply Filter.Eventually.of_forall
    rintro ⟨y, z⟩
    by_cases hy : y ∈ S
    · simp only [Set.indicator_of_mem hy, norm_mul]
      calc
        ‖fixedLatticeKernel hR A i k (x, z)‖ * ‖fixedLatticeKernel hR A j k (y, z)‖ *
            ‖u y j‖ = ‖fixedLatticeKernel hR A j k (y, z)‖ * ‖u y j‖ *
              ‖fixedLatticeKernel hR A i k (x, z)‖ := by ring
        _ ≤ C * ‖u y j‖ * ‖fixedLatticeKernel hR A i k (x, z)‖ := by
          gcongr
          exact hC (y, z)
    · have hz : fixedLatticeKernel hR A j k (y, z) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp ↦
          hy ((tsupport_fixedLatticeKernel_subset hR A j k hp).1))
      simp [hz, Set.indicator_of_notMem hy]

/-- Fubini for one actual matrix contraction in `D D*`, keeping the common
source variable and the two literal lattice kernels
(`app:ch_background:prop:bg-frame`). -/
theorem integral_fixedLatticeProduct_contraction (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (i j k : Fin n) (x : E) :
    (∫ z, fixedLatticeKernel hR A i k (x, z) *
      ∫ y, fixedLatticeKernel hR A j k (y, z) * u y j) =
      ∫ y, (∫ z, fixedLatticeKernel hR A i k (x, z) *
        fixedLatticeKernel hR A j k (y, z)) * u y j := by
  calc
    _ = ∫ z, ∫ y, fixedLatticeKernel hR A i k (x, z) *
        fixedLatticeKernel hR A j k (y, z) * u y j := by
      simp only [integral_const_mul, mul_assoc]
    _ = ∫ y, ∫ z, fixedLatticeKernel hR A i k (x, z) *
        fixedLatticeKernel hR A j k (y, z) * u y j :=
      (integral_integral_swap (integrable_fixedLatticeProduct_weight
        hR hcell A u i j k x)).symm
    _ = _ := by simp only [integral_mul_const]

/-- The product-kernel entries act absolutely on every L² input, justifying
their finite matrix sums in the full normal identity
(`app:ch_background:prop:bg-frame`). -/
theorem integrable_fixedLatticeProductKernelEntry_mul_coordinate
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (i j : Fin n) (x : E) :
    Integrable (fun y ↦ fixedLatticeProductKernelEntry hR A i j (x, y) * u y j) := by
  simp only [fixedLatticeProductKernelEntry, Finset.sum_mul]
  apply integrable_finsetSum Finset.univ
  intro k _
  simpa only [integral_mul_const] using
    (integrable_fixedLatticeProduct_weight hR hcell A u i j k x).integral_prod_left

/-- The literal `D D*` term has the proposed product kernel on all real L².
This supplies the third term of the full correction in
`app:ch_background:prop:bg-frame`; the mixed terms are separate obligations. -/
theorem fixedLatticeOperator_normal_ae_integral
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    fixedLatticeOperator hR hcell A ((fixedLatticeOperator hR hcell A).adjoint u)
      =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦
        ∑ j, ∫ y, fixedLatticeProductKernelEntry hR A i j (x, y) * u y j) := by
  filter_upwards [fixedLatticeOperator_ae_integral hR hcell A
    ((fixedLatticeOperator hR hcell A).adjoint u)] with x hx
  rw [hx]
  ext i
  change (∑ k, ∫ z, fixedLatticeKernel hR A i k (x, z) *
    ((fixedLatticeOperator hR hcell A).adjoint u) z k) = _
  calc
    _ = ∑ k, ∫ z, fixedLatticeKernel hR A i k (x, z) *
        ∑ j, ∫ y, fixedLatticeKernel hR A j k (y, z) * u y j := by
      apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards [fixedLatticeOperator_adjoint_ae_integral hR hcell A u] with z hz
      rw [hz]
    _ = ∑ k, ∑ j, ∫ z, fixedLatticeKernel hR A i k (x, z) *
        ∫ y, fixedLatticeKernel hR A j k (y, z) * u y j := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [Finset.mul_sum]
      apply integral_finsetSum
      intro j _
      simpa only [integral_const_mul, mul_assoc] using
        (integrable_fixedLatticeProduct_weight hR hcell A u i j k x).integral_prod_right
    _ = ∑ j, ∑ k, ∫ y, (∫ z, fixedLatticeKernel hR A i k (x, z) *
        fixedLatticeKernel hR A j k (y, z)) * u y j := by
      simp_rw [integral_fixedLatticeProduct_contraction hR hcell A u]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [fixedLatticeProductKernelEntry, Finset.sum_mul]
      symm
      apply integral_finsetSum
      intro k _
      simpa only [integral_mul_const] using
        (integrable_fixedLatticeProduct_weight hR hcell A u i j k x).integral_prod_left

end JanetCartan.ContinuumNormal.FrozenImageComparison
