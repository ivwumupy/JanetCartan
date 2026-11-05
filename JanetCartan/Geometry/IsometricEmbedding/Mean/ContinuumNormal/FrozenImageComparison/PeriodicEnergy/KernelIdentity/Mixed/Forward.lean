module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Mixed.Convolution

/-!
# The forward frozen mixed composition

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the compact smooth
representative of the actual lattice adjoint permits the Euclidean channel's
Schwartz action on every L² input. Source differentiation and Fubini identify
the result with the explicit mixed kernel, retaining both source masks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E
local notation "S" => 𝓢(E, ℂ)

namespace KernelIdentity

private def latticeAdjointSchwartz (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (k : Fin n) : S :=
  ((latticeAdjoint_coordinate_regular hR hcell A u k).2.comp_left
    (g := fun r : ℝ ↦ (r : ℂ)) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (latticeAdjoint_coordinate_regular hR hcell A u k).1)

private theorem bessel_source_derivative (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (k a : Fin n) (x : E) :
    partialDeriv (imageBesselSchwartzCLM
      (SchwartzMap.smulLeftCLM ℂ (fun z ↦ (FixedCutoffs.physical hR 2 z : ℂ))
        (latticeAdjointSchwartz hR hcell A u k))) x a =
      ((∑ j, ∫ y, (∫ t : E, imageBesselKernel t *
        fderiv ℝ (fixedMixedSourceKernel hR A j k) (x - t, y)
          (EuclideanSpace.single a 1, 0)) * u y j : ℝ) : ℂ) := by
  let g : E → ℝ := fun z ↦ FixedCutoffs.physical hR 2 z *
    ∑ j, ∫ y, fixedLatticeKernel hR A j k (y, z) * u y j
  have hg : ContDiff ℝ ∞ g :=
    (FixedCutoffs.physical hR 2).contDiff.mul
      (latticeAdjoint_coordinate_regular hR hcell A u k).1
  have hgc : HasCompactSupport g := (FixedCutoffs.physical hR 2).hasCompactSupport.mul_right
  let w := SchwartzMap.smulLeftCLM ℂ (fun z ↦ (FixedCutoffs.physical hR 2 z : ℂ))
    (latticeAdjointSchwartz hR hcell A u k)
  have hχ : (fun z : E ↦ (FixedCutoffs.physical hR 2 z : ℂ)).HasTemperateGrowth :=
    ((FixedCutoffs.physical hR 2).hasCompactSupport.comp_left
      (g := fun r : ℝ ↦ (r : ℂ)) (by simp)).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp (FixedCutoffs.physical hR 2).contDiff)
  have hw : (w : E → ℂ) = fun z ↦ (g z : ℂ) := by
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply hχ]
    change (FixedCutoffs.physical hR 2 z : ℂ) * _ = _
    exact (Complex.ofReal_mul _ _).symm
  have hwc : HasCompactSupport (w : E → ℂ) := by
    rw [hw]
    exact hgc.comp_left (g := fun r : ℝ ↦ (r : ℂ)) (by simp)
  change partialDeriv (imageBesselSchwartzCLM w) x a = _
  rw [partialDeriv_imageBesselSchwartz_compact w hwc]
  have hd (z : E) : fderiv ℝ (w : E → ℂ) z (EuclideanSpace.single a 1) =
      ((∑ j, ∫ y, fderiv ℝ (fixedMixedSourceKernel hR A j k) (z, y)
        (EuclideanSpace.single a 1, 0) * u y j : ℝ) : ℂ) := by
    have he := Complex.ofRealCLM.hasFDerivAt.comp z
      (hg.differentiable (by simp) z).hasFDerivAt
    change HasFDerivAt (fun z ↦ (g z : ℂ)) _ z at he
    rw [hw, he.fderiv]
    change (fderiv ℝ g z (EuclideanSpace.single a 1) : ℂ) = _
    rw [fderiv_source_mul_latticeAdjoint_integral hR hcell A u k a z]
  simp_rw [hd, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  apply congrArg (fun r : ℝ ↦ (r : ℂ))
  simp only [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ ↦
      integral_fixedMixedSource_bessel_contraction hR hcell A u j k a x
  · intro j _
    simpa only [integral_const_mul, mul_assoc] using
      (integrable_fixedMixedSource_bessel_weight hR hcell A u j k a x).integral_prod_left

private theorem mixedEntry_integral_expand (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (i j : Fin n) (x : E) :
    (∫ y, fixedMixedKernelEntry hR A i j (x, y) * u y j) =
      FixedCutoffs.physical hR 1 x * ∑ a, ∑ k, A a i k *
        ∫ y, (∫ t : E, imageBesselKernel t *
          fderiv ℝ (fixedMixedSourceKernel hR A j k) (x - t, y)
            (EuclideanSpace.single a 1, 0)) * u y j := by
  have hi (a k : Fin n) : Integrable (fun y ↦ A a i k *
      ((∫ t : E, imageBesselKernel t * fderiv ℝ (fixedMixedSourceKernel hR A j k)
        (x - t, y) (EuclideanSpace.single a 1, 0)) * u y j)) := by
    apply Integrable.const_mul
    simpa only [integral_mul_const] using
      (integrable_fixedMixedSource_bessel_weight hR hcell A u j k a x).integral_prod_right
  simp only [fixedMixedKernelEntry, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum Finset.univ
    (fun a _ ↦ integrable_finsetSum Finset.univ fun k _ ↦ hi a k)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum Finset.univ (fun k _ ↦ hi a k)]
  simp only [integral_const_mul]

private theorem channelSchwartz_latticeAdjoint (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (i : Fin n) (x : E) :
    channelSchwartz (fun _ : E ↦ A) (fun _ ↦ 0)
      (FixedCutoffs.physical hR 2) (FixedCutoffs.physical hR 1)
      (latticeAdjointSchwartz hR hcell A u) i x =
      ((∑ j, ∫ y, fixedMixedKernelEntry hR A i j (x, y) * u y j : ℝ) : ℂ) := by
  change maskedCoefficientSchwartzCLM (fun _ : E ↦ A) (fun _ ↦ 0)
    (FixedCutoffs.physical hR 1) _ i x = _
  rw [maskedCoefficientSchwartzCLM_apply (fun _ : E ↦ A) (fun _ ↦ 0)
    (FixedCutoffs.physical hR 1)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 1).contDiff (FixedCutoffs.physical hR 1).hasCompactSupport]
  simp only [coefficientOperator, Matrix.zero_apply, Complex.ofReal_zero,
    zero_mul, Finset.sum_const_zero, add_zero]
  change (FixedCutoffs.physical hR 1 x : ℂ) *
    (∑ a, ∑ k, (A a i k : ℂ) * partialDeriv (imageBesselSchwartzCLM
      (SchwartzMap.smulLeftCLM ℂ (fun z ↦ (FixedCutoffs.physical hR 2 z : ℂ))
        (latticeAdjointSchwartz hR hcell A u k))) x a) = _
  simp_rw [bessel_source_derivative hR hcell A u, mixedEntry_integral_expand hR hcell A u]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end KernelIdentity

/-- The actual forward mixed composition `B D*` has its explicit mixed
kernel on every real L² input. Its source derivative acts on both original
source masks, and the Euclidean Bessel kernel remains undifferentiated
(`app:ch_background:prop:bg-frame`). -/
theorem fixedEuclideanChannel_comp_latticeAdjoint_ae_integral
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    fixedEuclideanChannel hR A ((fixedLatticeOperator hR hcell A).adjoint u)
      =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦
        ∑ j, ∫ y, fixedMixedKernelEntry hR A i j (x, y) * u y j) := by
  let v := KernelIdentity.latticeAdjointSchwartz hR hcell A u
  let f := (fixedLatticeOperator hR hcell A).adjoint u
  have hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ v i x) := by
    filter_upwards [euclideanComplexInclusion.coeFn_compLpL f,
      fixedLatticeOperator_adjoint_ae_integral hR hcell A u] with x hx hy
    change l2ComplexInclusion volume f x = euclideanComplexInclusion (f x) at hx
    rw [hx, hy]
    rfl
  have hB := euclideanChannel_schwartz_action (fun _ : E ↦ A) (fun _ ↦ 0)
    (FixedCutoffs.physical hR 2) (FixedCutoffs.physical hR 1)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 2).contDiff (FixedCutoffs.physical hR 2).hasCompactSupport
    (FixedCutoffs.physical hR 1).contDiff (FixedCutoffs.physical hR 1).hasCompactSupport v f hf
  filter_upwards [hB, euclideanComplexInclusion.coeFn_compLpL
    (fixedEuclideanChannel hR A f)] with x hx hy
  change l2ComplexInclusion volume (fixedEuclideanChannel hR A f) x =
    euclideanComplexInclusion (fixedEuclideanChannel hR A f x) at hy
  change l2ComplexInclusion volume (fixedEuclideanChannel hR A f) x = _ at hx
  rw [hy] at hx
  ext i
  apply Complex.ofReal_injective
  exact (congrArg (fun w : EuclideanSpace ℂ (Fin n) ↦ w i) hx).trans
    (KernelIdentity.channelSchwartz_latticeAdjoint hR hcell A u i x)

end JanetCartan.ContinuumNormal.FrozenImageComparison
