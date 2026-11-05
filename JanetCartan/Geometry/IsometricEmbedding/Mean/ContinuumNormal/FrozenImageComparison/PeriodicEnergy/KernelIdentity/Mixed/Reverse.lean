module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Mixed.Forward

/-!
# The actual Hilbert adjoint of the frozen mixed composition

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, Fubini in the L²
pairing reverses and transposes the continuous compact mixed kernel. The
forward identity is proved for the actual operators, and Hilbert adjunction
then identifies `D B*` without any additional mixed-identity hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped RealInnerProductSpace
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

namespace KernelIdentity

private theorem integrable_matrixEntry_pairing {K : E × E → ℝ}
    (hc : Continuous K) (hs : HasCompactSupport K) (u v : R²) (i j : Fin n) :
    Integrable (fun p : E × E ↦ K p * u p.1 i * v p.2 j) (volume.prod volume) := by
  let S := Prod.fst '' tsupport K
  let T := Prod.snd '' tsupport K
  have hS : IsCompact S := hs.image continuous_fst
  have hT : IsCompact T := hs.image continuous_snd
  have hu := (Lp.memLp u).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hv := (Lp.memLp v).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
  have hui := (hu.locallyIntegrable (by norm_num)).integrableOn_isCompact hS
    |>.integrable_indicator hS.measurableSet
  have hvi := (hv.locallyIntegrable (by norm_num)).integrableOn_isCompact hT
    |>.integrable_indicator hT.measurableSet
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  apply ((hui.norm.const_mul C).mul_prod hvi.norm).mono'
  · exact (hc.aestronglyMeasurable.mul hu.aestronglyMeasurable.comp_fst).mul
      hv.aestronglyMeasurable.comp_snd
  · apply Filter.Eventually.of_forall
    rintro ⟨x, y⟩
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ T
      · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hC (x, y)) (norm_nonneg (u x i))) (norm_nonneg (v y j))
      · have hz : K (x, y) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hp ↦ hy ⟨(x, y), hp, rfl⟩)
        simp [hz, Set.indicator_of_notMem hy]
    · have hz : K (x, y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp ↦ hx ⟨(x, y), hp, rfl⟩)
      simp [hz, Set.indicator_of_notMem hx]

private theorem compactMatrix_adjoint_ae_integral
    (K : Fin n → Fin n → E × E → ℝ)
    (hc : ∀ i j, Continuous (K i j)) (hs : ∀ i j, HasCompactSupport (K i j))
    (T : R² →L[ℝ] R²)
    (hT : ∀ v, T v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ j, ∫ y, K i j (x, y) * v y j)) (u : R²) :
    T.adjoint u =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (fun j ↦ ∑ i, ∫ x, K i j (x, y) * u x i) := by
  let g : E → E := fun y ↦ WithLp.toLp 2 (fun j ↦ ∑ i, ∫ x, K i j (x, y) * u x i)
  have hg : MemLp g 2 := by
    apply memLp_piLp_iff.mpr
    intro j
    change MemLp (fun y ↦ ∑ i, ∫ x, K i j (x, y) * u x i) 2
    apply memLp_finsetSum Finset.univ
    intro i _
    exact memLp_scalarKernel_integral ((hc i j).comp continuous_swap)
      ((hs i j).comp_homeomorph (Homeomorph.prodComm E E)) u i
  have hge : hg.toLp g =ᵐ[volume] g := hg.coeFn_toLp
  have he : T.adjoint u = hg.toLp g := by
    apply ext_inner_left ℝ
    intro v
    have hp (i j : Fin n) := integrable_matrixEntry_pairing (hc i j) (hs i j) u v i j
    rw [T.adjoint_inner_right, L2.inner_def, L2.inner_def]
    calc
      (∫ x, inner ℝ (T v x) (u x)) =
          ∫ x, ∑ i, ∑ j, ∫ y, K i j (x, y) * u x i * v y j := by
        apply integral_congr_ae
        filter_upwards [hT v] with x hx
        rw [hx]
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ by ring
      _ = ∑ i, ∑ j, ∫ x, ∫ y, K i j (x, y) * u x i * v y j := by
        rw [integral_finsetSum Finset.univ
          (fun i _ ↦ integrable_finsetSum Finset.univ fun j _ ↦ (hp i j).integral_prod_left)]
        exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum Finset.univ
          (fun j _ ↦ (hp i j).integral_prod_left)
      _ = ∑ j, ∑ i, ∫ y, ∫ x, K i j (x, y) * u x i * v y j := by
        calc
          _ = ∑ i, ∑ j, ∫ y, ∫ x, K i j (x, y) * u x i * v y j := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact integral_integral_swap (hp i j)
          _ = _ := Finset.sum_comm
      _ = ∫ y, ∑ j, ∑ i, ∫ x, K i j (x, y) * u x i * v y j := by
        rw [integral_finsetSum Finset.univ
          (fun j _ ↦ integrable_finsetSum Finset.univ fun i _ ↦ (hp i j).integral_prod_right)]
        exact Finset.sum_congr rfl fun j _ ↦ (integral_finsetSum Finset.univ
          (fun i _ ↦ (hp i j).integral_prod_right)).symm
      _ = ∫ y, inner ℝ (v y) (hg.toLp g y) := by
        apply integral_congr_ae
        filter_upwards [hge] with y hy
        rw [hy]
        simp only [g, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
          Finset.sum_mul, integral_mul_const]
  rw [he]
  exact hge

end KernelIdentity

/-- Actual Hilbert adjunction of the proved forward mixed identity gives
the reversed, transposed kernel for `D B*`, on every real L² input
(`app:ch_background:prop:bg-frame`). -/
theorem fixedLatticeOperator_comp_euclideanAdjoint_ae_integral
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    fixedLatticeOperator hR hcell A ((fixedEuclideanChannel hR A).adjoint u)
      =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦
        ∑ j, ∫ y, fixedMixedKernelEntry hR A j i (y, x) * u y j) := by
  have he := KernelIdentity.compactMatrix_adjoint_ae_integral (fixedMixedKernelEntry hR A)
    (KernelIdentity.continuous_mixedEntry hR hcell A)
    (KernelIdentity.hasCompactSupport_mixedEntry hR A)
    ((fixedEuclideanChannel hR A).comp (fixedLatticeOperator hR hcell A).adjoint)
    (fixedEuclideanChannel_comp_latticeAdjoint_ae_integral hR hcell A) u
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply] using he

end JanetCartan.ContinuumNormal.FrozenImageComparison
