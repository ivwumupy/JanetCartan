module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AugmentedReference

/-!
# Radial choice of the frozen incidence covector

Only the representative of the selected direction is rescaled. The physical
coordinates, Hamilton family, angular direction and original measures are
unchanged. This permits the fixed sphere used by the supported global carrier
constructor to have radius at most `1/2` (`bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- At a frozen incidence point the physical output is exactly the selected
covector, not merely a comparable one (`app:ch_background:eq:bg-Psi`). -/
theorem frozenAugmentedChart_center {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0) :
    frozenAugmentedChart T (augmentedInputCenter T (z₀ := z₀) (k := k)) =
      ((0, 0, k), spectatorCenter z₀) := by
  have hi := FrozenIncidence.dispersion_incidence T hP hz₀ hinc
  have hc : (adaptedSliceCoordinates T).equiv k =
      (inner ℝ T.data.adapted.normal k,
        T.data.adapted.embedding.toContinuousLinearMap.adjoint k) := by
    change (physicalCoordinates T k).ofLp = _
    have he := congrArg (physicalCoordinates T) (T.data.adapted.covector_decomposition k)
    change physicalCoordinates T (adaptedSpacetime T.data.adapted
      (WithLp.toLp 2 (inner ℝ T.data.adapted.normal k,
        T.data.adapted.embedding.toContinuousLinearMap.adjoint k))) = physicalCoordinates T k at he
    rw [physicalCoordinates_adapted] at he
    exact congrArg WithLp.ofLp he.symm
  change ((0, 0, (adaptedSliceCoordinates T).equiv.symm
    (inner ℝ (gradient (dispersion T) (spatialCarrier T (spectatorCenter z₀, z₀ 0)))
      (T.data.adapted.embedding.toContinuousLinearMap.adjoint k),
      T.data.adapted.embedding.toContinuousLinearMap.adjoint k)), spectatorCenter z₀) = _
  have hz : spatialCarrier T (spectatorCenter z₀, z₀ 0) = T.reference.spatialPatch z₀ := by
    simp only [spatialCarrier, carrierParameters_spectatorCenter]
  rw [hz, ← hi, ← hc, ContinuousLinearEquiv.symm_apply_apply]

/-- Incidence is linear in the selected physical covector (`bg-Psi`). -/
theorem incidence_smul_direction (t : ℝ) (k ξ : Euclidean n) :
    incidence (t • k) ξ = t * incidence k ξ := by
  simp only [incidence, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Choose a small positive radial representative without losing the frozen
incidence derivative or either angular direction. All choices precede the
immersion (`app:ch_background:defn:bg-row`). -/
theorem exists_small_incidence_representative {z₀ : Euclidean 3}
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) :
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧ t • k ≠ 0 ∧
      incidence (t • k) (P.toFun z₀) = 0 ∧
      fderiv ℝ (fun z ↦ incidence (t • k) (P.toFun z)) z₀
        (EuclideanSpace.single 0 1) ≠ 0 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) := by
  let t := (1 / 4 : ℝ) / ‖k‖
  have ht : 0 < t := div_pos (by norm_num) (norm_pos_iff.mpr hk)
  have hdiff : DifferentiableAt ℝ (fun z ↦ incidence k (P.toFun z)) z₀ := by
    by_contra h
    rw [fderiv_zero_of_not_differentiableAt h, zero_apply] at hd
    exact hd rfl
  have he : (fun z ↦ incidence (t • k) (P.toFun z)) =
      fun z ↦ t * incidence k (P.toFun z) := by
    funext z
    exact incidence_smul_direction t k (P.toFun z)
  refine ⟨t, ht, ?_, smul_ne_zero ht.ne' hk, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hk)
  · rw [incidence_smul_direction, hinc, mul_zero]
  · rw [he, fderiv_const_mul hdiff, smul_apply, smul_eq_mul]
    exact mul_ne_zero ht.ne' hd
  · exact NormedSpace.normalize_smul_of_pos ht k
  · rw [map_smul]
    exact NormedSpace.normalize_smul_of_pos ht _

end JanetCartan.ContinuumRow.CanonicalConic
