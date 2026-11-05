module

public import JanetCartan.Iteration.PhysicalMean.GroupedInput

/-!
# Full grouped current fields use the same original adjoints and inverse

The literal individual native forward-adjoint field estimated in
IndividualSource is exactly the grouped original raw field. No different
inverse, principal amplitude or sample-independent replacement appears
(`app:ch_mean_pairs:eq:mean-current-canonical`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open PhysicalForwardMean PhysicalSamplingShells RawInputRealization RawInputPartition ContinuumRow PeriodicLocalL2

/-- The actual original individual adjoint is the original shell isometry of
its native realization. The identity is exact for arbitrary data and therefore
also for the prescribed SAME current inverse applied to a source. -/
theorem annularShellEquiv_nativeAdjoint_eq_original {n : ℕ} {β : Type*}
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (radius : β → ℝ) (A : Input n radius →L[ℝ] OutputL2 n)
    (R : Lp ℂ 2 (annularShellMeasure radius) →L[ℝ] OutputL2 n)
    (hR : A.comp ((annularShellEquiv (V := ℂ) radius).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) = R)
    (w : OutputL2 n) :
    annularShellEquiv radius (R.adjoint w) = A.adjoint w := by
  let e : Lp ℂ 2 (annularShellMeasure radius) ≃ₗᵢ[ℝ] Input n radius :=
    { toLinearEquiv := (annularShellEquiv (V := ℂ) radius).toLinearEquiv.restrictScalars ℝ
      norm_map' := (annularShellEquiv (V := ℂ) radius).norm_map }
  have he : (annularShellEquiv (V := ℂ) radius).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ =
      e.toContinuousLinearEquiv.toContinuousLinearMap := rfl
  rw [← hR, he, ContinuousLinearMap.adjoint_comp, e.adjoint_eq_symm, ContinuousLinearMap.comp_apply]
  exact e.apply_symm_apply _

/-- The grouped FULL original current field is precisely the whole-shell
`individualNativeInverseField` whose source-dependent lower jets have already
been derived from the current inverse. This is an identity before estimating
any shell or sample, so all cross-shell terms are retained by GroupedCross. -/
theorem groupedOriginalCurrentField_eq_individualNativeInverseField {n N J : ℕ} {ν : Type*}
    (φ : ν → RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (m : ν → RefinedIndex J × Euclidean (n-1) → ℝ)
    (G : ν → Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (hφ : ∀ i, Continuous (Function.uncurry (φ i)))
    (hm : ∀ i, Continuous (m i)) (hms : ∀ i, HasCompactSupport (m i))
    (hGc : ∀ i a c, Continuous (fun z : (RefinedIndex J × Euclidean (n-1)) × Euclidean n ↦
      G i a c z.1.1 z.1.2 z.2))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hGK : ∀ i a c j η, tsupport (G i a c j η) ⊆ K)
    (A : ν → Input n (refinedRadius (J := J)) →L[ℝ] OutputL2 n)
    (An : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hAn : ∀ i, (A i).comp
      ((annularShellEquiv (V := ℂ) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      transferOutputOperator (realQuadratureChannel (An i)))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u : OutputL2 n) (i : ν) :
    groupedAnnularForwardField (fun ij : ν × RefinedIndex J ↦ refinedRadius ij.2)
      (fun z ↦ φ z.1.1 (z.1.2,z.2))
      (fun z ↦ m z.1.1 (z.1.2,z.2)*Real.sqrt ‖z.2‖)
      (fun a c z y ↦ G z.1.1 a c z.1.2 z.2 y)
      (fun ij ↦ ((A ij.1).adjoint (Q₀ u)) ij.2) i =
      individualNativeInverseField (φ i) (m i) (G i) (An i) Q₀ u := by
  let t : TopologicalSpace (RefinedIndex J) := inferInstance
  let f : RefinedIndex J → ℝ := fun j ↦ ((Fintype.equivFin (RefinedIndex J) j).val : ℝ)
  have hf : Function.Injective f := by
    intro j k h
    apply (Fintype.equivFin (RefinedIndex J)).injective
    apply Fin.ext
    change ((Fintype.equivFin (RefinedIndex J) j).val : ℝ) =
      ((Fintype.equivFin (RefinedIndex J) k).val : ℝ) at h
    exact_mod_cast h
  let mt : MetricSpace (RefinedIndex J) := MetricSpace.induced f hf inferInstance
  have hmt : t = mt.toUniformSpace.toTopologicalSpace := by
    have ht : t = ⊥ := DiscreteTopology.eq_bot
    have hm' : mt.toUniformSpace.toTopologicalSpace = ⊥ := by
      let : MetricSpace (RefinedIndex J) := mt
      exact DiscreteTopology.eq_bot
    exact ht.trans hm'.symm
  let : MetricSpace (RefinedIndex J) := mt.replaceTopology hmt
  let v : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) := fun i ↦
    (transferOutputOperator (realQuadratureChannel (An i))).adjoint (Q₀ u)
  have hv (i : ν) : annularShellEquiv (refinedRadius (J := J)) (v i) = (A i).adjoint (Q₀ u) :=
    annularShellEquiv_nativeAdjoint_eq_original _ (A i) _ (hAn i) (Q₀ u)
  funext x
  have he := groupedAnnularForwardField_eq_wholeIntegral
    (fun ij : ν × RefinedIndex J ↦ refinedRadius ij.2) (fun z ↦ φ z.1.1 (z.1.2,z.2))
    (fun z ↦ m z.1.1 (z.1.2,z.2)*Real.sqrt ‖z.2‖) (fun a c z y ↦ G z.1.1 a c z.1.2 z.2 y)
    hφ (fun i ↦ (hm i).mul (continuous_snd.norm.sqrt)) (fun i ↦ (hms i).mul_right)
    (fun a c i ↦ hGc i a c) hK (fun a c z ↦ hGK z.1.1 a c z.1.2 z.2) v i x
  simp only [hv] at he
  exact he

end JanetCartan.PhysicalMean
