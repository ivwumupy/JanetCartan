module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.FrozenIncidence.Characteristic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Cover

/-!
# Actual frozen incidence transversality

The primitive reciprocal-normal incidence and its first-coordinate derivative
imply the dispersion incidence and its transversality. The normal determinant
partial is the actual positive gap retained by the same quantitative family.
The literal cover corollary supplies the inputs from `CoverData.IsValid`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.FrozenIncidence
open HamiltonPhase ActualCarriers ActualCarriers.FrozenPhaseReference
open ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Smoothness of the actual dispersion gradient needed for the triangular
chart in `app:ch_seed:prop:seed-phase-charts`. -/
theorem gradient_dispersion_smooth : ContDiffOn ℝ ∞ (gradient (dispersion T))
    (ball (covectorCenter T) (2 * T.family.radius)) := by
  exact (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    ((dispersion_smooth T).fderiv_of_isOpen isOpen_ball (by simp))

/-- The frozen velocity along the actual patch is smooth on the doubled
interior (`app:ch_seed:prop:seed-phase-charts`). -/
theorem patch_gradient_smooth {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ (fun z ↦ gradient (dispersion T) (T.reference.spatialPatch z))
      (parameterInterior (2 * P.radius)) :=
  (gradient_dispersion_smooth T).comp (T.reference.spatialPatch_smooth hP)
    (fun _ hz ↦ spatialPatch_mem_dispersion_ball T (fun i ↦ (hz i).le))

/-- Incidence implies the actual frozen dispersion relation, using the
positive adapted determinant gap and the reciprocal-normal multiplier
(`app:ch_seed:prop:seed-phase-charts`, first proof paragraph). -/
theorem dispersion_incidence {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z) = 0) :
    ⟪T.data.adapted.normal, k⟫_ℝ =
      ⟪gradient (dispersion T) (T.reference.spatialPatch z),
        T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ := by
  have hzC : z ∈ parameterCube P.radius := fun i ↦ (hz i).le
  have hzD := parameterCube_subset_doubledInterior hP.1 hzC
  have hd := determinant_incidence_eq T hzD k
  have hzero : fderiv ℝ cubeDeterminant (P.toFun z) k = 0 := by
    rw [CubeCarrier.determinant_differential (hP.2.2.2.2.1 z hzC).1
      (hP.2.2.2.2.1 z hzC).2.1]
    change _ * incidence k (P.toFun z) = 0
    rw [hinc, mul_zero]
  rw [hzero] at hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left
    (T.data.buffered_transverse_pos (fun i ↦ (hzD i).le)).ne')

/-- A nonzero incident direction has a nonzero tangential component in the
same adapted coordinates (`app:ch_seed:prop:seed-phase-charts`). -/
theorem tangential_direction_ne_zero {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z) = 0) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint k ≠ 0 := by
  intro he
  have hω := dispersion_incidence T hP hz hinc
  rw [he, inner_zero_right] at hω
  have hd := T.data.adapted.covector_decomposition k
  rw [he, hω, zero_smul, map_zero, add_zero] at hd
  exact hk hd.symm

/-- Primitive first-coordinate transversality transfers to the actual
pairing with the dispersion gradient. Differentiation of the determinant
normal factor contributes zero at incidence
(`app:ch_seed:prop:seed-phase-charts`, first proof paragraph). -/
theorem dispersion_incidence_transverse {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    fderiv ℝ (fun w ↦ ⟪gradient (dispersion T) (T.reference.spatialPatch w),
      T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ) z
      (EuclideanSpace.single 0 1) ≠ 0 := by
  have hzC : z ∈ parameterCube P.radius := fun i ↦ (hz i).le
  have hzD := parameterCube_subset_doubledInterior hP.1 hzC
  have hsimple := (frozenDeterminantIncidence_simple hP hz hinc hd).2
  let G : Euclidean 3 → ℝ := fun w ↦
    ⟪gradient (dispersion T) (T.reference.spatialPatch w),
      T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ
  let A : Euclidean 3 → ℝ := fun w ↦
    fderiv ℝ cubeDeterminant (P.toFun w) T.data.adapted.normal
  have hG : DifferentiableAt ℝ G z :=
    (((patch_gradient_smooth T hP).contDiffAt
      ((isOpen_parameterInterior _).mem_nhds hzD)).inner ℝ contDiffAt_const).differentiableAt
      (by simp)
  have hA : DifferentiableAt ℝ A z := by
    have heq : determinant (cubeStress n) = cubeDeterminant := funext determinant_cubeStress
    have hh := ((contDiff_fderiv_determinant (n := n)).contDiffAt.comp z
      ((contDiffAt_const (c := cubeStress n)).prodMk (hP.2.2.2.1.contDiffAt
        ((isOpen_parameterInterior _).mem_nhds hzD)))).clm_apply
      (contDiffAt_const (c := T.data.adapted.normal))
    simpa only [Function.comp_apply, heq] using hh.differentiableAt (by simp)
  have hline : HasDerivAt (incidenceParameter z) (EuclideanSpace.single 0 1) 0 := by
    change HasDerivAt (fun t : ℝ ↦ z + t • EuclideanSpace.single 0 1) _ 0
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).const_add z
  have hline0 : incidenceParameter z 0 = z := by simp [incidenceParameter]
  have hAG := (hA.hasFDerivAt.mul (hG.hasFDerivAt.const_sub ⟪T.data.adapted.normal, k⟫_ℝ))
  have he : (fun t ↦ frozenDeterminantIncidence P z (k, t)) =ᶠ[𝓝 0]
      (fun t ↦ A (incidenceParameter z t) *
        (⟪T.data.adapted.normal, k⟫_ℝ - G (incidenceParameter z t))) := by
    have hev : ∀ᶠ t in 𝓝 0, incidenceParameter z t ∈ parameterInterior (2 * P.radius) :=
      hline.continuousAt.preimage_mem_nhds (by
        simpa only [hline0] using (isOpen_parameterInterior _).mem_nhds hzD)
    filter_upwards [hev] with t ht
    have heq : determinant (cubeStress n) = cubeDeterminant := funext determinant_cubeStress
    simpa only [frozenDeterminantIncidence, heq, A, G] using determinant_incidence_eq T ht k
  have hAG' := (hAG.comp_hasDerivAt_of_eq (0 : ℝ) hline hline0.symm).congr_of_eventuallyEq he
  have hscalar := CharacteristicRoot.hasDerivAt_scalarSlice
    ((contDiffAt_frozenDeterminantIncidence hP z (k, 0)
      (by simpa only [hline0] using hzC)).differentiableAt (by simp))
  intro hzero
  apply hsimple
  rw [hscalar.unique hAG']
  have hGzero : ⟪T.data.adapted.normal, k⟫_ℝ - G z = 0 :=
    sub_eq_zero.mpr (dispersion_incidence T hP hz hinc)
  change fderiv ℝ G z (EuclideanSpace.single 0 1) = 0 at hzero
  simp [hGzero, hzero]

/-- The literal frozen cover supplies incidence and its nonzero derivative at
`D.roots b a k`. This uses no current detector-root continuation
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem cover_dispersion_incidence {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    (b : Fin D.chartCount) (a : Fin (D.patchCount b))
    (T : PatchQuantitativeFamily (D.patches b a) U hU)
    {k : Euclidean n} (hk : k ≠ 0) (hkD : k ∈ D.domain b) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint k ≠ 0 ∧
    ⟪T.data.adapted.normal, k⟫_ℝ =
      ⟪gradient (dispersion T) (T.reference.spatialPatch (D.roots b a k)),
        T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ ∧
    fderiv ℝ (fun w ↦ ⟪gradient (dispersion T) (T.reference.spatialPatch w),
      T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ) (D.roots b a k)
      (EuclideanSpace.single 0 1) ≠ 0 := by
  obtain ⟨hP, hsec⟩ := hD.2.2.2.2.1 b a
  have hz := (hsec.2.1 k hkD).1
  have hi := (hsec.2.1 k hkD).2.2.2
  have hd : fderiv ℝ (fun w ↦ incidence k ((D.patches b a).toFun w))
      (D.roots b a k) (EuclideanSpace.single 0 1) ≠ 0 := by
    exact abs_pos.mp (hD.1.trans_le (hsec.2.2 k hkD _ (fun i ↦ (hz i).le)))
  exact ⟨tangential_direction_ne_zero T hP hz hk hi,
    dispersion_incidence T hP hz hi, dispersion_incidence_transverse T hP hz hi hd⟩

end JanetCartan.FullPhaseCharts.FrozenIncidence
