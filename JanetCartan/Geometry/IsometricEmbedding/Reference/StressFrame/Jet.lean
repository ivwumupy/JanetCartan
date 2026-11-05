module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.InverseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.JetComposition

/-!
# The second-jet coefficient of the projected stress frame

The rational finite-dimensional formula in `app:ch_seed:setup:seed-current`.
Both inversions are retained separately. Smoothness is asserted only where
both operators are units, as required for `app:ch_seed:eq:seed-frame-tame`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius JanetCartan.StressFrame

namespace JanetCartan.ProjectedStressFrame

/-- The first and second differentials used in `app:ch_seed:eq:seed-frame-tame`.
The second component is curried, with the differentiating direction first. -/
abbrev StressJet (n N : ℕ) :=
  (Euclidean n →L[ℝ] Euclidean N) ×
    (Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean N)

/-- The actual second jet in `app:ch_seed:eq:seed-frame-tame`. -/
def stressJet {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    StressJet n N := (fderiv ℝ F x, fderiv ℝ (fderiv ℝ F) x)

/-- The metric operator of a jet (`app:ch_seed:setup:seed-current`). -/
def jetMetric {n N : ℕ} (J : StressJet n N) : Euclidean n →L[ℝ] Euclidean n :=
  J.1.adjoint.comp J.1

/-- The inverse-Gram tangent projection formula on jets
(`app:ch_seed:setup:seed-current`). -/
def jetTangent {n N : ℕ} (J : StressJet n N) : Euclidean N →L[ℝ] Euclidean N :=
  J.1.comp ((Ring.inverse (jetMetric J)).comp J.1.adjoint)

/-- The projected Hessian of a jet (`app:ch_seed:setup:seed-current`). -/
def jetSecondForm {n N : ℕ} (J : StressJet n N) (i j : Fin n) : Euclidean N :=
  (ContinuousLinearMap.id ℝ (Euclidean N) - jetTangent J)
    (J.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

/-- The second-form contraction on the fixed Frobenius tensor space
(`app:ch_seed:setup:seed-current`). -/
def jetNormalMap {n N : ℕ} (J : StressJet n N) : MetricTensor n →L[ℝ] Euclidean N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H ↦ ∑ i, ∑ j, H i j • jetSecondForm J i j
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }

/-- The ambient operator `BB* + P_tan` on jets
(`app:ch_seed:setup:seed-current`). -/
def jetAmbient {n N : ℕ} (J : StressJet n N) : Euclidean N →L[ℝ] Euclidean N :=
  (jetNormalMap J).comp (jetNormalMap J).adjoint + jetTangent J

/-- The rational projected-stress coefficient of a fixed tensor
(`app:ch_seed:setup:seed-current`). -/
def jetStress {n N : ℕ} (Q : MetricTensor n) (J : StressJet n N) : MetricTensor n :=
  Q - (jetNormalMap J).adjoint (Ring.inverse (jetAmbient J) (jetNormalMap J Q))

/-- The metric coefficient is smooth (`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiff_jetMetric {n N : ℕ} : ContDiff ℝ ∞ (@jetMetric n N) := by
  exact ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclidean n)
    (F := Euclidean N)).toContinuousLinearEquiv.contDiff.comp
    contDiff_fst).clm_comp contDiff_fst

/-- Inverting the metric costs no additional jet order
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiffAt_jetTangent {n N : ℕ} {J : StressJet n N}
    (hg : IsUnit (jetMetric J)) : ContDiffAt ℝ ∞ (@jetTangent n N) J := by
  have hi : ContDiffAt ℝ ∞ Ring.inverse (jetMetric J) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hg.unit
  exact contDiffAt_fst.clm_comp ((hi.comp J contDiff_jetMetric.contDiffAt).clm_comp
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.contDiff.contDiffAt.comp J
      contDiffAt_fst))

/-- The projected Hessian is a smooth coefficient of the second jet
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiffAt_jetSecondForm {n N : ℕ} {J : StressJet n N}
    (hg : IsUnit (jetMetric J)) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun U : StressJet n N ↦ jetSecondForm U i j) J := by
  exact (contDiffAt_const.sub (contDiffAt_jetTangent hg)).clm_apply
    ((contDiffAt_snd.clm_apply contDiffAt_const).clm_apply contDiffAt_const)

/-- The second-form contraction is smooth in the fixed operator space
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiffAt_jetNormalMap {n N : ℕ} {J : StressJet n N}
    (hg : IsUnit (jetMetric J)) : ContDiffAt ℝ ∞ (@jetNormalMap n N) J := by
  rw [ContDiffAt, contDiffWithinAt_clm_apply]
  intro H
  change ContDiffWithinAt ℝ ∞ (fun U ↦ ∑ i, ∑ j, H i j • jetSecondForm U i j) Set.univ J
  exact (ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j _ ↦
    (contDiffAt_jetSecondForm hg i j).const_smul (H i j)).contDiffWithinAt

set_option maxHeartbeats 800000 in
/-- The ambient inverse argument is smooth on the metric unit locus
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiffAt_jetAmbient {n N : ℕ} {J : StressJet n N}
    (hg : IsUnit (jetMetric J)) : ContDiffAt ℝ ∞ (@jetAmbient n N) J := by
  have hb := contDiffAt_jetNormalMap hg
  exact (hb.clm_comp
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := MetricTensor n)
      (F := Euclidean N)).toContinuousLinearEquiv.contDiff.contDiffAt.comp J hb)).add
    (contDiffAt_jetTangent hg)

/-- The full rational coefficient is smooth at every jet satisfying the two
separate invertibility requirements (`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiffAt_jetStress {n N : ℕ} {J : StressJet n N}
    (hg : IsUnit (jetMetric J)) (hA : IsUnit (jetAmbient J)) (Q : MetricTensor n) :
    ContDiffAt ℝ ∞ (jetStress Q) J := by
  have hb := contDiffAt_jetNormalMap hg
  have hi : ContDiffAt ℝ ∞ Ring.inverse (jetAmbient J) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hA.unit
  exact contDiffAt_const.sub
    (((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := MetricTensor n)
      (F := Euclidean N)).toContinuousLinearEquiv.contDiff.contDiffAt.comp J hb).clm_apply
      ((hi.comp J (contDiffAt_jetAmbient hg)).clm_apply (hb.clm_apply contDiffAt_const)))

/-- The actual jet of a smooth map is smooth
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiff_stressJet {n N : ℕ} {F : Euclidean n → Euclidean N}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (stressJet F) := by
  have hd := hF.fderiv_right (show ∞ + 1 ≤ ∞ by simp)
  exact hd.prodMk (hd.fderiv_right (by simp))

/-- Local smoothness of the second jet on the manuscript's open working domain
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem contDiffOn_stressJet {n N : ℕ} {F : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) :
    ContDiffOn ℝ ∞ (stressJet F) s := by
  have hd := hF.fderiv_of_isOpen hs (show ∞ + 1 ≤ ∞ by simp)
  exact hd.prodMk (hd.fderiv_of_isOpen hs (by simp))

end JanetCartan.ProjectedStressFrame
