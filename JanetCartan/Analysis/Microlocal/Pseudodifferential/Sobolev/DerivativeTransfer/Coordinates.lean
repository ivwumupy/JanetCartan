module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Amplitude

/-!
# Derivatives in the paired physical positions

Coordinate identifications for `app:ch_regular_base:eq:graph-derivative-transfer`.
The original full amplitude retains two independent physical positions.
-/

@[expose] public noncomputable section
open scoped ContDiff RealInnerProductSpace
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
/-- `app:ch_regular_base:eq:graph-derivative-transfer`: concatenation of the
physical positions as a continuous linear map. -/
def pairedPositionCLM :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (2*d)) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p ↦ pairedPosition p.1 p.2
    map_add' := by
      intro p q
      ext i
      by_cases hi : i.val < d <;> simp [pairedPosition, hi]
    map_smul' := by
      intro t p
      ext i
      by_cases hi : i.val < d <;> simp [pairedPosition, hi] }

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: The derivative of pairing in the output position. -/
theorem hasFDerivAt_pairedPosition_left (x y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun z ↦ pairedPosition z y)
      (pairedPositionCLM.comp (ContinuousLinearMap.inl ℝ _ _)) x := by
  convert! pairedPositionCLM.hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)) using 1

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: The output basis vector in paired coordinates. -/
theorem pairedPosition_single_left (i : Fin d) : pairedPosition (EuclideanSpace.single i 1) 0 =
    EuclideanSpace.single (physicalOutputIndex i) 1 := by
  ext j
  by_cases hj : j.val < d
  · simp [pairedPosition, hj, EuclideanSpace.single, physicalOutputIndex,
      Fin.ext_iff]
  · have hne : j ≠ physicalOutputIndex i := by
      intro h; subst j; exact hj i.isLt
    simp [pairedPosition, hj, EuclideanSpace.single, hne]
/-- `app:ch_regular_base:eq:graph-derivative-transfer`: The derivative of pairing in the source position. -/
theorem hasFDerivAt_pairedPosition_right (x y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun z ↦ pairedPosition x z)
      (pairedPositionCLM.comp (ContinuousLinearMap.inr ℝ _ _)) y := by
  convert! pairedPositionCLM.hasFDerivAt.comp y
    ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)) using 1

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: The source basis vector in paired coordinates. -/
theorem pairedPosition_single_right (i : Fin d) : pairedPosition 0 (EuclideanSpace.single i 1) =
    EuclideanSpace.single (physicalSourceIndex i) 1 := by
  ext j
  by_cases hj : j.val < d
  · have hne : j ≠ physicalSourceIndex i := by
      intro h; subst j; simp only [physicalSourceIndex] at hj; omega
    simp [pairedPosition, hj, EuclideanSpace.single, hne]
  · have he : (↑j - d = ↑i) ↔ (↑j = d + ↑i) := by omega
    simp [pairedPosition, hj, EuclideanSpace.single, physicalSourceIndex, Fin.ext_iff, he]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: Output differentiation of the complete paired amplitude. -/
theorem fderiv_pairedPosition_left_apply (b : EuclideanSpace ℝ (Fin (2*d)) → ℂ)
    (hb : Differentiable ℝ b) (x y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    fderiv ℝ (fun z ↦ b (pairedPosition z y)) x (EuclideanSpace.single i 1) =
      euclideanCoordinateDerivList [physicalOutputIndex i] b (pairedPosition x y) := by
  have h := ((hb _).hasFDerivAt.comp x (hasFDerivAt_pairedPosition_left x y)).fderiv
  convert! congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℂ ↦
    L (EuclideanSpace.single i 1)) h using 1
  change fderiv ℝ b (pairedPosition x y) (EuclideanSpace.single (physicalOutputIndex i) 1) =
    fderiv ℝ b (pairedPosition x y) (pairedPosition (EuclideanSpace.single i 1) 0)
  rw [pairedPosition_single_left]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: Source differentiation of the complete paired amplitude. -/
theorem fderiv_pairedPosition_right_apply (b : EuclideanSpace ℝ (Fin (2*d)) → ℂ)
    (hb : Differentiable ℝ b) (x y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    fderiv ℝ (fun z ↦ b (pairedPosition x z)) y (EuclideanSpace.single i 1) =
      euclideanCoordinateDerivList [physicalSourceIndex i] b (pairedPosition x y) := by
  have h := ((hb _).hasFDerivAt.comp y (hasFDerivAt_pairedPosition_right x y)).fderiv
  convert! congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℂ ↦
    L (EuclideanSpace.single i 1)) h using 1
  change fderiv ℝ b (pairedPosition x y) (EuclideanSpace.single (physicalSourceIndex i) 1) =
    fderiv ℝ b (pairedPosition x y) (pairedPosition 0 (EuclideanSpace.single i 1))
  rw [pairedPosition_single_right]
end JanetCartan.Pseudodifferential
