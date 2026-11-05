module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalCoordinates
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilLeading
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced.Formula
public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Operator

/-!
# The physical reduced operator in characteristic coordinates

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, identify
`adaptedPencilApply` on the constructed coordinate split with the original
physical pencil action. For a symmetric stress frame and the actual negative
Christoffel contraction, this is exactly `NullTransport.reducedOperator`.
The complex extension uses the same real coefficients and the physical phase,
without any `P/i` renormalization. Its principal symbol is the original pencil
at the transported covector, by the proved phase differential and duality.

The consumer is `PhysicalKernel`, which closes the local two-term differential
identity for the actually constructed leading and correction columns. These
identifications do not claim a bounded integral or a complete residual estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped InnerProductSpace ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic

open ActualCarriers

variable {n d N : ℕ}

/-- The original real pencil action, retaining its full zeroth-order matrix.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def physicalPencilApply (Q : Euclidean n → Fin n → MetricTensor n)
    (B : Euclidean n → MetricTensor n) (u : Euclidean n → Fin n → ℝ)
    (x : Euclidean n) : Fin n → ℝ :=
  (∑ a, pencil (Q x) (EuclideanSpace.single a 1) *ᵥ partialDeriv u x a) + B x *ᵥ u x

/-- For the actual symmetric frame and Christoffel coefficient, the physical action is the
published reduced strain operator.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem physicalPencilApply_eq_reducedOperator
    (G : Euclidean n → Euclidean N) (Q : Euclidean n → Fin n → MetricTensor n)
    {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hu : DifferentiableAt ℝ u x) :
    physicalPencilApply Q (fun y ↦ GeometricProfile.reducedZerothCoefficient G (Q y) y)
        (fun y j ↦ u y j) x = NullTransport.reducedOperator G Q u x := by
  have hdu (a j : Fin n) : partialDeriv (fun y k ↦ u y k) x a j =
      partialDeriv (fun y ↦ u y j) x a := by
    have hf : DifferentiableAt ℝ (fun y k ↦ u y k) x :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).differentiableAt.comp x hu
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single a 1))
      (((ContinuousLinearMap.proj j).hasFDerivAt.comp x hf.hasFDerivAt).fderiv.symm)
  ext i
  rw [GeometricProfile.reducedOperator_eq_coefficients G Q u x hQ i]
  simp only [physicalPencilApply, Pi.add_apply, Finset.sum_apply, mulVec, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  rw [hdu]
  congr 1
  simp [pencil, NullTransport.principalCoefficient, (hQ i).apply j a]

/-- The original physical operator on a fixed-source slice is exactly the adapted action used to
construct the signed transport.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem physicalPencilApply_slice (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    {u : TwoTimePoint (Euclidean d) → Fin (d + 1) → ℝ}
    {q : TwoTimePoint (Euclidean d)} (hu : DifferentiableAt ℝ u q) :
    physicalPencilApply Q B (u ∘ physicalSlice (coordinateSplit i) q.2.1 q.2.2.2)
      ((coordinateSplit i).symm (q.1, q.2.2.1)) =
      adaptedPencilApply (coordinateSplit i) Q B u q := by
  let x := (coordinateSplit i).symm (q.1, q.2.2.1)
  have hu' : HasFDerivAt u (fderiv ℝ u q)
      (physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 x) := by
    simpa only [x, physicalSlice_at] using hu.hasFDerivAt
  have hd := hu'.comp x
    (hasFDerivAt_physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 x)
  have hpart (a : Fin (d + 1)) :
      partialDeriv (u ∘ physicalSlice (coordinateSplit i) q.2.1 q.2.2.2) x a =
        fderiv ℝ u q (physicalSliceDerivative (coordinateSplit i) (EuclideanSpace.single a 1)) := by
    rw [partialDeriv, hd.fderiv]
    rfl
  change (∑ a, pencil (Q x) (EuclideanSpace.single a 1) *ᵥ
    partialDeriv (u ∘ physicalSlice (coordinateSplit i) q.2.1 q.2.2.2) x a) + _ = _
  rw [← Fin.add_sum_removeNth i]
  simp only [Fin.removeNth, hpart, physicalSliceDerivative_apply, coordinateSplit_single_time,
    coordinateSplit_single_space, adaptedPencilApply, adaptedPencilCoefficient,
    coordinateSplit_symm_time, coordinateSplit_symm_space, Function.comp_apply, physicalSlice_at]
  rfl

/-- The literal complex extension of each real principal coefficient, for the physical operator P.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def complexPencilCoefficient (Q : Euclidean n → Fin n → MetricTensor n)
    (x : Euclidean n) (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ((pencil (Q x) (EuclideanSpace.single a 1)).map Complex.ofReal).mulVecLin

/-- The literal complex extension of the complete real zeroth-order matrix.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def complexPencilZeroth (B : Euclidean n → MetricTensor n)
    (x : Euclidean n) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ((B x).map Complex.ofReal).mulVecLin

/-- The complex physical operator agrees with the original real action on real columns.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem firstOrderApply_complexPencil_real
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    {u : Euclidean n → Fin n → ℝ} {x : Euclidean n} (hu : DifferentiableAt ℝ u x) :
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (fun y j ↦ (u y j : ℂ)) x = fun j ↦ (physicalPencilApply Q B u x j : ℂ) := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)
  have hd (a : Fin n) : partialDeriv (fun y j ↦ (u y j : ℂ)) x a =
      fun j ↦ (partialDeriv u x a j : ℂ) := by
    change fderiv ℝ (L ∘ u) x _ = _
    rw [(L.hasFDerivAt.comp x hu.hasFDerivAt).fderiv]
    rfl
  ext j
  simp [WKB.firstOrderApply, complexPencilCoefficient, complexPencilZeroth,
    mulVec, dotProduct, hd, physicalPencilApply]

/-- The complex physical principal symbol is the original pencil at the actual phase gradient.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem principalSymbol_complexPencil
    (Q : Euclidean n → Fin n → MetricTensor n) (φ : Euclidean n → ℝ)
    (x : Euclidean n) (ξ : Euclidean n)
    (hξ : ∀ a, partialDeriv φ x a = ξ a) :
    WKB.principalSymbol (complexPencilCoefficient Q) φ x =
      ((pencil (Q x) ξ).map Complex.ofReal).mulVecLin := by
  have hp : pencil (Q x) ξ = ∑ a, ξ a • pencil (Q x) (EuclideanSpace.single a 1) := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, pencilContinuousLinearMap_apply] using
      (congrArg (pencilContinuousLinearMap (Q x))
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr ξ)).symm
  apply LinearMap.ext
  intro u
  funext j
  simp only [WKB.principalSymbol, LinearMap.sum_apply, LinearMap.smul_apply,
    complexPencilCoefficient, Matrix.mulVecLin_apply, hξ, hp, Matrix.map_apply,
    mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_apply, Pi.smul_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The physical phase gradient is precisely the transported root covector, with the initial
time and covector held fixed.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem partialDeriv_twoTimePhase_physicalSlice
    (i : Fin (d + 1)) (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {q : TwoTimePoint (Euclidean d)}
    (hd : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hclock : (twoTimeState Φ (C.symm q)).1 = q.1)
    (hy : (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) (a : Fin (d + 1)) :
    partialDeriv (twoTimePhase C ∘ physicalSlice (coordinateSplit i) q.2.1 q.2.2.2)
      ((coordinateSplit i).symm (q.1, q.2.2.1)) a =
      (coordinateSplit i).symm
        (h (twoTimeState Φ (C.symm q)), (twoTimeState Φ (C.symm q)).2.2) a := by
  have hd' : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q)
      (physicalSlice (coordinateSplit i) q.2.1 q.2.2.2
        ((coordinateSplit i).symm (q.1, q.2.2.1))) := by
    simpa only [physicalSlice_at] using hd
  have hc := hd'.comp ((coordinateSplit i).symm (q.1, q.2.2.1))
    (hasFDerivAt_physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 _)
  rw [partialDeriv, hc.fderiv, ContinuousLinearMap.comp_apply, physicalSliceDerivative_apply]
  have hw : h (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) =
      h (twoTimeState Φ (C.symm q)) := by rw [← hclock, ← hy]
  rw [show twoTimePhaseDifferential h Φ C q
      (((coordinateSplit i) (EuclideanSpace.single a 1)).1,
        (0, (((coordinateSplit i) (EuclideanSpace.single a 1)).2, 0))) =
      h (twoTimeState Φ (C.symm q)) * ((coordinateSplit i) (EuclideanSpace.single a 1)).1 +
      ⟪(twoTimeState Φ (C.symm q)).2.2,
        ((coordinateSplit i) (EuclideanSpace.single a 1)).2⟫_ℝ by
        simp [twoTimePhaseDifferential, hw]]
  rw [← coordinateSplit_covector_pairing i
    (h (twoTimeState Φ (C.symm q)), (twoTimeState Φ (C.symm q)).2.2)]
  simp [EuclideanSpace.inner_single_right]

end JanetCartan.RegularSector.Characteristic
