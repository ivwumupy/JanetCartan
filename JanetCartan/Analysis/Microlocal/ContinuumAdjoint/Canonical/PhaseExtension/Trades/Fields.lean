module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Basic

/-!
# Smooth rectangular derivative fields for the extended position

These are the `hL`, `hV`, and derivative-trade inputs of
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
The parent must supply global smoothness and instantiate the uniform positive
`TransverseGap`, whose actual producer is `jc-adjoint-phase-extension-gap`.
No inverse identity is assumed.

Source: `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow

variable {n : ℕ}
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}

/-- The transpose matrix represents the full spatial derivative. This algebraic
identity feeds the right-inverse argument in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem spatialMatrix_transpose_mulVec (z : CarrierParameter) (x v : Euclidean n) :
    (spatialMatrix Y z x)ᵀ *ᵥ (fun i ↦ v i) =
      (fun j ↦ (fderiv ℝ (fun y ↦ Y (y, z)) x v) j) := by
  funext j
  let L := (EuclideanSpace.proj j).comp (fderiv ℝ (fun y ↦ Y (y, z)) x)
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
  simpa [L, Matrix.mulVec, dotProduct, spatialMatrix, map_sum, map_smul,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, mul_comm] using h

/-- The actual Gram formula is a right inverse to `D_x Y`; this proves the
initial trade in `app:ch_background:eq:bg-derivative-trade`. -/
theorem fderiv_spatial_initialField {δ : ℝ} (hδ : 0 < δ)
    {z : CarrierParameter} {x : Euclidean n}
    (hgap : TransverseGap δ (spatialMatrix Y z x)) (h : Euclidean (n - 1)) :
    fderiv ℝ (fun y ↦ Y (y, z)) x (initialField Y z x h) = h := by
  have ht : (spatialMatrix Y z x)ᵀ * (transverseLeftInverse (spatialMatrix Y z x))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, transverseLeftInverse_mul hδ hgap, Matrix.transpose_one]
  apply PiLp.ext
  intro j
  have he := spatialMatrix_transpose_mulVec (Y := Y) z x (initialField Y z x h)
  rw [initialField, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, ht, Matrix.one_mulVec] at he
  exact (congrFun he j).symm

/-- Differentiate the scalar phase in an arbitrary spatial direction, for the
exact endpoint identities of `app:ch_background:eq:bg-derivative-trade`. -/
theorem fderiv_phase_spatial {z : CarrierParameter} {x : Euclidean n}
    (hY : DifferentiableAt ℝ (fun y ↦ Y (y, z)) x)
    (η : Euclidean (n - 1)) (v : Euclidean n) :
    fderiv ℝ (fun y ↦ phase Y z y η) x v =
      inner ℝ (fderiv ℝ (fun y ↦ Y (y, z)) x v) η := by
  simpa [phase]
    using fderiv_inner_apply ℝ hY (differentiableAt_const η) v

/-- The EXACT initial derivative identity consumed by the scalar transport
endpoint (`app:ch_background:eq:bg-derivative-trade`). -/
theorem initialField_trade (hY : ContDiff ℝ ∞ Y) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ z x, TransverseGap δ (spatialMatrix Y z x))
    (z : CarrierParameter) (x : Euclidean n) (η h : Euclidean (n - 1)) :
    inner ℝ h η = fderiv ℝ (fun y ↦ phase Y z y η) x (initialField Y z x h) := by
  rw [fderiv_phase_spatial
    ((hY.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x),
    fderiv_spatial_initialField hδ (hgap z x)]

/-- The EXACT full-carrier derivative identity consumed by the scalar transport
endpoint. No original carrier direction is dropped
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem carrierField_trade (hY : ContDiff ℝ ∞ Y) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ z x, TransverseGap δ (spatialMatrix Y z x))
    (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n - 1))
    (h : CarrierParameter) :
    fderiv ℝ (fun w ↦ phase Y w x η) z h =
      fderiv ℝ (fun y ↦ phase Y z y η) x (carrierField Y z x h) := by
  have hz : DifferentiableAt ℝ (fun w ↦ Y (x, w)) z :=
    (hY.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z
  have he := fderiv_inner_apply ℝ hz (differentiableAt_const η) h
  simp only [fderiv_const_apply, _root_.zero_apply, inner_zero_right, zero_add] at he
  exact he.trans (initialField_trade hY hδ hgap z x η _)

/-- Joint smoothness of the actual spatial matrix supplied to the rational
inverse operation (`app:ch_background:eq:bg-derivative-trade`). -/
theorem spatialMatrix_contDiff (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ spatialMatrix Y p.1 p.2) := by
  let L : (Euclidean n →L[ℝ] Euclidean (n - 1)) →ₗ[ℝ] TransverseMatrix n :=
    { toFun := fun D i j ↦ (D (EuclideanSpace.single i 1)) j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hy : ContDiff ℝ ∞
      (fun q : (CarrierParameter × Euclidean n) × Euclidean n ↦ Y (q.2, q.1.1)) :=
    hY.comp (contDiff_snd.prodMk contDiff_fst.fst)
  exact L.toContinuousLinearMap.contDiff.comp (hy.fderiv contDiff_snd (by simp))

private theorem initialField_contDiff_apply (hY : ContDiff ℝ ∞ Y)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ z x, TransverseGap δ (spatialMatrix Y z x))
    {g : CarrierParameter × Euclidean n → Euclidean (n - 1)} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ initialField Y p.1 p.2 (g p)) := by
  have hL : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦
      transverseLeftInverse (spatialMatrix Y p.1 p.2)) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    exact (contDiffAt_transverseLeftInverse hδ (hgap p.1 p.2)).comp p
      (spatialMatrix_contDiff hY).contDiffAt
  apply (contDiff_piLp 2).mpr
  intro i
  change ContDiff ℝ ∞ (fun p ↦ ∑ j, transverseLeftInverse (spatialMatrix Y p.1 p.2) j i * g p j)
  apply ContDiff.sum
  intro j _
  exact ((Matrix.entryLinearMap ℝ ℝ j i).toContinuousLinearMap.contDiff.comp hL).mul
    ((contDiff_piLp 2).mp hg j)

/-- Global smoothness for each initial direction, in the argument order of `hL`
of the scalar transport endpoint (`app:ch_background:eq:bg-derivative-trade`). -/
theorem initialField_contDiff (hY : ContDiff ℝ ∞ Y) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ z x, TransverseGap δ (spatialMatrix Y z x)) (h : Euclidean (n - 1)) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ initialField Y p.1 p.2 h) :=
  initialField_contDiff_apply hY hδ hgap contDiff_const

/-- Global smoothness for each full carrier direction, in the argument order of
`hV` of the scalar transport endpoint
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem carrierField_contDiff (hY : ContDiff ℝ ∞ Y) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ z x, TransverseGap δ (spatialMatrix Y z x)) (h : CarrierParameter) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ carrierField Y p.1 p.2 h) := by
  have hy : ContDiff ℝ ∞
      (fun q : (CarrierParameter × Euclidean n) × CarrierParameter ↦ Y (q.1.2, q.2)) :=
    hY.comp (contDiff_fst.snd.prodMk contDiff_snd)
  exact initialField_contDiff_apply hY hδ hgap
    (hy.fderiv_apply contDiff_fst contDiff_const (by simp))

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
