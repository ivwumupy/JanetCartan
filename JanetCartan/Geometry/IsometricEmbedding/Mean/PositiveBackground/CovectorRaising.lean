module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Christoffel

/-!
# Covector raising for the transported positive background

The geometric part of `app:ch_background:eq:bg-current-raising` in `paper.tex`.
We construct the vector field by raising the correction with the actual induced
metric, and prove its exact tangent-strain identity. The covector correction is
an arbitrary smooth input here; its construction from the continuum inverse,
and the estimates on that construction, are separate obligations.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.PositiveBackground

variable {n N : ℕ}

/-- `app:ch_background:eq:bg-current-raising`: raise the correction covector with
the induced metric of the current immersion. -/
def raisedCorrection (G : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) (x : Euclidean n) : Euclidean n :=
  ((inducedMetric G x)⁻¹).toEuclideanLin (u x)

/-- `app:ch_background:eq:bg-current-raising`: the domain vector field
`X_G = X₀ + g_G⁻¹ u`. -/
def correctedVectorField (G : Euclidean n → Euclidean N)
    (X₀ u : Euclidean n → Euclidean n) : Euclidean n → Euclidean n :=
  X₀ + raisedCorrection G u

/-- `app:ch_background:prop:bg-positive`: applying `dG` to a domain vector field. -/
def tangentVariation (G : Euclidean n → Euclidean N)
    (X : Euclidean n → Euclidean n) (x : Euclidean n) : Euclidean N :=
  fderiv ℝ G x (X x)

/-- `app:ch_background:eq:bg-current-raising`: the physical base variation `dG X_G`. -/
def baseVariation (G : Euclidean n → Euclidean N)
    (X₀ u : Euclidean n → Euclidean n) : Euclidean n → Euclidean N :=
  tangentVariation G (correctedVectorField G X₀ u)

/-- `app:ch_background:eq:bg-current-raising`: applying the differential after
covector raising is the existing geometric tangential lift. -/
theorem tangentVariation_raisedCorrection (G : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) :
    tangentVariation G (raisedCorrection G u) = tangentLift G u := by
  funext x
  have h := congrArg (fderiv ℝ G x)
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (raisedCorrection G u x))
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] at h
  rw [tangentVariation, ← h]
  change (∑ i, (∑ j, (inducedMetric G x)⁻¹ i j * u x j) • partialDeriv G x i) = _
  simp only [Finset.sum_smul, tangentLift]

/-- `app:ch_background:eq:bg-current-raising`: the reference variation plus the
actual tangential lift of the correction. -/
theorem baseVariation_eq (G : Euclidean n → Euclidean N)
    (X₀ u : Euclidean n → Euclidean n) :
    baseVariation G X₀ u = tangentVariation G X₀ + tangentLift G u := by
  rw [← tangentVariation_raisedCorrection]
  funext x
  exact (fderiv ℝ G x).map_add _ _

/-- `app:ch_background:prop:bg-positive`: smooth domain fields produce smooth
tangential variations along a smooth immersion. No rank hypothesis is needed. -/
theorem contDiffOn_tangentVariation {G : Euclidean n → Euclidean N}
    {X : Euclidean n → Euclidean n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hX : ContDiffOn ℝ ∞ X U) :
    ContDiffOn ℝ ∞ (tangentVariation G X) U :=
  (hG.fderiv_of_isOpen hU (by simp)).clm_apply hX

/-- `app:ch_background:eq:bg-current-raising`: the raised domain covector is
smooth on the immersion domain, using the actual inverse induced metric. -/
theorem contDiffOn_raisedCorrection {G : Euclidean n → Euclidean N}
    {u : Euclidean n → Euclidean n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hu : ContDiffOn ℝ ∞ u U)
    (himm : IsImmersionOn G U) : ContDiffOn ℝ ∞ (raisedCorrection G u) U := by
  have hg := contDiffOn_inverse_inducedMetric hU hG himm
  apply (contDiffOn_piLp 2).mpr
  intro i
  change ContDiffOn ℝ ∞ (fun x ↦ ∑ j, (inducedMetric G x)⁻¹ i j * u x j) U
  apply ContDiffOn.sum
  intro j _
  let L : MetricTensor n →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i)
  let C : MetricTensor n →L[ℝ] ℝ := ⟨L, L.continuous_of_finiteDimensional⟩
  exact (C.contDiff.comp_contDiffOn hg).mul ((contDiffOn_piLp 2).mp hu j)

/-- `app:ch_background:eq:bg-current-raising`: smoothness of `X_G`, conditional
only on smoothness of the two input fields and the immersion. -/
theorem contDiffOn_correctedVectorField {G : Euclidean n → Euclidean N}
    {X₀ u : Euclidean n → Euclidean n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hX₀ : ContDiffOn ℝ ∞ X₀ U)
    (hu : ContDiffOn ℝ ∞ u U) (himm : IsImmersionOn G U) :
    ContDiffOn ℝ ∞ (correctedVectorField G X₀ u) U :=
  hX₀.add (contDiffOn_raisedCorrection hU hG hu himm)

/-- `app:ch_background:prop:bg-positive`: smoothness of the physical base variation. -/
theorem contDiffOn_baseVariation {G : Euclidean n → Euclidean N}
    {X₀ u : Euclidean n → Euclidean n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hX₀ : ContDiffOn ℝ ∞ X₀ U)
    (hu : ContDiffOn ℝ ∞ u U) (himm : IsImmersionOn G U) :
    ContDiffOn ℝ ∞ (baseVariation G X₀ u) U := by
  rw [baseVariation_eq]
  exact (contDiffOn_tangentVariation hU hG hX₀).add
    (contDiffOn_tangentLift hU hG hu himm)

/-- `app:ch_background:eq:bg-current-identity`: the geometric part of the exact
cancellation, with the factor `2` from the actual tangent strain. This theorem
does not assume or assert the continuum density cancellation. -/
theorem linearizedMetric_baseVariation {G : Euclidean n → Euclidean N}
    {X₀ u : Euclidean n → Euclidean n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hX₀ : ContDiffOn ℝ ∞ X₀ U)
    (hu : ContDiffOn ℝ ∞ u U) (himm : IsImmersionOn G U) :
    EqOn (linearizedMetric G (baseVariation G X₀ u))
      (linearizedMetric G (tangentVariation G X₀) + 2 • symmCovariantDeriv G u) U := by
  intro x hx
  have hV := (((contDiffOn_tangentVariation hU hG hX₀) x hx).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  have hT := (((contDiffOn_tangentLift hU hG hu himm) x hx).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [baseVariation_eq]
  have hadd : linearizedMetric G (tangentVariation G X₀ + tangentLift G u) x =
      linearizedMetric G (tangentVariation G X₀) x + linearizedMetric G (tangentLift G u) x := by
    ext i j
    simp only [linearizedMetric, partialDeriv, fderiv_add hV hT,
      add_apply, inner_add_left, inner_add_right, Matrix.add_apply]
    ring
  rw [hadd, linearizedMetric_tangentLift hU hG hu himm hx]
  rfl

end JanetCartan.PositiveBackground
