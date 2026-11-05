module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Analytic.Constructions

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A single circular bending

The elementary bending in Proposition `app:ch_seed:prop:seed-analytic` of
`paper.tex`. The target is the L² product of the old ambient space and one new
real normal direction. This gives the Euclidean product norm, and allows the
construction to be iterated without choosing coordinates.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The standard inclusion into the enlarged ambient space, used in
Proposition `app:ch_seed:prop:seed-analytic`. -/
def bendingInclusion : E →L[ℝ] WithLp 2 (E × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E ℝ)

@[simp] theorem bendingInclusion_apply (u : E) :
    bendingInclusion u = WithLp.toLp 2 (u, (0 : ℝ)) := rfl

/-- The new unit normal in Proposition `app:ch_seed:prop:seed-analytic`. -/
def bendingNormal : WithLp 2 (E × ℝ) := WithLp.toLp 2 (0, 1)

/-- The explicit circular bending of Proposition `app:ch_seed:prop:seed-analytic`.
The frequency is the manuscript's `n`, without an additional `2π` factor. -/
def circularBending (v : E) (n : ℝ) (Y : E) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2
    (Y + (Real.sin (n * inner ℝ v Y) / n - inner ℝ v Y) • v,
      (1 - Real.cos (n * inner ℝ v Y)) / n)

/-- The differential of the bending in Proposition `app:ch_seed:prop:seed-analytic`.
It rotates the distinguished direction into the new normal direction. -/
def circularBendingDifferential (v : E) (n : ℝ) (Y : E) :
    E →L[ℝ] WithLp 2 (E × ℝ) :=
  bendingInclusion +
    (Real.cos (n * inner ℝ v Y) - 1) • (innerSL ℝ v).smulRight (bendingInclusion v) +
    Real.sin (n * inner ℝ v Y) • (innerSL ℝ v).smulRight bendingNormal

/-- Proposition `app:ch_seed:prop:seed-analytic`: the bending is real analytic. -/
theorem circularBending_analyticAt (v : E) (n : ℝ) (Y : E) :
    AnalyticAt ℝ (circularBending v n) Y := by
  have ht := (innerSL ℝ v).analyticAt Y
  have hnt : AnalyticAt ℝ (fun Z ↦ n * inner ℝ v Z) Y := analyticAt_const.mul ht
  have hs := (Real.analyticAt_sin.comp hnt).div_const (c := n)
  have hc := ((analyticAt_const (v := (1 : ℝ))).sub (Real.analyticAt_cos.comp hnt)).div_const (c := n)
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.analyticAt _).comp
    ((analyticAt_id.add ((hs.sub ht).smul analyticAt_const)).prod hc)

/-- Proposition `app:ch_seed:prop:seed-analytic`: analyticity on the whole ambient space. -/
theorem circularBending_analyticOnNhd (v : E) (n : ℝ) :
    AnalyticOnNhd ℝ (circularBending v n) Set.univ :=
  fun Y _ ↦ circularBending_analyticAt v n Y

/-- Proposition `app:ch_seed:prop:seed-analytic`: the bending fixes the center. -/
@[simp] theorem circularBending_zero (v : E) (n : ℝ) :
    circularBending v n 0 = 0 := by
  simp [circularBending]

/-- Pointwise form of the differential in Proposition `app:ch_seed:prop:seed-analytic`. -/
theorem circularBendingDifferential_apply (v : E) (n : ℝ) (Y u : E) :
    circularBendingDifferential v n Y u = WithLp.toLp 2
      (u + ((Real.cos (n * inner ℝ v Y) - 1) * inner ℝ v u) • v,
        Real.sin (n * inner ℝ v Y) * inner ℝ v u) := by
  apply (WithLp.equiv 2 (E × ℝ)).injective
  simp [circularBendingDifferential, bendingNormal, smul_smul]

/-- Proposition `app:ch_seed:prop:seed-analytic`: the explicit Fréchet differential.
Positive frequencies in the manuscript satisfy the nonzero assumption here. -/
theorem circularBending_hasFDerivAt (v : E) {n : ℝ} (hn : n ≠ 0) (Y : E) :
    HasFDerivAt (circularBending v n) (circularBendingDifferential v n Y) Y := by
  have ht := (innerSL ℝ v).hasFDerivAt (x := Y)
  have hnt := ht.const_mul n
  have hs := ((hnt.sin.mul_const n⁻¹).sub ht).smul_const v
  have hc := ((hasFDerivAt_const (1 : ℝ) Y).sub hnt.cos).mul_const n⁻¹
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp Y
    (((hasFDerivAt_id Y).add hs).prodMk hc)
  convert! h using 1
  ext u
  rw [circularBendingDifferential_apply]
  apply (WithLp.equiv 2 (E × ℝ)).injective
  simp
  constructor
  · congr 1
    field_simp [hn]
  · field_simp [hn]

/-- Proposition `app:ch_seed:prop:seed-analytic`: identification with `fderiv`. -/
theorem circularBending_fderiv (v : E) {n : ℝ} (hn : n ≠ 0) (Y : E) :
    fderiv ℝ (circularBending v n) Y = circularBendingDifferential v n Y :=
  (circularBending_hasFDerivAt v hn Y).fderiv

/-- Proposition `app:ch_seed:prop:seed-analytic`: the center first jet is the standard inclusion. -/
@[simp] theorem circularBending_fderiv_zero (v : E) {n : ℝ} (hn : n ≠ 0) :
    fderiv ℝ (circularBending v n) 0 = bendingInclusion := by
  rw [circularBending_fderiv v hn]
  ext u
  rw [circularBendingDifferential_apply]
  simp

/-- Proposition `app:ch_seed:prop:seed-analytic`: smoothness of every order. -/
theorem circularBending_contDiff (v : E) (n : ℝ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (circularBending v n) :=
  (circularBending_analyticOnNhd v n).contDiff

/-- Proposition `app:ch_seed:prop:seed-analytic`: the differential fixes `vᗮ`. -/
theorem circularBendingDifferential_apply_of_inner_eq_zero
    (v : E) (n : ℝ) (Y u : E) (hu : inner ℝ v u = 0) :
    circularBendingDifferential v n Y u = bendingInclusion u := by
  rw [circularBendingDifferential_apply]
  simp [hu]

/-- Proposition `app:ch_seed:prop:seed-analytic`: the distinguished direction rotates
into the new normal direction. -/
theorem circularBendingDifferential_apply_self (v : E) (hv : ‖v‖ = 1) (n : ℝ) (Y : E) :
    circularBendingDifferential v n Y v =
      WithLp.toLp 2 (Real.cos (n * inner ℝ v Y) • v, Real.sin (n * inner ℝ v Y)) := by
  rw [circularBendingDifferential_apply]
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  simp only [hvv, mul_one]
  congr 2
  rw [sub_smul, one_smul, add_sub_cancel]

/-- Proposition `app:ch_seed:prop:seed-analytic`: preservation of the inner product
by the explicit differential. -/
theorem circularBendingDifferential_inner (v : E) (hv : ‖v‖ = 1) (n : ℝ) (Y u w : E) :
    inner ℝ (circularBendingDifferential v n Y u)
      (circularBendingDifferential v n Y w) = inner ℝ u w := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  simp only [circularBendingDifferential_apply, WithLp.prod_inner_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    Real.inner_apply, hvv]
  have huv : inner ℝ u v = inner ℝ v u := real_inner_comm _ _
  simp only [huv]
  have ht := Real.sin_sq_add_cos_sq (n * inner ℝ v Y)
  calc
    _ = inner ℝ u w + (inner ℝ v u * inner ℝ v w) *
        (Real.sin (n * inner ℝ v Y) ^ 2 + Real.cos (n * inner ℝ v Y) ^ 2 - 1) := by ring
    _ = _ := by rw [ht]; ring

/-- Proposition `app:ch_seed:prop:seed-analytic`: the bending has isometric differential
at every point. In particular this applies to every positive frequency. -/
theorem circularBending_isometry_fderiv (v : E) (hv : ‖v‖ = 1)
    {n : ℝ} (hn : n ≠ 0) (Y : E) :
    Isometry (fderiv ℝ (circularBending v n) Y) := by
  rw [circularBending_fderiv v hn]
  exact (LinearMap.isometryOfInner (circularBendingDifferential v n Y).toLinearMap
    (circularBendingDifferential_inner v hv n Y)).isometry

/-- Proposition `app:ch_seed:prop:seed-analytic`: the differential preserves the metric. -/
theorem circularBending_fderiv_inner (v : E) (hv : ‖v‖ = 1)
    {n : ℝ} (hn : n ≠ 0) (Y u w : E) :
    inner ℝ (fderiv ℝ (circularBending v n) Y u)
      (fderiv ℝ (circularBending v n) Y w) = inner ℝ u w := by
  rw [circularBending_fderiv v hn]
  exact circularBendingDifferential_inner v hv n Y u w

/-- Proposition `app:ch_seed:prop:seed-analytic`: differentiating the explicit
first derivative at the center gives the normal rank-one bilinear map. -/
theorem circularBendingDifferential_hasFDerivAt_zero (v : E) (n : ℝ) :
    HasFDerivAt (circularBendingDifferential v n)
      ((n • innerSL ℝ v).smulRight ((innerSL ℝ v).smulRight bendingNormal)) 0 := by
  let : NormedSpace ℝ (E →L[ℝ] WithLp 2 (E × ℝ)) := inferInstance
  have ht := (innerSL ℝ v).hasFDerivAt (x := (0 : E))
  have hnt := ht.const_mul n
  have hc := (hnt.cos.sub (hasFDerivAt_const (1 : ℝ) (0 : E))).smul_const
    ((innerSL ℝ v).smulRight (bendingInclusion v))
  have hs := hnt.sin.smul_const ((innerSL ℝ v).smulRight (bendingNormal (E := E)))
  have h := ((hasFDerivAt_const (bendingInclusion (E := E)) (0 : E)).add hc).add hs
  convert! h using 1
  ext u w
  simp

/-- Proposition `app:ch_seed:prop:seed-analytic`: the second Fréchet derivative exists
at zero and is `n v ⊗ v` in the new normal direction. -/
theorem circularBending_hasFDerivAt_fderiv_zero (v : E) {n : ℝ} (hn : n ≠ 0) :
    HasFDerivAt (fderiv ℝ (circularBending v n))
      ((n • innerSL ℝ v).smulRight ((innerSL ℝ v).smulRight bendingNormal)) 0 := by
  have heq : fderiv ℝ (circularBending v n) = circularBendingDifferential v n :=
    funext (circularBending_fderiv v hn)
  rw [heq]
  exact circularBendingDifferential_hasFDerivAt_zero v n

/-- Proposition `app:ch_seed:prop:seed-analytic`: the second center jet as a
continuous bilinear map. -/
theorem circularBending_secondFDeriv_zero (v : E) {n : ℝ} (hn : n ≠ 0) :
    fderiv ℝ (fderiv ℝ (circularBending v n)) 0 =
      (n • innerSL ℝ v).smulRight ((innerSL ℝ v).smulRight bendingNormal) :=
  (circularBending_hasFDerivAt_fderiv_zero v hn).fderiv

/-- Proposition `app:ch_seed:prop:seed-analytic`: evaluation of the second center jet. -/
theorem circularBending_secondFDeriv_zero_apply (v : E) {n : ℝ} (hn : n ≠ 0) (u w : E) :
    fderiv ℝ (fderiv ℝ (circularBending v n)) 0 u w =
      (n * inner ℝ v u * inner ℝ v w) • bendingNormal := by
  rw [circularBending_secondFDeriv_zero v hn]
  simp [smul_smul, mul_assoc]

/-- Proposition `app:ch_seed:prop:seed-analytic`: the iterated directional derivative,
in the form used for coordinate second fundamental forms. -/
theorem circularBending_fderiv_fderiv_apply_zero (v : E) {n : ℝ} (hn : n ≠ 0) (u w : E) :
    fderiv ℝ (fun Y ↦ fderiv ℝ (circularBending v n) Y w) 0 u =
      WithLp.toLp 2 (0, n * inner ℝ v u * inner ℝ v w) := by
  have h := (circularBending_hasFDerivAt_fderiv_zero v hn).clm_apply
    (hasFDerivAt_const w (0 : E))
  rw [h.fderiv]
  apply (WithLp.equiv 2 (E × ℝ)).injective
  simp [bendingNormal, smul_smul, mul_assoc]

end JanetCartan
