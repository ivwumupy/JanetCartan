module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

import Mathlib.Tactic.NormNum

/-!
# Calculus of the induced metric

Smoothness, coordinate derivatives, and first variation for Section 2,
`main:eq:metric-expansion`. Matrices carry the Frobenius norm. The local statements
use open sets because `partialDeriv` is defined using the ordinary derivative.
The limit lemmas require convergence of first derivatives, as supplied by C¹ convergence.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set Filter Topology

namespace JanetCartan

variable {n N : ℕ} {F Y Z : Euclidean n → Euclidean N} {x : Euclidean n}
  {s : Set (Euclidean n)} {r m : ℕ∞ω}

-- Transfer coordinate calculus from the product norm to the Frobenius norm.
private def metricTensorOfEntries (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

/-- Section 2, `main:eq:metric-expansion`: coordinate differentiation is additive. -/
theorem partialDeriv_add (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x)
    (i : Fin n) : partialDeriv (Y + Z) x i = partialDeriv Y x i + partialDeriv Z x i := by
  simp only [partialDeriv, fderiv_add hY hZ, add_apply]

/-- Section 2, `main:eq:metric-expansion`: constant scalars commute with coordinate derivatives. -/
theorem partialDeriv_smul (hY : DifferentiableAt ℝ Y x) (a : ℝ) (i : Fin n) :
    partialDeriv (a • Y) x i = a • partialDeriv Y x i := by
  simp only [partialDeriv, fderiv_const_smul hY a, smul_apply]

/-- Section 2, `main:eq:metric-expansion`: additivity in the variation at a point. -/
theorem linearizedMetric_add_apply (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x) :
    linearizedMetric F (Y + Z) x = linearizedMetric F Y x + linearizedMetric F Z x := by
  ext i j
  simp only [linearizedMetric, partialDeriv_add hY hZ, inner_add_left, inner_add_right,
    Matrix.add_apply]
  ac_rfl

/-- Section 2, `main:eq:metric-expansion`: homogeneity in the variation at a point. -/
theorem linearizedMetric_smul_apply (hY : DifferentiableAt ℝ Y x) (a : ℝ) :
    linearizedMetric F (a • Y) x = a • linearizedMetric F Y x := by
  ext i j
  simp only [linearizedMetric, partialDeriv_smul hY, inner_smul_right, real_inner_smul_left,
    Matrix.smul_apply, smul_eq_mul, mul_add]

/-- Section 2, `main:eq:metric-expansion`: the linearization is additive on differentiable fields. -/
theorem linearizedMetric_add (hY : Differentiable ℝ Y) (hZ : Differentiable ℝ Z) :
    linearizedMetric F (Y + Z) = linearizedMetric F Y + linearizedMetric F Z := by
  funext x
  exact linearizedMetric_add_apply (hY x) (hZ x)

/-- Section 2, `main:eq:metric-expansion`: the linearization commutes with real scalars. -/
theorem linearizedMetric_smul (hY : Differentiable ℝ Y) (a : ℝ) :
    linearizedMetric F (a • Y) = a • linearizedMetric F Y := by
  funext x
  exact linearizedMetric_smul_apply (hY x) a

/-- Section 2, `main:eq:metric-expansion`: the zero variation produces zero strain. -/
@[simp] theorem linearizedMetric_zero : linearizedMetric F 0 = 0 := by
  ext x i j
  simp [linearizedMetric, partialDeriv]

/-- Section 2, `main:eq:metric-expansion`: the polarization is symmetric in its two fields. -/
theorem linearizedMetric_comm : linearizedMetric F Y = linearizedMetric Y F := by
  ext x i j
  exact add_comm _ _

/-- Section 2, `main:eq:metric-expansion`: a coordinate derivative loses one order of regularity. -/
theorem contDiff_partialDeriv (hF : ContDiff ℝ m F) (hr : r + 1 ≤ m) (i : Fin n) :
    ContDiff ℝ r (fun x ↦ partialDeriv F x i) :=
  (hF.fderiv_right hr).clm_apply contDiff_const

/-- Section 2, `main:eq:metric-expansion`: local regularity of a coordinate derivative. -/
theorem contDiffAt_partialDeriv (hF : ContDiffAt ℝ m F x) (hr : r + 1 ≤ m) (i : Fin n) :
    ContDiffAt ℝ r (fun x ↦ partialDeriv F x i) x :=
  (hF.fderiv_right hr).clm_apply contDiffAt_const

/-- Section 2, `main:eq:metric-expansion`: regularity of coordinate derivatives on an open chart. -/
theorem contDiffOn_partialDeriv_of_le (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 ≤ m) (i : Fin n) : ContDiffOn ℝ r (fun x ↦ partialDeriv F x i) s :=
  (hF.fderiv_of_isOpen hs hr).clm_apply contDiffOn_const

/-- Section 2, `main:eq:metric-expansion`: the metric of a C^(r+1) map is C^r,
including smooth maps by taking r = m = ∞. -/
theorem contDiff_inducedMetric (hF : ContDiff ℝ m F) (hr : r + 1 ≤ m) :
    ContDiff ℝ r (inducedMetric F) := by
  apply (metricTensorOfEntries n).contDiff.comp
  exact contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦
    (contDiff_partialDeriv hF hr i).inner ℝ (contDiff_partialDeriv hF hr j)

/-- Section 2, `main:eq:metric-expansion`: regularity of the metric on an open chart. -/
theorem contDiffOn_inducedMetric_of_le (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 ≤ m) : ContDiffOn ℝ r (inducedMetric F) s := by
  apply (metricTensorOfEntries n).contDiff.comp_contDiffOn
  exact contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦
    (contDiffOn_partialDeriv_of_le hs hF hr i).inner ℝ (contDiffOn_partialDeriv_of_le hs hF hr j)

/-- Section 2, `main:eq:metric-expansion`: regularity of the linearized metric. -/
theorem contDiff_linearizedMetric (hF : ContDiff ℝ m F) (hY : ContDiff ℝ m Y)
    (hr : r + 1 ≤ m) : ContDiff ℝ r (linearizedMetric F Y) := by
  apply (metricTensorOfEntries n).contDiff.comp
  exact contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦
    ((contDiff_partialDeriv hF hr i).inner ℝ (contDiff_partialDeriv hY hr j)).add
      ((contDiff_partialDeriv hY hr i).inner ℝ (contDiff_partialDeriv hF hr j))

/-- Section 2, `main:eq:metric-expansion`: regularity of the linearized metric on an open chart. -/
theorem contDiffOn_linearizedMetric (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hY : ContDiffOn ℝ m Y s) (hr : r + 1 ≤ m) :
    ContDiffOn ℝ r (linearizedMetric F Y) s := by
  apply (metricTensorOfEntries n).contDiff.comp_contDiffOn
  exact contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦
    ((contDiffOn_partialDeriv_of_le hs hF hr i).inner ℝ
      (contDiffOn_partialDeriv_of_le hs hY hr j)).add
    ((contDiffOn_partialDeriv_of_le hs hY hr i).inner ℝ
      (contDiffOn_partialDeriv_of_le hs hF hr j))

/-- Section 2, `main:eq:metric-expansion`: spatial derivative of each metric coefficient. -/
theorem partialDeriv_inducedMetric_apply (hF : ContDiffAt ℝ 2 F x) (i j k : Fin n) :
    partialDeriv (fun y ↦ inducedMetric F y i j) x k =
      inner ℝ (partialDeriv F x i) (partialDeriv (fun y ↦ partialDeriv F y j) x k) +
      inner ℝ (partialDeriv (fun y ↦ partialDeriv F y i) x k) (partialDeriv F x j) := by
  exact fderiv_inner_apply ℝ
    ((contDiffAt_partialDeriv hF (r := 1) (by decide) i).differentiableAt (by decide))
    ((contDiffAt_partialDeriv hF (r := 1) (by decide) j).differentiableAt (by decide)) _

/-- Section 2, `main:eq:metric-expansion`: spatial derivative of the linearized metric. -/
theorem partialDeriv_linearizedMetric (hF : ContDiffAt ℝ 2 F x)
    (hY : ContDiffAt ℝ 2 Y x) (i j k : Fin n) :
    partialDeriv (fun y ↦ linearizedMetric F Y y i j) x k =
      (inner ℝ (partialDeriv F x i) (partialDeriv (fun y ↦ partialDeriv Y y j) x k) +
        inner ℝ (partialDeriv (fun y ↦ partialDeriv F y i) x k) (partialDeriv Y x j)) +
      (inner ℝ (partialDeriv Y x i) (partialDeriv (fun y ↦ partialDeriv F y j) x k) +
        inner ℝ (partialDeriv (fun y ↦ partialDeriv Y y i) x k) (partialDeriv F x j)) := by
  have hF' (l : Fin n) :=
    (contDiffAt_partialDeriv hF (r := 1) (by decide) l).differentiableAt (by decide)
  have hY' (l : Fin n) :=
    (contDiffAt_partialDeriv hY (r := 1) (by decide) l).differentiableAt (by decide)
  unfold partialDeriv linearizedMetric
  rw [fderiv_fun_add ((hF' i).inner ℝ (hY' j)) ((hY' i).inner ℝ (hF' j))]
  simp only [add_apply]
  rw [fderiv_inner_apply ℝ (hF' i) (hY' j), fderiv_inner_apply ℝ (hY' i) (hF' j)]
  rfl

private theorem hasDerivAt_metricTensor {f : ℝ → MetricTensor n} {g : MetricTensor n}
    {t : ℝ} (h : ∀ i j, HasDerivAt (fun a ↦ f a i j) (g i j) t) : HasDerivAt f g t := by
  have hd := (metricTensorOfEntries n).hasFDerivAt.comp t
    (hasFDerivAt_pi.mpr fun i ↦ hasFDerivAt_pi.mpr fun j ↦ (h i j).hasFDerivAt)
  have hd' := hd.hasDerivAt
  change HasDerivAt f (fun i j ↦ (1 : ℝ) • g i j) t at hd'
  simpa only [one_smul] using hd'

/-- Section 2, `main:eq:metric-expansion`: the derivative along an affine variation
is the linearized metric, evaluated at the varying map. -/
theorem hasDerivAt_inducedMetric (hF : DifferentiableAt ℝ F x)
    (hY : DifferentiableAt ℝ Y x) (t : ℝ) :
    HasDerivAt (fun a : ℝ ↦ inducedMetric (F + a • Y) x)
      (linearizedMetric (F + t • Y) Y x) t := by
  apply hasDerivAt_metricTensor
  intro i j
  have hd (k : Fin n) : HasDerivAt (fun a : ℝ ↦ partialDeriv (F + a • Y) x k)
      (partialDeriv Y x k) t := by
    have hd := ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (partialDeriv Y x k)).hasFDerivAt (x := t)
    simpa [partialDeriv_add hF (hY.const_smul _), partialDeriv_smul hY]
      using (hd.const_add (partialDeriv F x k)).hasDerivAt
  exact (hd i).inner ℝ (hd j)

/-- Section 2, `main:eq:metric-expansion`: Dγ_F Y is the first variation of γ at F. -/
theorem hasDerivAt_inducedMetric_zero (hF : DifferentiableAt ℝ F x)
    (hY : DifferentiableAt ℝ Y x) :
    HasDerivAt (fun t : ℝ ↦ inducedMetric (F + t • Y) x) (linearizedMetric F Y x) 0 := by
  simpa using hasDerivAt_inducedMetric hF hY 0

/-- Section 2, `main:eq:metric-expansion`: the derivative of the linearized metric
in its variation argument is the same linear operator. -/
theorem hasDerivAt_linearizedMetric (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x) (t : ℝ) :
    HasDerivAt (fun a : ℝ ↦ linearizedMetric F (Y + a • Z) x)
      (linearizedMetric F Z x) t := by
  have hd := ((ContinuousLinearMap.id ℝ ℝ).smulRight
    (linearizedMetric F Z x)).hasFDerivAt (x := t)
  have hd' := (hd.const_add (linearizedMetric F Y x)).hasDerivAt
  change HasDerivAt (fun a : ℝ ↦ linearizedMetric F Y x + a • linearizedMetric F Z x)
    ((1 : ℝ) • linearizedMetric F Z x) t at hd'
  simpa only [one_smul, linearizedMetric_add_apply hY (hZ.const_smul _),
    linearizedMetric_smul_apply hZ] using hd'

/-- Section 2, `main:eq:metric-expansion`: a C¹ map has a continuous induced metric. -/
theorem continuousOn_inducedMetric (hs : IsOpen s) (hF : ContDiffOn ℝ 1 F s) :
    ContinuousOn (inducedMetric F) s :=
  (contDiffOn_inducedMetric_of_le hs hF (r := 0) (by simp)).continuousOn

/-- Section 2, `main:eq:metric-expansion`: C¹ fields have a continuous linearized metric. -/
theorem continuousOn_linearizedMetric (hs : IsOpen s) (hF : ContDiffOn ℝ 1 F s)
    (hY : ContDiffOn ℝ 1 Y s) : ContinuousOn (linearizedMetric F Y) s :=
  (contDiffOn_linearizedMetric hs hF hY (r := 0) (by simp)).continuousOn

/-- Section 2, `main:eq:metric-expansion`: convergence of first derivatives gives
convergence of coordinate derivatives. No convergence of function values is needed. -/
theorem tendsto_partialDeriv {ι : Type*} {l : Filter ι}
    {Fs : ι → Euclidean n → Euclidean N}
    (hF : Tendsto (fun a ↦ fderiv ℝ (Fs a) x) l (𝓝 (fderiv ℝ F x))) (i : Fin n) :
    Tendsto (fun a ↦ partialDeriv (Fs a) x i) l (𝓝 (partialDeriv F x i)) :=
  (continuous_id.clm_apply continuous_const).continuousAt.tendsto.comp hF

/-- Section 2, `main:eq:metric-expansion`: continuity of γ under C¹ convergence,
expressed using only the pointwise first-derivative convergence it needs. -/
theorem tendsto_inducedMetric {ι : Type*} {l : Filter ι}
    {Fs : ι → Euclidean n → Euclidean N}
    (hF : Tendsto (fun a ↦ fderiv ℝ (Fs a) x) l (𝓝 (fderiv ℝ F x))) :
    Tendsto (fun a ↦ inducedMetric (Fs a) x) l (𝓝 (inducedMetric F x)) :=
  tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦
    (tendsto_partialDeriv hF i).inner (tendsto_partialDeriv hF j)

/-- Section 2, `main:eq:metric-expansion`: joint continuity of the linearized metric
under convergence of the two first derivatives. -/
theorem tendsto_linearizedMetric {ι : Type*} {l : Filter ι}
    {Fs Ys : ι → Euclidean n → Euclidean N}
    (hF : Tendsto (fun a ↦ fderiv ℝ (Fs a) x) l (𝓝 (fderiv ℝ F x)))
    (hY : Tendsto (fun a ↦ fderiv ℝ (Ys a) x) l (𝓝 (fderiv ℝ Y x))) :
    Tendsto (fun a ↦ linearizedMetric (Fs a) (Ys a) x) l (𝓝 (linearizedMetric F Y x)) :=
  tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦
    ((tendsto_partialDeriv hF i).inner (tendsto_partialDeriv hY j)).add
      ((tendsto_partialDeriv hY i).inner (tendsto_partialDeriv hF j))

/-- Section 9, `main:eq:final-Cr`, using `main:eq:metric-expansion`: passage to the
metric equation when the first derivatives converge and the metric defects vanish.
The construction of such a convergent family is a separate analytic input. -/
theorem isIsometricOn_of_tendsto_fderiv {ι : Type*} {l : Filter ι} [l.NeBot]
    {Fs : ι → Euclidean n → Euclidean N} {g : MetricField n}
    (hF : ∀ x ∈ s, Tendsto (fun a ↦ fderiv ℝ (Fs a) x) l (𝓝 (fderiv ℝ F x)))
    (herror : ∀ x ∈ s, Tendsto (fun a ↦ inducedMetric (Fs a) x - g x) l (𝓝 0)) :
    IsIsometricOn g F s := by
  intro x hx
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((tendsto_inducedMetric (hF x hx)).sub tendsto_const_nhds) (herror x hx))

/-- Section 2 (`main:sec:geometry`): coordinate second derivatives commute for a `C²` map. -/
theorem partialDeriv_partialDeriv_comm {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (hF : ContDiffAt ℝ 2 F x) (i j : Fin n) :
    partialDeriv (fun y ↦ partialDeriv F y j) x i =
      partialDeriv (fun y ↦ partialDeriv F y i) x j := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  simp only [partialDeriv, fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_const_apply, zero_apply, ContinuousLinearMap.comp_apply,
    add_apply, ContinuousLinearMap.flip_apply, map_zero, zero_add]
  exact (hF.isSymmSndFDerivAt (by norm_num)) _ _

end JanetCartan
