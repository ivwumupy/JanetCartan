module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Retained

/-!
# Local linearity of the actual differential operators

These local identities feed the initial-scalar source map for
`app:ch_response:cor:current-atoms`. Differentiability is required at every
addition of derivatives; equality on a neighborhood suffices for reconstruction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PrimarySourceAdmission.InitialScalarCalculus
open NullTransport ResponseTransfer LeadingWave

/-- Reduced-operator additivity retains the Christoffel terms in the correction
of `app:ch_waves:eq:primary-algebraic-correction`. -/
theorem reducedOperator_add {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {u v : Euclidean n → Euclidean n} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    reducedOperator F Q (u + v) x = reducedOperator F Q u x + reducedOperator F Q v x := by
  ext i
  simp only [reducedOperator, AmbientResponse.symmCovariantDeriv_add_apply F hu hv,
    tensorPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib, Pi.add_apply]

/-- Real homogeneity of the same reduced operator
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem reducedOperator_real_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) :
    reducedOperator F Q (c • u) x = c • reducedOperator F Q u x := by
  ext i
  simp only [reducedOperator, AmbientResponse.symmCovariantDeriv_smul_apply F hu c,
    tensorPairing, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    mul_left_comm, ← Finset.mul_sum]

/-- Reconstruction depends only on the germ of its input
(`app:ch_waves:eq:WKB-W`). -/
theorem completedVariationComplex_zero_congr {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    {u v : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (he : u =ᶠ[𝓝 x] v) :
    completedVariationComplex F u 0 x = completedVariationComplex F v 0 x := by
  have hd (i j : Fin n) : partialDeriv (fun y ↦ u y j) x i =
      partialDeriv (fun y ↦ v y j) x i := by
    have hj : (fun y ↦ u y j) =ᶠ[𝓝 x] (fun y ↦ v y j) :=
      he.mono fun _ h ↦ congrArg (fun b ↦ b j) h
    exact congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1))
      hj.fderiv_eq
  simp only [completedVariationComplex, he.self_of_nhds, hd]

/-- Local additivity of the full reconstruction, used before taking strain
(`app:ch_waves:eq:WKB-W`). -/
theorem completedVariationComplex_zero_add {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    {u v : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    completedVariationComplex F (u + v) 0 x =
      completedVariationComplex F u 0 x + completedVariationComplex F v 0 x := by
  rw [completedVariationComplex_zero_eq_firstOrder F (hu.add hv),
    completedVariationComplex_zero_eq_firstOrder F hu,
    completedVariationComplex_zero_eq_firstOrder F hv]
  simp only [WKB.firstOrderApply, partialDeriv, fderiv_add hu hv,
    _root_.add_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  abel

/-- Real scaling of the full complex reconstruction preserves both quadratures
(`app:ch_waves:eq:WKB-W`). -/
theorem completedVariationComplex_zero_real_smul {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) :
    completedVariationComplex F (c • u) 0 x = c • completedVariationComplex F u 0 x := by
  simpa only [Complex.coe_smul, Pi.smul_def] using
    completedVariationComplex_zero_const_smul F (c : ℂ) hu

/-- Local additivity of the complete strain in the literal source
(`app:ch_response:cor:current-atoms`). -/
theorem complexLinearizedMetric_add {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u v : Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    WKB.complexLinearizedMetric F (u + v) x =
      WKB.complexLinearizedMetric F u x + WKB.complexLinearizedMetric F v x := by
  ext i j
  simp only [WKB.complexLinearizedMetric, partialDeriv, fderiv_add hu hv,
    _root_.add_apply, PiLp.add_apply, Matrix.add_apply]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  ring

/-- Real homogeneity of the complete strain
(`app:ch_response:cor:current-atoms`). -/
theorem complexLinearizedMetric_real_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) :
    WKB.complexLinearizedMetric F (c • u) x = c • WKB.complexLinearizedMetric F u x := by
  ext i j
  simp only [WKB.complexLinearizedMetric, partialDeriv, fderiv_const_smul hu,
    _root_.smul_apply, PiLp.smul_apply, Matrix.smul_apply]
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_add, ← Finset.smul_sum]

end JanetCartan.PrimarySourceAdmission.InitialScalarCalculus
