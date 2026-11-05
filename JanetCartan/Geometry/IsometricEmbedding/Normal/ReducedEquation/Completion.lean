module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.CanonicalReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Reduction

/-!
# The reduced equation and its canonical completion

Complete Section 4.1 of `paper-v2.tex` on the actual normal inverse and the
actual reduced operator. The canonical field's normality, normal equation,
and regularity are consequences of full normal rank and the original smooth
immersion. The source keeps its factor `1/2`, and the error is exactly the
inverse-Gram reconstruction of the reduced error.

The stress lift is the existing `LeadingWave.reconstruction` with
`canonicalNormalCompletion`; no solution operator or analytic response
identity is needed for `new:lem:completion` and `main:eq:stress-lift`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan

namespace AmbientResponse

/-- Contracting the tangent–normal formula with an actual stress removes
the normal field and leaves exactly twice the reduced contraction. This is
the projection step from `main:eq:tangent-normal` to
`main:eq:reduced-equation`, with the connection of the induced metric. -/
theorem tensorPairing_linearizedMetric_tangent_add_normal {n N : ℕ}
    {F w : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hw : ContDiffOn ℝ ∞ w s) (hi : IsImmersionOn F s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x)
    {x : Euclidean n} (hx : x ∈ s) {Q : MetricTensor n}
    (hQ : Q ∈ stressSpace F x) :
    tensorPairing Q (linearizedMetric F (tangentLift F u + w) x) =
      2 * tensorPairing Q (symmCovariantDeriv F u x) := by
  have hzero : tensorPairing Q (normalPairing F w x) = 0 := by
    rw [← inner_normalMap_eq_tensorPairing, hQ.2, inner_zero_right]
  rw [linearizedMetric_tangent_add_normal hs hF hu hw hi hnormal hx]
  change inner ℝ Q ((2 : ℝ) • symmCovariantDeriv F u x -
    (2 : ℝ) • normalPairing F w x) = _
  rw [inner_sub_right, inner_smul_right, inner_smul_right]
  change 2 * tensorPairing Q (symmCovariantDeriv F u x) -
    2 * tensorPairing Q (normalPairing F w x) = _
  rw [hzero, mul_zero, sub_zero]

/-- The actual normal completion has the exact error tensor in
`new:lem:completion` / `main:eq:completion-error`. The normal equation and
normal-field smoothness are proved from the original full-normal-rank
immersion; neither is an additional premise. Only a basis of the actual
stress space at the point is used, so a uniform positive Gram bound is not
needed for this identity. -/
theorem completedVariation_error_eq_inverseGram {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hi : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hhSmooth : ContDiffOn ℝ ∞ h s)
    {x : Euclidean n} (hx : x ∈ s) (hh : (h x).IsSymm)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : LinearIndependent ℝ (Q x))
    (hspan : (Submodule.span ℝ (Set.range (Q x)) : Set (MetricTensor n)) = stressSpace F x) :
    linearizedMetric F (completedVariation F u h) x - h x =
      (2 : ℝ) • ∑ i, ∑ j, ((stressGram (Q x))⁻¹ i j *
        (NullTransport.reducedOperator F Q u x j -
          (1 / 2 : ℝ) * tensorPairing (Q x j) (h x))) • Q x i := by
  have hw := contDiffOn_canonicalNormalCompletion hs hF
    ((contDiffOn_symmCovariantDeriv hs hF hu hi).sub
      (hhSmooth.const_smul (1 / 2 : ℝ))) hi hrank
  have he := strain_error_eq_inverseGram hs hF hu hw hi
    (fun y _ ↦ canonicalNormalCompletion_mem_normalSpace F y _) hx hh
    (canonicalNormalCompletion_normal_equation (hrank x hx) _) hQ hspan
  change linearizedMetric F (completedVariation F u h) x - h x = _ at he
  simpa only [NullTransport.reducedOperator] using he

/-- The canonical completed variation solves the full metric equation
exactly when its covector solves the manuscript's reduced equation, with
the factor `1/2` in the source (`new:lem:completion`,
`main:eq:reduced-equation`). -/
theorem completedVariation_eq_iff_reduced_equation {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hi : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hhSmooth : ContDiffOn ℝ ∞ h s)
    {x : Euclidean n} (hx : x ∈ s) (hh : (h x).IsSymm)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : LinearIndependent ℝ (Q x))
    (hspan : (Submodule.span ℝ (Set.range (Q x)) : Set (MetricTensor n)) = stressSpace F x) :
    linearizedMetric F (completedVariation F u h) x = h x ↔
      NullTransport.reducedOperator F Q u x =
        fun j ↦ (1 / 2 : ℝ) * tensorPairing (Q x j) (h x) := by
  rw [← sub_eq_zero, completedVariation_error_eq_inverseGram
    hs hF hu hi hrank hhSmooth hx hh Q hQ hspan, stressGram_eq_gram,
    ← inverseGramReconstruction_eq_sum]
  simp only [smul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    inverseGramReconstruction_eq_zero_iff hQ, funext_iff, Pi.zero_apply, sub_eq_zero]

end AmbientResponse

namespace NullTransport

/-- Every solution of the full tangent–normal metric equation satisfies
the reduced equation, before making any choice of normal completion.
Only membership of the supplied frame tensors in `K_F` is needed for this
necessary condition (`main:eq:reduced-equation`). -/
theorem reduced_equation_of_linearizedMetric_tangent_add_normal {n N : ℕ}
    {F w : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hw : ContDiffOn ℝ ∞ w s) (hi : IsImmersionOn F s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x)
    {x : Euclidean n} (hx : x ∈ s)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : ∀ j, Q x j ∈ stressSpace F x)
    (hmetric : linearizedMetric F (tangentLift F u + w) x = h x) :
    reducedOperator F Q u x = fun j ↦ (1 / 2 : ℝ) * tensorPairing (Q x j) (h x) := by
  funext j
  have he := AmbientResponse.tensorPairing_linearizedMetric_tangent_add_normal
    hs hF hu hw hi hnormal hx (hQ j)
  rw [hmetric] at he
  change tensorPairing (Q x j) (symmCovariantDeriv F u x) = _
  linarith

end NullTransport

namespace LeadingWave

open AmbientResponse

/-- The differential lift in `main:eq:stress-lift` uses the actual canonical
normal inverse. Its full linearized metric is the displayed inverse-Gram
reconstruction of the actual reduced operator, including the factor two. -/
theorem reconstruction_canonical_strain_eq_inverseGram {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hi : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    {x : Euclidean n} (hx : x ∈ s)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : LinearIndependent ℝ (Q x))
    (hspan : (Submodule.span ℝ (Set.range (Q x)) : Set (MetricTensor n)) = stressSpace F x) :
    linearizedMetric F (reconstruction F (canonicalNormalCompletion F) u) x =
      (2 : ℝ) • ∑ i, ∑ j, ((stressGram (Q x))⁻¹ i j *
        NullTransport.reducedOperator F Q u x j) • Q x i := by
  have he := completedVariation_error_eq_inverseGram (h := (0 : MetricField n))
    hs hF hu hi hrank contDiffOn_const hx Matrix.isSymm_zero Q hQ hspan
  have hsame : completedVariation F u (0 : MetricField n) =
      reconstruction F (canonicalNormalCompletion F) u := by
    funext y
    simp only [completedVariation, reconstruction, LeadingWave.normalCorrection,
      Pi.add_apply, Pi.zero_apply, smul_zero, sub_zero]
  rw [hsame] at he
  simpa [tensorPairing] using he

/-- The lift's metric change lies in the actual symmetric stress kernel,
as asserted after `main:eq:stress-lift`. This geometric fact requires no
choice of stress basis. -/
theorem reconstruction_canonical_strain_mem_stressSpace {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hi : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    {x : Euclidean n} (hx : x ∈ s) :
    linearizedMetric F (reconstruction F (canonicalNormalCompletion F) u) x ∈
      stressSpace F x := by
  refine ⟨linearizedMetric_isSymm _ _ _, ?_⟩
  have he := congrArg (normalMapLinear F x)
    (reconstruction_canonical_half_strain hs hF hu hi hrank hx)
  rw [map_smul] at he
  change (1 / 2 : ℝ) • normalMap F x
    (linearizedMetric F (reconstruction F (canonicalNormalCompletion F) u) x) =
      normalMap F x (ProjectedStressFrame.stressProjection F x (symmCovariantDeriv F u x)) at he
  rw [ProjectedStressFrame.normalMap_stressProjection (hrank x hx)] at he
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

/-- The actual stress lift has zero linearized metric precisely when its
covector solves the homogeneous reduced equation. Both directions use the
same canonical lift and the same stress frame (`main:eq:stress-lift`). -/
theorem reconstruction_canonical_strain_eq_zero_iff {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hi : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    {x : Euclidean n} (hx : x ∈ s)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : LinearIndependent ℝ (Q x))
    (hspan : (Submodule.span ℝ (Set.range (Q x)) : Set (MetricTensor n)) = stressSpace F x) :
    linearizedMetric F (reconstruction F (canonicalNormalCompletion F) u) x = 0 ↔
      NullTransport.reducedOperator F Q u x = 0 := by
  have he := completedVariation_eq_iff_reduced_equation (h := (0 : MetricField n))
    hs hF hu hi hrank contDiffOn_const hx Matrix.isSymm_zero Q hQ hspan
  have hsame : completedVariation F u (0 : MetricField n) =
      reconstruction F (canonicalNormalCompletion F) u := by
    funext y
    simp only [completedVariation, reconstruction, LeadingWave.normalCorrection,
      Pi.add_apply, Pi.zero_apply, smul_zero, sub_zero]
  rw [hsame] at he
  simpa [tensorPairing, funext_iff] using he

end LeadingWave
end JanetCartan
