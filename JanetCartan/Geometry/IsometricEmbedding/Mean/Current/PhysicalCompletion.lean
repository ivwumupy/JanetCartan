module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Completion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient
public import JanetCartan.Geometry.IsometricEmbedding.Calculus

/-!
# The physical normal completion of the current mean

The field in `main:eq:mean-normal-field` uses the actual canonical normal
inverse of the SAME immersion. Its smoothness, normality and strain are
derived here. The full tensor error is reconstructed from the reduced defect
with the original stress frame. These identities are consumed by the mean
field in `UniformStep.identities_sampled_history_fields`; quantitative
residual estimates and the prepared/canonical fields remain separate inputs.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CurrentMean

open AmbientResponse

variable {n N : ℕ}

/-- The actual signed normal field in `main:eq:mean-normal-field`, with the
factor `-1/2` and the original geometric normal inverse. -/
def meanNormalCorrection (F : Euclidean n → Euclidean N) (T : MetricField n) :
    Euclidean n → Euclidean N :=
  fun x ↦ -(1 / 2 : ℝ) • canonicalNormalCompletion F x (T x)

/-- The correction in `main:eq:mean-normal-field` is normal to the SAME
immersion at every point. -/
theorem meanNormalCorrection_mem_normalSpace
    (F : Euclidean n → Euclidean N) (T : MetricField n) (x : Euclidean n) :
    meanNormalCorrection F T x ∈ normalSpace F x :=
  (normalSpace F x).smul_mem _ (canonicalNormalCompletion_mem_normalSpace F x (T x))

/-- Smoothness of `main:eq:mean-normal-field` follows from immersion and
full normal rank, rather than from an assumed smooth completion field. -/
theorem contDiffOn_meanNormalCorrection {F : Euclidean n → Euclidean N}
    {T : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞ (meanNormalCorrection F T) U :=
  (contDiffOn_canonicalNormalCompletion hU hF hT hi hrank).const_smul _

/-- The physical strain of `main:eq:mean-normal-field` removes exactly the
orthogonal complement of the normal-map kernel. Differentiation of the
actual normal field supplies this identity. -/
theorem linearizedMetric_meanNormalCorrection {F : Euclidean n → Euclidean N}
    {T : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {x : Euclidean n} (hx : x ∈ U) :
    linearizedMetric F (meanNormalCorrection F T) x =
      (normalMapToNormal F x).kerᗮ.starProjection (T x) := by
  rw [linearizedMetric_normal hU hF
    (contDiffOn_meanNormalCorrection hU hF hT hi hrank)
    (fun y _ ↦ meanNormalCorrection_mem_normalSpace F T y) hx]
  have he : meanNormalCorrection F T x =
      ((normalCorrection (normalMapToNormal F x)
        (normalMapToNormal_surjective (hrank x hx)) (T x) : normalSpace F x) : Euclidean N) := by
    simp only [meanNormalCorrection, canonicalNormalCompletion, dite_eq_left (hrank x hx),
      LinearMap.comp_apply, Submodule.subtype_apply, normalCorrection]
    rfl
  have hp : normalPairing F (meanNormalCorrection F T) x =
      (normalMapToNormal F x).adjoint
        (normalCorrection (normalMapToNormal F x)
          (normalMapToNormal_surjective (hrank x hx)) (T x)) := by
    rw [adjoint_normalMapToNormal]
    ext i j
    change inner ℝ (meanNormalCorrection F T x) _ = _
    rw [he]
    rfl
  change (-2 : ℝ) • normalPairing F (meanNormalCorrection F T) x = _
  rw [hp, normalCorrection_strain]

/-- The singly completed physical mean field of `main:eq:mean-normal-field`.
Here `W` is the accumulated preparation and auxiliary field, and `H` is the
literal final sampled self tensor. -/
def completedMeanField (F W : Euclidean n → Euclidean N) (target H : MetricField n) :
    Euclidean n → Euclidean N :=
  W + meanNormalCorrection F (target - linearizedMetric F W - H)

/-- Smoothness of the SAME completed field used in `main:eq:mean-equation`. -/
theorem contDiffOn_completedMeanField {F W : Euclidean n → Euclidean N}
    {target H : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (htarget : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞ (completedMeanField F W target H) U :=
  hW.add (contDiffOn_meanNormalCorrection hU hF
    ((htarget.sub (AmbientResponse.contDiffOn_linearizedMetric hU hF hW)).sub hH) hi hrank)

/-- The full physical error of `main:eq:mean-equation` has exactly the
negative projected-defect sign, for the actual geometric normal map. -/
theorem completedMeanField_error_eq_projection {F W : Euclidean n → Euclidean N}
    {target H : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (htarget : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {x : Euclidean n} (hx : x ∈ U) :
    linearizedMetric F (completedMeanField F W target H) x + H x - target x =
      -(normalMapToNormal F x).ker.starProjection
        (target x - linearizedMetric F W x - H x) := by
  have hT : ContDiffOn ℝ ∞ (target - linearizedMetric F W - H) U :=
    (htarget.sub (AmbientResponse.contDiffOn_linearizedMetric hU hF hW)).sub hH
  have hn := contDiffOn_meanNormalCorrection hU hF hT hi hrank
  rw [completedMeanField, linearizedMetric_add_apply
    (((hW x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((hn x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)),
    linearizedMetric_meanNormalCorrection hU hF hT hi hrank hx,
    Submodule.starProjection_orthogonal_val]
  simp only [Pi.sub_apply]
  abel

/-- The remaining physical error in `main:eq:mean-equation` belongs to the
actual symmetric stress space. No tensor component has been discarded. -/
theorem completedMeanField_error_mem_stressSpace {F W : Euclidean n → Euclidean N}
    {target H : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (htarget : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {x : Euclidean n} (hx : x ∈ U)
    (htargetSymm : (target x).IsSymm) (hHSymm : (H x).IsSymm) :
    linearizedMetric F (completedMeanField F W target H) x + H x - target x ∈
      stressSpace F x := by
  refine ⟨((linearizedMetric_isSymm _ _ _).add hHSymm).sub htargetSymm, ?_⟩
  rw [completedMeanField_error_eq_projection hU hF hW htarget hH hi hrank hx]
  have hk := LinearMap.mem_ker.mp
    (Submodule.starProjection_apply_mem (normalMapToNormal F x).ker
      (target x - linearizedMetric F W x - H x))
  have hzero := congrArg Subtype.val hk
  change normalMap F x _ = 0 at hzero
  change normalMapLinear F x (-_) = 0
  rw [map_neg]
  change -normalMap F x _ = 0
  rw [hzero, neg_zero]

/-- The reduced-to-full transfer in `main:eq:mean-equation` for the actual
completed field and the SAME stress frame. The reduced coordinates are the
contractions of the literal uncompleted defect, with their original sign. -/
theorem completedMeanField_error_eq_inverseGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F W : Euclidean n → Euclidean N} {target H : MetricField n}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (htarget : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {x : Euclidean n} (hx : x ∈ U)
    (htargetSymm : (target x).IsSymm) (hHSymm : (H x).IsSymm)
    {Q : ι → MetricTensor n} (hQ : LinearIndependent ℝ Q)
    (hspan : (Submodule.span ℝ (Set.range Q) : Set (MetricTensor n)) = stressSpace F x) :
    linearizedMetric F (completedMeanField F W target H) x + H x - target x =
      -inverseGramReconstruction Q
        (fun j ↦ tensorPairing (Q j) (target x - linearizedMetric F W x - H x)) := by
  have hm := completedMeanField_error_mem_stressSpace
    hU hF hW htarget hH hi hrank hx htargetSymm hHSymm
  have hc (j : ι) : tensorPairing (Q j)
      (linearizedMetric F (completedMeanField F W target H) x + H x - target x) =
        -tensorPairing (Q j) (target x - linearizedMetric F W x - H x) := by
    have hj : Q j ∈ stressSpace F x := by
      rw [← hspan]
      exact Submodule.subset_span (Set.mem_range_self j)
    have hjker : Q j ∈ (normalMapToNormal F x).ker := by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact hj.2
    rw [completedMeanField_error_eq_projection hU hF hW htarget hH hi hrank hx]
    change inner ℝ (Q j) (-_) = -inner ℝ (Q j) _
    rw [inner_neg_right, ← Submodule.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff).mpr hjker]
  rw [stressTensor_eq_inverseGram hQ hspan hm, inverseGramReconstruction_eq_sum]
  simp only [hc, stressGram_eq_gram, mul_neg, neg_smul, Finset.sum_neg_distrib]

/-- The actual physical mean error is controlled by the reduced residual
and the SAME inverse Gram matrix (`main:eq:mean-equation`). This is the
pointwise transfer used after `main:lem:mean-recurrence`. -/
theorem completedMeanField_error_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F W : Euclidean n → Euclidean N} {target H : MetricField n}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (htarget : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {x : Euclidean n} (hx : x ∈ U)
    (htargetSymm : (target x).IsSymm) (hHSymm : (H x).IsSymm)
    {Q : ι → MetricTensor n} (hQ : LinearIndependent ℝ Q)
    (hspan : (Submodule.span ℝ (Set.range Q) : Set (MetricTensor n)) = stressSpace F x) :
    ‖linearizedMetric F (completedMeanField F W target H) x + H x - target x‖ ≤
      ∑ i, ∑ j, |(stressGram Q)⁻¹ i j| *
        |tensorPairing (Q j) (target x - linearizedMetric F W x - H x)| * ‖Q i‖ := by
  rw [completedMeanField_error_eq_inverseGram
    hU hF hW htarget hH hi hrank hx htargetSymm hHSymm hQ hspan, norm_neg]
  exact norm_inverseGramReconstruction_le Q _

/-- The physical coarse/fine split in `main:eq:mean-coarse-size` and
`main:eq:mean-fine-size` uses one completion, with the same immersion and
coarse self tensor. The equality holds on the domain where both fields are
differentiable; no global derivative of an unspecified extension is used. -/
theorem completedMeanField_eq_coarse_add_fine
    (F Vc Va : Euclidean n → Euclidean N) (target H Hc : MetricField n)
    {x : Euclidean n} (hVc : DifferentiableAt ℝ Vc x) (hVa : DifferentiableAt ℝ Va x) :
    completedMeanField F (Vc + Va) target H x =
      (Vc x + (1 / 2 : ℝ) • canonicalNormalCompletion F x
        (linearizedMetric F Vc x + Hc x)) +
      (Va x - (1 / 2 : ℝ) • canonicalNormalCompletion F x
        (target x - linearizedMetric F Va x - (H x - Hc x))) := by
  simp only [completedMeanField, meanNormalCorrection, Pi.add_apply, Pi.sub_apply,
    linearizedMetric_add_apply hVc hVa, map_sub, map_add, neg_smul, smul_sub, smul_add]
  abel

end JanetCartan.CurrentMean
