module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.Linearity
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Variation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.Regularity

/-!
# Full ambient strain reconstruction

The geometric and tensor algebra in `main:eq:completion-error` and
`app:ch_response:prop:response-ambient`. The reconstruction theorem below applies
to the actual canonical normal completion, whose normal equation and smoothness
are proved from full normal rank and immersion.
The reduced solver identity is the stated analytic input; this module does not
construct that solver.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.AmbientResponse

/-- The linearized metric is a symmetric tensor, as required in
`main:eq:completion-error`. -/
theorem linearizedMetric_isSymm {n N : ℕ} (F Y : Euclidean n → Euclidean N)
    (x : Euclidean n) : (linearizedMetric F Y x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [linearizedMetric, real_inner_comm (partialDeriv F x j),
    real_inner_comm (partialDeriv Y x j)]
  exact add_comm _ _

/-- The full tangent–normal formula `main:eq:tangent-normal`, assembled from
the checked tangential and normal variation theorems. -/
theorem linearizedMetric_tangent_add_normal {n N : ℕ}
    {F w : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hw : ContDiffOn ℝ ∞ w s) (himm : IsImmersionOn F s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x) :
    EqOn (linearizedMetric F (tangentLift F u + w))
      ((2 : ℝ) • symmCovariantDeriv F u - (2 : ℝ) • normalPairing F w) s := by
  intro x hx
  have hT := (((contDiffOn_tangentLift hs hF hu himm) x hx).contDiffAt
    (hs.mem_nhds hx)).differentiableAt (by simp)
  have hwx := ((hw x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hadd : linearizedMetric F (tangentLift F u + w) x =
      linearizedMetric F (tangentLift F u) x + linearizedMetric F w x := by
    ext i j
    simp only [linearizedMetric, partialDeriv, fderiv_add hT hwx,
      add_apply, inner_add_left, inner_add_right, Matrix.add_apply]
    ring
  rw [hadd, linearizedMetric_tangentLift hs hF hu himm hx,
    linearizedMetric_normal hs hF hw hnormal hx]
  simp only [Pi.smul_apply, Pi.sub_apply, neg_smul, sub_eq_add_neg, two_smul, Pi.add_apply]

/-- A solution of the actual normal equation leaves an error in the actual
stress space (`main:eq:normal-completion`). This is the algebraic input for
full tensor reconstruction; no quotient identity is used. -/
theorem strain_error_mem_stressSpace {n N : ℕ}
    {F w : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hw : ContDiffOn ℝ ∞ w s) (himm : IsImmersionOn F s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x)
    {x : Euclidean n} (hx : x ∈ s) (hh : (h x).IsSymm)
    (heq : normalMap F x (normalPairing F w x) =
      normalMap F x (symmCovariantDeriv F u x - (1 / 2 : ℝ) • h x)) :
    linearizedMetric F (tangentLift F u + w) x - h x ∈ stressSpace F x := by
  refine ⟨(linearizedMetric_isSymm _ _ _).sub hh, ?_⟩
  have hstrain := linearizedMetric_tangent_add_normal hs hF hu hw himm hnormal hx
  have hid : linearizedMetric F (tangentLift F u + w) x - h x =
      (2 : ℝ) • (symmCovariantDeriv F u x - (1 / 2 : ℝ) • h x -
        normalPairing F w x) := by
    rw [hstrain]
    ext i j
    simp only [Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hid]
  change normalMapLinear F x ((2 : ℝ) • _) = 0
  rw [map_smul, map_sub]
  change (2 : ℝ) • (normalMap F x _ - normalMap F x _) = 0
  rw [heq, sub_self, smul_zero]

/-- The full error formula `main:eq:completion-error` for a smooth solution of
the normal equation. The canonical specialization below discharges normality,
the normal equation, and regularity from the geometric hypotheses. -/
theorem strain_error_eq_inverseGram {n N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {F w : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hw : ContDiffOn ℝ ∞ w s) (himm : IsImmersionOn F s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x)
    {x : Euclidean n} (hx : x ∈ s) (hh : (h x).IsSymm)
    (heq : normalMap F x (normalPairing F w x) =
      normalMap F x (symmCovariantDeriv F u x - (1 / 2 : ℝ) • h x))
    {Q : ι → MetricTensor n} (hQ : LinearIndependent ℝ Q)
    (hspan : (Submodule.span ℝ (Set.range Q) : Set (MetricTensor n)) = stressSpace F x) :
    linearizedMetric F (tangentLift F u + w) x - h x =
      (2 : ℝ) • ∑ i, ∑ j, ((stressGram Q)⁻¹ i j *
        (tensorPairing (Q j) (symmCovariantDeriv F u x) -
          (1 / 2 : ℝ) * tensorPairing (Q j) (h x))) • Q i := by
  have hmem := strain_error_mem_stressSpace hs hF hu hw himm hnormal hx hh heq
  have hzero (j : ι) : tensorPairing (Q j) (normalPairing F w x) = 0 := by
    have hQj : Q j ∈ stressSpace F x := by
      rw [← hspan]
      exact Submodule.subset_span (Set.mem_range_self j)
    rw [← inner_normalMap_eq_tensorPairing, hQj.2, inner_zero_right]
  have hc (j : ι) :
      tensorPairing (Q j) (linearizedMetric F (tangentLift F u + w) x - h x) =
        2 * (tensorPairing (Q j) (symmCovariantDeriv F u x) -
          (1 / 2 : ℝ) * tensorPairing (Q j) (h x)) := by
    rw [linearizedMetric_tangent_add_normal hs hF hu hw himm hnormal hx]
    change inner ℝ (Q j) ((2 : ℝ) • symmCovariantDeriv F u x -
        (2 : ℝ) • normalPairing F w x - h x) = _
    simp only [inner_sub_right, inner_smul_right]
    change 2 * tensorPairing (Q j) _ - 2 * tensorPairing (Q j) _ -
      tensorPairing (Q j) _ = _
    rw [hzero]
    ring
  rw [stressTensor_eq_inverseGram hQ hspan hmem]
  simp only [hc, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- The tangential lift plus the canonical normal correction from
`main:eq:normal-completion`. By linearity of `canonicalNormalCompletion`, this
is the field `V_G(u) - (1/2) N_G h` in `app:ch_response:eq:response-full-map`. -/
def completedVariation {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) (h : MetricField n) : Euclidean n → Euclidean N :=
  tangentLift F u + fun x ↦ canonicalNormalCompletion F x
    (symmCovariantDeriv F u x - (1 / 2 : ℝ) • h x)

/-- The exact sign and factor in the response map
`app:ch_response:eq:response-full-map`. -/
theorem completedVariation_eq {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) (h : MetricField n) :
    completedVariation F u h =
      (tangentLift F u + fun x ↦ canonicalNormalCompletion F x (symmCovariantDeriv F u x)) -
        (1 / 2 : ℝ) • (fun x ↦ canonicalNormalCompletion F x (h x)) := by
  funext x
  simp only [completedVariation, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_sub, map_smul]
  abel

/-- Full-tensor reconstruction with the complete signed residual
`(A_Γ - I) z` from `app:ch_response:eq:response-full-identity`.

The analytic premise is exactly `app:ch_regular:eq:exact-physical` at the
observation point. The normal equation and normality are proved for the actual
canonical inverse. Its smoothness is proved from the smooth input fields,
immersion, and full normal rank. -/
theorem completedVariation_error_eq_full_residual {n N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hhSmooth : ContDiffOn ℝ ∞ h s)
    {x : Euclidean n} (hx : x ∈ s) (hh : (h x).IsSymm)
    {Q : ι → MetricTensor n} (hQ : LinearIndependent ℝ Q)
    (hspan : (Submodule.span ℝ (Set.range Q) : Set (MetricTensor n)) = stressSpace F x)
    (z : Euclidean n → ι → ℝ)
    (A : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ))
    (hphysical : ∀ j, tensorPairing (Q j) (symmCovariantDeriv F u x) =
      (1 / 2 : ℝ) * tensorPairing (Q j) (h x) + (A z x j - z x j)) :
    linearizedMetric F (completedVariation F u h) x - h x =
      (2 : ℝ) • ∑ i, ∑ j, ((stressGram Q)⁻¹ i j * (A z x j - z x j)) • Q i := by
  have hw := contDiffOn_canonicalNormalCompletion hs hF
    ((contDiffOn_symmCovariantDeriv hs hF hu himm).sub (hhSmooth.const_smul (1 / 2 : ℝ)))
    himm hrank
  have heq := strain_error_eq_inverseGram hs hF hu hw himm
    (fun y _ ↦ canonicalNormalCompletion_mem_normalSpace F y _) hx hh
    (canonicalNormalCompletion_normal_equation (hrank x hx) _) hQ hspan
  change linearizedMetric F (completedVariation F u h) x - h x = _ at heq
  rw [heq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hphysical, add_sub_cancel_left]

/-- Smoothness of the actual field in `app:ch_response:eq:response-full-map`.
The canonical correction's smoothness follows from full normal rank. -/
theorem contDiffOn_completedVariation {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hh : ContDiffOn ℝ ∞ h s) (himm : IsImmersionOn F s)
    (hrank : HasFullNormalRankOn F s) :
    ContDiffOn ℝ ∞ (completedVariation F u h) s :=
  (contDiffOn_tangentLift hs hF hu himm).add
    (contDiffOn_canonicalNormalCompletion hs hF
      ((contDiffOn_symmCovariantDeriv hs hF hu himm).sub (hh.const_smul (1 / 2 : ℝ)))
      himm hrank)

/-- Additivity of the actual completion in `app:ch_response:eq:response-full-map`
at every point where the two reduced solutions are differentiable. -/
theorem completedVariation_add_apply {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u v : Euclidean n → Euclidean n} (h k : MetricField n) {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    completedVariation F (u + v) (h + k) x =
      completedVariation F u h x + completedVariation F v k x := by
  simp only [completedVariation, tangentLift_add, Pi.add_apply,
    symmCovariantDeriv_add_apply F hu hv, smul_add]
  rw [show symmCovariantDeriv F u x + symmCovariantDeriv F v x -
      ((1 / 2 : ℝ) • h x + (1 / 2 : ℝ) • k x) =
      (symmCovariantDeriv F u x - (1 / 2 : ℝ) • h x) +
      (symmCovariantDeriv F v x - (1 / 2 : ℝ) • k x) by abel, map_add]
  abel

/-- Real homogeneity of the actual completion in
`app:ch_response:eq:response-full-map`. -/
theorem completedVariation_smul_apply {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → Euclidean n} (h : MetricField n) {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (a : ℝ) :
    completedVariation F (a • u) (a • h) x = a • completedVariation F u h x := by
  simp only [completedVariation, tangentLift_smul, Pi.add_apply, Pi.smul_apply,
    symmCovariantDeriv_smul_apply F hu a]
  rw [smul_comm (1 / 2 : ℝ) a, ← smul_sub, map_smul, smul_add]

/-- The reduced source `e_i = (1/2) Q_i : h` in
`app:ch_response:eq:response-full-map`, for a spatially varying stress frame. -/
def stressSource {n : ℕ} {ι : Type*} (Q : Euclidean n → ι → MetricTensor n) :
    MetricField n →ₗ[ℝ] (Euclidean n → ι → ℝ) where
  toFun h x i := (1 / 2 : ℝ) * tensorPairing (Q x i) (h x)
  map_add' h k := by
    ext x i
    change (1 / 2 : ℝ) * inner ℝ (Q x i) (h x + k x) = _
    simp only [inner_add_right, mul_add, Pi.add_apply]
    rfl
  map_smul' a h := by
    ext x i
    change (1 / 2 : ℝ) * inner ℝ (Q x i) (a • h x) = _
    simp only [inner_smul_right, Pi.smul_apply, smul_eq_mul]
    change (1 / 2 : ℝ) * (a * tensorPairing (Q x i) (h x)) =
      a * ((1 / 2 : ℝ) * tensorPairing (Q x i) (h x))
    ring

/-- The source cutoff in `app:ch_response:eq:response-full-map`. -/
def cutoffSource {n : ℕ} {ι : Type*} (χ : Euclidean n → ℝ) :
    (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ) where
  toFun e x := χ x • e x
  map_add' e f := by ext x i; simp [mul_add]
  map_smul' a e := by ext x i; simp [mul_left_comm]

/-- The same complete corrected source `z = T (χ₂ e)` for every residual
component in `app:ch_response:eq:response-full-identity`. -/
def correctedStressSource {n : ℕ} {ι : Type*}
    (Q : Euclidean n → ι → MetricTensor n) (χ : Euclidean n → ℝ)
    (T : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ)) :
    MetricField n →ₗ[ℝ] (Euclidean n → ι → ℝ) :=
  T.comp ((cutoffSource χ).comp (stressSource Q))

/-- The actual ambient response in `app:ch_response:eq:response-full-map`.
The real linear solver and source inverse are analytic inputs. -/
def ambientResponse {n N : ℕ} {ι : Type*} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → ι → MetricTensor n) (χ : Euclidean n → ℝ)
    (T : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ))
    (S : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (h : MetricField n) : Euclidean n → Euclidean N :=
  completedVariation F (S (correctedStressSource Q χ T h)) h

/-- The reduced source retains the tensor source's support, as required in
`app:ch_response:prop:response-ambient`. -/
theorem support_stressSource_subset {n : ℕ} {ι : Type*}
    (Q : Euclidean n → ι → MetricTensor n) (h : MetricField n) :
    Function.support (stressSource Q h) ⊆ Function.support h := by
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  ext i
  change (1 / 2 : ℝ) * tensorPairing (Q x i) (h x) = 0
  rw [hx]
  change (1 / 2 : ℝ) * inner ℝ (Q x i) 0 = 0
  simp

/-- Smoothness of the reduced source in `app:ch_response:eq:response-full-map`. -/
theorem contDiffOn_stressSource {n : ℕ} {ι : Type*} [Fintype ι]
    {Q : Euclidean n → ι → MetricTensor n} {h : MetricField n}
    {s : Set (Euclidean n)} (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) s)
    (hh : ContDiffOn ℝ ∞ h s) : ContDiffOn ℝ ∞ (stressSource Q h) s := by
  apply contDiffOn_pi.mpr
  intro i
  exact ((hQ i).inner ℝ hh).const_smul (1 / 2 : ℝ)

/-- The source cutoff fixes the whole reduced source for the supported tensors
in `app:ch_response:prop:response-ambient`. -/
theorem cutoffSource_stressSource_eq {n : ℕ} {ι : Type*}
    (Q : Euclidean n → ι → MetricTensor n) (χ : Euclidean n → ℝ)
    (h : MetricField n) (hh : Function.support h ⊆ {x | χ x = 1}) :
    cutoffSource χ (stressSource Q h) = stressSource Q h := by
  funext x
  by_cases hx : x ∈ Function.support h
  · change χ x • stressSource Q h x = stressSource Q h x
    rw [hh hx, one_smul]
  · have hz : stressSource Q h x = 0 := by
      by_contra hn
      exact hx (support_stressSource_subset Q h hn)
    change χ x • stressSource Q h x = stressSource Q h x
    rw [hz, smul_zero]

/-- The response of `app:ch_response:prop:response-ambient` is one real linear
map on any source subspace whose solved covectors are differentiable on the
chart. Its values are the restrictions of the actual ambient field; no global
regularity outside the chart is assumed. -/
def ambientResponseLinear {n N : ℕ} {ι : Type*} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → ι → MetricTensor n) (χ : Euclidean n → ℝ)
    (T : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ))
    (S : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (D : Submodule ℝ (MetricField n)) (s : Set (Euclidean n))
    (hS : ∀ h : D, ∀ x ∈ s, DifferentiableAt ℝ
      (S (correctedStressSource Q χ T h)) x) : D →ₗ[ℝ] (s → Euclidean N) where
  toFun h x := ambientResponse F Q χ T S h x
  map_add' h k := by
    funext x
    change completedVariation F (S (correctedStressSource Q χ T (↑h + ↑k)))
      (↑h + ↑k) x = _
    rw [map_add, map_add]
    exact completedVariation_add_apply F h k (hS h x x.property) (hS k x x.property)
  map_smul' a h := by
    funext x
    change completedVariation F (S (correctedStressSource Q χ T (a • ↑h)))
      (a • ↑h) x = _
    rw [map_smul, map_smul]
    exact completedVariation_smul_apply F h (hS h x x.property) a

/-- Smoothness of the response field in `app:ch_response:eq:response-full-map`.
Only smoothness of the reduced solution remains an analytic input. -/
theorem contDiffOn_ambientResponse {n N : ℕ} {ι : Type*}
    {F : Euclidean n → Euclidean N} (Q : Euclidean n → ι → MetricTensor n)
    (χ : Euclidean n → ℝ)
    (T : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ))
    (S : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hh : ContDiffOn ℝ ∞ h s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hS : ContDiffOn ℝ ∞ (S (correctedStressSource Q χ T h)) s) :
    ContDiffOn ℝ ∞ (ambientResponse F Q χ T S h) s :=
  contDiffOn_completedVariation hs hF hS hh himm hrank

/-- The full tensor identity `app:ch_response:eq:response-full-identity` for the
literal source `z = T (χ₂ e)`. The sole residual identity input is the reduced
solver's `app:ch_regular:eq:exact-physical` for this supported source.
The cutoff is removed from the leading source term using its support hypothesis.
The geometric completion, its regularity, and the stress reconstruction are
proved here, and the entire signed residual uses this same `z`. -/
theorem ambientResponse_error_eq_full_residual {n N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {F : Euclidean n → Euclidean N} (Q : Euclidean n → ι → MetricTensor n)
    (χ : Euclidean n → ℝ)
    (T A : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ))
    (S : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hh : ContDiffOn ℝ ∞ h s)
    (hsymm : ∀ x ∈ s, (h x).IsSymm)
    (hsupport : Function.support h ⊆ {x | χ x = 1})
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hQ : ∀ x ∈ s, LinearIndependent ℝ (Q x))
    (hspan : ∀ x ∈ s,
      (Submodule.span ℝ (Set.range (Q x)) : Set (MetricTensor n)) = stressSpace F x)
    (hS : ContDiffOn ℝ ∞ (S (correctedStressSource Q χ T h)) s)
    (hphysical : ∀ x ∈ s, ∀ j,
      tensorPairing (Q x j)
        (symmCovariantDeriv F (S (correctedStressSource Q χ T h)) x) =
        cutoffSource χ (stressSource Q h) x j +
          (A (correctedStressSource Q χ T h) x j - correctedStressSource Q χ T h x j)) :
    EqOn (linearizedMetric F (ambientResponse F Q χ T S h) - h)
      (fun x ↦ (2 : ℝ) • ∑ i, ∑ j, ((stressGram (Q x))⁻¹ i j *
        (A (correctedStressSource Q χ T h) x j - correctedStressSource Q χ T h x j)) •
          Q x i) s := by
  rw [cutoffSource_stressSource_eq Q χ h hsupport] at hphysical
  intro x hx
  exact completedVariation_error_eq_full_residual hs hF hS himm hrank hh hx
    (hsymm x hx) (hQ x hx) (hspan x hx) (correctedStressSource Q χ T h) A (hphysical x hx)

end JanetCartan.AmbientResponse
