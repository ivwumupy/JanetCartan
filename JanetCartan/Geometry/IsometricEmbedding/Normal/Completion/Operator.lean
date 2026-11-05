module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.NormalMap
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Inverting the ambient normal operator

The fixed-space realization of canonical normal completion in
`app:ch_waves:eq:ambient-normal-inverse`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.AmbientResponse

/-- The extended adjoint in `app:ch_waves:eq:ambient-normal-inverse` is the
actual second-form pairing on every ambient vector. -/
theorem adjoint_normalMapLinear {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) :
    (normalMapLinear F x).adjoint w =
      normalPairing F (fun _ ↦ w) x := by
  apply ext_inner_right ℝ
  intro H
  rw [LinearMap.adjoint_inner_left]
  change inner ℝ w (normalMap F x H) =
    tensorPairing (normalPairing F (fun _ ↦ w) x) H
  rw [inner_normalMap_eq_tensorPairing F (fun _ ↦ w)]
  exact real_inner_comm _ H

/-- The invertible ambient operator `BB* + P_tan` from
`app:ch_waves:eq:ambient-normal-inverse`. -/
def ambientNormalOperator {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : Euclidean N →L[ℝ] Euclidean N :=
  ((normalMapLinear F x).comp (normalMapLinear F x).adjoint).toContinuousLinearMap +
    tangentProjection F x

/-- The action of the ambient operator in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem ambientNormalOperator_apply {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) :
    ambientNormalOperator F x w =
      normalMap F x (normalPairing F (fun _ ↦ w) x) + tangentProjection F x w := by
  change normalMap F x ((normalMapLinear F x).adjoint w) + tangentProjection F x w = _
  rw [adjoint_normalMapLinear]

/-- Full normal rank makes the ambient operator in
`app:ch_waves:eq:ambient-normal-inverse` injective on both orthogonal summands. -/
theorem ambientNormalOperator_injective {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n}
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    Function.Injective (ambientNormalOperator F x) := by
  apply (injective_iff_map_eq_zero (ambientNormalOperator F x)).mpr
  intro w hw
  have ht : tangentProjection F x w = 0 := by
    have h := congrArg (tangentProjection F x) hw
    simpa only [ambientNormalOperator_apply, map_add, tangentProjection_normalMap,
      tangentProjection_idempotent, map_zero, zero_add] using h
  have hn : w ∈ normalSpace F x :=
    (Submodule.starProjection_apply_eq_zero_iff _).mp ht
  have hz : NormalInverse.normalOperator (normalMapToNormal F x) ⟨w, hn⟩ = 0 := by
    apply Subtype.ext
    change normalMap F x ((normalMapToNormal F x).adjoint ⟨w, hn⟩) = 0
    rw [adjoint_normalMapToNormal]
    simpa only [ambientNormalOperator_apply, ht, add_zero] using hw
  have he := (NormalInverse.normalOperator_bijective (normalMapToNormal F x)
    (normalMapToNormal_surjective hrank)).1 (hz.trans (map_zero _).symm)
  exact congrArg Subtype.val he

/-- Full normal rank gives an actual unit, without any inverse identity as a
hypothesis (`app:ch_waves:eq:ambient-normal-inverse`). -/
theorem ambientNormalOperator_isUnit {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n}
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    IsUnit (ambientNormalOperator F x) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨ambientNormalOperator_injective hrank,
    LinearMap.injective_iff_surjective.mp (ambientNormalOperator_injective hrank)⟩

/-- The existing canonical normal completion solves the ambient equation in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem ambientNormalOperator_canonicalNormalCompletion {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (H : MetricTensor n) :
    ambientNormalOperator F x (canonicalNormalCompletion F x H) = normalMap F x H := by
  rw [ambientNormalOperator_apply, canonicalNormalCompletion_normal_equation hrank,
    tangentProjection_eq_zero_of_mem_normalSpace
      (canonicalNormalCompletion_mem_normalSpace F x H), add_zero]

/-- The canonical completion from `main:eq:normal-completion` is exactly the
fixed ambient inverse formula of `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem canonicalNormalCompletion_eq_ambient_inverse {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (H : MetricTensor n) :
    canonicalNormalCompletion F x H =
      Ring.inverse (ambientNormalOperator F x) (normalMap F x H) := by
  rw [← ambientNormalOperator_canonicalNormalCompletion hrank H]
  have h := congrArg (fun L : Euclidean N →L[ℝ] Euclidean N ↦
    L (canonicalNormalCompletion F x H))
    (Ring.inverse_mul_cancel _ (ambientNormalOperator_isUnit hrank))
  exact h.symm

end JanetCartan.AmbientResponse
