module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondForm
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothInverse
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Completion.Operator
public import JanetCartan.Analysis.Matrix.Symmetric

/-!
# The ambient normal inverse as a second-jet coefficient

The fixed-space formulas of `app:ch_waves:eq:ambient-normal-inverse`, with
invertibility proved from the actual orthogonal tangent/normal splitting.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.TensorFrobenius

namespace JanetCartan.GeometricProfile

/-- `app:ch_waves:eq:ambient-normal-inverse`: the tangent summand makes the
normal Gram operator invertible on the whole ambient space. -/
theorem isUnit_normalOperator_add_starProjection
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (B : E →L[ℝ] F) (P : Submodule ℝ F)
    (hrange : Set.range B = (Pᗮ : Set F)) :
    IsUnit (B.comp B.adjoint + P.starProjection) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  suffices hi : Function.Injective (B.comp B.adjoint + P.starProjection) from
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  have hp : P.starProjection w = 0 := by
    have h := congrArg P.starProjection hw
    have hb : P.starProjection (B (B.adjoint w)) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).mpr (by rw [← SetLike.mem_coe, ← hrange]; exact Set.mem_range_self _)
    have hid : P.starProjection (P.starProjection w) = P.starProjection w :=
      Submodule.starProjection_eq_self_iff.mpr (by simp)
    simpa only [_root_.add_apply, ContinuousLinearMap.comp_apply,
      map_add, hb, zero_add, hid, map_zero] using h
  have hb : B (B.adjoint w) = 0 := by
    simpa only [_root_.add_apply, ContinuousLinearMap.comp_apply, hp,
      add_zero] using hw
  have ha : B.adjoint w = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [ContinuousLinearMap.adjoint_inner_left, hb, inner_zero_right]
  have hn : w ∈ Pᗮ := (Submodule.starProjection_apply_eq_zero_iff _).mp hp
  have hwmem : w ∈ Set.range B := by rw [hrange]; exact hn
  obtain ⟨v, hv⟩ := hwmem
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ w w = inner ℝ (B.adjoint w) v := by
      rw [ContinuousLinearMap.adjoint_inner_left, hv]
    _ = 0 := by rw [ha, inner_zero_left]

/-- `app:ch_waves:eq:ambient-normal-inverse`: `A = BB* + P_tan`, as a
rational function of the first and second derivatives on a fixed space. -/
def secondJetAmbientOperator {n N : ℕ} (J : SecondJet (Euclidean n) (Euclidean N)) :
    Euclidean N →L[ℝ] Euclidean N :=
  (secondJetNormalMap J).comp (secondJetNormalMap J).adjoint +
    (ContinuousLinearMap.id ℝ _ - firstJetNormalProjection J.1)

/-- `app:ch_waves:eq:ambient-normal-inverse`: the ambient inverse coefficient
`Nmathsf = A⁻¹ B`, before restricting to the stress orthogonal complement. -/
def secondJetNormalInverse {n N : ℕ} (J : SecondJet (Euclidean n) (Euclidean N)) :
    MetricTensor n →L[ℝ] Euclidean N :=
  (Ring.inverse (secondJetAmbientOperator J)).comp (secondJetNormalMap J)

/-- `app:ch_waves:eq:ambient-normal-inverse`: the jet formula is the already
constructed ambient geometric operator. -/
theorem secondJetAmbientOperator_eq {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x)) :
    secondJetAmbientOperator (secondJet f x) = AmbientResponse.ambientNormalOperator f x := by
  rw [secondJetAmbientOperator, secondJetNormalMap_eq hf hi]
  have hp := firstJetNormalProjection_eq hi
  change firstJetNormalProjection (secondJet f x).1 = normalProjection f x at hp
  rw [hp]
  ext w : 1
  change _ + (w - normalProjection f x w) = _ + tangentProjection f x w
  rw [normalProjection_eq_sub_tangentProjection, sub_sub_cancel]
  rfl

/-- `app:ch_waves:eq:ambient-normal-inverse`: invertibility on a compact jet
range needs only immersion and normal rank, not an inverse identity. -/
theorem secondJetAmbientOperator_isUnit {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hi : Function.Injective J.1)
    (hrank : Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N))) :
    IsUnit (secondJetAmbientOperator J) := by
  have hp : firstJetNormalProjection J.1 =
      (LinearMap.range J.1.toLinearMap)ᗮ.starProjection := by
    have h := firstJetNormalProjection_eq (f := fun y ↦ J.1 y) (x := 0)
      (by simpa using hi)
    simpa [normalProjection, normalSpace] using h
  simp only [secondJetAmbientOperator, hp,
    ← Submodule.starProjection_orthogonal, Submodule.orthogonal_orthogonal]
  exact isUnit_normalOperator_add_starProjection _ _ hrank

/-- `app:ch_waves:eq:ambient-normal-inverse`: the ambient operator is smooth
on the immersive jet domain. -/
theorem contDiffAt_secondJetAmbientOperator {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : IsUnit (firstJetMetric J.1)) :
    ContDiffAt ℝ ∞ (@secondJetAmbientOperator n N) J := by
  have hB := contDiffAt_secondJetNormalMap hJ
  exact (hB.clm_comp (NormalInverse.contDiff_adjoint.contDiffAt.comp J hB)).add
    (contDiffAt_const.sub ((contDiffAt_firstJetNormalProjection hJ).comp J contDiffAt_fst))

/-- `app:ch_waves:eq:ambient-normal-inverse`: inversion is smooth near each
nondegenerate second jet. -/
theorem contDiffAt_secondJetNormalInverse {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : IsUnit (firstJetMetric J.1))
    (hA : IsUnit (secondJetAmbientOperator J)) :
    ContDiffAt ℝ ∞ (@secondJetNormalInverse n N) J := by
  have hinv : ContDiffAt ℝ ∞ Ring.inverse (secondJetAmbientOperator J) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hA.unit
  exact (hinv.comp J (contDiffAt_secondJetAmbientOperator hJ)).clm_comp
    (contDiffAt_secondJetNormalMap hJ)

/-- `app:ch_waves:eq:reconstruction`: the completion map supplied to the
existing reconstruction is exactly the ambient second-jet inverse. -/
theorem secondJetNormalInverse_eq_canonicalNormalCompletion {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N))) :
    (secondJetNormalInverse (secondJet f x)).toLinearMap =
      AmbientResponse.canonicalNormalCompletion f x := by
  ext H : 1
  change Ring.inverse (secondJetAmbientOperator (secondJet f x))
    (secondJetNormalMap (secondJet f x) H) = _
  rw [secondJetAmbientOperator_eq hf hi, secondJetNormalMap_eq hf hi]
  exact (AmbientResponse.canonicalNormalCompletion_eq_ambient_inverse hrank H).symm

end JanetCartan.GeometricProfile
