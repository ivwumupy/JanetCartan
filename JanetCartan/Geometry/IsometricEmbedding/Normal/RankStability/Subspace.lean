module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.RankStability.Operator
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Identifying nearby normal spaces

The fixed-space identification needed for `main:prop:seed` and
`app:ch_seed:setup:seed-current`: restriction of orthogonal projection is an
isomorphism between two subspaces whenever their ambient projections differ
by less than one in operator norm. No equality of the subspaces is assumed.
-/

@[expose] public noncomputable section

namespace JanetCartan.NormalRankStability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- `app:ch_seed:setup:seed-current`: projection from a moving subspace
to a fixed one, retaining the actual subspace types. -/
def projectionBetween (P Q : Submodule ℝ V) : P →L[ℝ] Q :=
  Q.orthogonalProjectionOnto.comp P.subtypeL

/-- `main:prop:seed`: the quantitative lower bound for the normal-space
identification, with loss equal to the distance between the projections. -/
theorem projectionBetween_lower_bound (P Q : Submodule ℝ V) (v : P) :
    (1 - ‖Q.starProjection - P.starProjection‖) * ‖v‖ ≤
      ‖projectionBetween P Q v‖ := by
  have h := (P.starProjection - Q.starProjection).le_opNorm (v : V)
  rw [sub_apply,
    Submodule.starProjection_eq_self_iff.mpr v.property, norm_sub_rev P.starProjection] at h
  have ht := norm_sub_norm_le (v : V) (Q.starProjection v)
  change (1 - ‖Q.starProjection - P.starProjection‖) * ‖(v : V)‖ ≤
    ‖Q.starProjection v‖
  nlinarith

/-- `main:prop:seed`: nearby orthogonal projection is injective on the
original normal space. -/
theorem projectionBetween_injective (P Q : Submodule ℝ V)
    (hclose : ‖Q.starProjection - P.starProjection‖ < 1) :
    Function.Injective (projectionBetween P Q) := by
  apply (injective_iff_map_eq_zero _).2
  intro v hv
  have h := projectionBetween_lower_bound P Q v
  rw [hv, norm_zero] at h
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp this

/-- `main:prop:seed`: nearby normal spaces have equal dimension and
restricted projection is onto, proved using injection in both directions. -/
theorem projectionBetween_bijective (P Q : Submodule ℝ V)
    (hclose : ‖Q.starProjection - P.starProjection‖ < 1) :
    Function.Bijective (projectionBetween P Q) := by
  have hi := projectionBetween_injective P Q hclose
  have hj := projectionBetween_injective Q P (by rwa [norm_sub_rev])
  have hdim : Module.finrank ℝ P = Module.finrank ℝ Q :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective
      (f := (projectionBetween P Q).toLinearMap) hi)
      (LinearMap.finrank_le_finrank_of_injective
        (f := (projectionBetween Q P).toLinearMap) hj)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

/-- `app:ch_seed:setup:seed-current`: an actual continuous linear
identification of the two normal spaces, given by orthogonal projection. -/
def projectionEquiv (P Q : Submodule ℝ V)
    (hclose : ‖Q.starProjection - P.starProjection‖ < 1) : P ≃L[ℝ] Q :=
  (LinearEquiv.ofBijective (projectionBetween P Q).toLinearMap
    (projectionBetween_bijective P Q hclose)).toContinuousLinearEquiv

/-- `app:ch_seed:setup:seed-current`: the identification is the specified
projection, rather than an arbitrary choice of basis. -/
@[simp] theorem projectionEquiv_apply (P Q : Submodule ℝ V)
    (hclose : ‖Q.starProjection - P.starProjection‖ < 1) (v : P) :
    projectionEquiv P Q hclose v = Q.orthogonalProjectionOnto v := rfl

/-- `main:prop:seed`: explicit distortion bound for the inverse
identification of nearby normal spaces. -/
theorem projectionEquiv_symm_bound (P Q : Submodule ℝ V)
    (hclose : ‖Q.starProjection - P.starProjection‖ < 1) (w : Q) :
    (1 - ‖Q.starProjection - P.starProjection‖) *
      ‖(projectionEquiv P Q hclose).symm w‖ ≤ ‖w‖ := by
  have h := projectionBetween_lower_bound P Q ((projectionEquiv P Q hclose).symm w)
  change (1 - ‖Q.starProjection - P.starProjection‖) *
    ‖(projectionEquiv P Q hclose).symm w‖ ≤
      ‖projectionEquiv P Q hclose ((projectionEquiv P Q hclose).symm w)‖ at h
  simpa using h

/-- `app:ch_seed:setup:seed-current`: the fixed-space identification by
orthogonal projection has operator norm at most one. -/
theorem projectionBetween_norm_le (P Q : Submodule ℝ V) :
    ‖projectionBetween P Q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa [projectionBetween] using Q.norm_orthogonalProjectionOnto_apply_le (v : V)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- `app:ch_seed:setup:seed-current`: an adjoint gap for the projected
map on a fixed normal space gives the same gap on the actual normal space.
The proof uses the adjoint of the proved identification, not a constant-space
assumption. -/
theorem adjoint_lower_bound_of_projection (P Q : Submodule ℝ V)
    (hclose : ‖P.starProjection - Q.starProjection‖ < 1)
    (B : E →L[ℝ] Q) {κ : ℝ} (hκ : 0 ≤ κ)
    (hgap : ∀ y, κ * ‖y‖ ≤ ‖((projectionBetween Q P).comp B).adjoint y‖) :
    ∀ z, κ * ‖z‖ ≤ ‖B.adjoint z‖ := by
  let T := projectionBetween Q P
  have hi := projectionBetween_injective Q P hclose
  have hs : Function.Surjective T.adjoint :=
    (surjective_iff_adjoint_injective T.adjoint).mpr (by simpa [T] using hi)
  intro z
  obtain ⟨y, rfl⟩ := hs z
  have hn : ‖T.adjoint y‖ ≤ ‖y‖ := by
    calc
      ‖T.adjoint y‖ ≤ ‖T.adjoint‖ * ‖y‖ := T.adjoint.le_opNorm y
      _ = ‖T‖ * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (projectionBetween_norm_le Q P)
        (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  exact (mul_le_mul_of_nonneg_left hn hκ).trans (by
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] using hgap y)

/-- `main:prop:seed`: quantitative rank and Gram stability with varying
normal spaces. Compare the normal maps only after the explicit projection
to the reference normal space; the resulting Gram bound holds on the actual
new normal space with its induced Euclidean inner product. -/
theorem surjective_and_normal_gap_of_projected_norm_sub_le
    (P Q : Submodule ℝ V) (B : E →L[ℝ] P) (C : E →L[ℝ] Q)
    {κ : ℝ} (hκ : 0 < κ) (hgap : ∀ y, κ * ‖y‖ ≤ ‖B.adjoint y‖)
    (hproj : ‖P.starProjection - Q.starProjection‖ < 1)
    (hclose : ‖(projectionBetween Q P).comp C - B‖ ≤ κ / 2) :
    Function.Surjective C ∧ ∀ y,
      (κ ^ 2 / 4) * ‖y‖ ^ 2 ≤ inner ℝ (NormalPerturbation.normal C y) y := by
  have hb (y : P) : κ / 2 * ‖y‖ ≤
      ‖((projectionBetween Q P).comp C).adjoint y‖ := by
    have h := adjoint_lower_bound_sub_norm B ((projectionBetween Q P).comp C) hgap y
    have hm := mul_le_mul_of_nonneg_right hclose (norm_nonneg y)
    nlinarith
  have hc := adjoint_lower_bound_of_projection P Q hproj C (by positivity) hb
  convert surjective_and_normal_gap_of_adjoint_lower_bound C (by positivity) hc using 1
  ring_nf

end JanetCartan.NormalRankStability
