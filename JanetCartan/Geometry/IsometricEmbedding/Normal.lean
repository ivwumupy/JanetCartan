module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient

/-!
# Completed normal statements

The original manuscript statements, assembled from their constructive leaf proofs.
Shared definitions live in `Normal/Defs.lean` to keep the import graph acyclic.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan

/-- Equation main:eq:tangent-normal, using the connection of γ(F). -/
theorem linearizedMetric_tangentLift_add {n N : ℕ}
    {F w : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hw : ContDiffOn ℝ ∞ w s) (himm : IsImmersionOn F s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x) :
    EqOn (linearizedMetric F (tangentLift F u + w))
      (2 • symmCovariantDeriv F u - 2 • normalPairing F w) s := by
  simpa only [two_smul] using
    AmbientResponse.linearizedMetric_tangent_add_normal hs hF hu hw himm hnormal

/-- Normal completion in Section 2: the reduced stress equations imply the full tensor equation.

The quantified orthogonality hypothesis is independent of a choice of stress frame.
-/
theorem exists_normal_completion {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {h : MetricField n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hh : ContDiffOn ℝ ∞ h s) (hsymm : ∀ x ∈ s, (h x).IsSymm)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hreduced : ∀ x ∈ s, ∀ Q ∈ stressSpace F x,
      tensorPairing Q (2 • symmCovariantDeriv F u x - h x) = 0) :
    ∃ w : Euclidean n → Euclidean N,
      ContDiffOn ℝ ∞ w s ∧ (∀ x ∈ s, w x ∈ normalSpace F x) ∧
      EqOn (linearizedMetric F (tangentLift F u + w)) h s := by
  let w : Euclidean n → Euclidean N := fun x ↦
    AmbientResponse.canonicalNormalCompletion F x
      (symmCovariantDeriv F u x - (1 / 2 : ℝ) • h x)
  have hw : ContDiffOn ℝ ∞ w s :=
    AmbientResponse.contDiffOn_canonicalNormalCompletion hs hF
      ((AmbientResponse.contDiffOn_symmCovariantDeriv hs hF hu himm).sub
        (hh.const_smul (1 / 2 : ℝ))) himm hrank
  have hnormal : ∀ x ∈ s, w x ∈ normalSpace F x :=
    fun x _ ↦ AmbientResponse.canonicalNormalCompletion_mem_normalSpace F x _
  refine ⟨w, hw, hnormal, ?_⟩
  intro x hx
  let e := linearizedMetric F (tangentLift F u + w) x - h x
  have he : e ∈ stressSpace F x :=
    AmbientResponse.strain_error_mem_stressSpace hs hF hu hw himm hnormal hx
      (hsymm x hx) (AmbientResponse.canonicalNormalCompletion_normal_equation
        (hrank x hx) _)
  have hnormalPairing : tensorPairing e (normalPairing F w x) = 0 := by
    rw [← inner_normalMap_eq_tensorPairing, he.2, inner_zero_right]
  have heq : e = (2 : ℝ) • symmCovariantDeriv F u x - h x -
      (2 : ℝ) • normalPairing F w x := by
    dsimp only [e]
    rw [AmbientResponse.linearizedMetric_tangent_add_normal hs hF hu hw himm hnormal hx]
    simp only [Pi.sub_apply, Pi.smul_apply]
    abel
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change inner ℝ e e = 0
  calc
    inner ℝ e e = inner ℝ e ((2 : ℝ) • symmCovariantDeriv F u x - h x -
        (2 : ℝ) • normalPairing F w x) := congrArg (inner ℝ e) heq
    _ = 0 := by
      rw [inner_sub_right, inner_smul_right]
      change tensorPairing e ((2 : ℝ) • symmCovariantDeriv F u x - h x) -
        2 * tensorPairing e (normalPairing F w x) = 0
      have hred : tensorPairing e ((2 : ℝ) • symmCovariantDeriv F u x - h x) = 0 := by
        simpa only [two_smul] using hreduced x hx e he
      rw [hred, hnormalPairing, mul_zero, sub_self]

end JanetCartan
