module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The linearized metric of a normal field

The normal contribution in `main:eq:tangent-normal` follows by differentiating
the orthogonality of the field to the coordinate derivatives of the immersion.
Pairing with a normal vector removes the orthogonal projection in the definition
of the second fundamental form. Symmetry of the second derivative then gives
the factor of two. This identity does not require injectivity of the differential.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set Filter Topology

namespace JanetCartan

/-- The mixed coordinate derivatives used in `main:eq:tangent-normal` commute. -/
private theorem partialDeriv_partialDeriv_comm {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ ∞ F x) (i j : Fin n) :
    partialDeriv (fun y ↦ partialDeriv F y j) x i =
      partialDeriv (fun y ↦ partialDeriv F y i) x j := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  simp only [partialDeriv, fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hF.isSymmSndFDerivAt (by simp) _ _

/-- Differentiating normality gives the sign of the normal term in
`main:eq:tangent-normal`, with the actual projected second fundamental form. -/
theorem inner_partialDeriv_normalField {n N : ℕ} {F w : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hw : ContDiffOn ℝ ∞ w s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x) {x : Euclidean n} (hx : x ∈ s)
    (i j : Fin n) :
    inner ℝ (partialDeriv w x i) (partialDeriv F x j) =
      -normalPairing F w x i j := by
  have hFx := (hF x hx).contDiffAt (hs.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fun y ↦ partialDeriv F y j) x :=
    ((hFx.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).differentiableAt
      one_ne_zero
  have hwx := ((hw x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hzero : (fun y ↦ inner ℝ (partialDeriv F y j) (w y)) =ᶠ[𝓝 x]
      (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hnormal y hy _ ⟨EuclideanSpace.single j 1, rfl⟩
  have hderiv := congrArg (fun A : Euclidean n →L[ℝ] ℝ ↦ A (EuclideanSpace.single i 1))
    hzero.fderiv_eq
  rw [fderiv_inner_apply ℝ hd hwx, fderiv_const_apply] at hderiv
  have hproj : normalPairing F w x i j =
      inner ℝ (w x) (partialDeriv (fun y ↦ partialDeriv F y j) x i) := by
    exact (normalSpace F x).inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨w x, hnormal x hx⟩ _
  rw [hproj]
  change inner ℝ (partialDeriv F x j) (partialDeriv w x i) +
    inner ℝ (partialDeriv (fun y ↦ partialDeriv F y j) x i) (w x) = 0 at hderiv
  rw [real_inner_comm (partialDeriv F x j) (partialDeriv w x i),
    real_inner_comm _ (w x)]
  exact eq_neg_of_add_eq_zero_left hderiv

/-- The normal contribution in `main:eq:tangent-normal`: a smooth normal field
has linearized metric equal to minus twice its pairing with the second fundamental form. -/
theorem linearizedMetric_normal {n N : ℕ}
    {F w : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hw : ContDiffOn ℝ ∞ w s)
    (hnormal : ∀ x ∈ s, w x ∈ normalSpace F x) :
    EqOn (linearizedMetric F w) ((-2 : ℝ) • normalPairing F w) s := by
  intro x hx
  ext i j
  have hsymm : normalPairing F w x j i = normalPairing F w x i j := by
    exact congrArg
      (fun v ↦ inner ℝ (w x) ((normalSpace F x).orthogonalProjectionOnto v : Euclidean N))
      (partialDeriv_partialDeriv_comm ((hF x hx).contDiffAt (hs.mem_nhds hx)) j i)
  change inner ℝ (partialDeriv F x i) (partialDeriv w x j) +
    inner ℝ (partialDeriv w x i) (partialDeriv F x j) =
      (-2 : ℝ) * normalPairing F w x i j
  rw [real_inner_comm (partialDeriv w x j) (partialDeriv F x i),
    inner_partialDeriv_normalField hs hF hw hnormal hx j i,
    inner_partialDeriv_normalField hs hF hw hnormal hx i j, hsymm,
    ← neg_add, ← two_mul, neg_mul]

end JanetCartan
