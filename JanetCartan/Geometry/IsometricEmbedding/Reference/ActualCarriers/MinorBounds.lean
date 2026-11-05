module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.MinorBounds.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PencilContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Compact

/-!
# Finite buffered patches with bounded minor inverses

Step 2 of `app:ch_seed:prop:seed-actual-menu` and the finite low class of
`app:ch_regular_base:thm:sector`. A positive Frobenius adjugate gap and an
upper matrix norm bound on a compact set give a finite cover by balls.
Each ball retains one ordered minor on the closed ball of twice the radius,
with a uniform positive determinant gap and an explicit inverse norm bound.

These are conditional deductions. The actual carrier construction must supply
the adjugate gap (from `SignedRegularity`) and the upper bound for its actual
current pencil. `PencilContinuity` supplies continuity for the current pencil.
No rank gap is identified with a numbered singular value.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Frobenius Topology

namespace JanetCartan.ActualCarriers

/-- The determinant threshold used on buffered minor patches in Step 2 of
`app:ch_seed:prop:seed-actual-menu`. The matrix dimension is `m+1`. -/
def minorPatchGap (m : ℕ) (a : ℝ) : ℝ := (a / (m + 1)) / 2

/-- The explicit common Frobenius bound for minor inverses in
`app:ch_regular_base:thm:sector`. The neighborhood matrix bound is `M+1`. -/
def minorPatchInverseBound (m : ℕ) (a M : ℝ) : ℝ :=
  (minorPatchGap m a)⁻¹ * (m * (m.factorial * (max 1 (M + 1)) ^ m))

/-- Positive input gaps give positive determinant thresholds on the buffered
patches (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem minorPatchGap_pos (m : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < minorPatchGap m a := by
  unfold minorPatchGap
  positivity

/-- A continuous real matrix family with a positive adjugate gap and bounded
norm on a compact set has finitely many buffered balls. Each ball has one
fixed, ordered `(n-1)` minor, an actual two-sided inverse on the doubled
closed ball, and a uniform Frobenius inverse bound. This is the concrete
minor input for `app:ch_regular_base:thm:sector` and Step 2 of
`app:ch_seed:prop:seed-actual-menu`.

The norm bound is only assumed on `K`; continuity extends it to `M+1` on
the buffered balls. No determinant bound or inverse is an input. -/
theorem exists_finite_buffered_minor_cover {X : Type*} [MetricSpace X]
    {m : ℕ} (A : X → MetricTensor (m + 1)) (hA : Continuous A)
    {K : Set X} (hK : IsCompact K) {a M : ℝ} (ha : 0 < a)
    (hgap : ∀ x ∈ K, a ≤ ‖(A x).adjugate‖)
    (hbound : ∀ x ∈ K, ‖A x‖ ≤ M) :
    ∃ t : Finset K, ∃ radius : K → ℝ,
      ∃ row col : K → Fin (m + 1),
        (∀ x, 0 < radius x) ∧
        K ⊆ ⋃ x ∈ t, Metric.ball (x : X) (radius x) ∧
        ∀ x ∈ t, ∀ y ∈ Metric.closedBall (x : X) (2 * radius x),
          minorPatchGap m a ≤ |(cofactorMinor (A y) (row x) (col x)).det| ∧
          cofactorMinor (A y) (row x) (col x) *
            (cofactorMinor (A y) (row x) (col x))⁻¹ = 1 ∧
          (cofactorMinor (A y) (row x) (col x))⁻¹ *
            cofactorMinor (A y) (row x) (col x) = 1 ∧
          ‖(cofactorMinor (A y) (row x) (col x))⁻¹‖ ≤
            minorPatchInverseBound m a M := by
  classical
  have hδ := minorPatchGap_pos m ha
  have local_patch (x : K) : ∃ r c : Fin (m + 1), ∃ ε > 0,
      ∀ y ∈ Metric.closedBall (x : X) (2 * ε),
        minorPatchGap m a ≤ |(A y).adjugate r c| ∧ ‖A y‖ ≤ M + 1 := by
    obtain ⟨r, c, hrc⟩ := exists_large_cofactor (A x) (hgap x x.property)
    have hstrict : minorPatchGap m a < |(A x).adjugate r c| := by
      have hpos : 0 < a / (m + 1 : ℝ) := by positivity
      dsimp [minorPatchGap]
      linarith
    have hopen : IsOpen {y | minorPatchGap m a < |(A y).adjugate r c| ∧
        ‖A y‖ < M + 1} :=
      (isOpen_lt continuous_const
        (((continuous_apply c).comp ((continuous_apply r).comp hA.matrix_adjugate)).abs)).inter
        (isOpen_lt hA.norm continuous_const)
    obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hopen x
      ⟨hstrict, (hbound x x.property).trans_lt (by linarith)⟩
    refine ⟨r, c, R / 3, by positivity, ?_⟩
    intro y hy
    have hy' : y ∈ Metric.ball (x : X) R := by
      rw [Metric.mem_ball]
      have := Metric.mem_closedBall.mp hy
      linarith
    exact ⟨(hsub hy').1.le, (hsub hy').2.le⟩
  choose row col radius hpos hpatch using local_patch
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : K ↦ Metric.ball (x : X) (radius x)) (fun _ ↦ Metric.isOpen_ball)
    (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hpos ⟨x, hx⟩)⟩)
  refine ⟨t, radius, row, col, hpos, ht, ?_⟩
  intro x _ y hy
  obtain ⟨hg, hM⟩ := hpatch x y hy
  refine ⟨?_, cofactorMinor_inverse_bounds (A y) (row x) (col x) hM hδ hg⟩
  rwa [abs_det_cofactorMinor]

/-- Specialization to the literal current pencil on the protected compact
angular set (`app:ch_seed:prop:seed-actual-menu`, Step 2). The producer must
supply its uniform adjugate gap and upper norm bound; all fixed minors and
buffered inverse estimates are then constructed here. -/
theorem exists_angular_pencil_minor_cover {m : ℕ}
    (Q : Fin (m + 1) → MetricTensor (m + 1)) (γ : ℝ) {a M : ℝ} (ha : 0 < a)
    (hgap : ∀ ξ ∈ SignedPairs.angularSet (m + 1) γ, a ≤ ‖(pencil Q ξ).adjugate‖)
    (hbound : ∀ ξ ∈ SignedPairs.angularSet (m + 1) γ, ‖pencil Q ξ‖ ≤ M) :
    ∃ t : Finset (SignedPairs.angularSet (m + 1) γ),
      ∃ radius : SignedPairs.angularSet (m + 1) γ → ℝ,
      ∃ row col : SignedPairs.angularSet (m + 1) γ → Fin (m + 1),
        (∀ x, 0 < radius x) ∧
        SignedPairs.angularSet (m + 1) γ ⊆
          ⋃ x ∈ t, Metric.ball (x : Euclidean (m + 1)) (radius x) ∧
        ∀ x ∈ t, ∀ ξ ∈ Metric.closedBall (x : Euclidean (m + 1)) (2 * radius x),
          minorPatchGap m a ≤ |(cofactorMinor (pencil Q ξ) (row x) (col x)).det| ∧
          cofactorMinor (pencil Q ξ) (row x) (col x) *
            (cofactorMinor (pencil Q ξ) (row x) (col x))⁻¹ = 1 ∧
          (cofactorMinor (pencil Q ξ) (row x) (col x))⁻¹ *
            cofactorMinor (pencil Q ξ) (row x) (col x) = 1 ∧
          ‖(cofactorMinor (pencil Q ξ) (row x) (col x))⁻¹‖ ≤
            minorPatchInverseBound m a M :=
  exists_finite_buffered_minor_cover (pencil Q) (pencilContinuousLinearMap Q).continuous
    (SignedPairs.isCompact_angularSet (m + 1) γ) ha hgap hbound

end JanetCartan.ActualCarriers
