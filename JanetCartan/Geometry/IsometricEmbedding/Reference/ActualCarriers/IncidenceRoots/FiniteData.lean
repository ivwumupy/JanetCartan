module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Frozen
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Cover

/-!
# Frozen cylinder data for the smaller finite incidence cover

The finite geometric input to the assembly of
`exists_current_incidence_root_on_cylinder`, Step 3 of
`app:ch_seed:prop:seed-actual-menu`. Existence is proved from
`FrozenMenu.CoverData.IsValid` in `IncidenceRoots.Refinement`. No current
phase, root or implicit solution is a field. Each selected chart retains
all the patches of its source chart, including empty patch lists.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ActualCarriers

open FrozenMenu CharacteristicRoot

/-- A finite refinement of the frozen cover by buffered covector balls,
with a fixed scalar interval for each selected patch
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
structure IncidenceRefinement {n : ℕ} (D : CoverData n) where
  chartCount : ℕ
  sourceChart : Fin chartCount → Fin D.chartCount
  center : Fin chartCount → Euclidean n
  radius : Fin chartCount → ℝ
  halfWidth : (j : Fin chartCount) → Fin (D.patchCount (sourceChart j)) → ℝ
  gap : (j : Fin chartCount) → Fin (D.patchCount (sourceChart j)) → ℝ
  endpointMargin : (j : Fin chartCount) → Fin (D.patchCount (sourceChart j)) → ℝ

/-- The frozen geometric conditions needed for finite assembly. They require
the original cube interior, the literal determinant equation, positive
endpoint margins and a gap on the whole buffered cylinder. Proving this
predicate is a geometric construction, separate from perturbing the phases
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def IncidenceRefinement.IsValid {n : ℕ} {D : CoverData n}
    (R : IncidenceRefinement D) : Prop :=
  (∀ j, 0 < R.radius j) ∧
  (∀ j, Metric.closedBall (R.center j) (2 * R.radius j) ⊆ D.domain (R.sourceChart j)) ∧
  (Metric.sphere (0 : Euclidean n) 1 ⊆ ⋃ j, Metric.ball (R.center j) (R.radius j)) ∧
  (∀ j a, 0 < R.halfWidth j a ∧ 0 < R.gap j a ∧ 0 < R.endpointMargin j a ∧
    let P := D.patches (R.sourceChart j) a
    let z := D.roots (R.sourceChart j) a (R.center j)
    (∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
      incidenceParameter z t ∈ parameterInterior P.radius) ∧
    (∀ q ∈ Metric.closedBall (R.center j) (2 * R.radius j),
      ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
        2 * R.gap j a ≤ |scalarDerivative (frozenDeterminantIncidence P z) (q, t)|) ∧
    (∀ q ∈ Metric.closedBall (R.center j) (2 * R.radius j),
      (frozenDeterminantIncidence P z (q, -R.halfWidth j a) ≤ -R.endpointMargin j a ∧
        R.endpointMargin j a ≤ frozenDeterminantIncidence P z (q, R.halfWidth j a)) ∨
      (frozenDeterminantIncidence P z (q, R.halfWidth j a) ≤ -R.endpointMargin j a ∧
        R.endpointMargin j a ≤ frozenDeterminantIncidence P z (q, -R.halfWidth j a))))

end JanetCartan.ActualCarriers
