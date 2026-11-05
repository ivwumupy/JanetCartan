module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Bounds

/-!
# Continuing actual carrier incidence roots

The fixed-cylinder and finite-cover construction in Step 3 of
`app:ch_seed:prop:seed-actual-menu`, from the published frozen incidence
sections. Actual phases are inputs, together with joint smoothness and
uniform `C¹` comparison of their literal determinant incidence equations.
All radii, thresholds and gaps are selected from frozen data first.

The smaller finite cover is constructed from the published frozen sections.
The parent construction must instantiate the analytic comparison inputs.
Detector persistence and high-order tame implicit-root bounds are owned by
separate modules.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

open FrozenMenu CharacteristicRoot

/-- Continue a published frozen incidence section to literal current roots.
The scalar interval, covector neighborhood, gap and perturbation threshold
are fixed before the physical domain, current frame, phase or error is chosen.
Existence, joint smoothness, interior containment, uniqueness and low bounds
are conclusions (`app:ch_seed:prop:seed-actual-menu`, Step 3).

The Hamilton-phase and pencil-continuity producers remain responsible for
the displayed smoothness and two comparison inequalities. -/
theorem exists_current_incidence_continuation {n : ℕ} {P : Patch n}
    {c₀ C₀ d : ℝ} (hP : P.IsValid c₀ C₀) {V : Set (Euclidean n)}
    {z₀ : Euclidean n → Euclidean 3} (hsec : P.IsIncidenceSection V z₀ d)
    (hd : 0 < d) {k : Euclidean n} (hk : k ∈ V) :
    ∃ (r a c δ : ℝ) (g₀ : Euclidean n → ℝ),
      0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < δ ∧
      (∀ t ∈ Icc (-a) a, incidenceParameter (z₀ k) t ∈ parameterInterior P.radius) ∧
      ContDiffOn ℝ ∞ g₀ (Metric.ball k (2 * r)) ∧
      (∀ q ∈ Metric.ball k (2 * r), g₀ q ∈ Ioo (-a) a ∧
        frozenDeterminantIncidence P (z₀ k) (q, g₀ q) = 0) ∧
      ∀ (X : Set (Euclidean n)), IsOpen X →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n)
          (Θ : Euclidean n → Euclidean 3 → ℝ) (ε : ℝ), ε ≤ δ →
        (∀ p ∈ X ×ˢ Metric.ball k (2 * r), ∀ t ∈ Icc (-a) a,
          ContDiffAt ℝ ∞ (currentIncidence Q Θ (z₀ k)) (p, t)) →
        (∀ p ∈ X ×ˢ Metric.ball k (2 * r), ∀ t ∈ Icc (-a) a,
          |currentIncidence Q Θ (z₀ k) (p, t) -
            frozenDeterminantIncidence P (z₀ k) (p.2, t)| ≤ ε ∧
          |scalarDerivative (currentIncidence Q Θ (z₀ k)) (p, t) -
            scalarDerivative (frozenDeterminantIncidence P (z₀ k)) (p.2, t)| ≤ ε) →
        ∃ g : Euclidean n × Euclidean n → ℝ,
          ContDiffOn ℝ ∞ g (X ×ˢ Metric.ball k (2 * r)) ∧
          ContDiffOn ℝ ∞ (fun p ↦ incidenceParameter (z₀ k) (g p))
            (X ×ˢ Metric.ball k (2 * r)) ∧
          (∀ p ∈ X ×ˢ Metric.ball k (2 * r),
            g p ∈ Ioo (-a) a ∧
            incidenceParameter (z₀ k) (g p) ∈ parameterInterior P.radius ∧
            currentIncidence Q Θ (z₀ k) (p, g p) = 0 ∧
            c ≤ |scalarDerivative (currentIncidence Q Θ (z₀ k)) (p, g p)| ∧
            |g p - g₀ p.2| ≤ ε / c ∧
            ‖fderiv ℝ g p‖ ≤ ‖fderiv ℝ (currentIncidence Q Θ (z₀ k)) (p, g p)‖ / c) ∧
          (∀ p ∈ X ×ˢ Metric.ball k (2 * r), ∀ t ∈ Icc (-a) a,
            currentIncidence Q Θ (z₀ k) (p, t) = 0 ↔ g p = t) := by
  obtain ⟨r, a, c, e, hr, ha, hc, he, hi, hgap, hend⟩ :=
    exists_frozen_incidence_cylinder_of_section hP hsec hd hk
  obtain ⟨δ, g₀, hδ, hg₀, hroot₀, hpert⟩ :=
    exists_current_incidence_root_on_cylinder hP (z₀ k) k hr ha hc he hi hgap hend
  exact ⟨r, a, c, δ, g₀, hr, ha, hc, hδ, hi, hg₀, hroot₀, hpert⟩

/-- Construct the fixed smaller finite cover and all actual incidence roots
from frozen cover data and the explicit smoothness and `C¹` comparison
of the literal current incidence equation. This proves the incidence-root
part of `app:ch_seed:prop:seed-actual-menu`, Step 3, conditionally on the
Hamilton-phase and pencil-continuity inputs displayed below. Every chart and
constant is chosen before the actual frame, phase, higher norms and accuracy.
The outer balls contain the smaller balls that cover the sphere. -/
theorem exists_uniform_current_incidence_roots {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) :
    ∃ R : IncidenceRefinement D, R.IsValid ∧ ∃ η c B δ : ℝ, 0 < η ∧ 0 < c ∧ 0 < B ∧ 0 < δ ∧
      (∀ j a, ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a), ∀ i : Fin 3,
        |incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) t i| + η <
          (D.patches (R.sourceChart j) a).radius) ∧
      ∀ (X : Set (Euclidean n)), IsOpen X →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (Θ : (b : Fin D.chartCount) → Fin (D.patchCount b) →
          Euclidean n → Euclidean 3 → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ δ →
      (∀ j a, ∀ p ∈ X ×ˢ Metric.ball (R.center j) (2 * R.radius j),
        ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
          ContDiffAt ℝ ∞ (currentIncidence Q (Θ (R.sourceChart j) a)
            (D.roots (R.sourceChart j) a (R.center j))) (p, t)) →
      (∀ j a, ∀ p ∈ X ×ˢ Metric.ball (R.center j) (2 * R.radius j),
        ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
          let z := D.roots (R.sourceChart j) a (R.center j)
          let f := currentIncidence Q (Θ (R.sourceChart j) a) z
          let f₀ := frozenDeterminantIncidence (D.patches (R.sourceChart j) a) z
          |f (p, t) - f₀ (p.2, t)| ≤ ε ∧
            |scalarDerivative f (p, t) - scalarDerivative f₀ (p.2, t)| ≤ ε) →
      (∀ j a, ∀ p ∈ X ×ˢ Metric.ball (R.center j) (2 * R.radius j),
        ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
          let z := D.roots (R.sourceChart j) a (R.center j)
          let f := currentIncidence Q (Θ (R.sourceChart j) a) z
          let f₀ := fun w : (Euclidean n × Euclidean n) × ℝ ↦
            frozenDeterminantIncidence (D.patches (R.sourceChart j) a) z (w.1.2, w.2)
          ‖fderiv ℝ f (p, t) - fderiv ℝ f₀ (p, t)‖ ≤ ε) →
      ∃ g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
          Euclidean n × Euclidean n → ℝ,
        ∀ j a,
          let U := X ×ˢ Metric.ball (R.center j) (2 * R.radius j)
          let z := D.roots (R.sourceChart j) a (R.center j)
          let f := currentIncidence Q (Θ (R.sourceChart j) a) z
          ContDiffOn ℝ ∞ (g j a) U ∧
          ContDiffOn ℝ ∞ (fun p ↦ incidenceParameter z (g j a p)) U ∧
          (∀ p ∈ U,
            g j a p ∈ Ioo (-R.halfWidth j a) (R.halfWidth j a) ∧
            incidenceParameter z (g j a p) ∈ parameterInterior (D.patches (R.sourceChart j) a).radius ∧
            incidenceParameter z (g j a p) 1 = 0 ∧
            incidenceParameter z (g j a p) 2 = 0 ∧
            f (p, g j a p) = 0 ∧
            c ≤ |scalarDerivative f (p, g j a p)| ∧
            ‖incidenceParameter z (g j a p) - D.roots (R.sourceChart j) a p.2‖ ≤ ε / c ∧
            ‖fderiv ℝ (g j a) p‖ ≤ ‖fderiv ℝ f (p, g j a p)‖ / c) ∧
          (∀ p ∈ U, ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
            f (p, t) = 0 ↔ g j a p = t) ∧
          (∀ p ∈ U, ‖fderiv ℝ (g j a) p‖ ≤ B) := by
  obtain ⟨R, hR⟩ := exists_valid_incidenceRefinement hD
  obtain ⟨η, hη, hbuffer⟩ := IncidenceRefinement.exists_uniform_interior_margin hR
  obtain ⟨c, δ, hc, hδ, hroots⟩ := exists_current_incidence_roots_of_refinement hD R hR
  obtain ⟨B, hB, hderiv⟩ := IncidenceRefinement.exists_uniform_root_derivative_bound hD hR hc
  refine ⟨R, hR, η, c, B, min δ 1, hη, hc, hB, lt_min hδ zero_lt_one, hbuffer, ?_⟩
  intro X hX Q Θ ε hε₀ hε hf hclose hfull
  obtain ⟨g, hg⟩ := hroots X hX Q Θ ε hε₀
    (hε.trans (min_le_left _ _)) hf hclose
  refine ⟨g, ?_⟩
  intro j a
  refine ⟨(hg j a).1, (hg j a).2.1, (hg j a).2.2.1, (hg j a).2.2.2, ?_⟩
  apply hderiv j a X hX Q (Θ (R.sourceChart j) a) (g j a) (hg j a).1
  · intro p hp t ht
    exact ⟨hf j a p hp t ht, (hfull j a p hp t ht).trans
      (hε.trans (min_le_right _ _))⟩
  · intro p hp
    have h := (hg j a).2.2.1 p hp
    exact ⟨h.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end JanetCartan.ActualCarriers
