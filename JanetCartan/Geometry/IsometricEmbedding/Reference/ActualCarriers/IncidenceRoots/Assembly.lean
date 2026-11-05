module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Refinement
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Continuation

/-!
# Uniform actual roots on the finite incidence cover

Step 3 of `app:ch_seed:prop:seed-actual-menu`. The finite refinement is
constructed from frozen data. The Hamilton-phase and pencil-continuity producers
must supply smoothness and the two literal incidence comparison inequalities.
The resulting root displacement is measured against the published frozen
sections, as needed by `exists_uniform_detection_at_supplied_roots`.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace JanetCartan.ActualCarriers

open FrozenMenu CharacteristicRoot

/-- Assemble smooth actual roots on every buffered chart of a finite refinement,
with a common transverse gap and perturbation threshold. Uniqueness holds on
the entire fixed scalar interval, both spectators stay fixed, and the root
error is measured against the original frozen section. Constants precede all
current data and higher norms (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem exists_current_incidence_roots_of_refinement {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) (R : IncidenceRefinement D) (hR : R.IsValid) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
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
            f (p, t) = 0 ↔ g j a p = t) := by
  classical
  choose δ g₀ hδ hg₀ hroot₀ hpert using fun j a ↦
    exists_current_incidence_root_on_cylinder
      (hD.2.2.2.2.1 (R.sourceChart j) a).1
      (D.roots (R.sourceChart j) a (R.center j)) (R.center j)
      (hR.1 j) (hR.2.2.2 j a).1 (hR.2.2.2 j a).2.1
      (hR.2.2.2 j a).2.2.1 (hR.2.2.2 j a).2.2.2.1
      (hR.2.2.2 j a).2.2.2.2.1 (hR.2.2.2 j a).2.2.2.2.2
  obtain ⟨δ₀, hδ₀, hδbound⟩ := Pi.exists_forall_pos_add_lt
    (fun i : (j : Fin R.chartCount) × Fin (D.patchCount (R.sourceChart j)) ↦ hδ i.1 i.2)
  obtain ⟨c, hc, hcbound⟩ := Pi.exists_forall_pos_add_lt
    (fun i : (j : Fin R.chartCount) × Fin (D.patchCount (R.sourceChart j)) ↦
      (hR.2.2.2 i.1 i.2).2.1)
  have hc_le (j a) : c ≤ R.gap j a := by simpa using (hcbound ⟨j, a⟩).le
  refine ⟨c, δ₀, hc, hδ₀, ?_⟩
  intro X hX Q Θ ε hε₀ hε hf hclose
  choose g hg hzg hroot huniq using fun j a ↦
    hpert j a X hX Q (Θ (R.sourceChart j) a) ε
      (hε.trans (by simpa using (hδbound ⟨j, a⟩).le)) (hf j a) (hclose j a)
  refine ⟨g, fun j a ↦ ⟨hg j a, hzg j a, ?_, huniq j a⟩⟩
  intro p hp
  have hr := hroot j a p hp
  have hcenter : R.center j ∈ D.domain (R.sourceChart j) :=
    hR.2.1 j (Metric.mem_closedBall_self (mul_nonneg (by norm_num) (hR.1 j).le))
  have hpD : p.2 ∈ D.domain (R.sourceChart j) :=
    hR.2.1 j (Metric.ball_subset_closedBall hp.2)
  have hsec := (hD.2.2.2.2.1 (R.sourceChart j) a).2
  have hz := hsec.2.1 (R.center j) hcenter
  have hid : incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g₀ j a p.2) =
      D.roots (R.sourceChart j) a p.2 := by
    apply incidenceParameter_eq_frozen_section
      (hD.2.2.2.2.1 (R.sourceChart j) a).1 hsec hD.1 hcenter hpD
    · exact fun i ↦ ((hR.2.2.2 j a).2.2.2.1 _
        (Ioo_subset_Icc_self (hroot₀ j a p.2 hp.2).1) i).le
    · exact (hroot₀ j a p.2 hp.2).2
  refine ⟨hr.1, hr.2.1, ?_, ?_, hr.2.2.1,
    (hc_le j a).trans hr.2.2.2.1, ?_, ?_⟩
  · exact (incidenceParameter_spectators _ _).1.trans hz.2.1
  · exact (incidenceParameter_spectators _ _).2.trans hz.2.2.1
  · rw [← hid, norm_incidenceParameter_sub]
    exact hr.2.2.2.2.1.trans (div_le_div_of_nonneg_left hε₀ hc (hc_le j a))
  · exact hr.2.2.2.2.2.trans
      (div_le_div_of_nonneg_left (norm_nonneg _) hc (hc_le j a))

end JanetCartan.ActualCarriers
