module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedFlowProfiles.RetainedMinor

/-!
# Recovering frozen minors on the actual null-gap cover

Evaluate the existing common null-gap theorem at the cube-frame member of
the SAME retained Hamilton family. The momentum comparison at arbitrarily
small tolerance identifies that member's carrier gradient with the frozen
patch. Thus the original cover witnesses retain their frozen minor bounds,
without identifying independently selected covers or radii.
Sources: `app:ch_waves:thm:leading`, `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedFlowProfiles
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The cube-frame member of the supplied Hamilton family has exactly the
original frozen carrier covector throughout the buffered patch. This follows
from its proved momentum comparison, without equating existential charts
(`app:lem:common-hamilton-phase`, `app:ch_waves:thm:leading`). -/
theorem carrierGradient_eq_frozen_of_cube_frame (Q₀ : _)
    (hQ₀ : Q₀.1 = fun _ ↦ cubeStress n)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {z : Euclidean 3} (hz : z ∈ parameterInterior (2 * P.radius)) :
    T.carrierGradient Q₀ x z = P.toFun z := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := exists_buffered_carrier_value_threshold T hε
  have hl : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q₀.1 - fun _ ↦ cubeStress n) < δ := by
    rw [hQ₀, sub_self, cNorm_zero]
    exact hδ
  simpa only [zero_add] using (hb Q₀ hl x hx z hz).le

/-- The original null-gap producer admits its SAME cover and constants with
frozen minor evidence retained. No new cover is intersected with an independent
choice. On any supplied doubled cell inside this cover, use `μ / 2` in
`exists_source_direction_profiles`; the cell, row and column stay unchanged
(`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_actual_null_gaps_with_frozen_minors (hn : 2 ≤ n)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ μ κ : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        (∀ z ∈ parameterCube (3 * P.radius / 2), ∀ r c, z ∈ V r c →
          μ ≤ |(cubePencil (P.toFun z)).adjugate r c|) ∧
        ∀ Q, cNorm K 6 (Q.1 - fun _ ↦ cubeStress n) < δ →
          ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, x ∈ K →
          ∀ z ∈ parameterCube (3 * P.radius / 2),
            κ ≤ fderiv ℝ (determinant (Q.1 x)) (T.carrierGradient Q x z)
              T.data.adapted.normal ∧
            ∀ r c, z ∈ V r c →
              μ ≤ |(pencil (Q.1 x) (T.carrierGradient Q x z)).adjugate r c| := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hb⟩ :=
    exists_actual_null_gaps hn hP T hK hKU hball
  let Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨fun _ ↦ cubeStress n, contDiffOn_const, by
      rw [sub_self, cNorm_zero]
      exact T.family.threshold_pos⟩
  have hsmall : cNorm K 6 (Q₀.1 - fun _ ↦ cubeStress n) < δ := by
    change cNorm K 6 ((fun _ ↦ cubeStress n) - fun _ ↦ cubeStress n) < δ
    rw [sub_self, cNorm_zero]
    exact hδ
  refine ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, ?_, hb⟩
  intro z hz r c hzV
  have hzero : (0 : Euclidean n) ∈ ball 0 T.physicalRadius := mem_ball_self T.physicalRadius_pos
  have hg := carrierGradient_eq_frozen_of_cube_frame T Q₀ rfl hzero
    (fun i ↦ (hz i).trans_lt (by linarith [hP.1]))
  have hm := (hb Q₀ hsmall 0 hzero
    (hball (mem_closedBall_self T.data.localReference.stateRadius_pos.le)) z hz).2 r c hzV
  simpa only [hg, Q₀, pencil_cubeStress] using hm

end JanetCartan.ContinuumRow.NormalizedFlowProfiles
