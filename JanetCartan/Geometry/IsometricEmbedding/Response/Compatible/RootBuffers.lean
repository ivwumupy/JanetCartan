module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryRegularity

/-!
# Buffered direct roots for the actual primary phase

For `app:ch_response:eq:response-exact-phase` and
`app:ch_response:lem:energy-carrier-jets`, construct physical, parameter and
covector buffers from the literal selected primary chart. This local result
is chosen before the nearby patch parameters. Uniformity over the whole
finite family and current-coefficient neighborhood, whole flowout containment,
and the actual fixed response remain separate obligations.
-/

open Set Metric Filter
open scoped ContDiff Topology
@[expose] public noncomputable section

namespace JanetCartan.CompatibleResponse
open ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}

/-- Construct common physical, parameter and covector buffers from the open
root domain and the continuous actual gradient. The gradient lies strictly
inside the covector buffer, while the ENTIRE physical/covector product stays
in the root domain. Consumer: `exists_buffered_primary_root`, for
`app:ch_response:lem:energy-carrier-jets`. -/
theorem exists_root_graph_buffers
    {V : Set (Euclidean (d + 1) × Euclidean 3)} (hV : IsOpen V)
    {g : Euclidean (d + 1) × Euclidean 3 → Euclidean (d + 1)}
    (hg : ContinuousOn g V) {x₀ : Euclidean (d + 1)} {c₀ : Euclidean 3}
    (hbase : (x₀, c₀) ∈ V)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    (hroot : spacetimeRootState (x₀, g (x₀, c₀)) ∈ D) :
    ∃ r > (0 : ℝ), ∃ s > (0 : ℝ),
      closedBall x₀ (4 * r) ×ˢ closedBall c₀ (4 * r) ⊆ V ∧
      MapsTo g (closedBall x₀ (4 * r) ×ˢ closedBall c₀ (4 * r))
        (ball (g (x₀, c₀)) (s / 2)) ∧
      MapsTo spacetimeRootState (closedBall x₀ (4 * r) ×ˢ closedBall (g (x₀, c₀)) s) D := by
  have hc : Continuous (spacetimeRootState (d := d)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.comp continuous_fst).prodMk
      ((spatialPartCLM.continuous.comp continuous_fst).prodMk
        (spatialPartCLM.continuous.comp continuous_snd))
  obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.mp (hD.preimage hc)
    (x₀, g (x₀, c₀)) hroot
  have hn := (hg.continuousAt (hV.mem_nhds hbase)).preimage_mem_nhds
    (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < δ / 4)))
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hbase) hn)
  have hsmall : 4 * (min δ ε / 16) < ε := by
    have := min_le_right δ ε
    have := lt_min hδ hε
    linarith
  have hphysical : 4 * (min δ ε / 16) < δ := by
    have := min_le_left δ ε
    have := lt_min hδ hε
    linarith
  have hb : closedBall x₀ (4 * (min δ ε / 16)) ×ˢ
      closedBall c₀ (4 * (min δ ε / 16)) ⊆ ball (x₀, c₀) ε := by
    intro q hq
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_le_of_lt hq.1 hsmall, lt_of_le_of_lt hq.2 hsmall⟩
  refine ⟨min δ ε / 16, by positivity, δ / 2, by positivity, ?_, ?_, ?_⟩
  · exact fun q hq ↦ (hεV (hb hq)).1
  · intro q hq
    have h := (hεV (hb hq)).2
    simpa only [mem_preimage, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using h
  · intro q hq
    apply hδD
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_le_of_lt hq.1 hphysical, lt_of_le_of_lt hq.2 (by linarith)⟩

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open FrozenMenu CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct a homogeneous direct root, an actual transverse coordinate and
common closed physical/parameter/covector buffers for the SAME selected primary
phase. The determinant equation, nonzero root derivative, smooth primary phase,
root eikonal equation and complete physical/covector product containment are
all conclusions. No root gap, phase matching or buffer premise is added.

This closes the local inputs to `root_characteristic_preserves_primary_phase`
in `app:ch_response:lem:energy-carrier-jets`. The choices may depend on the
current frame and the base point; uniform finite-family choices and the
whole-segment flow construction are not asserted by this theorem. -/
theorem exists_buffered_primary_root {c C : ℝ} (hP : P.IsValid c C)
    (Q : _) {x₀ : Euclidean (d + 1)} {z₀ : Euclidean 3}
    (hx₀ : x₀ ∈ ball 0 T.physicalRadius) (hz₀ : z₀ ∈ parameterInterior (2 * P.radius)) :
    ∃ i : Fin (d + 1), ∃ D : Set (RootState (Euclidean d)),
    ∃ h : RootState (Euclidean d) → ℝ, ∃ r > (0 : ℝ), ∃ s > (0 : ℝ),
      let x := primaryCoordinateChange i x₀
      let g := fun q : Euclidean (d + 1) × Euclidean 3 ↦
        gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y q.2) q.1
      let B := closedBall x (4 * r) ×ˢ closedBall z₀ (4 * r)
      IsOpen D ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ U ∧ w.2.2 ≠ 0 ∧
        determinant (Q.1 ((coordinateSplit i).symm (w.1, w.2.1)))
          ((coordinateSplit i).symm (h w, w.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q.1 ((coordinateSplit i).symm (w.1, w.2.1))))
          ((coordinateSplit i).symm (h w, w.2.2)) ((coordinateSplit i).symm (1, 0)) ≠ 0) ∧
      (∀ w ∈ D, ∀ a : ℝ, 0 < a →
        (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
      (∀ q ∈ B, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
        q.2 ∈ parameterInterior (2 * P.radius)) ∧
      ContDiffOn ℝ ∞ (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) B ∧
      ContDiffOn ℝ ∞ g B ∧
      (∀ q ∈ B, spacetimeRootState (q.1, g q) ∈ D ∧ rootSuspension h (q.1, g q) = 0) ∧
      MapsTo g B (ball (g (x, z₀)) (s / 2)) ∧
      MapsTo spacetimeRootState (closedBall x (4 * r) ×ˢ closedBall (g (x, z₀)) s) D := by
  obtain ⟨i, hi⟩ := exists_coordinateSplit_transverse _ (T.primary_determinant_fderiv_ne_zero Q hx₀ hz₀)
  obtain ⟨D, h, hD, hh, hroot, hscale, V, hV, hbase, hsub, hφ, hg, he⟩ :=
    T.exists_primary_root_equation_in_coordinates hP i Q hx₀ hz₀ hi
  obtain ⟨r, hr, s, hs, hB, hgB, hprod⟩ :=
    exists_root_graph_buffers hV hg.continuousOn hbase hD (he _ hbase).1
  exact ⟨i, D, h, r, hr, s, hs, hD, hh, hroot, hscale,
    fun q hq ↦ hsub q (hB hq), hφ.mono hB, hg.mono hB,
    fun q hq ↦ he q (hB hq), hgB, hprod⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
