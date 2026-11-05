module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedPhases

/-!
# Smoothness and comparison of the selected literal carriers

These are the common objects for signed directions, continued incidence and
joint tame bounds in `app:ch_seed:prop:seed-actual-menu`. Every estimate is
derived from the actual quantitative Hamilton family.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The selected carrier is jointly smooth on the doubled open patch and
the full fixed physical ball (`app:ch_seed:prop:seed-actual-menu`, item 1). -/
theorem carrier_smooth {c C : ℝ} (hP : P.IsValid c C) (Q : _) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦ T.carrier Q q.1 q.2)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) := by
  apply contDiffOn_carrierPhase (T.currentChart Q)
    ((T.family.coordinates_smooth Q).mono
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius))) (T.reference.spatialPatch_smooth hP)
  intro x hx z hz
  exact T.reference.target_contains x hx z hz

/-- The same literal physical gradient is jointly smooth, including its
parameter derivatives (`app:ch_seed:prop:seed-actual-menu`, Steps 2–3). -/
theorem carrierGradient_smooth {c C : ℝ} (hP : P.IsValid c C) (Q : _) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦ T.carrierGradient Q q.1 q.2)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) := by
  apply contDiffOn_carrierGradient (T.currentChart Q) (T.family.momentum_smooth Q)
    ((T.family.coordinates_smooth Q).mono
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius))) (T.reference.spatialPatch_smooth hP)
  intro x hx z hz
  exact T.reference.target_contains x hx z hz

/-- Exact characteristicity for the literal constructed carrier on the whole
doubled patch; this uses the retained buffered target, not merely inner-cube
validity (`app:ch_seed:prop:seed-actual-menu`, item 1). -/
theorem carrier_characteristic (Q : _) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball (0 : Euclidean n) T.physicalRadius)
    (hz : z ∈ parameterInterior (2 * P.radius)) :
    determinant (Q.1 x) (T.carrierGradient Q x z) = 0 :=
  carrierPhase_normalizedSymbol_determinant_eq_zero hU Q.1 Q.2.1
    (T.currentChart Q) T.reference.spatialPatch (T.reference.target_contains x hx z hz)

/-- Full momentum comparisons give arbitrarily small value and parameter
derivative errors for the same constructed gradient on the entire physical
ball. The input is primitive frame `C⁶` closeness. This supplies the exact
comparisons consumed by signed-pair stability, with no assumed carrier
estimate (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem exists_carrier_comparison_threshold {c C : ℝ} (hP : P.IsValid c C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius,
      ∀ z ∈ parameterCube P.radius,
        ‖T.carrierGradient Q x z - P.toFun z‖ ≤ ε ∧
        ‖fderiv ℝ (T.carrierGradient Q x) z - fderiv ℝ P.toFun z‖ ≤ ε := by
  obtain ⟨L, hL, hderiv⟩ := T.reference.exists_patch_derivative_bound hP
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨δ, hδ, hc⟩ := T.family.exists_momentum_comparison_threshold (div_pos hε hLpos)
  refine ⟨δ, hδ, fun Q hQ x hx z hz ↦ ?_⟩
  let I : CarrierFullPhaseInput T.reference (normalizedHomogeneousSymbol hU Q.1 Q.2.1)
      (ε / L) := {
    flow := T.family.flow Q
    chart := T.currentChart Q
    target_eq := rfl
    section_eq := T.family.section_eq Q
    momentum_smooth := T.family.momentum_smooth Q
    coordinates_smooth := (T.family.coordinates_smooth Q).mono
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius))
    section_source := fun _ hu _ hz ↦ T.current_section_source Q hu (fun i ↦ (hz i).le)
    comparison := fun q hq ↦ ⟨(hc Q hQ q (ball_subset_closedBall hq)).1.le,
      (hc Q hQ q (ball_subset_closedBall hq)).2.le⟩ }
  have hh := I.carrier_comparison (div_nonneg hε.le hLpos.le) hP hx hz
  refine ⟨hh.1.trans (div_le_self hε.le hL), hh.2.trans ?_⟩
  calc
    _ ≤ (ε / L) * L := mul_le_mul_of_nonneg_left (hderiv z hz).1 (by positivity)
    _ = ε := div_mul_cancel₀ ε hLpos.ne'

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
