module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.RootDomain

/-!
# Uniform primary-gradient band for the retained selector

The original coefficient comparison places the same primary gradient in a
fixed annulus about its nonzero frozen covector. The constants and parameter
buffer precede every coefficient and history. This supplies `hgradient` and
the two selector radii of `IntegratedEnvelope.Assembly`, from the actual
primary chart (`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open CompatibleResponse

/-- The actual primary coordinate permutation preserves the covector norm
(`app:ch_response:eq:response-exact-phase`). -/
theorem norm_primaryCoordinateChange {d : ℕ} (i : Fin (d + 1)) (v : Euclidean (d + 1)) :
    ‖primaryCoordinateChange i v‖ = ‖v‖ := by
  have h := primaryCoordinateChange_pairing i v v
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (primaryCoordinateChange i v), norm_nonneg v]

end JanetCartan.ResponseTransfer.RetainedFactors

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ResponseTransfer.RetainedFactors

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

/-- Derive a uniform positive gradient band from the original `C⁶` comparison,
with no estimate on the desired response. Both bounds use only the frozen
nonzero covector, and hold for every retained coordinate permutation and
all original physical points (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_primary_gradient_band
    {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Euclidean 3} (hc₀ : c₀ ∈ parameterInterior (2 * P.radius))
    (hξ : P.toFun c₀ ≠ 0) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      closedBall c₀ (4 * s) ⊆ parameterInterior (2 * P.radius) ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ i : Fin (d + 1), ∀ y : E,
        (primaryCoordinateChange i).symm y ∈ ball 0 T.physicalRadius →
      ∀ c ∈ closedBall c₀ (4 * s),
        ‖P.toFun c₀‖ / 2 ≤ ‖fderiv ℝ (fun x ↦ T.primaryPhaseInCoordinates i Q x c) y‖ ∧
        ‖fderiv ℝ (fun x ↦ T.primaryPhaseInCoordinates i Q x c) y‖ ≤ 2 * ‖P.toFun c₀‖ := by
  let V : Set (Coeff × E) := univ ×ˢ {ξ : E | ‖P.toFun c₀‖ / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2 * ‖P.toFun c₀‖}
  have hnorm : 0 < ‖P.toFun c₀‖ := norm_pos_iff.mpr hξ
  have hV : IsOpen V := isOpen_univ.prod
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  obtain ⟨δ, hδ, hδT, s, hs, hparam, hpair⟩ :=
    T.exists_uniform_primary_pair_neighborhood hP hframe hc₀ hV
      (show (cubeStress (d + 1), P.toFun c₀) ∈ V from
        ⟨mem_univ _, by dsimp; constructor <;> linarith⟩)
  refine ⟨δ, hδ, hδT, s, hs, hparam, ?_⟩
  intro Q hQ i y hy c hc
  have hb := (hpair Q hQ _ hy c hc).2
  have he : ‖fderiv ℝ (fun x ↦ T.primaryPhaseInCoordinates i Q x c) y‖ =
      ‖T.carrierGradient Q ((primaryCoordinateChange i).symm y) c‖ := by
    rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map]
    change ‖gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x c) y‖ = _
    rw [T.primaryPhaseInCoordinates_gradient hP i Q hy (hparam hc), norm_primaryCoordinateChange]
  rw [he]
  exact ⟨hb.1.le, hb.2.le⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
