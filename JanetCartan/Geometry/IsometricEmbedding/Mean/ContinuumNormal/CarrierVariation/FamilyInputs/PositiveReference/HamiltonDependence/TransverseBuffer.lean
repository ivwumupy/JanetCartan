module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.RetainedGeometry
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# A transverse buffer at a retained positive reference

The retained frame constructor bounds its trajectories by a closed state ball.
For the comparison in `app:lem:common-hamilton-phase`, a new local flow about
the reference's actual initial momentum needs a slightly larger transverse
ball. Compactness supplies this buffer, and the scalar symbol comparison
preserves its gap. The consumer is `exists_retained_positiveReference_comparison`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open HamiltonPhase

/-- Enlarge the retained closed state ball strictly, preserving transversality
for all sufficiently close symbols. The outer state compact and the unit normal
are those of the actual frame constructor (`app:lem:common-hamilton-phase`). -/
theorem exists_positiveReference_transverse_buffer {n : ℕ}
    (H₀ : HomogeneousSymbol (Euclidean n)) {D : Set (Euclidean n × Euclidean n)}
    (hD : IsOpen D) (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    {w : Euclidean n × Euclidean n} {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hR₀D : closedBall w R₀ ⊆ D) (ν : Euclidean n) (hν : ‖ν‖ = 1)
    (hgap : ∀ z ∈ closedBall w R, ⟪H₀.hp z, ν⟫_ℝ ≠ 0) :
    ∃ S δ : ℝ, R < S ∧ S < R₀ ∧ 0 < δ ∧
      ∀ H : HomogeneousSymbol (Euclidean n), D ⊆ H.domain →
        ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall w R₀) 3 (fun z ↦ H.h z - H₀.h z) < δ →
        ∀ z ∈ closedBall w S, ⟪H.hp z, ν⟫_ℝ ≠ 0 := by
  have hc : ContinuousOn (fun z ↦ ⟪H₀.hp z, ν⟫_ℝ) D :=
    fun z hz ↦ ((H₀.hasFDerivAt_hp z (hDH₀ hz)).continuousAt.inner
      continuousAt_const).continuousWithinAt
  let V := D ∩ (fun z ↦ ⟪H₀.hp z, ν⟫_ℝ) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV : IsOpen V := hc.isOpen_inter_preimage hD isClosed_singleton.isOpen_compl
  have hRV : closedBall w R ⊆ V := fun z hz ↦
    ⟨hR₀D (closedBall_subset_closedBall hRR₀.le hz), hgap z hz⟩
  obtain ⟨e, he, heb⟩ := (isCompact_closedBall w R).exists_cthickening_subset_open hV hRV
  rw [cthickening_closedBall he.le hR.le] at heb
  let S := R + min e (R₀ - R) / 2
  have hRS : R < S := by dsimp [S]; have := lt_min he (sub_pos.mpr hRR₀); linarith
  have hSR₀ : S < R₀ := by have := min_le_right e (R₀ - R); dsimp [S]; linarith
  have hSe : S ≤ e + R := by have := min_le_left e (R₀ - R); dsimp [S]; linarith
  have hSV : closedBall w S ⊆ V := (closedBall_subset_closedBall hSe).trans heb
  have hSD : closedBall w S ⊆ D := hSV.trans inter_subset_left
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall w S).exists_isMinOn
    ⟨w, mem_closedBall_self (hR.trans hRS).le⟩ (hc.abs.mono hSD)
  let c := |⟪H₀.hp z, ν⟫_ℝ|
  have hcz : 0 < c := abs_pos.mpr (hSV hz).2
  refine ⟨S, c / 2, hRS, hSR₀, half_pos hcz, ?_⟩
  intro H hDH hH hsmall y hy
  have hd := abs_normal_velocity_sub_le_cNorm_three H H₀ hD hDH hDH₀
    (hH.of_le (by simp)) (hH₀.of_le (by simp)) (isCompact_closedBall _ _)
    hR₀D ν (closedBall_subset_closedBall hSR₀.le hy)
  rw [hν, mul_one] at hd
  have hm : c ≤ |⟪H₀.hp y, ν⟫_ℝ| := hmin hy
  have ht := abs_sub_abs_le_abs_sub ⟪H₀.hp y, ν⟫_ℝ ⟪H.hp y, ν⟫_ℝ
  rw [abs_sub_comm] at ht
  apply abs_pos.mp
  linarith

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
