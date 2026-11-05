module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Joint frame profiles for the normalized source family

The Hamilton and null-flow constructions consume the joint frame norm, rather
than separate norms of its rows. Here the exact source-scaling formula supplies
all joint orders on the closure of the supplied bounded working domain. The
scale interval precedes every order and each constant precedes the source scale.
No inverse of the unnormalized second form is used at zero.

Sources: `app:ch_background:prop:bg-normalized`, `app:ch_seed:setup:seed-current`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedFlowProfiles
open ProjectedStressFrame ActualCarriers.CurrentFullPhase

/-- The actual normalized source frame has uniform all-order joint bounds on
the original physical domain, together with an `O(σ)` difference from the cube
frame. The consumer is admission to the SAME retained Hamilton family and its
principal null-transport formulas (`app:ch_background:prop:bg-normalized`). -/
theorem exists_source_frame_profiles {n : ℕ} (H : FlatReference n)
    {U : Set (Euclidean n)} (hbounded : Bornology.IsBounded U) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀,
        IsImmersionOn (sourceDilation H.map σ) U ∧
        HasFullNormalRankOn (sourceDilation H.map σ) U ∧
        ∀ x ∈ closure U,
          ContDiffAt ℝ ∞ (projectedStress (sourceDilation H.map σ)) x) ∧
      ∀ m : ℕ, ∃ C > (0 : ℝ), ∀ σ ∈ Ioc (0 : ℝ) σ₀,
        cNorm (closure U) m
            (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) ≤ C * σ ∧
        cNorm (closure U) m (projectedStress (sourceDilation H.map σ)) ≤ C := by
  have hK : IsCompact (closure U) := hbounded.isCompact_closure
  obtain ⟨W, hW, hKW, σ₀, hσ₀, hσ₁, _, hgeom, hb⟩ :=
    exists_projectedStress_dilation_bounds H hK
  have hs (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) (x) (hx : x ∈ closure U) :
      ContDiffAt ℝ ∞ (projectedStress (sourceDilation H.map σ)) x :=
    (contDiffOn_pi.mpr (hgeom σ hσ).2.2).contDiffAt (hW.mem_nhds (hKW hx))
  refine ⟨σ₀, hσ₀, hσ₁, ?_, ?_⟩
  · intro σ hσ
    exact ⟨fun x hx ↦ (hgeom σ hσ).1 x (hKW (subset_closure hx)),
      fun x hx ↦ (hgeom σ hσ).2.1 x (hKW (subset_closure hx)), hs σ hσ⟩
  · intro m
    obtain ⟨B, hB, hbound⟩ := hb m
    let D : ℝ := (m + 1) * B
    let Z : ℝ := cNorm (closure U) m (fun _ : Euclidean n ↦ cubeStress n)
    have hD : 0 < D := mul_pos (by positivity) hB
    have hZ : 0 ≤ Z := cNorm_nonneg ..
    refine ⟨D + Z + 1, by positivity, ?_⟩
    intro σ hσ
    have hdiff : cNorm (closure U) m
        (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) ≤ D * σ := by
      have hj := frame_cNorm_le_of_componentwise hK
        (f := projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n)
        (fun x hx ↦ ((hs σ hσ x hx).sub contDiffAt_const).of_le (by simp))
        (mul_nonneg hB.le hσ.1.le) (fun i ↦ by
          simpa only [Pi.sub_apply] using hbound σ hσ i)
      exact hj.trans_eq (by dsimp [D]; ring)
    have hadd := cNorm_add_le_of_contDiffAt
      (f := projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n)
      (g := fun _ ↦ cubeStress n) hK
      (fun x hx ↦ ((hs σ hσ x hx).sub contDiffAt_const).of_le (by simp))
      (fun _ _ ↦ (contDiffAt_const :
        ContDiffAt ℝ m (fun _ : Euclidean n ↦ cubeStress n) _))
    rw [sub_add_cancel] at hadd
    exact ⟨hdiff.trans (mul_le_mul_of_nonneg_right (by linarith) hσ.1.le),
      (hadd.trans (add_le_add hdiff (le_refl Z))).trans (by
        have := mul_le_of_le_one_right hD.le (hσ.2.trans hσ₁)
        linarith)⟩

end JanetCartan.ContinuumRow.NormalizedFlowProfiles
