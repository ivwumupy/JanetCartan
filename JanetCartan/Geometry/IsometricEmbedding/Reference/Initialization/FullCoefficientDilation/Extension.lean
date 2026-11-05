module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.FullCoefficientDilation.Bounds

/-!
# Source dilation and the fixed full-coefficient extension

The same literal source-dilated reference from `main:prop:seed` satisfies the
fixed affine-extension estimate of `app:ch_regular:eq:coefficient-extension`.
The given Seeley operator is never reselected, and its all-order constants
are chosen before the source scale. This supplies the reference-margin input
for `ProtectedFlow.exists_extendedReducedCoefficients_low_neighborhood`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ReferenceInitialization.FullCoefficientDilation
open GeometricProfile ProjectedStressFrame ProtectedFlow
variable {n : ℕ}

/-- The given affine extension of the actual reference coefficients is `O(σ)`
in every global seminorm (`app:ch_regular:eq:coefficient-extension`). The same
scale interval also controls the unextended full array and literal principal
frame; all geometric hypotheses are proved from the actual flat reference. -/
theorem exists_extendedReducedCoefficients_dilation_bounds (G : FlatReference n)
    (p : BallExtension.Parameters (Euclidean n)) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ closedBall p.center p.radius ⊆ U ∧
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
        (∀ σ ∈ Ioc (0 : ℝ) σ₀,
          ContDiff ℝ ∞ (sourceDilation G.map σ) ∧
          IsImmersionOn (sourceDilation G.map σ) U ∧
          HasFullNormalRankOn (sourceDilation G.map σ) U ∧
          ContDiff ℝ ∞
            (extendedReducedCoefficients p (fun _ _ ↦ 0) (sourceDilation G.map σ))) ∧
        ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Ioc (0 : ℝ) σ₀,
          cNorm univ m
            (extendedReducedCoefficients p (fun _ _ ↦ 0) (sourceDilation G.map σ) -
              reducedCoefficientBackground (fun _ _ ↦ 0)) ≤ C * σ ∧
          cNorm (closedBall p.center p.radius) m
            (geometricReducedCoefficients (sourceDilation G.map σ) -
              reducedCoefficientBackground (fun _ _ ↦ 0)) ≤ C * σ ∧
          ∀ i, cNorm (closedBall p.center p.radius) m
            (fun x ↦ projectedStress (sourceDilation G.map σ) x i - cubeStress n i) ≤
            C * σ := by
  obtain ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, _, hgeom, hb⟩ :=
    exists_fullReducedCoefficients_dilation_bounds G (isCompact_closedBall p.center p.radius)
  refine ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨hF, hi, hr, _⟩ := hgeom σ hσ
    exact ⟨hF, hi, hr, contDiff_extendedReducedCoefficients p (fun _ _ ↦ 0)
      contDiff_const hF hU hi hr hKU⟩
  · intro m
    obtain ⟨A, hA, hA_bound⟩ := exists_cNorm_vector_seeleyExtension_le
      (F := ReducedCoefficientIndex n → ℝ) p m
    obtain ⟨B, hB, hB_bound⟩ := hb m
    refine ⟨(1 + A) * B, mul_pos (by positivity) hB, ?_⟩
    intro σ hσ
    obtain ⟨_, _, _, ha⟩ := hgeom σ hσ
    have hd : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞
        (geometricReducedCoefficients (sourceDilation G.map σ) -
          reducedCoefficientBackground (fun _ _ ↦ 0)) x := fun x hx ↦
      (ha.contDiffAt (hU.mem_nhds (hKU hx))).sub
        (contDiff_reducedCoefficientBackground contDiff_const).contDiffAt
    have he := hA_bound _ hd
    have hraw := (hB_bound σ hσ).1
    have hle : B * σ ≤ (1 + A) * B * σ := by
      nlinarith [mul_pos hA (mul_pos hB hσ.1)]
    refine ⟨?_, hraw.trans hle, fun i ↦ ((hB_bound σ hσ).2 i).trans hle⟩
    simp only [extendedReducedCoefficients, add_sub_cancel_left]
    exact (he.trans (mul_le_mul_of_nonneg_left hraw hA.le)).trans
      (by nlinarith [mul_pos hB hσ.1])

end JanetCartan.ReferenceInitialization.FullCoefficientDilation
