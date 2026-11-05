module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian.Differential
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Determinant

/-!
# Tame jets of the genuine transport Jacobian

The determinant and reciprocal are fixed smooth operations on the compact
set of differentials with bounded norm and a determinant gap. Interpolation
in the composition theorem leaves one high forward norm, with shift one.
The forward estimates are explicit inputs from `bg-mixed-input`; no Jacobian
jet or amplitude bound is an input.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

private theorem exists_local_comp_bound
    (a : InputVariables n) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set (InputVariables n)} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    {S : Set (Euclidean n →L[ℝ] Euclidean n)} (hS : IsCompact S)
    (m : ℕ) (g : (Euclidean n →L[ℝ] Euclidean n) → ℝ)
    (hg : ∀ A ∈ S, ContDiffAt ℝ m g A) :
    ∃ C > (0 : ℝ), ∀ f : InputVariables n → (Euclidean n →L[ℝ] Euclidean n),
      ContDiffOn ℝ ∞ f W → MapsTo f (closedBall a ρ) S →
      cNorm (closedBall a ρ) m (g ∘ f) ≤ C * (1 + cNorm (closedBall a ρ) m f) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    a hρ hS (le_refl m) hg
  refine ⟨C, hC, ?_⟩
  intro f hf hrange
  obtain ⟨F, hF, _, _, he⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall a hρ hW hball hf
  have hecomp : ∀ p ∈ closedBall a ρ, g ∘ F =ᶠ[𝓝 p] g ∘ f := by
    intro p hp
    exact (he p hp).mono (fun q hq ↦ congrArg g hq)
  rw [← GeometricProfile.cNorm_eq_of_eventuallyEq hecomp m,
    ← GeometricProfile.cNorm_eq_of_eventuallyEq he m]
  exact hb F hF (fun p hp ↦ (he p hp).eq_of_nhds ▸ hrange hp)

/-- Normalized-shell bounds for the genuine absolute Jacobian and its
reciprocal. Constants precede `Y`; the only low bound is the first forward
seminorm and the determinant gap. Exactly one high norm occurs at order
`m+1`. This supplies the Jacobian part of `app:ch_background:prop:bg-frame`,
Step 1, from the actual forward map of `bg-Psi`. -/
theorem exists_transportAbsoluteJacobian_oneHigh_bound
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    {ρ : ℝ} (hρ : 0 < ρ) {W : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) {M δ : ℝ} (_hM : 0 ≤ M) (hδ : 0 < δ) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)),
      ContDiffOn ℝ ∞ (transportAveragedGradient Y) W →
      cNorm (closedBall a ρ) 1 (transportAveragedGradient Y) ≤ M →
      (∀ p ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y p) →
      cNorm (closedBall a ρ) m (transportAbsoluteJacobian c Y) +
        cNorm (closedBall a ρ) m (fun p ↦ (transportAbsoluteJacobian c Y p)⁻¹) ≤
          C * (1 + cNorm (closedBall a ρ) (m + 1) (transportAveragedGradient Y)) := by
  let B := ‖transportDifferentialRestriction c‖ * M
  let S : Set (Euclidean n →L[ℝ] Euclidean n) := {A | ‖A‖ ≤ B ∧ δ ≤ |A.det|}
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : Euclidean n →L[ℝ] Euclidean n) B).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const ContinuousLinearMap.continuous_det.abs))
      (fun A hA ↦ by simpa only [mem_closedBall, dist_zero_right] using hA.1)
  have hdet (A) (hA : A ∈ S) : A.det ≠ 0 := abs_pos.mp (hδ.trans_le hA.2)
  obtain ⟨C₀, hC₀, hb₀⟩ := exists_local_comp_bound a hρ hW hball hS m
    (fun A ↦ |A.det|) (fun A hA ↦
      (NormalComparison.contDiff_normalJacobianDet.contDiffAt.abs (hdet A hA)).of_le
        (by simp))
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_local_comp_bound a hρ hW hball hS m
    (fun A ↦ |A.det|⁻¹) (fun A hA ↦
      (NormalComparison.contDiffAt_reciprocalAbsNormalJacobian (hdet A hA)).of_le
        (by simp))
  let D := ((m + 1 : ℕ) : ℝ) * ‖transportDifferentialRestriction c‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨(C₀ + C₁) * (1 + D), by positivity, ?_⟩
  intro Y hY hlow hgap
  have hA := transportSliceDifferential_contDiffOn c Y hW hY
  have hA0 : cNorm (closedBall a ρ) 0 (transportSliceDifferential c Y) ≤ B := by
    apply (cNorm_transportSliceDifferential_le c Y hW (isCompact_closedBall a ρ)
      hball hY 0).trans
    simpa [B] using mul_le_mul_of_nonneg_left hlow (norm_nonneg
      (transportDifferentialRestriction c))
  have hrange : MapsTo (transportSliceDifferential c Y) (closedBall a ρ) S := by
    intro p hp
    refine ⟨?_, hgap p hp⟩
    apply le_trans ?_ hA0
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
        (fun q hq ↦ (hA.contDiffAt (hW.mem_nhds (hball hq))).of_le
          (by simp : (0 : ℕ∞ω) ≤ ∞)) hp (le_refl 0)
  have h₀ := hb₀ _ hA hrange
  have h₁ := hb₁ _ hA hrange
  have hhigh := cNorm_transportSliceDifferential_le c Y hW
    (isCompact_closedBall a ρ) hball hY m
  change _ ≤ D * _ at hhigh
  change cNorm _ m (transportAbsoluteJacobian c Y) ≤ _ at h₀
  change cNorm _ m (fun p ↦ (transportAbsoluteJacobian c Y p)⁻¹) ≤ _ at h₁
  have hF := cNorm_nonneg (closedBall a ρ) (m + 1) (transportAveragedGradient Y)
  calc
    _ ≤ (C₀ + C₁) * (1 + cNorm (closedBall a ρ) m
        (transportSliceDifferential c Y)) := by linarith
    _ ≤ (C₀ + C₁) * (1 + D * cNorm (closedBall a ρ) (m + 1)
        (transportAveragedGradient Y)) := by gcongr
    _ ≤ _ := by nlinarith

end JanetCartan.ContinuumNormalReduction.TransportSymbol
