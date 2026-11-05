module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ForwardJacobian.Composition
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian

/-!
# Differences of the literal absolute transport Jacobian

The slice differential is a fixed linear restriction of the actual forward
differential. The determinant and reciprocal estimates below are deduced from
this identity and the common positive gap in `app:ch_background:eq:bg-jacobian`.
Consumer: the primitive-input comparison in `ForwardJacobian`, supplying the
full amplitude comparison in `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Restricting the difference of full forward differentials costs one
derivative, with both positions and spectator retained (`bg-jacobian`). -/
theorem cNorm_transportSliceDifferential_sub_le
    (c : TransportSliceCoordinates n)
    {Y Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {K W : Set (InputVariables n)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hY : ContDiffOn ℝ ∞ (transportAveragedGradient Y) W)
    (hY₀ : ContDiffOn ℝ ∞ (transportAveragedGradient Y₀) W) (m : ℕ) :
    cNorm K m (transportSliceDifferential c Y - transportSliceDifferential c Y₀) ≤
      ((m + 1 : ℕ) : ℝ) * ‖transportDifferentialRestriction c‖ *
        cNorm K (m + 1) (transportAveragedGradient Y - transportAveragedGradient Y₀) := by
  let f := transportAveragedGradient Y - transportAveragedGradient Y₀
  let R := transportDifferentialRestriction c
  have hf : ContDiffOn ℝ ∞ f W := hY.sub hY₀
  have he (p) (hp : p ∈ K) :
      transportSliceDifferential c Y - transportSliceDifferential c Y₀
        =ᶠ[𝓝 p] R ∘ fderiv ℝ f := by
    filter_upwards [hW.mem_nhds (hKW hp)] with q hq
    have hd := (hY.contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp)
    have hd₀ := (hY₀.contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp)
    simp only [Pi.sub_apply, Function.comp_apply, f, fderiv_sub hd hd₀, map_sub,
      transportSliceDifferential_eq_restriction c Y hd,
      transportSliceDifferential_eq_restriction c Y₀ hd₀, R]
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq he m]
  have hb := cNorm_le_sum_of_bounds (s := K) (r := m)
    (C := fun _ ↦ ‖R‖ * cNorm K (m + 1) f)
    (fun _ _ ↦ mul_nonneg (norm_nonneg R) (cNorm_nonneg _ _ _)) (by
      intro j hj p hp
      have hp' := hf.contDiffAt (hW.mem_nhds (hKW hp))
      apply (R.norm_iteratedFDeriv_comp_left
        (hp'.fderiv_right (m := ∞) (by simp)) (by simp)).trans
      rw [norm_iteratedFDeriv_fderiv]
      exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun q hq ↦ (hf.contDiffAt (hW.mem_nhds (hKW hq))).of_le (by simp)) hp
        (Nat.add_le_add_right hj 1)) (norm_nonneg R))
  simpa only [R, f, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc] using hb

/-- The absolute determinant and reciprocal depend quantitatively on the
actual slice differential. The reference and positive gap precede the constant;
the smallness premise is subsequently produced from primitive jets by
`exists_transportForwardJacobian_sub_le` (`bg-jacobian`, Step 4'). -/
theorem exists_transportAbsoluteJacobian_sub_le
    (c : TransportSliceCoordinates n)
    {Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {K W : Set (InputVariables n)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hY₀ : ContDiffOn ℝ ∞ (transportAveragedGradient Y₀) W)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap₀ : ∀ p ∈ K, δ ≤ transportAbsoluteJacobian c Y₀ p) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)),
      ContDiffOn ℝ ∞ (transportAveragedGradient Y) W →
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian c Y p) →
      cNorm K m (transportSliceDifferential c Y - transportSliceDifferential c Y₀) ≤ 1 →
      cNorm K m (transportAbsoluteJacobian c Y - transportAbsoluteJacobian c Y₀) +
        cNorm K m ((fun p ↦ (transportAbsoluteJacobian c Y p)⁻¹) -
          (fun p ↦ (transportAbsoluteJacobian c Y₀ p)⁻¹)) ≤
        C * cNorm K m (transportSliceDifferential c Y - transportSliceDifferential c Y₀) := by
  let g₀ := transportSliceDifferential c Y₀
  have hg₀ := transportSliceDifferential_contDiffOn c Y₀ hW hY₀
  have hg₀' : ∀ p ∈ K, ContDiffAt ℝ m g₀ p :=
    fun p hp ↦ (hg₀.contDiffAt (hW.mem_nhds (hKW hp))).of_le (by simp)
  let B := 1 + cNorm K m g₀
  let S : Set (Euclidean n →L[ℝ] Euclidean n) := {D | ‖D‖ ≤ B ∧ δ ≤ |D.det|}
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : Euclidean n →L[ℝ] Euclidean n) B).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const ContinuousLinearMap.continuous_det.abs))
      (fun D hD ↦ by simpa only [mem_closedBall, dist_zero_right] using hD.1)
  have hrange₀ : MapsTo g₀ K S := by
    intro p hp
    refine ⟨?_, hgap₀ p hp⟩
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hg₀' hp (Nat.zero_le m)
    rw [norm_iteratedFDeriv_zero] at hh
    dsimp [B]
    linarith
  have hdet (D) (hD : D ∈ S) : D.det ≠ 0 := abs_pos.mp (hδ.trans_le hD.2)
  obtain ⟨C₀, hC₀, hb₀⟩ := ForwardJacobian.exists_compact_comp_sub_le hK hS
    (f := fun D ↦ |D.det|)
    (fun D hD ↦ NormalComparison.contDiff_normalJacobianDet.contDiffAt.abs (hdet D hD))
    m hg₀' hrange₀
  obtain ⟨C₁, hC₁, hb₁⟩ := ForwardJacobian.exists_compact_comp_sub_le hK hS
    (f := fun D ↦ |D.det|⁻¹)
    (fun D hD ↦ NormalComparison.contDiffAt_reciprocalAbsNormalJacobian (hdet D hD))
    m hg₀' hrange₀
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro Y hY hgap hsmall
  let g := transportSliceDifferential c Y
  have hg := transportSliceDifferential_contDiffOn c Y hW hY
  have hg' : ∀ p ∈ K, ContDiffAt ℝ m g p :=
    fun p hp ↦ (hg.contDiffAt (hW.mem_nhds (hKW hp))).of_le (by simp)
  have hrange : MapsTo g K S := by
    intro p hp
    refine ⟨?_, hgap p hp⟩
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun q hq ↦ (hg' q hq).sub (hg₀' q hq)) hp (Nat.zero_le m)
    have h₀ := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hg₀' hp (Nat.zero_le m)
    simp only [norm_iteratedFDeriv_zero] at hh h₀
    change ‖g p - g₀ p‖ ≤ cNorm K m (g - g₀) at hh
    have ht := norm_le_norm_sub_add (g p) (g₀ p)
    change cNorm K m (g - g₀) ≤ 1 at hsmall
    dsimp [B]
    linarith
  have h₀ := hb₀ g hg' hrange hsmall
  have h₁ := hb₁ g hg' hrange hsmall
  change cNorm K m (transportAbsoluteJacobian c Y - transportAbsoluteJacobian c Y₀) ≤ _ at h₀
  change cNorm K m ((fun p ↦ (transportAbsoluteJacobian c Y p)⁻¹) -
    (fun p ↦ (transportAbsoluteJacobian c Y₀ p)⁻¹)) ≤ _ at h₁
  exact (add_le_add h₀ h₁).trans_eq (by ring)

end JanetCartan.ContinuumNormal.CarrierVariation
