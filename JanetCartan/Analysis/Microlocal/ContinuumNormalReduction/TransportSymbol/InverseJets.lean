module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.ForwardJets
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Scaling
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Smooth
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.InverseJetBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets

/-!
# Tame transport inverse jets on a buffered shell

The inverse deduction in Step 1 of `app:ch_background:prop:bg-frame`.
The input is the actual averaged gradient, a genuine inverse identity, fixed
buffered domains and a fixed normalized differential gap. There is no
inverse-jet bound among the premises. Both positions and the spectator are
retained. The constants are chosen before the geometry and its inverse vary.

The shell can be any compact subset of the open output chart whose inverse
image lies in the fixed input working ball. Geometric producers must supply
these containments and primitive mixed-jet estimates for `Y` from
`app:ch_background:eq:bg-mixed-input`. The final assembly derives all forward
estimates from those primitive jets and gives a common fixed loss of two
derivatives for the inverse, absolute Jacobian, and reciprocal.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

private def inverseSliceProjection : InputVariables n →L[ℝ] ℝ × Euclidean (n - 1) :=
  (((ContinuousLinearMap.fst ℝ ℝ (Euclidean 2)).comp
    (ContinuousLinearMap.fst ℝ (ℝ × Euclidean 2) (Euclidean (n - 1)))).prod
    (ContinuousLinearMap.snd ℝ (ℝ × Euclidean 2) (Euclidean (n - 1)))).comp
    (ContinuousLinearMap.snd ℝ (Euclidean n × Euclidean n)
      ((ℝ × Euclidean 2) × Euclidean (n - 1)))

private theorem cNorm_inverse_slice_le
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω K : Set (Variables n × Euclidean 2)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hu : ContDiffOn ℝ ∞ u Ω) (m : ℕ) :
    cNorm K m u ≤ ‖(inverseSliceProjection : InputVariables n →L[ℝ] _)‖ *
      cNorm K m (inverseCoordinates u) := by
  let P := (inverseSliceProjection : InputVariables n →L[ℝ] ℝ × Euclidean (n - 1))
  have he : P ∘ inverseCoordinates u = u := by
    funext p
    rfl
  have hg := inverseCoordinates_contDiffOn hu
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (norm_nonneg P)
      (sSup_norm_iteratedFDeriv_nonneg K j (inverseCoordinates u)))
  intro j hj p hp
  rw [← he]
  apply (P.norm_iteratedFDeriv_comp_left
    (hg.contDiffAt (hΩ.mem_nhds (hKΩ hp))) (by simp : (j : ℕ∞ω) ≤ ∞)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK
      (fun q hq ↦ (hg.contDiffAt (hΩ.mem_nhds (hKΩ hq))).of_le
        (by simp : (m : ℕ∞ω) ≤ ∞)) hj) (mem_image_of_mem _ hp)) (norm_nonneg P)

/-- One-high joint shell bounds for the genuine inverse and its full coordinate
substitution. The only high seminorm is that of the forward averaged-gradient
map; the derivative loss is zero at this step. This supplies the inverse input
of the shell estimate in `app:ch_background:prop:bg-frame`, Step 1.
The normalized gap is a fixed first-derivative condition, not an inverse-jet
estimate. -/
theorem exists_inverseCoordinates_oneHigh_bound
    (a : InputVariables n) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set (InputVariables n)} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {K : Set (Variables n × Euclidean 2)} (hK : IsCompact K)
    {M : ℝ} (hM : 0 ≤ M) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (Ω : Set (Variables n × Euclidean 2)),
      IsOpen Ω → K ⊆ Ω → ContDiffOn ℝ ∞ (augmentedTransportGradient Y) W →
      ContDiffOn ℝ ∞ u Ω → cNorm (closedBall a ρ) 1 (augmentedTransportGradient Y) ≤ M →
      MapsTo (inverseCoordinates u) K (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      cNorm K m (inverseCoordinates u) + cNorm K m u ≤
        C * (1 + cNorm (closedBall a ρ) m (augmentedTransportGradient Y)) := by
  obtain ⟨C, hC, hb⟩ := HamiltonPhase.exists_inverse_cNorm_bound a hρ hW hball A hM m
  let P := (inverseSliceProjection : InputVariables n →L[ℝ] ℝ × Euclidean (n - 1))
  refine ⟨(1 + ‖P‖) * C, by positivity, ?_⟩
  intro Y u Ω hΩ hKΩ hY hu hlow hrange hgap heq
  have hi := hb (augmentedTransportGradient Y) (inverseCoordinates u) Ω K hΩ hKΩ
    hY (inverseCoordinates_contDiffOn hu) hlow hrange hgap
    (augmentedTransportGradient_inverseCoordinates Y u heq)
  have hs := cNorm_inverse_slice_le hΩ hK hKΩ hu m
  calc
    _ ≤ (1 + ‖P‖) * cNorm K m (inverseCoordinates u) := by
      dsimp [P]
      nlinarith
    _ ≤ (1 + ‖P‖) * (C * (1 + cNorm (closedBall a ρ) m
        (augmentedTransportGradient Y))) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

/-- A primitive forward bound with shift `D` transfers to the actual inverse
with exactly the same shift. Constants for all orders precede `Y`, `u`, and
the geometry norm sequence `H`. In the application `H j = ‖G‖_(C^j)` and the
forward premise is produced from `app:ch_background:eq:bg-mixed-input`.
This is the inverse part of the normalized-shell bound consumed by the literal
transport-amplitude estimate in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_inverseCoordinates_fixedShift_bound
    (a : InputVariables n) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set (InputVariables n)} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {K : Set (Variables n × Euclidean 2)} (hK : IsCompact K)
    {M : ℝ} (hM : 0 ≤ M) (D : ℕ) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (Ω : Set (Variables n × Euclidean 2)) (H : ℕ → ℝ),
      IsOpen Ω → K ⊆ Ω → ContDiffOn ℝ ∞ (augmentedTransportGradient Y) W →
      ContDiffOn ℝ ∞ u Ω → cNorm (closedBall a ρ) 1 (augmentedTransportGradient Y) ≤ M →
      MapsTo (inverseCoordinates u) K (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      (∀ j, 0 ≤ H j) →
      (∀ m, cNorm (closedBall a ρ) m (augmentedTransportGradient Y) ≤
        B m * (1 + H (m + D))) →
      ∀ m, cNorm K m (inverseCoordinates u) + cNorm K m u ≤
        C m * (1 + H (m + D)) := by
  choose C hC hb using
    exists_inverseCoordinates_oneHigh_bound a hρ hW hball A hK hM
  refine ⟨fun m ↦ C m * (1 + B m), fun m ↦ mul_pos (hC m) (by linarith [hB m]), ?_⟩
  intro Y u Ω H hΩ hKΩ hY hu hlow hrange hgap heq hH hhigh m
  apply (hb m Y u Ω hΩ hKΩ hY hu hlow hrange hgap heq).trans
  calc
    C m * (1 + cNorm (closedBall a ρ) m (augmentedTransportGradient Y)) ≤
        C m * (1 + B m * (1 + H (m + D))) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hhigh m)) (hC m).le
    _ ≤ C m * (1 + B m) * (1 + H (m + D)) := by
      nlinarith [mul_nonneg (hC m).le (hH (m + D))]

/-- Primitive mixed jets of `Y` control the genuine inverse, its full joint
substitution, the supplied absolute Jacobian, and its reciprocal. There is
one high primitive norm at order `m+2`; all constants precede the varying
geometry, inverse, and Jacobian. The fixed low bound is only `C²` of `Y`.
The normalized differential gap and actual inverse identity describe the
buffered chart, and `J` is identified with the literal, volume-normalized
absolute determinant. No forward or inverse high bound is assumed.

This assembles `bg-Psi`, `bg-jacobian`, and `bg-mixed-input` for the inverse
and Jacobian inputs of the shell deduction in
`app:ch_background:prop:bg-frame`, Step 1. `Q` may be the closed output ball
used for interpolation in `exists_amplitude_oneHigh_bound_of_primitiveArray_cNorm`.
-/
theorem exists_transportInverseJacobian_primitive_bound
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    {ρ : ℝ} (hρ : 0 < ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {Q : Set (Variables n × Euclidean 2)} (hQ : IsCompact Q)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (J : InputVariables n → ℝ) (Ω : Set (Variables n × Euclidean 2)),
      ContDiffOn ℝ ∞ Y V → cNorm L 2 Y ≤ M →
      IsOpen Ω → Q ⊆ Ω → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) Q (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      EqOn J (transportAbsoluteJacobian c Y) W →
      (∀ q ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y q) →
      ∀ m, (cNorm Q m (inverseCoordinates u) + cNorm Q m u) +
        (cNorm (closedBall a ρ) m J + cNorm (closedBall a ρ) m (fun q ↦ (J q)⁻¹)) ≤
          C m * (1 + cNorm L (m + 2) Y) := by
  obtain ⟨B, hB, hb⟩ := exists_transportForward_cNorm_bound
    (isCompact_closedBall a ρ) hball hW hK hWK hV hL hLV hT hIT hsegT hseg
  have hlow : 0 ≤ B 1 * (1 + M) := mul_nonneg (hB 1).le (by linarith)
  choose Cᵤ hCᵤ huBound using
    exists_inverseCoordinates_oneHigh_bound a hρ hW hball A hQ hlow
  choose Cⱼ hCⱼ hjBound using
    exists_suppliedTransportJacobian_oneHigh_bound c a hρ hW hball
      (Subset.refl (closedBall a ρ)) hlow hδ
  refine ⟨fun m ↦ Cᵤ m * (1 + B m) + Cⱼ m * (1 + B (m + 1)),
    fun m ↦ add_pos (mul_pos (hCᵤ m) (by linarith [hB m]))
      (mul_pos (hCⱼ m) (by linarith [hB (m + 1)])), ?_⟩
  intro Y u J Ω hY hYM hΩ hQΩ hu hrange hgap heq hJ hdet m
  have hf := transportAveragedGradient_contDiffOn hW hV hT hIT hsegT hY
  have ha := augmentedTransportGradient_contDiffOn hW hV hT hIT hsegT hY
  have hl : cNorm (closedBall a ρ) 1 (transportAveragedGradient Y) ≤ B 1 * (1 + M) ∧
      cNorm (closedBall a ρ) 1 (augmentedTransportGradient Y) ≤ B 1 * (1 + M) := by
    have hm : B 1 * (1 + cNorm L 2 Y) ≤ B 1 * (1 + M) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hYM) (hB 1).le
    exact ⟨((hb Y hY 1).1).trans hm, ((hb Y hY 1).2).trans hm⟩
  have hi := huBound m Y u Ω hΩ hQΩ ha hu hl.2 hrange hgap heq
  have hj := hjBound m Y J hf hJ hl.1 hdet
  have hiHigh : cNorm (closedBall a ρ) m (augmentedTransportGradient Y) ≤
      B m * (1 + cNorm L (m + 2) Y) :=
    ((hb Y hY m).2).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (cNorm_mono_order (by omega : m + 1 ≤ m + 2))) (hB m).le)
  have hjHigh : cNorm (closedBall a ρ) (m + 1) (transportAveragedGradient Y) ≤
      B (m + 1) * (1 + cNorm L (m + 2) Y) := by
    simpa only [Nat.add_assoc] using (hb Y hY (m + 1)).1
  have hi' : cNorm Q m (inverseCoordinates u) + cNorm Q m u ≤
      (Cᵤ m * (1 + B m)) * (1 + cNorm L (m + 2) Y) := by
    apply hi.trans
    apply (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hiHigh) (hCᵤ m).le).trans
    nlinarith [mul_nonneg (hCᵤ m).le (cNorm_nonneg L (m + 2) Y)]
  have hj' : cNorm (closedBall a ρ) m J +
      cNorm (closedBall a ρ) m (fun q ↦ (J q)⁻¹) ≤
      (Cⱼ m * (1 + B (m + 1))) * (1 + cNorm L (m + 2) Y) := by
    apply hj.trans
    apply (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hjHigh) (hCⱼ m).le).trans
    nlinarith [mul_nonneg (hCⱼ m).le (cNorm_nonneg L (m + 2) Y)]
  exact (add_le_add hi' hj').trans_eq (by ring)

/-- Final one-high geometry estimate for the genuine inverse and supplied
absolute Jacobian, with the fixed shift `D+2`. The primitive producer supplies
`cNorm L j Y ≤ B j * (1 + H (j+D))`, where `H j` is the geometry norm at order
`j` in `app:ch_background:eq:bg-mixed-input`. No monotonicity of `H` is
needed. All forward estimates have been discharged by differentiating the
literal integral. The parent transport-symbol construction supplies the
actual chart identities, primitive smoothness and bounds, and fixed gaps.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_transportInverseJacobian_fixedShift_bound
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    {ρ : ℝ} (hρ : 0 < ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {Q : Set (Variables n × Euclidean 2)} (hQ : IsCompact Q)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (D : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (J : InputVariables n → ℝ) (Ω : Set (Variables n × Euclidean 2)) (H : ℕ → ℝ),
      ContDiffOn ℝ ∞ Y V → cNorm L 2 Y ≤ M →
      IsOpen Ω → Q ⊆ Ω → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) Q (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      EqOn J (transportAbsoluteJacobian c Y) W →
      (∀ q ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y q) →
      (∀ j, 0 ≤ H j) → (∀ j, cNorm L j Y ≤ B j * (1 + H (j + D))) →
      ∀ m, (cNorm Q m (inverseCoordinates u) + cNorm Q m u) +
        (cNorm (closedBall a ρ) m J + cNorm (closedBall a ρ) m (fun q ↦ (J q)⁻¹)) ≤
          C m * (1 + H (m + (D + 2))) := by
  obtain ⟨C, hC, hb⟩ := exists_transportInverseJacobian_primitive_bound
    c a hρ hW hball hK hWK hV hL hLV hT hIT hsegT hseg A hQ hM hδ
  refine ⟨fun m ↦ C m * (1 + B (m + 2)),
    fun m ↦ mul_pos (hC m) (by linarith [hB (m + 2)]), ?_⟩
  intro Y u J Ω H hY hYM hΩ hQΩ hu hrange hgap heq hJ hdet hH hhigh m
  apply (hb Y u J Ω hY hYM hΩ hQΩ hu hrange hgap heq hJ hdet m).trans
  have hh := hhigh (m + 2)
  rw [show m + 2 + D = m + (D + 2) by omega] at hh
  apply (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hh) (hC m).le).trans
  nlinarith [mul_nonneg (hC m).le (hH (m + (D + 2)))]

end JanetCartan.ContinuumNormalReduction.TransportSymbol
