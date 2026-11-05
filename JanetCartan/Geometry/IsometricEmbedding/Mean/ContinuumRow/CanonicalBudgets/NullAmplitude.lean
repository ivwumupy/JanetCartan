module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# The actual null amplitude in canonical carrier coordinates

This instantiates the proved scalar/null-amplitude tame theorem with the SAME
coefficient and flow outputs retained from
`exists_projected_local_positive_amplitude`. The fixed parameter relabeling
costs no derivatives. Its source and target compact sets do not vary with the
derivative order. The two qualitative smoothness inputs are also exact outputs
of that producer; no scalar or null-amplitude bound is an input.

Consumer: the canonical principal-normal reconstruction in
`app:ch_background:eq:bg-mixed-input`; source: `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude AmplitudeTame ActualCarriers.ConstructedCarrierJets

/-- The scalar and null amplitude occurring literally in `normalField` have
uniform `C¹` and additive one-high bounds on every fixed compact subset of the
producer's physical working cylinder. All constants precede `F`, the initial
scalar and the retained maps. Fixed primitive `C¹⁵` budgets supply the low
norms; the sharp scalar reserve is thirteen. The displayed hypotheses are
the coefficient, flow, domain and regularity outputs of
`exists_projected_local_positive_amplitude`, for the same `Q`, `Φ` and `Y`.
Source: `app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_canonical_nullAmplitude_bounds {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (K : Set (Euclidean n)) (z : Euclidean 3) {ρ R τ : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
      (closedBall ((0 : Euclidean n), z) ρ))
    (A H : ℕ → ℝ) (hA : ∀ j, 0 < A j) (hH : ∀ j, 0 < H j)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLW : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) L
      ((coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 64))))
    {M₁₅ Mᵣ : ℝ} (hM₁₅ : 0 ≤ M₁₅) (hMᵣ : 0 ≤ Mᵣ) :
    ∃ M > 0, ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
      let p₀ := ((0 : Euclidean (n - 1)), z)
      let C := coordinates (adaptedCoordinates T.data.adapted)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let Bρ := closedBall ((0 : Euclidean n), z) ρ
      let α := carrierScalarAmplitude T Q F row col Φ Y initial
      let b := fun w ↦ α w • carrierNullvector T Q col w
      IsOpen D → Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) →
      ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      (∀ w ∈ Bρ, ContDiffAt ℝ ∞ (carrierNullvector T Q col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportDirection T Q row col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportPotential T Q F row col) w) →
      (∀ j, cNorm Bρ j (carrierNullvector T Q col) +
        cNorm Bρ j (carrierConullvector T Q row) +
        cNorm Bρ j (carrierAdaptedDenominator T Q row col) +
        cNorm Bρ j (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) +
        cNorm Bρ j (carrierTransportDirection T Q row col) +
        cNorm Bρ j (carrierTransportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) →
      (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) →
      ContDiffOn ℝ ∞ initial (ball p₀ (R / 4)) →
      ContDiffOn ℝ ∞ α (C ⁻¹' D) → ContDiffOn ℝ ∞ b (C ⁻¹' D) →
      cNorm K 15 F ≤ M₁₅ → cNorm (closedBall p₀ (R / 8)) 15 initial ≤ Mᵣ →
      (cNorm L 1 (fun p ↦ α (p.1, parameter p.2)) +
        cNorm L 1 (fun p ↦ b (p.1, parameter p.2)) ≤ M) ∧
      ∀ j, cNorm L j (fun p ↦ α (p.1, parameter p.2)) +
        cNorm L j (fun p ↦ b (p.1, parameter p.2)) ≤
        B j * (1 + cNorm K (j + 13) F + cNorm (closedBall p₀ (R / 8)) (j + 13) initial) := by
  let p₀ := ((0 : Euclidean (n - 1)), z)
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
  have hW : IsCompact W :=
    (isCompact_Icc.prod (isCompact_closedBall p₀ (R / 64))).image C.symm.continuous
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  obtain ⟨E, hE, he⟩ := exists_cNorm_fixed_pullback_le (G := ℝ)
    hL hW (fun _ _ ↦ hψ.contDiffAt) hLW
  obtain ⟨E', hE', he'⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean n)
    hL hW (fun _ _ ↦ hψ.contDiffAt) hLW
  obtain ⟨B, hB, hb⟩ := exists_carrierScalarAmplitude_joint_tame T (N := N)
    K z hρ hR hτ hτR hbuffer A H hA hH hM₁₅ hMᵣ
  let B' := fun j ↦ (E j + E' j) * B j
  have hB' (j) : 0 < B' j := mul_pos (add_pos (hE j) (hE' j)) (hB j)
  refine ⟨B' 1 * (1 + M₁₅ + Mᵣ), mul_pos (hB' 1) (by positivity), B', hB', ?_⟩
  intro Q F row col D Φ Y initial
  dsimp only
  intro hD hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hr hα hbreg hFM hrM
  let α := carrierScalarAmplitude T Q F row col Φ Y initial
  let b := fun w ↦ α w • carrierNullvector T Q col w
  have hWD : W ⊆ C ⁻¹' D := by
    rintro w ⟨q, hq, rfl⟩
    change C (C.symm q) ∈ D
    rw [C.apply_symm_apply]
    exact hsmall ((workingCylinder_subsets p₀ hτ hR).1 hq)
  have hCD : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
  have hbound (j) : cNorm L j (α ∘ ψ) + cNorm L j (b ∘ ψ) ≤
      (E j + E' j) * (cNorm W j α + cNorm W j b) := by
    have h₁ := he α (fun w hw ↦ hα.contDiffAt (hCD.mem_nhds (hWD hw))) j
    have h₂ := he' b (fun w hw ↦ hbreg.contDiffAt (hCD.mem_nhds (hWD hw))) j
    nlinarith [mul_nonneg (hE j).le (cNorm_nonneg W j b),
      mul_nonneg (hE' j).le (cNorm_nonneg W j α)]
  have hh := hb Q F row col D Φ Y initial hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hr
    ((cNorm_mono_order (by omega : 12 ≤ 15)).trans hFM)
    ((cNorm_mono_order (by omega : 5 ≤ 15)).trans hrM)
  have hhigh (j) : cNorm L j (α ∘ ψ) + cNorm L j (b ∘ ψ) ≤
      B' j * (1 + cNorm K (j + 13) F + cNorm (closedBall p₀ (R / 8)) (j + 13) initial) :=
    (hbound j).trans ((mul_le_mul_of_nonneg_left (hh j) (add_pos (hE j) (hE' j)).le).trans_eq
      (by dsimp [B']; ring))
  refine ⟨?_, hhigh⟩
  apply (hhigh 1).trans
  apply mul_le_mul_of_nonneg_left _ (hB' 1).le
  exact add_le_add
    (add_le_add (le_refl 1) ((cNorm_mono_order (by omega : 1 + 13 ≤ 15)).trans hFM))
    ((cNorm_mono_order (by omega : 1 + 13 ≤ 15)).trans hrM)

end JanetCartan.ContinuumRow.CanonicalCarrier
