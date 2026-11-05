module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Physical
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Adapted

/-!
# Joint one-high bound for the named positive null amplitude

This is the analytic deduction from `exists_projected_local_positive_amplitude`.
The coefficient and flow sequences are fixed before the immersion. A fixed
`C¹²` immersion budget and `C⁵` initial-data budget produce every low bound
used in the characteristic formula. One fixed reserve `D = 13` controls both
`carrierScalarAmplitude` and its product with the SAME `carrierNullvector`.
The parent null-transport assembly must instantiate this result with the
constructed projected frame and flow and retain its positivity/coverage data.
Source: `app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.NullTransport
open ActualCarriers FrozenMenu CurrentFullPhase ActualFlow FlowAmplitude AmplitudeTame

/-- The named scalar and null amplitude have a joint additive one-high bound
on the fixed physical working set, with `D = 13`. Constants precede `Q`, `F`,
`r`, both maps, and their high norms. The displayed inputs are projections of
`exists_projected_local_positive_amplitude`, plus fixed primitive budgets
`cNorm K 12 F ≤ M₁₂` and `cNorm (closedBall p₀ (R/8)) 5 r ≤ Mᵣ`.
Smooth initial data on `ball p₀ (R/4)` suffice. No amplitude or integral jet
is an input (`app:ch_waves:eq:joint-tame`). -/
theorem exists_carrierScalarAmplitude_joint_tame {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (K : Set (Euclidean n)) (z : Euclidean 3) {ρ R τ : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
      (closedBall ((0 : Euclidean n), z) ρ))
    (A H : ℕ → ℝ) (hA : ∀ j, 0 < A j) (hH : ∀ j, 0 < H j)
    {M₁₂ Mᵣ : ℝ} (hM₁₂ : 0 ≤ M₁₂) (hMᵣ : 0 ≤ Mᵣ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ),
      let p₀ := ((0 : Euclidean (n - 1)), z)
      let C := coordinates (adaptedCoordinates T.data.adapted)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let Bρ := closedBall ((0 : Euclidean n), z) ρ
      Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
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
      ContDiffOn ℝ ∞ r (ball p₀ (R / 4)) → cNorm K 12 F ≤ M₁₂ →
      cNorm (closedBall p₀ (R / 8)) 5 r ≤ Mᵣ →
      ∀ j, cNorm (C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))) j
          (carrierScalarAmplitude T Q F row col Φ Y r) +
        cNorm (C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))) j
          (fun w ↦ carrierScalarAmplitude T Q F row col Φ Y r w • carrierNullvector T Q col w) ≤
        B j * (1 + cNorm K (j + 13) F + cNorm (closedBall p₀ (R / 8)) (j + 13) r) := by
  let p₀ := ((0 : Euclidean (n - 1)), z)
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let Bρ := closedBall ((0 : Euclidean n), z) ρ
  let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
  let M := (A 7 + A 1 + H 7 + H 5) * (1 + M₁₂) + Mᵣ
  have hM : 0 ≤ M := by
    dsimp [M]
    have := hA 7
    have := hA 1
    have := hH 7
    have := hH 5
    positivity
  have hcenter : C.symm (0, p₀) = ((0 : Euclidean n), z) := by
    simp [C, p₀, coordinates_symm_apply]
  obtain ⟨B, hB, hb⟩ := exists_cNorm_physicalTransport_bounds (V := Euclidean n)
    C (0, z) p₀ hρ hτ hR hτR hcenter hbuffer hM
  refine ⟨fun j ↦ B j * (1 + H (j + 8) + A (j + 8)),
    fun j ↦ mul_pos (hB j) (by linarith [hH (j + 8), hA (j + 8)]), ?_⟩
  intro Q F row col D Φ Y r
  dsimp only
  intro hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hr hFlow hrLow j
  let c := carrierTransportPotential T Q F row col
  let k := carrierNullvector T Q col
  have hck (i) : cNorm Bρ i c + cNorm Bρ i k ≤ A i * (1 + cNorm K (i + 5) F) := by
    have hh := hcoeff i
    linarith [cNorm_nonneg Bρ i (carrierConullvector T Q row),
      cNorm_nonneg Bρ i (carrierAdaptedDenominator T Q row col),
      cNorm_nonneg Bρ i (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹),
      cNorm_nonneg Bρ i (carrierTransportDirection T Q row col)]
  have hcLow : cNorm Bρ 7 c ≤ A 7 * (1 + M₁₂) := by
    have hh := hck 7
    change _ ≤ A 7 * (1 + cNorm K 12 F) at hh
    have := mul_le_mul_of_nonneg_left (show 1 + cNorm K 12 F ≤ 1 + M₁₂ by linarith) (hA 7).le
    linarith [cNorm_nonneg Bρ 7 k]
  have hkLow : cNorm Bρ 1 k ≤ A 1 * (1 + M₁₂) := by
    have hh := hck 1
    have hlo : cNorm K (1 + 5) F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFlow
    have := mul_le_mul_of_nonneg_left (show 1 + cNorm K (1 + 5) F ≤ 1 + M₁₂ by linarith) (hA 1).le
    linarith [cNorm_nonneg Bρ 1 c]
  have hΦLow : cNorm J 7 Φ ≤ H 7 * (1 + M₁₂) := by
    have hh := hflow 7
    change _ ≤ H 7 * (1 + cNorm K 12 F) at hh
    have := mul_le_mul_of_nonneg_left (show 1 + cNorm K 12 F ≤ 1 + M₁₂ by linarith) (hH 7).le
    linarith [cNorm_nonneg J 7 Y]
  have hYLow : cNorm J 5 Y ≤ H 5 * (1 + M₁₂) := by
    have hh := hflow 5
    have hlo : cNorm K (5 + 5) F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFlow
    have := mul_le_mul_of_nonneg_left (show 1 + cNorm K (5 + 5) F ≤ 1 + M₁₂ by linarith) (hH 5).le
    linarith [cNorm_nonneg J 5 Φ]
  have hmajor : A 7 * (1 + M₁₂) ≤ M ∧ A 1 * (1 + M₁₂) ≤ M ∧
      H 7 * (1 + M₁₂) ≤ M ∧ H 5 * (1 + M₁₂) ≤ M ∧ Mᵣ ≤ M := by
    dsimp [M]
    have ha7 := mul_nonneg (hA 7).le (by linarith : 0 ≤ 1 + M₁₂)
    have ha1 := mul_nonneg (hA 1).le (by linarith : 0 ≤ 1 + M₁₂)
    have hh7 := mul_nonneg (hH 7).le (by linarith : 0 ≤ 1 + M₁₂)
    have hh5 := mul_nonneg (hH 5).le (by linarith : 0 ≤ 1 + M₁₂)
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hmΦ : MapsTo (fun q ↦ (q.1, Φ q))
      (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 4)) :=
    hΦD.mono_right hbig
  have hmY : MapsTo (fun q ↦ (q.1, Y q))
      (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64)) J := by
    intro q hq
    have hh := hYU (hsmall ((workingCylinder_subsets p₀ hτ hR).1 hq))
    exact ⟨Ioo_subset_Icc_self hh.1, ball_subset_closedBall hh.2⟩
  have hh := hb Φ Y c k r hΦ hY (fun w hw ↦ (hreg w hw).2.2)
    (fun w hw ↦ (hreg w hw).1) hr hmΦ hmY
    (hΦLow.trans hmajor.2.2.1) (hYLow.trans hmajor.2.2.2.1)
    (hcLow.trans hmajor.1) (hkLow.trans hmajor.2.1) (hrLow.trans hmajor.2.2.2.2) j
  change cNorm (C.symm '' _) j (carrierScalarAmplitude T Q F row col Φ Y r) +
    cNorm (C.symm '' _) j (fun w ↦ carrierScalarAmplitude T Q F row col Φ Y r w • k w) ≤ _ at hh
  apply hh.trans
  have hfh := hflow (j + 8)
  have hch := hck (j + 8)
  simp only [Nat.add_assoc] at hfh hch
  have hrh := cNorm_mono_order (s := closedBall p₀ (R / 8)) (f := r) (by omega : j + 8 ≤ j + 13)
  have hf0 := cNorm_nonneg K (j + 13) F
  have hr0 := cNorm_nonneg (closedBall p₀ (R / 8)) (j + 13) r
  have hi : 1 + cNorm J (j + 8) Φ + cNorm J (j + 8) Y + cNorm Bρ (j + 8) c +
      cNorm Bρ (j + 8) k + cNorm (closedBall p₀ (R / 8)) (j + 8) r ≤
      (1 + H (j + 8) + A (j + 8)) *
        (1 + cNorm K (j + 13) F + cNorm (closedBall p₀ (R / 8)) (j + 13) r) := by
    nlinarith [mul_nonneg (hH (j + 8)).le hr0, mul_nonneg (hA (j + 8)).le hr0,
      hH (j + 8), hA (j + 8)]
  exact (mul_le_mul_of_nonneg_left hi (hB j).le).trans_eq (by ring)

end JanetCartan.NullTransport
