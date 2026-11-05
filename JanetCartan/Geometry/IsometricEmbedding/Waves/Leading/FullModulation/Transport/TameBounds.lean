module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Physical
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.InitialData

/-!
# Joint one-high bound for the named positive null amplitude

This analytic deduction is instantiated by `FullModulation.exists_positive_amplitude`.
The coefficient and flow sequences are fixed before the immersion. A fixed
`C¹²` immersion budget and `C⁵` initial-data budget produce every low bound
used in the characteristic formula. One fixed reserve `D = 13` controls both
`scalarAmplitude` and its product with the SAME `nullvector`.
`Transport.Construction` instantiates this result with its actual maps.
The leading-wave parent retains the projected-frame inputs and finite cover.
Source: `app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude AmplitudeTame

/-- The named scalar and null amplitude have a joint additive one-high bound
on the fixed physical working set, with `D = 13`. Constants precede `Q`, `F`,
`r`, both maps, and their high norms. The displayed inputs are projections of
`FullModulation.exists_positive_amplitude`, plus fixed primitive budgets
`cNorm K 12 F ≤ M₁₂` and a `C⁵` budget on the ORIGINAL `(y,z)`
section ball. The projection proof supplies all lifted initial-data bounds. No amplitude or integral jet
is an input (`app:ch_waves:eq:joint-tame`). -/
theorem exists_scalarAmplitude_joint_tame {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (K : Set (Euclidean n)) (z : (Euclidean 3 × Euclidean (n - 1))) {ρ R τ : ℝ}
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
        (D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))))
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) → Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
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
      (∀ w ∈ Bρ, ContDiffAt ℝ ∞ (nullvector T Q col) w ∧
        ContDiffAt ℝ ∞ (transportDirection T Q row col) w ∧
        ContDiffAt ℝ ∞ (transportPotential T Q F row col) w) →
      (∀ j, cNorm Bρ j (nullvector T Q col) +
        cNorm Bρ j (conullvector T Q row) +
        cNorm Bρ j (adaptedDenominator T Q row col) +
        cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
        cNorm Bρ j (transportDirection T Q row col) +
        cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) →
      (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) →
      ContDiffOn ℝ ∞ r (ball (p₀.1, p₀.2.1) (R / 4)) → cNorm K 12 F ≤ M₁₂ →
      cNorm (closedBall (p₀.1, p₀.2.1) (R / 8)) 5 r ≤ Mᵣ →
      ∀ j, cNorm (C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))) j
          (scalarAmplitude T Q F row col Φ Y r) +
        cNorm (C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))) j
          (fun w ↦ scalarAmplitude T Q F row col Φ Y r w • nullvector T Q col w) ≤
        B j * (1 + cNorm K (j + 13) F + cNorm (closedBall (p₀.1, p₀.2.1) (R / 8)) (j + 13) r) := by
  let p₀ := ((0 : Euclidean (n - 1)), z)
  let C := coordinates (Z := (Euclidean 3 × Euclidean (n - 1))) (adaptedCoordinates T.data.adapted)
  let Bρ := closedBall ((0 : Euclidean n), z) ρ
  let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
  let M := (A 7 + A 1 + H 7 + H 5) * (1 + M₁₂) + 6 * Mᵣ
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
  refine ⟨fun j ↦ B j * (1 + H (j + 8) + A (j + 8) + (j + 9 : ℝ)),
    fun j ↦ mul_pos (hB j) (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith [hH (j + 8), hA (j + 8)]), ?_⟩
  intro Q F row col D Φ Y r
  dsimp only
  intro hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hr hFlow hrLow j
  let c := transportPotential T Q F row col
  let k := nullvector T Q col
  have hck (i) : cNorm Bρ i c + cNorm Bρ i k ≤ A i * (1 + cNorm K (i + 5) F) := by
    have hh := hcoeff i
    linarith [cNorm_nonneg Bρ i (conullvector T Q row),
      cNorm_nonneg Bρ i (adaptedDenominator T Q row col),
      cNorm_nonneg Bρ i (fun w ↦ (adaptedDenominator T Q row col w)⁻¹),
      cNorm_nonneg Bρ i (transportDirection T Q row col)]
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
      H 7 * (1 + M₁₂) ≤ M ∧ H 5 * (1 + M₁₂) ≤ M ∧ 6 * Mᵣ ≤ M := by
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
  have hrLift := contDiffOn_initialScalar hr (initialProjection_mapsTo_ball p₀ (R / 4))
  have hrLiftLow : cNorm (closedBall p₀ (R / 8)) 5 (initialScalar r) ≤ M := by
    have hh := cNorm_initialScalar_le p₀ hR hr 5
    norm_num only at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hrLow (by norm_num : (0 : ℝ) ≤ 6)).trans
      hmajor.2.2.2.2)
  have hh := hb Φ Y c k (initialScalar r) hΦ hY (fun w hw ↦ (hreg w hw).2.2)
    (fun w hw ↦ (hreg w hw).1) hrLift hmΦ hmY
    (hΦLow.trans hmajor.2.2.1) (hYLow.trans hmajor.2.2.2.1)
    (hcLow.trans hmajor.1) (hkLow.trans hmajor.2.1) hrLiftLow j
  change cNorm (C.symm '' _) j (scalarAmplitude T Q F row col Φ Y r) +
    cNorm (C.symm '' _) j (fun w ↦ scalarAmplitude T Q F row col Φ Y r w • k w) ≤ _ at hh
  apply hh.trans
  have hfh := hflow (j + 8)
  have hch := hck (j + 8)
  simp only [Nat.add_assoc] at hfh hch
  have hrh : cNorm (closedBall p₀ (R / 8)) (j + 8) (initialScalar r) ≤
      (j + 9 : ℝ) * cNorm (closedBall (p₀.1, p₀.2.1) (R / 8)) (j + 13) r := by
    have hh := cNorm_initialScalar_le p₀ hR hr (j + 8)
    push_cast at hh
    rw [add_assoc, show (8 : ℝ) + 1 = 9 by norm_num] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left (cNorm_mono_order (by omega))
    positivity
  have hf0 := cNorm_nonneg K (j + 13) F
  have hr0 := cNorm_nonneg (closedBall (p₀.1, p₀.2.1) (R / 8)) (j + 13) r
  have hi : 1 + cNorm J (j + 8) Φ + cNorm J (j + 8) Y + cNorm Bρ (j + 8) c +
      cNorm Bρ (j + 8) k + cNorm (closedBall p₀ (R / 8)) (j + 8) (initialScalar r) ≤
      (1 + H (j + 8) + A (j + 8) + (j + 9 : ℝ)) *
        (1 + cNorm K (j + 13) F + cNorm (closedBall (p₀.1, p₀.2.1) (R / 8)) (j + 13) r) := by
    have hj : 0 ≤ (j + 9 : ℝ) := by positivity
    nlinarith [mul_nonneg (hH (j + 8)).le hr0, mul_nonneg (hA (j + 8)).le hr0,
      mul_nonneg hj hf0, hH (j + 8), hA (j + 8)]
  exact (mul_le_mul_of_nonneg_left hi (hB j).le).trans_eq (by ring)

end JanetCartan.LeadingWave.FullModulation
