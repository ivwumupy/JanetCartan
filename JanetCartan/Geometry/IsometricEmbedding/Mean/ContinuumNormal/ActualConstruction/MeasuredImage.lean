module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.SourceImage
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement

/-!
# The supplied measurement image and the literal frozen image

The coefficient cutoff returned by `NormalizedMeasurement` is one on the full
measurement support, not just on the physical core. Consequently its zero-scale
image is exactly the original source-masked frozen periodic image on all L² data.
The source comparison therefore applies to that literal image with no second
choice of coefficients, masks or operators. The actual normalized coefficient
producer gives a linear source-scale error, with both constants and the source
cap before the scale. Consumers are normalized full-normal comparison and the
frozen-gap assembly in `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.ActualConstruction

open ContinuumRow GeometricProfile FrozenImageComparison FrozenCoercivity AmplitudeBound

variable {n : ℕ}

/-- The measured coefficient multiplier depends only on coefficients where
the measurement is nonzero (`app:ch_background:defn:bg-row`). -/
private theorem measured_coefficient_eq_of_support
    (c d χ : C(Torus n, ℝ)) (i j : Fin n)
    (heq : ∀ z, χ z ≠ 0 → c z = d z) :
    cutoffMultiplier χ ∘L reducedCoefficientMultiplier c i j =
      cutoffMultiplier χ ∘L reducedCoefficientMultiplier d i j := by
  ext1 f
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn χ (reducedCoefficientMultiplier c i j f),
    cutoffMultiplier_coeFn χ (reducedCoefficientMultiplier d i j f),
    reducedCoefficientMultiplier_coeFn c i j f, reducedCoefficientMultiplier_coeFn d i j f]
    with z hleft hright hc hd
  change cutoffMultiplier χ (reducedCoefficientMultiplier c i j f) z =
    cutoffMultiplier χ (reducedCoefficientMultiplier d i j f) z
  rw [hleft, hright, hc, hd]
  by_cases hz : χ z = 0
  · simp only [hz, zero_smul]
  · rw [heq z hz]

/-- Coefficient agreement on the entire measurement support identifies the
actual bounded image operators on every L² input, retaining both fixed masks
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-frame`). -/
theorem imageChannel_eq_of_measurement_support
    (c d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χ χsrc : C(Torus n, ℝ))
    (heq : ∀ j z, χ z ≠ 0 → c j z = d j z) :
    imageChannel c χ χsrc = imageChannel d χ χsrc := by
  have hweak : cutoffMultiplier χ ∘L reducedWeakOperator c =
      cutoffMultiplier χ ∘L reducedWeakOperator d := by
    simp only [reducedWeakOperator, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_finsetSum, ← ContinuousLinearMap.comp_assoc,
      measured_coefficient_eq_of_support _ _ χ _ _ (heq _)]
  simp only [imageChannel, ← ContinuousLinearMap.comp_assoc, hweak]

/-- The actual normalized coefficient extension at zero scale gives the
literal frozen periodic image. The supplied plateau is the original measurement
producer's plateau, not a newly chosen extension (`bg-uniform-normalized`,
`app:ch_background:prop:bg-frame`). -/
theorem retained_imageChannel_eq_fixedPeriodicChannel
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (χcoeff : Euclidean n → ℝ)
    (hplateau : closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1})
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χcoeff (centeredTorusRepresentative z) *
      ProtectedFlow.reducedCoefficientBackground (fun _ _ ↦ 0)
        (centeredTorusRepresentative z) j) :
    imageChannel d (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2) =
      fixedPeriodicChannel hr hcell (frozenImageArrays (cubeStress n)) := by
  apply imageChannel_eq_of_measurement_support
  intro j z hz
  have hx := FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hz)
  have hone : χcoeff (centeredTorusRepresentative z) = 1 :=
    (interior_subset (s := {x | χcoeff x = 1})) (hplateau hx)
  rw [hd, hone, one_mul, frozen_cube_imageCoefficients_eq_background j z
    (centeredTorusRepresentative z)]

/-- The actual normalized source gives a linear normal-error bound on the
supplied fixed measurement. Both constants and the source cap precede every
scale and every coefficient realization with the literal formula. The reference
is the original source-masked frozen cube image, so the normalized coercivity
assembly may choose its source cap after its frozen gap without changing any
operator (`bg-uniform-normalized`, `app:ch_background:prop:bg-frame`). -/
theorem exists_supplied_measurement_imageNormal_bounds
    (H : FlatReference n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (houter : 6 * r < 1 / 2)
    (χcoeff : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χcoeff)
    (hs : tsupport χcoeff ⊆ ball 0 (5 * r))
    (hp : closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1})
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χcoeff (centeredTorusRepresentative z) *
      ProtectedFlow.reducedCoefficientBackground (fun _ _ ↦ 0)
        (centeredTorusRepresentative z) j) :
    ∃ Bimage > (0 : ℝ), ∃ Cimage > (0 : ℝ),
    ∃ σcap > (0 : ℝ), σcap ≤ 1 ∧ (∀ j z, |d j z| ≤ Bimage) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σcap,
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j z, c j z = χcoeff (centeredTorusRepresentative z) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (centeredTorusRepresentative z) j) →
        (∀ j z, |c j z| ≤ Bimage) ∧ ‖c - d‖ ≤ Bimage * σ ∧
        ‖NormalPerturbation.normal (imageChannel c
            (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)) -
          NormalPerturbation.normal
            (fixedPeriodicChannel hr hcell (frozenImageArrays (cubeStress n)))‖ ≤ Cimage * σ := by
  obtain ⟨σ₀, hσ₀, hσ₁, c₀, c, hc₀, _hc₀smooth, _hc₀plateau, hc,
    _hcsmooth, _hcplateau, hjets, _hformula, _hweak, _hadjoint⟩ :=
    RetainedAssembly.NormalizedImage.exists_normalized_image_coefficients H
      (by positivity : 0 < 4 * r) (by linarith : 4 * r < 5 * r)
      (by linarith : 5 * r < 6 * r) houter hχ hs hp
  have hd₀ : d = c₀ := by
    funext j
    ext z
    rw [hd, hc₀]
  obtain ⟨B, hB, hzero, hbound⟩ := hjets 0
  let χ := FixedCutoffs.periodic (n := n) hr hcell 1
  let χsrc := FixedCutoffs.periodic (n := n) hr hcell 2
  let L := ‖χ‖ * (((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * B) * ‖χsrc‖
  have habsolute₀ (j : ReducedCoefficientIndex n) (z : Torus n) : |d j z| ≤ B := by
    rw [hd₀]
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, Real.norm_eq_abs] using
      hzero j (centeredTorusRepresentative z)
  have hA₀ : ‖imageChannel d χ χsrc‖ ≤ L := by
    simpa only [L, add_mul] using imageChannel_norm_le_of_bounds d χ χsrc hB.le hB.le
      (fun a i j z ↦ habsolute₀ (.inl (a, i, j)) z)
      (fun i j z ↦ habsolute₀ (.inr (i, j)) z)
  refine ⟨B, hB, 3 * L ^ 2 + 1, by positivity, σ₀, hσ₀, hσ₁, habsolute₀, ?_⟩
  intro σ hσ a ha
  have haeq : a = c σ hσ := by
    funext j
    ext z
    rw [ha, hc]
  have habsolute (j : ReducedCoefficientIndex n) (z : Torus n) : |a j z| ≤ B := by
    rw [haeq]
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, Real.norm_eq_abs] using
      (hbound σ hσ j (centeredTorusRepresentative z)).2
  have hentry (j : ReducedCoefficientIndex n) (z : Torus n) : |a j z - d j z| ≤ B * σ := by
    rw [haeq, hd₀]
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, ContinuousMap.sub_apply, Real.norm_eq_abs] using
      (hbound σ hσ j (centeredTorusRepresentative z)).1
  have hnonneg : 0 ≤ B * σ := mul_nonneg hB.le hσ.1.le
  have hnorm : ‖a - d‖ ≤ B * σ := by
    apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
    intro j
    exact (ContinuousMap.norm_le _ hnonneg).mpr (hentry j)
  have hD : ‖imageChannel a χ χsrc - imageChannel d χ χsrc‖ ≤ L * σ := by
    convert norm_imageChannel_sub_le_of_coefficient_bounds a d χ χsrc hnonneg hnonneg
      (fun a i j z ↦ hentry (.inl (a, i, j)) z)
      (fun i j z ↦ hentry (.inr (i, j)) z) using 1
    dsimp only [L]
    ring
  have hnormal := NormalPerturbation.norm_normal_add_sub_le_of_bounds
    (imageChannel d χ χsrc) (imageChannel a χ χsrc - imageChannel d χ χsrc) hA₀ hD
  simp only [add_sub_cancel] at hnormal
  have hσsq : σ ^ 2 ≤ σ := by nlinarith [hσ.2.trans hσ₁]
  have hlinear : 2 * L * (L * σ) + (L * σ) ^ 2 ≤ (3 * L ^ 2 + 1) * σ := by
    nlinarith [mul_le_mul_of_nonneg_left hσsq (sq_nonneg L)]
  refine ⟨habsolute, hnorm, ?_⟩
  rw [← retained_imageChannel_eq_fixedPeriodicChannel hr hcell χcoeff hp d hd]
  exact hnormal.trans hlinear

/-- Apply actual source coefficient convergence on the supplied fixed
measurement and coefficient masks. The bound precedes tolerance; the source cap
precedes every scale. The reference normal is the literal source-masked frozen
image from `RetainedFrozen.Coercivity` (`bg-uniform-normalized`, `bg-global-bound`). -/
theorem exists_supplied_measurement_imageNormal_threshold
    (H : FlatReference n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (houter : 6 * r < 1 / 2)
    (χcoeff : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χcoeff)
    (hs : tsupport χcoeff ⊆ ball 0 (5 * r))
    (hp : closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1})
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χcoeff (centeredTorusRepresentative z) *
      ProtectedFlow.reducedCoefficientBackground (fun _ _ ↦ 0)
        (centeredTorusRepresentative z) j) :
    ∃ Bimage > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ σcap > (0 : ℝ), σcap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) σcap,
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j z, c j z = χcoeff (centeredTorusRepresentative z) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (centeredTorusRepresentative z) j) →
        (∀ j z, |c j z| ≤ Bimage) ∧ ‖c - d‖ < ε ∧
        ‖NormalPerturbation.normal (imageChannel c
            (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)) -
          NormalPerturbation.normal
            (fixedPeriodicChannel hr hcell (frozenImageArrays (cubeStress n)))‖ < ε := by
  obtain ⟨B, hB, C, hC, σ₀, hσ₀, hσ₁, _hdB, hbound⟩ :=
    exists_supplied_measurement_imageNormal_bounds H hr hcell houter χcoeff hχ hs hp d hd
  refine ⟨B, hB, ?_⟩
  intro ε hε
  let σcap := min σ₀ (ε / (2 * (B + C)))
  have hdenom : 0 < 2 * (B + C) := by positivity
  refine ⟨σcap, lt_min hσ₀ (div_pos hε hdenom), (min_le_left _ _).trans hσ₁, ?_⟩
  intro σ hσ c hc
  obtain ⟨habsolute, hcoeff, hnormal⟩ :=
    hbound σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩ c hc
  have hbudget := (le_div_iff₀ hdenom).mp (hσ.2.trans (min_le_right _ _))
  have hBσ : 0 ≤ B * σ := mul_nonneg hB.le hσ.1.le
  have hCσ : 0 ≤ C * σ := mul_nonneg hC.le hσ.1.le
  exact ⟨habsolute, hcoeff.trans_lt (by nlinarith), hnormal.trans_lt (by nlinarith)⟩

end JanetCartan.ContinuumNormal.ActualConstruction
