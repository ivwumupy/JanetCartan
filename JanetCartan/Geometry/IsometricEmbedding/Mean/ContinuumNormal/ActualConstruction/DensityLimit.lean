module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.SourceComparison

/-!
# The zero-scale density in the actual normalized carrier

The original prescribed scalar evaluates its density at the divided ODE
footpoint. At zero scale the spatial part is the differential of the seed
footpoint, and it retains the transverse label on the initial Cauchy section.
Thus `sourceDensityPairLimit`, supplied by the actual wider-density comparison,
has spatial dependence even at zero. The frozen label-multiplier gap instead
uses `v (0, z)`. A smooth density in the original fixed-low class distinguishes
these two expressions; they cannot be identified during coercivity assembly.

Consumer: joining `NormalizedFrozenGap.exists_uniform_source_frozen_gaps`
with `NormalizedNormalLimit` on one weighted row. The missing analytic input is
coercivity for the limit with BOTH divided ODE labels, or a checked normal
comparison with the realized frozen label model. This file computes the
actual density limit; it does not assume or assert that missing operator gap.
Sources: `app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`app:ch_background:eq:bg-full-complex-amplitude`, `bg-frame`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.ActualConstruction

open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier FrozenModel
open CarrierVariation.FamilyInputs PositiveReference WideDensity
open NormalizedBackground.SourceGeometry

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The actual source-density footpoint at zero is the seed spatial
differential, with its original carrier label unchanged
(`app:ch_background:eq:bg-Nsigma`, `bg-full-complex-amplitude`). -/
theorem sourceDensityFootpointExtension_zero_eq_differential
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (x : Euclidean n) (z : CarrierParameter) :
    sourceDensityFootpointExtension T Y (0, (x, z)) =
      (WithLp.toLp 2 (fun j ↦ fderiv ℝ (fun y ↦ (densityFootpoint T Y (y, z)).1 j) 0 x),
        parameter z) := by
  simp only [sourceDensityFootpointExtension, sourcePhaseExtension_zero, inner_gradient_left]

/-- The retained adapted section is the original time-zero Cauchy plane
(`app:ch_waves:thm:leading`, `app:ch_background:eq:bg-T`). -/
private theorem densityFootpoint_initial_section
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (y : Euclidean (n - 1)) (z : CarrierParameter) :
    densityFootpoint T Y (T.data.adapted.embedding y, z) = Y (0, (y, parameter z)) := by
  rw [densityFootpoint_eq, coordinates_apply]
  have he : adaptedCoordinates T.data.adapted (T.data.adapted.embedding y) = (0, y) := by
    simpa only [adaptedCoordinates_symm_apply, zero_smul, zero_add] using
      (adaptedCoordinates T.data.adapted).apply_symm_apply (0, y)
  rw [he]

/-- On the initial section the divided zero-scale ODE label is exactly
the transverse coordinate. The seed null-flow constructor supplies smoothness
and the time-zero inverse identity on an open initial ball, hence `hinit`.
This identifies the limit used by the wider-density comparison
(`app:ch_background:eq:bg-Nsigma`, `bg-full-complex-amplitude`). -/
theorem sourceDensityFootpointExtension_zero_on_initial_section
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z : CarrierParameter)
    (hY : DifferentiableAt ℝ Y (0, (0, parameter z)))
    (hinit : ∀ᶠ q in 𝓝 ((0 : Euclidean (n - 1)), parameter z), Y (0, q) = q)
    (y : Euclidean (n - 1)) :
    sourceDensityFootpointExtension T Y (0, (T.data.adapted.embedding y, z)) =
      (y, parameter z) := by
  apply Prod.ext
  · ext j
    simp only [sourceDensityFootpointExtension, WithLp.ofLp_toLp,
      sourcePhaseExtension_zero, inner_gradient_left]
    let E := T.data.adapted.embedding.toContinuousLinearMap
    let f := fun x : Euclidean n ↦ (densityFootpoint T Y (x, z)).1 j
    have hcoord : densityCoordinates T ((0 : Euclidean n), z) = (0, (0, parameter z)) := by
      simp [densityCoordinates, coordinates_apply]
    have hf : DifferentiableAt ℝ f 0 := by
      have hy : DifferentiableAt ℝ (fun x : Euclidean n ↦ densityFootpoint T Y (x, z)) 0 := by
        unfold densityFootpoint
        apply DifferentiableAt.comp 0 (hcoord.symm ▸ hY)
        exact (densityCoordinates T).differentiableAt.comp 0
          (differentiableAt_id.prodMk (differentiableAt_const z))
      exact (PiLp.proj 2 (fun _ : Fin (n - 1) ↦ ℝ) j).differentiableAt.comp 0 hy.fst
    have he : (fun u : Euclidean (n - 1) ↦ f (E u)) =ᶠ[𝓝 0] (fun u ↦ u j) := by
      have hi := ((continuous_id.prodMk continuous_const).continuousAt
        (x := (0 : Euclidean (n - 1)))).tendsto.eventually hinit
      filter_upwards [hi] with u hu
      change (densityFootpoint T Y (T.data.adapted.embedding u, z)).1 j = u j
      simp only [id_eq] at hu
      rw [densityFootpoint_initial_section T Y u z, hu]
    have hc := fderiv_comp (f := E) (g := f) 0
      (by simpa only [map_zero] using hf) E.differentiableAt
    rw [E.fderiv, map_zero] at hc
    have hid := he.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (f ∘ E) 0 =
      fderiv ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n - 1) ↦ ℝ) j) 0 at hid
    rw [ContinuousLinearMap.fderiv] at hid
    have ha := congrArg (fun A ↦ A y) (hc.symm.trans hid)
    simpa only [ContinuousLinearMap.comp_apply, PiLp.proj_apply, E, f,
      LinearIsometry.coe_toContinuousLinearMap] using ha
  · rfl

/-- The original density class contains smooth densities with nonconstant
transverse trace at any prescribed finite low order. The original `L/4` and
`L/8` balls and the full interval are retained (`app:ch_background:prop:bg-frame`). -/
private theorem exists_permitted_density_with_nonconstant_transverse_trace
    (y : Euclidean (n - 1)) (hy : y ≠ 0) (zc : Euclidean 3)
    {L : ℝ} (hL : 0 < L) (d₀ : ℕ) :
    ∃ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiff ℝ ∞ v ∧
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zc) (L / 4), 0 < 1 + v q) ∧
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zc) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) ∧
      cNorm (closedBall ((0 : Euclidean (n - 1)), zc) (L / 8)) d₀ v ≤ 1 ∧
      (∀ z, v (0, z) = 0) ∧ (∀ z, 0 < v (y, z)) := by
  let f : Euclidean (n - 1) × Euclidean 3 → ℝ := fun q ↦ inner ℝ y q.1
  have hf : ContDiff ℝ ∞ f := contDiff_const.inner ℝ contDiff_fst
  let K := closedBall ((0 : Euclidean (n - 1)), zc) (L / 4)
  let B := cNorm K d₀ f
  have hB : 0 ≤ B := cNorm_nonneg ..
  let a := 1 / (4 * (B + 1))
  have ha : 0 < a := by dsimp only [a]; positivity
  let v := a • f
  have hv : ContDiff ℝ ∞ v := hf.const_smul a
  have hproduct : a * (4 * (B + 1)) = 1 := div_mul_cancel₀ 1 (by positivity)
  have hab : a * B ≤ 1 / 4 := by nlinarith
  have hnorm : cNorm K d₀ v ≤ 1 / 4 := by
    rw [cNorm_smul a (hf.of_le (by simp)), Real.norm_eq_abs, abs_of_pos ha]
    exact hab
  have hpoint (q) (hq : q ∈ K) : |v q| ≤ 1 / 4 :=
    (norm_le_cNorm (isCompact_closedBall _ _) (hv.of_le (by simp)) hq).trans hnorm
  have hsmall : closedBall ((0 : Euclidean (n - 1)), zc) (L / 8) ⊆ K :=
    closedBall_subset_closedBall (by linarith)
  refine ⟨v, hv, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hp := (abs_le.mp (hpoint q (ball_subset_closedBall hq))).1
    linarith
  · intro q hq
    have hp := abs_le.mp (hpoint q (hsmall hq))
    constructor <;> linarith [hp.1, hp.2]
  · exact (cNorm_mono_set hsmall (isCompact_closedBall _ _) (hv.of_le (by simp))).trans
      (hnorm.trans (by norm_num))
  · intro z
    simp [v, f]
  · intro z
    exact mul_pos ha (real_inner_self_pos.mpr hy)

/-- Both physical positions retain their own initial transverse label in
the actual zero-scale density. This is the literal `sourceDensityPairLimit`
consumed by the full normal-amplitude comparison
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-Nsigma`). -/
theorem sourceDensityPairLimit_on_initial_section
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z : CarrierParameter)
    (hY : DifferentiableAt ℝ Y (0, (0, parameter z)))
    (hinit : ∀ᶠ q in 𝓝 ((0 : Euclidean (n - 1)), parameter z), Y (0, q) = q)
    (y y' : Euclidean (n - 1)) (η : Euclidean (n - 1))
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    sourceDensityPairLimit T v Y
        ((T.data.adapted.embedding y, T.data.adapted.embedding y'), z, η) =
      (1 + v (y, parameter z)) * (1 + v (y', parameter z)) := by
  simp only [sourceDensityPairLimit, densityPair, densityEndpoint, Bool.false_eq_true,
    ↓reduceIte, sourceDensityFootpointExtension_zero_on_initial_section T Y z hY hinit]

/-- A density in the ORIGINAL permitted class distinguishes the actual
divided-footpoint limit from the frozen label square. The same initial
ball, carrier label and any prescribed low order are retained; no small
or unit-density substitution justifies identifying the two limits.
This locates the missing weighted-limit coercivity input for
`NormalizedFrozenGap` and the actual normal assembly
(`app:ch_background:prop:bg-frame`, `bg-uniform-normalized`). -/
theorem exists_permitted_density_source_limit_ne_frozen
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z : CarrierParameter)
    (hY : DifferentiableAt ℝ Y (0, (0, parameter z)))
    (hinit : ∀ᶠ q in 𝓝 ((0 : Euclidean (n - 1)), parameter z), Y (0, q) = q)
    (y : Euclidean (n - 1)) (hy : y ≠ 0) (η : Euclidean (n - 1))
    (zc : Euclidean 3) {L : ℝ} (hL : 0 < L) (d₀ : ℕ) :
    ∃ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiff ℝ ∞ v ∧
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zc) (L / 4), 0 < 1 + v q) ∧
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zc) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) ∧
      cNorm (closedBall ((0 : Euclidean (n - 1)), zc) (L / 8)) d₀ v ≤ 1 ∧
      sourceDensityPairLimit T v Y
        ((T.data.adapted.embedding y, T.data.adapted.embedding y), z, η) ≠
          (1 + v (0, parameter z)) ^ 2 := by
  obtain ⟨v, hv, hpositive, hrange, hnorm, hzero, hnonconstant⟩ :=
    exists_permitted_density_with_nonconstant_transverse_trace y hy zc hL d₀
  refine ⟨v, hv, hpositive, hrange, hnorm, ?_⟩
  rw [sourceDensityPairLimit_on_initial_section T Y z hY hinit y y η v, hzero]
  have hp := hnonconstant (parameter z)
  intro he
  nlinarith [sq_nonneg (v (y, parameter z))]

end JanetCartan.ContinuumNormal.ActualConstruction
