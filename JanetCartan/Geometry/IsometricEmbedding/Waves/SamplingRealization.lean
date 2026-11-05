module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Family
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Geometry

/-! # One separated realization for every unchanged prefix

Conditional deduction of `app:ch_waves:eq:sampling-all-prefixes` and
`app:ch_waves:eq:background-quadrature`. The fixed finite chart family uses the
product of the literal `Sampling.shiftLaw` measures. No successful event or
sample is an input. The event is proved measurable, its probability tends to
one, and it is intersected with almost-sure shift admissibility.

The full-output Bernstein inequality, its common positive block/variance upper
parameters, the trace bound, the prefix count and actual carrier derivative
bounds remain analytic inputs. Thus this is not the unconditional sampling
or Janet–Cartan theorem. `jc-simultaneous-sampling` must instantiate them with
the actual WKB rows on the paper's Euclidean Hilbert spaces. Later canonical
updates may select only from the already covered prefixes. The background
conclusion is universal in the carrier family, so it requires no new sampling
when accuracy is changed.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace JanetCartan.Sampling.Realization
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

variable {J ι E H : Type*} [Fintype J]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The mean normal is exactly the manuscript's colored-mask Lebesgue integral
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem patchMeanNormal_eq_colored {p : ℕ} {B h W : ℝ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hψ : Continuous ψ) (hwc : Continuous w) (hh : h ≠ 0)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    patchMeanNormal p B ψ w h T =
      ∑ c, ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h)) w h c z •
        (ψ z • atomNormal (T c z)) := by
  have he := sum_blockIntegrals_eq_sum_coloredMask_integrals
    (integerCube (blockCutoff p B h)) hw hwc hh
    (fun c z ↦ ψ z • atomNormal (T c z)) (fun c ↦
      hψ.smul ((hT c).clm_comp (ContinuousLinearMap.adjoint.continuous.comp (hT c))))
  simpa only [patchMeanNormal, smul_smul, mul_comm] using he

/-- On the literal finite chart law, the all-prefix event has probability tending
to one, conditional on full-output concentration and the uniform scalar bounds
of `app:ch_waves:eq:sampling-all-prefixes`. -/
theorem tendsto_familyGood_probability_one {p : ℕ} (B : ℝ)
    {ψ : J → Point → ℝ} {w : ℝ → ℝ}
    (hψ : ∀ j, Continuous (ψ j)) (hw : Continuous w)
    (s : ℝ → Finset ι)
    (T : ℝ → ι → J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ Λ k j c, Continuous (T Λ k j c))
    (τ : ℝ → ι → ℝ) (n : ℕ) {A C K ε : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hε : 0 < ε)
    (hcard : ∀ᶠ Λ in atTop, ((s Λ).card : ℝ) ≤ K * Λ)
    (htrace : ∀ᶠ Λ in atTop, ∀ k ∈ s Λ,
      0 ≤ τ Λ k ∧ τ Λ k ≤ C * (A * (Λ * samplingMesh ε Λ ^ 3)) * Λ ^ n)
    (hconcentration : ∀ Λ > 0, ∀ k ∈ s Λ, ∀ t > 0,
      let R := A * (Λ * samplingMesh ε Λ ^ 3)
      let v := C * R
      v + R * t / 3 ≤ t ^ 2 →
      familyShiftLaw J p B (samplingMesh ε Λ)
        {ξ | t < ‖familyDeviation p B ψ w (samplingMesh ε Λ) (T Λ k) ξ‖} ≤
      ENNReal.ofReal (14 * τ Λ k / v * Real.exp (-(t ^ 2 / (2 * (v + R * t / 3)))))) :
    Tendsto (fun Λ => (familyShiftLaw J p B (samplingMesh ε Λ)).real
      (allPrefixesGood (s Λ) (fun k ↦ familyDeviation p B ψ w (samplingMesh ε Λ) (T Λ k))
        (samplingTolerance ε Λ))) atTop (𝓝 1) :=
  tendsto_probability_one _
    (fun _Λ hΛ ↦ isProbabilityMeasure_familyShiftLaw p B (Real.rpow_pos_of_pos hΛ _))
    s _ τ n hA hC hε
    (fun Λ ↦ measurableSet_familyGood B _ hψ hw _ _ (hT Λ) _)
    hcard htrace hconcentration

/-- A single admissible separated realization satisfies every fixed prefix
normal bound and deterministic background quadrature, simultaneously over a
fixed finite chart/color family (`app:ch_waves:thm:sampling`,
`app:ch_waves:eq:sampling-all-prefixes`, `app:ch_waves:eq:background-quadrature`).

Only the precise lower-level concentration, trace and count bounds are assumed;
there is no successful-sample hypothesis. Background carrier regularity and
actual derivative bounds are quantified after the chosen shifts, so this same
realization serves every later carrier accuracy with those bounds. -/
theorem eventually_exists_separated_realization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} {P : J → ℝ} {ψ : J → Point → ℝ}
    (hψ : ∀ j, PatchBounds (ψ j) B (P j)) (hψc : ∀ j, Continuous (ψ j))
    (s : ℝ → Finset ι)
    (T : ℝ → ι → J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ Λ k j c, Continuous (T Λ k j c))
    (τ : ℝ → ι → ℝ) (n : ℕ) {A C K ε : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hε : 0 < ε)
    (hcard : ∀ᶠ Λ in atTop, ((s Λ).card : ℝ) ≤ K * Λ)
    (htrace : ∀ᶠ Λ in atTop, ∀ k ∈ s Λ,
      0 ≤ τ Λ k ∧ τ Λ k ≤ C * (A * (Λ * samplingMesh ε Λ ^ 3)) * Λ ^ n)
    (hconcentration : ∀ Λ > 0, ∀ k ∈ s Λ, ∀ t > 0,
      let R := A * (Λ * samplingMesh ε Λ ^ 3)
      let v := C * R
      v + R * t / 3 ≤ t ^ 2 →
      familyShiftLaw J p B (samplingMesh ε Λ)
        {ξ | t < ‖familyDeviation p B ψ (convolvedBoxWindow κ p)
          (samplingMesh ε Λ) (T Λ k) ξ‖} ≤
      ENNReal.ofReal (14 * τ Λ k / v * Real.exp (-(t ^ 2 / (2 * (v + R * t / 3)))))) :
    ∀ᶠ Λ in atTop, ∃ ξ : J → ShiftSpace p B (samplingMesh ε Λ),
      (∀ j q i, 0 ≤ extendedShift (ξ j) q i ∧
        extendedShift (ξ j) q i < samplingMesh ε Λ) ∧
      (∀ k ∈ s Λ, ‖familyDeviation p B ψ (convolvedBoxWindow κ p)
        (samplingMesh ε Λ) (T Λ k) ξ‖ ≤ samplingTolerance ε Λ) ∧
      (∀ j, SampleGeometry p B (P j) 1 (ψ j) (convolvedBoxWindow κ p)
        (samplingMesh ε Λ) (extendedShift (ξ j))) ∧
      (∀ (G : J → (Fin 3 → Fin (p + 1)) → Point → V) (D : J → ℝ),
        (∀ j c, ContDiff ℝ p (fun z ↦ ψ j z • G j c z)) →
        (∀ j, 0 ≤ D j) →
        (∀ j c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ j z • G j c z) z‖ ≤ D j) →
        ‖familyBackgroundError p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
          (fun j ↦ extendedShift (ξ j)) G‖ ≤
            backgroundQuadratureConstant p B * (∑ j, D j) * samplingMesh ε Λ ^ p) := by
  have hwc := (contDiff_convolvedBoxWindow hc hs p).continuous
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hn hk hp
  have ht := tendsto_familyGood_probability_one B hψc hwc s T hT τ n
    hA hC hε hcard htrace hconcentration
  have hpos := ht.eventually (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpos] with Λ hΛ hpos
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hh : 0 < samplingMesh ε Λ := Real.rpow_pos_of_pos hΛpos _
  have hh₁ : samplingMesh ε Λ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith)
  obtain ⟨ξ, hgood, hξ⟩ := exists_mem_of_positive_of_ae _ hpos
    (ae_admissible_familyShift (J := J) (p := p) (B := B) hh)
  refine ⟨ξ, hξ, hgood, ?_, ?_⟩
  · intro j
    exact sampleGeometry_of_admissible hw (hψ j) hh hh₁ _ (hξ j)
  · intro G D hG hD hderiv
    exact norm_familyBackgroundError_le hc hs hm hn hk hp hψ G hG D hD hderiv hh hh₁ _ hξ

end JanetCartan.Sampling.Realization
