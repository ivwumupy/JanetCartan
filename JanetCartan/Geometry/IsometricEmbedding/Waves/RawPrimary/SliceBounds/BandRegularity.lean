module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BranchIntegral

/-!
# Smoothness needed for finite differentiation of the original bands

This is used to commute the finite original-band sum with physical derivatives
in `app:ch_waves:eq:individual-raw-slice`. The density is arbitrary original
Hilbert data. Only the phase, amplitude and masks are differentiated.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition NormalComparison

variable {n : ℕ} {X F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The normalized SAME band integral is smooth on the original physical
chart for arbitrary band data. Compactness supplies domination, with no
frequency-uniform estimate claimed by this lemma
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiffOn_normalized_rawSliceBandIntegral
    (hn : 1 ≤ n) {U : Set X} {V Ω : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hband : wideBand n 0 ⊆ Ω)
    {S : X → Euclidean (n - 1) → ℝ} {A : X → Euclidean (n - 1) → F}
    {χ : X → ℝ} {ζ : Euclidean (n - 1)} {τ : ℝ}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U) (hζ : ζ ∈ V) (hτ : τ ≠ 0)
    (β : Euclidean (n - 1) → ℂ) (j : ℕ)
    (hβ : ∀ η ∉ wideBand n j, β η = 0)
    (hmask : ContDiffOn ℝ ∞
      (fun θ ↦ (Real.sqrt ‖θ‖ : ℂ) * β ((2 : ℝ) ^ j • θ)) Ω)
    (hshift : ∀ θ ∈ Ω, ζ + (τ * (2 : ℝ) ^ j) • θ ∈ V)
    (f : WideBandL2 n j) :
    ContDiffOn ℝ ∞ (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      rawSliceBandIntegral S A χ ζ τ β j f y) U := by
  let φ : X × Euclidean (n - 1) → ℝ := fun q ↦
    rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) q.1 q.2
  let B : X × Euclidean (n - 1) → F := fun q ↦ rawSliceBandAmplitude A χ ζ τ β j q.1 q.2
  have hφ : ContDiffOn ℝ ∞ φ (U ×ˢ Ω) :=
    contDiffOn_rawPrimaryPhaseDifference hS hζ hshift
  have hc : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦ (χ q.1 : ℂ)) (U ×ˢ Ω) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hχ.comp contDiffOn_fst (fun _ h ↦ h.1))
  have hm : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦
      (Real.sqrt ‖q.2‖ : ℂ) * β ((2 : ℝ) ^ j • q.2)) (U ×ˢ Ω) :=
    hmask.comp contDiffOn_snd (fun _ h ↦ h.2)
  have ha : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦
      A q.1 (ζ + (τ * (2 : ℝ) ^ j) • q.2)) (U ×ˢ Ω) :=
    hA.comp (f := fun q : X × Euclidean (n - 1) ↦
      (q.1, ζ + (τ * (2 : ℝ) ^ j) • q.2)) (by fun_prop)
      (fun q hq ↦ ⟨hq.1, hshift q.2 hq.2⟩)
  have hB : ContDiffOn ℝ ∞ B (U ×ˢ Ω) := by
    have hh : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦
        ((χ q.1 : ℂ) * ((Real.sqrt ‖q.2‖ : ℂ) * β ((2 : ℝ) ^ j • q.2))) •
          A q.1 (ζ + (τ * (2 : ℝ) ^ j) • q.2)) (U ×ˢ Ω) := (hc.mul hm).smul ha
    simpa only [B, rawSliceBandAmplitude, mul_assoc] using hh
  have hK : IsCompact (wideBand n 0) :=
    (isCompact_closedBall _ _).diff Metric.isOpen_ball
  let : IsFiniteMeasure (volume.restrict (wideBand n 0)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hf : IntegrableOn (wideBandDilation n j f) (wideBand n 0) volume :=
    MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp _)
  have h := (contDiffOn_weightedCompactIntegral hU hΩ hK hband hf
    (((contDiffOn_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_const (c := (2 : ℝ) ^ j)).mul hφ))).cexp.smul hB)).const_smul
        (normalOperatorScale n ((2 : ℝ) ^ j))
  apply h.congr
  intro x _
  rw [normalized_rawSliceBandIntegral hn S A χ ζ hτ β j hβ f x]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with θ
  change (oscillatoryFactor ((2 : ℝ) ^ j) (φ (x, θ)) * wideBandDilation n j f θ) • B (x, θ) = _
  rw [mul_smul, smul_comm]
  rfl

/-- The original physical cutoff extends this same normalized band smoothly
by zero, so finite sums can be differentiated globally
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiff_normalized_rawSliceBandIntegral
    (hn : 1 ≤ n) {U : Set X} {V Ω : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hband : wideBand n 0 ⊆ Ω)
    {S : X → Euclidean (n - 1) → ℝ} {A : X → Euclidean (n - 1) → F}
    {χ : X → ℝ} {ζ : Euclidean (n - 1)} {τ : ℝ}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U) (hχU : tsupport χ ⊆ U) (hζ : ζ ∈ V) (hτ : τ ≠ 0)
    (β : Euclidean (n - 1) → ℂ) (j : ℕ)
    (hβ : ∀ η ∉ wideBand n j, β η = 0)
    (hmask : ContDiffOn ℝ ∞
      (fun θ ↦ (Real.sqrt ‖θ‖ : ℂ) * β ((2 : ℝ) ^ j • θ)) Ω)
    (hshift : ∀ θ ∈ Ω, ζ + (τ * (2 : ℝ) ^ j) • θ ∈ V)
    (f : WideBandL2 n j) :
    ContDiff ℝ ∞ (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      rawSliceBandIntegral S A χ ζ τ β j f y) := by
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hU
    (contDiffOn_normalized_rawSliceBandIntegral hn hU hΩ hband hS hA hχ hζ hτ
      β j hβ hmask hshift f)
  apply Subset.trans (tsupport_smul_subset_right _ _)
  apply Subset.trans (tsupport_smul_subset_left (fun y ↦ (χ y : ℂ)) _)
  exact (tsupport_comp_subset (g := fun a : ℝ ↦ (a : ℂ)) (by simp) χ).trans hχU

end JanetCartan.RawPrimary.SliceBounds
