module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Integral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.Atoms

/-!
# Differentiated amplitudes of the literal raw wide-band field

This is the exact integral identity needed in
`app:ch_waves:eq:individual-raw-slice`. It differentiates the SAME
`rawSliceBandIntegral`, with its physical cutoff, Fourier scalar, half
derivative, original wide band and inverse-frequency parameter `τ * 2^j`.
No weak derivative or differentiated integral identity is a hypothesis.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition NormalComparison

variable {n : ℕ} {X F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The literal differentiated band amplitude, before its `L^(s-q)`
normalization. Its frequency factor is exactly `(2^j)^q`
(`app:ch_waves:eq:individual-raw-slice`). -/
def rawSliceBandDerivativeAmplitude (S : X → Euclidean (n - 1) → ℝ)
    (A : X → Euclidean (n - 1) → F) (χ : X → ℝ) (ζ : Euclidean (n - 1))
    (τ : ℝ) (β : Euclidean (n - 1) → ℂ) (j : ℕ)
    {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s)
    (x : X) (θ : Euclidean (n - 1)) : F :=
  sliceDerivativeAmplitude
    (fun y ↦ rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) y θ)
    (fun y ↦ rawSliceBandAmplitude A χ ζ τ β j y θ) v b x

variable [FiniteDimensional ℝ X] [CompleteSpace F]

/-- All physical derivatives of the normalized SAME raw band integral are
the finite sum of exact branch integrals. Every Hilbert datum is permitted:
its integrability follows from the compact original band. The hypotheses
concern only the original smooth phase, amplitude, physical cutoff, rescaled
input mask and shifted-chart containment
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem iteratedFDeriv_normalized_rawSliceBandIntegral_eq_branches
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
    (f : WideBandL2 n j) (s : ℕ) {x : X} (hx : x ∈ U) (v : Fin s → X) :
    iteratedFDeriv ℝ s (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      rawSliceBandIntegral S A χ ζ τ β j f y) x v =
      normalOperatorScale n ((2 : ℝ) ^ j) •
        ∑ b : SliceDerivativeBranch s, (((2 : ℝ) ^ j : ℝ) : ℂ) ^ b.phaseCount •
          ∫ θ in wideBand n 0,
            (oscillatoryFactor ((2 : ℝ) ^ j)
              (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) x θ) *
                wideBandDilation n j f θ) •
              rawSliceBandDerivativeAmplitude S A χ ζ τ β j v b x θ := by
  let φ : X × Euclidean (n - 1) → ℝ := fun q ↦
    rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) q.1 q.2
  let B : X × Euclidean (n - 1) → F := fun q ↦ rawSliceBandAmplitude A χ ζ τ β j q.1 q.2
  have hφ : ContDiffOn ℝ ∞ φ (U ×ˢ Ω) :=
    contDiffOn_rawPrimaryPhaseDifference hS hζ hshift
  have hB : ContDiffOn ℝ ∞ B (U ×ˢ Ω) := by
    have hc : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦ (χ q.1 : ℂ)) (U ×ˢ Ω) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hχ.comp contDiffOn_fst (fun _ h ↦ h.1))
    have hm : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦
        (Real.sqrt ‖q.2‖ : ℂ) * β ((2 : ℝ) ^ j • q.2)) (U ×ˢ Ω) :=
      hmask.comp contDiffOn_snd (fun _ h ↦ h.2)
    have ha : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦
        A q.1 (ζ + (τ * (2 : ℝ) ^ j) • q.2)) (U ×ˢ Ω) := by
      have hmap : ContDiffOn ℝ ∞ (fun q : X × Euclidean (n - 1) ↦
          (q.1, ζ + (τ * (2 : ℝ) ^ j) • q.2)) (U ×ˢ Ω) := by fun_prop
      exact hA.comp hmap (fun q hq ↦ ⟨hq.1, hshift q.2 hq.2⟩)
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
  let T : X → F := fun y ↦ ∫ θ in wideBand n 0, wideBandDilation n j f θ •
    (Complex.exp (Complex.I * ((2 : ℝ) ^ j * φ (y, θ) : ℝ)) • B (y, θ))
  have hT : ContDiffOn ℝ ∞ T U :=
    contDiffOn_weightedCompactIntegral hU hΩ hK hband hf
      ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (contDiffOn_const.mul hφ))).cexp.smul hB)
  have hid : (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      rawSliceBandIntegral S A χ ζ τ β j f y) =
      fun y ↦ normalOperatorScale n ((2 : ℝ) ^ j) • T y := by
    funext y
    rw [normalized_rawSliceBandIntegral hn S A χ ζ hτ β j hβ f y]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with θ
    change (oscillatoryFactor ((2 : ℝ) ^ j) (φ (y, θ)) * wideBandDilation n j f θ) • B (y, θ) =
      wideBandDilation n j f θ • (oscillatoryFactor ((2 : ℝ) ^ j) (φ (y, θ)) • B (y, θ))
    rw [mul_smul]
    exact smul_comm _ _ _
  rw [hid, iteratedFDeriv_const_smul_apply'
    ((hT.contDiffAt (hU.mem_nhds hx)).of_le (by simp)), smul_apply]
  congr 1
  exact iteratedFDeriv_compactOscillatoryIntegral_eq_branches hU hΩ hK hband hf hφ hB
    ((2 : ℝ) ^ j) s hx v

end JanetCartan.RawPrimary.SliceBounds
