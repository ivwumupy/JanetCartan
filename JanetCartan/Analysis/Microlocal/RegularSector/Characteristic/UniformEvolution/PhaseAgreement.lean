module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ConicConstruction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds

/-!
# The retained auxiliary phase gives the same solver kernels

The germ input below is exactly the union-of-supports conclusion of
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`, applied
to its two literal collared matrices. It identifies the conic phase with
the already constructed smooth phase `G`, without replacing either chart or
amplitude. Both masks and the original Fourier multiplier remain present.

Consumers: the solver test action and its reversed-triangle adjoint in
`app:ch_regular_base:lem:retarded-kernel` and `fixed-time-representation`.
No boundedness is inferred merely from phase congruence.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open AmplitudeBounds ConicPhase FourierIntegral EvolutionIntegral
open KernelIdentification UncutTestAction
variable {d q : ℕ}
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The original support germs imply equality wherever the actual solver
amplitude is nonzero. The two matrices are the producer's collared `Fs 0`
and `Fs 1` (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem solver_phase_eq_on_support
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    {p : T} (hp : (W₀ + W₁) p ≠ 0) : G p = phase ℓ C p := by
  apply (hG p ?_).eq_of_nhds
  by_cases h₀ : W₀ p = 0
  · right
    apply subset_tsupport W₁
    intro h₁
    exact hp (by simp [h₀, h₁])
  · exact Or.inl (subset_tsupport W₀ h₀)

/-- The literal elapsed graph keeps the same amplitude, source mask and
multiplier when using the producer's smooth supported phase. This equality
also preserves its literal Hilbert adjoint (`fixed-time-representation`). -/
theorem solver_elapsedGraph_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ) (r : ℝ) :
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β r =
      elapsedGraph (curriedPhase ℓ C)
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β r := by
  apply FullLowBounds.fullGraphOperator_phase_congr
  intro x y ξ hA
  have hW : (W₀ + W₁) (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ≠ 0 := by
    intro hz
    apply hA
    simp only [elapsedAmplitude, curryCharacteristicMatrix, Pi.add_apply] at hz ⊢
    rw [hz]
    simp
  exact congrArg (fun v : ℝ ↦ (x 0 - r) * ξ 0 + v)
    (solver_phase_eq_on_support ℓ C W₀ W₁ G hG hW)

/-- Equality of the original uncut retarded test actions, with source
multiplication before Fourier multiplication and the physical normalization
unchanged (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem solver_retardedPhysicalIntegral_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (a : ℝ) (u : graphTestSpace (d + 1) q) (x : E) :
    retardedPhysicalIntegral (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β hs a u x =
      retardedPhysicalIntegral (curriedPhase ℓ C)
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β hs a u x := by
  unfold retardedPhysicalIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  apply congrFun
  apply graphOperator_phase_congr
  intro y z η hW
  exact solver_phase_eq_on_support ℓ C W₀ W₁ G hG hW

/-- The same supported replacement preserves the original reversed time
triangle with its conjugate multiplier. This is a literal kernel identity,
independent of later bounded realization (`retarded-kernel`). -/
theorem solver_reverseRetardedFrequency_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout β : E → ℂ) (u : E → Fin q → ℂ) (a c : ℝ) (ξ : E) :
    reverseRetardedFrequency (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout β u a c ξ =
      reverseRetardedFrequency (curriedPhase ℓ C)
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout β u a c ξ := by
  have he (s t : ℝ) (y : Euclidean d) :
      reverseTimeFourierKernel (fun t s y η ↦ G (t, (s, (y, η))))
          (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout u ξ t s y =
        reverseTimeFourierKernel (curriedPhase ℓ C)
          (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout u ξ t s y := by
    by_cases hW : (W₀ + W₁) (t, (s, (y, spatialPart ξ))) = 0
    · change W₀ (t, (s, (y, spatialPart ξ))) + W₁ (t, (s, (y, spatialPart ξ))) = 0 at hW
      simp only [reverseTimeFourierKernel, curryCharacteristicMatrix, Pi.add_apply, hW,
        Matrix.conjTranspose_zero, Matrix.zero_mulVec, smul_zero]
    · unfold reverseTimeFourierKernel
      dsimp only
      rw [solver_phase_eq_on_support ℓ C W₀ W₁ G hG hW]
      rfl
  unfold reverseRetardedFrequency
  simp_rw [he]

/-- The residual's retained phase germ is only asserted on the time plateau.
The actual output mask suffices to transfer its elapsed graph, using precisely
that weaker producer conclusion (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem residual_elapsedGraph_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W : T → Mat) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1)) (r : ℝ) :
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W) χout χsource β r =
      elapsedGraph (curriedPhase ℓ C) (curryCharacteristicMatrix W) χout χsource β r := by
  apply FullLowBounds.fullGraphOperator_phase_congr
  intro x y ξ hA
  have hx : χout x ≠ 0 := fun hx ↦ hA
    (elapsedAmplitude_eq_zero_of_mask _ χout χsource β r x y ξ (Or.inl hx))
  have hW : W (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ≠ 0 := by
    intro hz
    apply hA
    simp [elapsedAmplitude, curryCharacteristicMatrix, hz]
  exact congrArg (fun v : ℝ ↦ (x 0 - r) * ξ 0 + v)
    ((hG _ (hout x hx) hW).eq_of_nhds)

/-- The residual's original retarded action is unchanged on the actual output
plateau. Only the weaker residual germ returned by `ConicConstruction` is used;
the source mask still acts before Fourier multiplication (`retarded-kernel`). -/
theorem residual_retardedPhysicalIntegral_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W : T → Mat) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (hs : ContDiff ℝ ∞ χsource) (a : ℝ)
    (u : graphTestSpace (d + 1) q) (x : E) :
    retardedPhysicalIntegral (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W) χout χsource β hs a u x =
      retardedPhysicalIntegral (curriedPhase ℓ C)
        (curryCharacteristicMatrix W) χout χsource β hs a u x := by
  by_cases hx : χout x = 0
  · simp only [retardedPhysicalIntegral, hx, zero_smul]
  unfold retardedPhysicalIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  unfold graphOperator
  dsimp only
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hW : W (x 0, (s, (spatialPart x, η))) = 0
  · simp only [curryCharacteristicMatrix, hW, Matrix.zero_mulVec, smul_zero]
  · unfold graphOscillation
    dsimp only
    rw [(hG _ (hout x hx) hW).eq_of_nhds]
    rfl

/-- The SAME output plateau suffices for the residual's reversed triangle.
This retains the conjugate transpose, conjugate right multiplier and original
time endpoints (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem residual_reverseRetardedFrequency_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W : T → Mat) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout β : E → ℂ)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (u : E → Fin q → ℂ) (a c : ℝ) (ξ : E) :
    reverseRetardedFrequency (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W) χout β u a c ξ =
      reverseRetardedFrequency (curriedPhase ℓ C)
        (curryCharacteristicMatrix W) χout β u a c ξ := by
  have he (s t : ℝ) (y : Euclidean d) :
      reverseTimeFourierKernel (fun t s y η ↦ G (t, (s, (y, η))))
          (curryCharacteristicMatrix W) χout u ξ t s y =
        reverseTimeFourierKernel (curriedPhase ℓ C)
          (curryCharacteristicMatrix W) χout u ξ t s y := by
    by_cases hx : χout (timeSpacePoint t y) = 0
    · simp only [reverseTimeFourierKernel, hx, star_zero, zero_smul,
        Matrix.mulVec_zero, smul_zero]
    by_cases hW : W (t, (s, (y, spatialPart ξ))) = 0
    · simp only [reverseTimeFourierKernel, curryCharacteristicMatrix, hW,
        Matrix.conjTranspose_zero, Matrix.zero_mulVec, smul_zero]
    have hk : κ =ᶠ[𝓝 t] (fun _ ↦ 1) := by
      simpa only [timeSpacePoint_time] using hout (timeSpacePoint t y) hx
    unfold reverseTimeFourierKernel
    dsimp only
    rw [(hG _ hk hW).eq_of_nhds]
    rfl
  unfold reverseRetardedFrequency
  simp_rw [he]

/-- The solver's datum-wise integral is exactly the original supported-phase
integral. Consequently any constructed bounded realization has the SAME
action; this equality alone asserts no boundedness (`fixed-time-representation`). -/
theorem solver_elapsedGraphIntegral_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ) (Δ : ℝ) (u : SpacetimeL2 d q) :
    elapsedGraphIntegral Δ (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β u =
      elapsedGraphIntegral Δ (curriedPhase ℓ C)
        (curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁) χout χsource β u := by
  unfold elapsedGraphIntegral
  simp_rw [solver_elapsedGraph_eq_supported ℓ C W₀ W₁ G hG]

/-- The residual's supported phase gives the identical datum-wise integral
on the actual output plateau (`energy-complete-residual`). -/
theorem residual_elapsedGraphIntegral_eq_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W : T → Mat) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (Δ : ℝ) (u : SpacetimeL2 d q) :
    elapsedGraphIntegral Δ (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix W) χout χsource β u =
      elapsedGraphIntegral Δ (curriedPhase ℓ C)
        (curryCharacteristicMatrix W) χout χsource β u := by
  unfold elapsedGraphIntegral
  simp_rw [residual_elapsedGraph_eq_supported ℓ C W G κ hG χout χsource β hout]

end JanetCartan.RegularSector.Characteristic.UniformEvolution
