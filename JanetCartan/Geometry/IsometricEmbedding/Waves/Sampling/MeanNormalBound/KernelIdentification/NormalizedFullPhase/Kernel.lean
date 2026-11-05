module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.Normal

/-!
# The full two-position inverse-Jacobian kernel

Connects the actual full-band normal to the actual `UniformNormalData` kernel
in `app:ch_osc:eq:osc-exact-normal-kernel`. The global smooth zero extension
retains both physical positions; on the physical chart its amplitude is the
literal inverse-Jacobian amplitude on the averaged-gradient image.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal
namespace JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
open SamplingKernelBounds ContinuumRow NormalComparison Pseudodifferential RawInputPartition
open ColoredNormalComparison RawInputHilbert AmplitudeBound

/-- The actual inverse-coordinate normal kernel, with the full Fourier
prefactor and both physical positions (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
def fullPhaseInverseKernel {n r : ℕ} {G : UniformNormalGeometry n r}
    {C : ℕ → ℝ} (F : UniformNormalData G C) (K ε : ℝ) (x y : Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ :=
  (K / (2 * Real.pi)) ^ n • ∫ ξ,
    oscillatoryFactor K (inner ℝ (x - y) ξ) •
      F.pairedInverseAmplitude ε ξ (pairedPosition x y)

/-- The global inverse kernel is the actual original normal kernel, including
outside either physical support (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem fullPhaseInverseKernel_eq_maskedNormalKernel {n r : ℕ}
    {G : UniformNormalGeometry n r} {C : ℕ → ℝ} (F : UniformNormalData G C)
    (K : ℝ) {ε : ℝ} (hε : ε ∈ Set.Icc 0 G.ε₀) (x y : Euclidean n) :
    fullPhaseInverseKernel F K ε x y =
      maskedNormalKernel G.D K (F.phase ε) (F.amplitude ε) (fun _ ↦ 1) x y :=
  (F.maskFreeNormalKernel_eq_paired_integral hε K x y).symm

/-- On the physical chart the kernel has the literal absolute inverse
Jacobian, extended by zero outside the averaged-gradient image. Neither
physical position is collapsed to the diagonal
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem fullPhaseInverseKernel_eq_inverseJacobian {n r : ℕ}
    {G : UniformNormalGeometry n r} {C : ℕ → ℝ} (F : UniformNormalData G C)
    (K : ℝ) {ε : ℝ} (hε : ε ∈ Set.Icc 0 G.ε₀) {x y : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) :
    fullPhaseInverseKernel F K ε x y =
      (K / (2 * Real.pi)) ^ n • ∫ ξ,
        oscillatoryFactor K (inner ℝ (x - y) ξ) •
          (averagedGradient (F.phase ε) x y '' G.D).indicator
            (fun ζ ↦ |(fderiv ℝ (averagedGradient (F.phase ε) x y)
                (F.inverseChart ε x y ζ)).det|⁻¹ •
              normalAmplitude (F.amplitude ε) x y (F.inverseChart ε x y ζ)) ξ := by
  rw [fullPhaseInverseKernel_eq_maskedNormalKernel F K hε]
  rw [F.maskedNormalKernel_eq_inverse_integral hε K (fun _ ↦ 1) hx hy]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  congr 1
  by_cases hξ : ξ ∈ averagedGradient (F.phase ε) x y '' G.D
  · simp only [Set.indicator_of_mem hξ, inverseJacobianAmplitude, one_smul]
  · simp only [Set.indicator_of_notMem hξ]


/-- The actual uniform Hilbert-adjoint normal acts by its inverse-Jacobian
kernel. The constant mask is constructed here, not assumed as an operator
identity (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem uniformOscillatoryOperator_normal_ae_inverseKernel {n r : ℕ}
    {G : UniformNormalGeometry n r} {C : ℕ → ℝ} (F : UniformNormalData G C)
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : ε ∈ Set.Icc 0 G.ε₀)
    (f : NormalOutputL2 n r) (i : Fin r) :
    ((F.uniformOscillatoryOperator K ε).comp
      (F.uniformOscillatoryOperator K ε).adjoint f) i =ᵐ[volume]
      fun x ↦ ∑ k, ∫ y, fullPhaseInverseKernel F K ε x y i k * f k y := by
  let g : Lp ℂ ∞ (volume.restrict G.D) :=
    boundedSymbol (fun _ ↦ 1) aestronglyMeasurable_const 1 (by simp)
  have hg : g =ᵐ[volume.restrict G.D] fun _ ↦ (1 : ℂ) := boundedSymbol_coeFn _ _ _ _
  have hm : multiplicationOperator g = ContinuousLinearMap.id ℂ
      (Lp ℂ 2 (volume.restrict G.D)) := by
    ext f
    filter_upwards [multiplicationOperator_coeFn g f, hg] with u hu hgu
    simpa [hgu] using hu
  have h := F.uniformOscillatoryNormalOperator_ae_maskedNormalKernel hK hε
    (m := fun _ ↦ (1 : ℝ)) continuousOn_const g
      (by simpa only [Complex.ofReal_one] using hg) f i
  rw [UniformNormalData.uniformOscillatoryNormalOperator, hm,
    ContinuousLinearMap.id_comp] at h
  simpa only [fullPhaseInverseKernel_eq_maskedNormalKernel F K hε] using h

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {m : ℕ}

variable (D : BandKernelData P (m + 1)) (q : SeparatedSampling.Point → P)
  (hq : Continuous q) (χ : SeparatedSampling.Point → ℝ) (hχ : Continuous χ)
  (j : ℕ) (B : ℝ) (v : Euclidean 2)
  {G : UniformNormalGeometry (m + 1) (m + 1)} {C : ℕ → ℝ}
  (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Set.Icc 0 G.ε₀)
  (hphase : ∀ u ∈ Set.Icc (-B) B ×ˢ wideBand (m + 1) 0, ∀ x,
    D.phase ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) =
      (2 : ℝ) ^ j * F.phase ε x (fullInputCoordinates m u))
  (hamplitude : ∀ u ∈ Set.Icc (-B) B ×ˢ wideBand (m + 1) 0, ∀ x i,
    (Real.sqrt (((2 : ℝ) ^ j) ^ m) : ℂ) * (χ (carrierSamplingEquiv (u.1, v)) : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j • u.2‖ : ℂ) * D.mask ((2 : ℝ) ^ j • u.2) *
        D.amplitude ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) i =
    (normalOperatorScale (m + 1) ((2 : ℝ) ^ j) : ℂ) *
      F.amplitude ε x (fullInputCoordinates m u) i)
  (hsupport : ∀ w, w ∉ fullInputDomain m 0 B → ∀ x, F.amplitude ε x w = 0)



include hε hphase hamplitude hsupport in
/-- The literal full-band normal acts on full vector-valued Euclidean L² by
the actual two-position inverse-Jacobian kernel. Primitive phase, amplitude
and support matching are its only additional inputs; the sampling parent
retains their same-object instantiation
(`app:ch_waves:eq:sampling-prefix-normal`,
`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem fullBandKernelOperator_normal_ae_inverseKernel
    (f : SamplingKernelBounds.Output (m + 1)) :
    atomNormal (fullBandKernelOperator D q hq χ hχ j B v) f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ k, ∫ y,
        fullPhaseInverseKernel F ((2 : ℝ) ^ j) ε x y i k * f y k) := by
  rw [fullBandKernelOperator_normal_eq_uniform D q hq χ hχ j B v
    F hε hphase hamplitude hsupport]
  exact samplingOutputConjugation_ae_kernel _ _
    (uniformOscillatoryOperator_normal_ae_inverseKernel F (by positivity) hε) f

end JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
