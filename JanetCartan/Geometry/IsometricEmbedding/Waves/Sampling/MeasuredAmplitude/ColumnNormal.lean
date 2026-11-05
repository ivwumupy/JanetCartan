module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.Normal

/-!
# Full normal identification from phase agreement on the measured support

The raw kernel and canonical homotopy have different global extensions.
Only points with nonzero measured amplitude enter their operators. These
lemmas use the existing literal coordinate isometries and adjoint formulas
at precisely those points. The concrete consumer is the retained measured
kernel; the original global phase-matching interface is left unchanged.
No output normal or successful sampling bound is assumed.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
namespace JanetCartan.Sampling.MeasuredAmplitude
open SamplingKernelBounds ContinuumRow NormalComparison Pseudodifferential RawInputPartition
open ColoredNormalComparison RawInputHilbert MeanNormalBound MeanNormalBound.NormalizedFullPhase

variable {P : Type*} [TopologicalSpace P] {m : ℕ}
  {G : UniformNormalGeometry (m + 1) (m + 1)} {C : ℕ → ℝ}

/-- The normalized physical column only needs phase agreement where its
measured amplitude is nonzero. Zero amplitudes are handled by the exact
amplitude normalization, without imposing a global phase identity
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem normalizedFullBandColumn_coordinate_ae_of_supported_phase
    (D : BandKernelData P (m + 1)) (q : SeparatedSampling.Point → P)
    (χ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (F : UniformNormalData G C) (ε : ℝ) (u : ℝ × Euclidean m)
    (hphase : ∀ x, F.amplitude ε x (fullInputCoordinates m u) ≠ 0 →
      D.phase ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) =
        (2 : ℝ) ^ j * F.phase ε x (fullInputCoordinates m u))
    (hamplitude : ∀ x i,
      (Real.sqrt (((2 : ℝ) ^ j) ^ m) : ℂ) * (χ (carrierSamplingEquiv (u.1, v)) : ℂ) *
        (Real.sqrt ‖(2 : ℝ) ^ j • u.2‖ : ℂ) * D.mask ((2 : ℝ) ^ j • u.2) *
          D.amplitude ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) i =
      (normalOperatorScale (m + 1) ((2 : ℝ) ^ j) : ℂ) *
        F.amplitude ε x (fullInputCoordinates m u) i)
    (i : Fin (m + 1)) :
    finiteL2CoordinateIsometry volume
      (Real.sqrt (((2 : ℝ) ^ j) ^ m) •
        fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)) i =ᵐ[volume]
      fun x ↦ (normalOperatorScale (m + 1) ((2 : ℝ) ^ j) : ℂ) *
        oscillatoryFactor ((2 : ℝ) ^ j) (F.phase ε x (fullInputCoordinates m u)) *
          F.amplitude ε x (fullInputCoordinates m u) i := by
  filter_upwards [finiteL2Coordinates_apply_ae volume
    (Real.sqrt (((2 : ℝ) ^ j) ^ m) •
      fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)) i,
    Lp.coeFn_smul (Real.sqrt (((2 : ℝ) ^ j) ^ m))
      (fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)),
    fullBandColumn_coe D q χ v (u.1, (2 : ℝ) ^ j • u.2)] with x h₁ h₂ h₃
  change (finiteL2CoordinateIsometry volume _ i) x = _ at h₁
  rw [h₁, h₂]
  change (Real.sqrt (((2 : ℝ) ^ j) ^ m) •
    (fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)) x) i = _
  rw [h₃]
  simp only [BandKernelData.kernel, bandKernel, PiLp.smul_apply, Complex.real_smul,
    smul_eq_mul, oscillatoryFactor, Complex.ofReal_mul]
  by_cases hz : F.amplitude ε x (fullInputCoordinates m u) = 0
  · have ha := hamplitude x i
    simp only [hz, Pi.zero_apply, mul_zero] at ha ⊢
    linear_combination
      Complex.exp ((D.phase ((q (carrierSamplingEquiv (u.1, v)),
        (2 : ℝ) ^ j • u.2), x) : ℂ) * Complex.I) * ha
  · rw [hphase x hz, Complex.ofReal_mul]
    rw [show (((2 : ℝ) ^ j : ℝ) : ℂ) *
        (F.phase ε x (fullInputCoordinates m u) : ℂ) * Complex.I =
        Complex.I * (((2 : ℝ) ^ j : ℝ) : ℂ) *
          (F.phase ε x (fullInputCoordinates m u) : ℂ) by ring]
    simp only [← mul_assoc]
    linear_combination
      Complex.exp (Complex.I * (((2 : ℝ) ^ j : ℝ) : ℂ) *
        (F.phase ε x (fullInputCoordinates m u) : ℂ)) * hamplitude x i

variable [FirstCountableTopology P] [LocallyCompactSpace P]

variable (D : BandKernelData P (m + 1)) (q : SeparatedSampling.Point → P)
  (hq : Continuous q) (χ : SeparatedSampling.Point → ℝ) (hχ : Continuous χ)
  (j : ℕ) (B : ℝ) (v : Euclidean 2)
  {G : UniformNormalGeometry (m + 1) (m + 1)} {C : ℕ → ℝ}
  (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Set.Icc 0 G.ε₀)
  (hphase : ∀ u ∈ Set.Icc (-B) B ×ˢ wideBand (m + 1) 0, ∀ x, F.amplitude ε x (fullInputCoordinates m u) ≠ 0 →
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
/-- The actual adjoints agree isometrically after literal zero extension.
No containment of the entire annulus in the phase chart is assumed
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem uniformOscillatoryOperator_adjoint_eq_normalizedFullBand_of_supported_phase
    (f : SamplingKernelBounds.Output (m + 1)) :
    zeroExtension G.isOpen_D.measurableSet
      ((F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε).adjoint
        (finiteL2CoordinateIsometry volume f)) =
      normalizedFullInputEmbedding m j B
        ((fullBandKernelOperator D q hq χ hχ j B v).adjoint f) := by
  apply Lp.ext
  have hN := (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_fullInputDomain m 0 B)).mp
    (normalizedFullBandAdjoint_ae D q hq χ hχ j B v f)
  have hE := (normalizedFullInputEmbedding_apply_ae m j B
    ((fullBandKernelOperator D q hq χ hχ j B v).adjoint f)).trans hN
  filter_upwards [zeroExtended_uniformOscillatoryOperator_adjoint_ae F ((2 : ℝ) ^ j) hε
    (finiteL2CoordinateIsometry volume f), hE] with w h₁ h₂
  rw [h₁, h₂]
  by_cases hw : w ∈ fullInputDomain m 0 B
  · rw [Set.indicator_of_mem hw]
    let u := (fullInputCoordinates m).symm w
    have hu : u ∈ Set.Icc (-B) B ×ˢ wideBand (m + 1) 0 := by
      apply (fullInputCoordinates_mem_domain m 0 B u).mp
      simpa only [u, MeasurableEquiv.apply_symm_apply] using hw
    have hk := normalizedFullBandColumn_coordinate_ae_of_supported_phase D q χ j v F ε u
      (hphase u hu) (hamplitude u hu)
    have hi := inner_eq_sum_integral_of_coordinate_kernel
      (Real.sqrt (((2 : ℝ) ^ j) ^ m) • fullBandColumn D q χ v
        (u.1, (2 : ℝ) ^ j • u.2)) f _ hk
    simpa only [u, MeasurableEquiv.apply_symm_apply] using hi.symm
  · rw [Set.indicator_of_notMem hw]
    simp [hsupport w hw]

include hε hphase hamplitude hsupport in
/-- Exact full-output normal identification with the actual uniform
oscillatory operator, using the genuine adjoints and isometric input
cancellation (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandKernelOperator_normal_eq_uniform_of_supported_phase :
    atomNormal (fullBandKernelOperator D q hq χ hχ j B v) =
      samplingOutputConjugation (m + 1)
        ((F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε).comp
          (F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε).adjoint) := by
  let T := fullBandKernelOperator D q hq χ hχ j B v
  let A := F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε
  let e := finiteL2CoordinateIsometry (I := Fin (m + 1))
    (volume : Measure (Euclidean (m + 1)))
  let J := normalizedFullInputEmbedding m j B
  let Z := zeroExtension (μ := volume) G.isOpen_D.measurableSet
  have h (f : SamplingKernelBounds.Output (m + 1)) :
      Z (A.adjoint (e f)) = J (T.adjoint f) :=
    uniformOscillatoryOperator_adjoint_eq_normalizedFullBand_of_supported_phase D q hq χ hχ j B v
      F hε hphase hamplitude hsupport f
  ext1 f
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g (T (T.adjoint f)) = inner ℂ g (e.symm (A (A.adjoint (e f))))
  calc
    _ = inner ℂ (T.adjoint g) (T.adjoint f) := (T.adjoint_inner_left (T.adjoint f) g).symm
    _ = inner ℂ (J (T.adjoint g)) (J (T.adjoint f)) := (J.inner_map_map _ _).symm
    _ = inner ℂ (Z (A.adjoint (e g))) (Z (A.adjoint (e f))) :=
      congrArg₂ (inner ℂ) (h g).symm (h f).symm
    _ = inner ℂ (A.adjoint (e g)) (A.adjoint (e f)) := Z.inner_map_map _ _
    _ = inner ℂ (e g) (A (A.adjoint (e f))) := A.adjoint_inner_left _ _
    _ = _ := by simpa only [e.apply_symm_apply] using e.inner_map_map g (e.symm (A (A.adjoint (e f))))

end JanetCartan.Sampling.MeasuredAmplitude
