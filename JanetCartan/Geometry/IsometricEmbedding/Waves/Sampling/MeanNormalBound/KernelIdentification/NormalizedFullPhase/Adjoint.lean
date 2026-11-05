module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.PhaseMatching
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.OutputTransfer

/-!
# The actual full-phase adjoint after input normalization

For `app:ch_waves:eq:sampling-prefix-normal`, identify the Hilbert adjoints
from primitive phase/amplitude matching. Zero extension is explicit: the
uniform amplitude must vanish outside the normalized full band, and both inputs are
extended by zero into full Euclidean space. These are primitive support inputs
from the same cutoff construction, not conclusions about operators.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
open SamplingKernelBounds ContinuumRow NormalComparison Pseudodifferential RawInputPartition
open ColoredNormalComparison RawInputHilbert

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {m : ℕ}

/-- The actual full-band adjoint in normalized Euclidean input coordinates.
This uses the derived original adjoint and the literal input unitary
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normalizedFullBandAdjoint_ae
    (D : BandKernelData P (m + 1)) (q : SeparatedSampling.Point → P)
    (hq : Continuous q) (χ : SeparatedSampling.Point → ℝ) (hχ : Continuous χ)
    (j : ℕ) (B : ℝ) (v : Euclidean 2) (f : SamplingKernelBounds.Output (m + 1)) :
    fullInputL2Coordinates m 0 B (fullBandDilation (m + 1) j B
      ((fullBandKernelOperator D q hq χ hχ j B v).adjoint f))
      =ᵐ[volume.restrict (fullInputDomain m 0 B)] fun w ↦
        inner ℂ (Real.sqrt (((2 : ℝ) ^ j) ^ m) • fullBandColumn D q χ v
          (((fullInputCoordinates m).symm w).1,
            (2 : ℝ) ^ j • ((fullInputCoordinates m).symm w).2)) f := by
  have hd := fullBandDilation_apply_ae (m + 1) j B
    ((fullBandKernelOperator D q hq χ hχ j B v).adjoint f)
  have ha := ae_weightedPullback (fullInputDilation (m + 1) j)
    (map_fullBandMeasure_dilation (m + 1) j B)
    (fullBandKernelOperator_adjoint_ae D q hq χ hχ j B v f)
  have hi : fullBandDilation (m + 1) j B
      ((fullBandKernelOperator D q hq χ hχ j B v).adjoint f) =ᵐ[fullBandMeasure (m + 1) 0 B]
      fun u ↦ inner ℂ (Real.sqrt (((2 : ℝ) ^ j) ^ m) •
        fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)) f := by
    filter_upwards [hd, ha] with u h₁ h₂
    rw [h₁]
    change (Real.sqrt (((2 : ℝ) ^ j) ^ m) : ℂ) *
      ((fullBandKernelOperator D q hq χ hχ j B v).adjoint f)
        (fullInputDilation (m + 1) j u) = _
    rw [h₂, inner_smul_left_eq_smul, Complex.real_smul]
    rfl
  exact (fullInputL2Coordinates_apply_ae m 0 B _).trans
    ((fullInputCoordinates_restrict_measurePreserving m 0 B).symm.quasiMeasurePreserving.ae_eq_comp hi)

/-- Zero extending the actual uniform adjoint removes its domain indicator
because its original amplitude vanishes off the input chart. The proof uses
`UniformNormalData`'s actual kernel theorem
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem zeroExtended_uniformOscillatoryOperator_adjoint_ae
    {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Set.Icc 0 G.ε₀)
    (f : NormalOutputL2 n r) :
    zeroExtension G.isOpen_D.measurableSet ((F.uniformOscillatoryOperator K ε).adjoint f)
      =ᵐ[volume] fun u ↦ ∑ i, ∫ x,
        star ((normalOperatorScale n K : ℂ) * oscillatoryFactor K (F.phase ε x u) *
          F.amplitude ε x u i) * f i x := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq G.isOpen_D.measurableSet).mp
    (F.uniformOscillatoryOperator_adjoint_ae_integral K hε f)
  refine ((zeroExtension_coeFn G.isOpen_D.measurableSet _).trans h).trans
    (Filter.Eventually.of_forall fun u ↦ ?_)
  by_cases hu : u ∈ G.D
  · exact Set.indicator_of_mem hu _
  · rw [Set.indicator_of_notMem hu]
    have hz (x : Euclidean n) : F.amplitude ε x u = 0 :=
      F.amplitude_eq_zero_off_carrier hε (z := (x, u)) (fun hx ↦ hu (G.D₀_subset hx.2))
    simp [hz]

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
/-- The actual adjoints agree isometrically after literal zero extension.
No containment of the entire annulus in the phase chart is assumed
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem uniformOscillatoryOperator_adjoint_eq_normalizedFullBand
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
    have hk := normalizedFullBandColumn_coordinate_ae D q χ j v F ε u
      (hphase u hu) (hamplitude u hu)
    have hi := inner_eq_sum_integral_of_coordinate_kernel
      (Real.sqrt (((2 : ℝ) ^ j) ^ m) • fullBandColumn D q χ v
        (u.1, (2 : ℝ) ^ j • u.2)) f _ hk
    simpa only [u, MeasurableEquiv.apply_symm_apply] using hi.symm
  · rw [Set.indicator_of_notMem hw]
    simp [hsupport w hw]

include hε hphase hamplitude hsupport in
/-- The adjoint transport identity as an equality of bounded maps on the full
Euclidean output (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem toSamplingOutput_uniformOscillatoryOperator_adjoint :
    (zeroExtension G.isOpen_D.measurableSet).toContinuousLinearMap.comp
      (toSamplingOutput (F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε)).adjoint =
      (normalizedFullInputEmbedding m j B).toContinuousLinearMap.comp
        (fullBandKernelOperator D q hq χ hχ j B v).adjoint := by
  rw [toSamplingOutput_adjoint]
  ext1 f
  exact uniformOscillatoryOperator_adjoint_eq_normalizedFullBand D q hq χ hχ j B v
    F hε hphase hamplitude hsupport f

end JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
