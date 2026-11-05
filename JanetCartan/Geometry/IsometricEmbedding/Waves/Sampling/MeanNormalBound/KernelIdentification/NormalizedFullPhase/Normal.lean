module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.Adjoint

/-!
# Forward and normal identification for the normalized full input

The exact bridge used by `app:ch_waves:eq:sampling-prefix-normal`. Every
analytic matching premise is a primitive phase, amplitude or support equality;
the forward, adjoint and normal identities are deductions.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
namespace JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
open SamplingKernelBounds ContinuumRow NormalComparison Pseudodifferential RawInputPartition
open ColoredNormalComparison RawInputHilbert

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
/-- The actual full-phase operator is the normalized full-band operator after
restriction to the original supported inputs. It is derived by taking the
Hilbert adjoint of the proved kernel identity
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem toSamplingOutput_uniformOscillatoryOperator_eq :
    (toSamplingOutput (F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε)).comp
      (restriction G.D) =
      (fullBandKernelOperator D q hq χ hχ j B v).comp
        (normalizedFullInputEmbedding m j B).toContinuousLinearMap.adjoint := by
  apply ContinuousLinearMap.adjoint.injective
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ← adjoint_zeroExtension G.isOpen_D.measurableSet]
  exact toSamplingOutput_uniformOscillatoryOperator_adjoint D q hq χ hχ j B v
    F hε hphase hamplitude hsupport

include hε hphase hamplitude hsupport in
/-- Forward identification on each original full-band input, with both the
input isometry and the output coordinate isometry made explicit
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem fullBandKernelOperator_eq_uniformOscillatoryOperator
    (f : FullBandInput (m + 1) j B) :
    fullBandKernelOperator D q hq χ hχ j B v f =
      (finiteL2CoordinateIsometry volume).symm
        (F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε
          (restriction G.D (normalizedFullInputEmbedding m j B f))) := by
  change _ = ((toSamplingOutput (F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε)).comp
    (restriction G.D)) (normalizedFullInputEmbedding m j B f)
  rw [toSamplingOutput_uniformOscillatoryOperator_eq D q hq χ hχ j B v
    F hε hphase hamplitude hsupport, ContinuousLinearMap.comp_apply]
  have hi := congrArg (fun T ↦ T f)
    (normalizedFullInputEmbedding_adjoint_comp m j B)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hi
  exact congrArg (fullBandKernelOperator D q hq χ hχ j B v) hi.symm

include hε hphase hamplitude hsupport in
/-- Exact full-output normal identification with the actual uniform
oscillatory operator, using the genuine adjoints and isometric input
cancellation (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandKernelOperator_normal_eq_uniform :
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
    uniformOscillatoryOperator_adjoint_eq_normalizedFullBand D q hq χ hχ j B v
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

include hε hphase hamplitude hsupport in
/-- The normal bridge preserves the exact operator norm; it incurs no
coordinate or band-count loss (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_fullBandKernelOperator_normal_eq_uniform :
    ‖atomNormal (fullBandKernelOperator D q hq χ hχ j B v)‖ =
      ‖(F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε).comp
        (F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε).adjoint‖ := by
  rw [fullBandKernelOperator_normal_eq_uniform D q hq χ hχ j B v
    F hε hphase hamplitude hsupport, norm_samplingOutputConjugation]

include hε hphase hamplitude hsupport in
/-- The forward bridge also preserves the exact operator norm. This is an
identity, not an oscillatory estimate (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_fullBandKernelOperator_eq_uniform :
    ‖fullBandKernelOperator D q hq χ hχ j B v‖ =
      ‖F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε‖ := by
  have h := norm_fullBandKernelOperator_normal_eq_uniform D q hq χ hχ j B v
    F hε hphase hamplitude hsupport
  change ‖atomNormal _‖ = ‖atomNormal (F.uniformOscillatoryOperator ((2 : ℝ) ^ j) ε)‖ at h
  rw [norm_atomNormal, norm_atomNormal] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
