module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Matrices
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Differentiating actual source coefficients

The compact-parameter argument for `app:ch_regular_base:thm:actual-calculus`,
Step 1. The measure below is the pushforward of normalized torus measure by
its centered representative. Thus all formulas concern `scalarCoefficient`
itself, with its existing normalization.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {n : ℕ}

private def representativeMeasure (n : ℕ) : Measure (Euclidean n) :=
  (volume : Measure (Torus n)).map centeredTorusRepresentative

private instance (n : ℕ) : IsFiniteMeasure (representativeMeasure n) := by
  unfold representativeMeasure
  infer_instance

private theorem representativeMeasure_restrict (n : ℕ) :
    (representativeMeasure n).restrict (fundamentalCell n) = representativeMeasure n := by
  apply Measure.restrict_eq_self_of_ae_mem
  apply (ae_map_iff measurable_centeredTorusRepresentative.aemeasurable
    (isCompact_fundamentalCell n).measurableSet).mpr
  exact ae_of_all _ centeredTorusRepresentative_mem

private theorem coefficient_integral (ℓ : ℝ) {f : Euclidean n → ℂ}
    (hf : Continuous f) (k : Fin n → ℤ) :
    scalarCoefficient ℓ f k = ∫ z in fundamentalCell n,
      periodicLift (UnitAddTorus.mFourier (-k)) z * f (ℓ • z)
        ∂representativeMeasure n := by
  rw [representativeMeasure_restrict, representativeMeasure,
    integral_map measurable_centeredTorusRepresentative.aemeasurable]
  · simp only [scalarCoefficient, UnitAddTorus.mFourierCoeff, boxAmplitudePeriodization,
      amplitudePeriodization, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, smul_eq_mul]
  · exact ((contDiff_periodicLift_mFourier (-k)).continuous.mul
      (hf.comp (continuous_const_smul ℓ))).aestronglyMeasurable

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual source coefficients are jointly smooth in any finite-dimensional
spectator parameter. Used for the output/covector jets of
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem contDiff_scalarCoefficient_parameter {f : E × Euclidean n → ℂ}
    (hf : ContDiff ℝ ∞ f) (ℓ : ℝ) (k : Fin n → ℤ) :
    ContDiff ℝ ∞ (fun p ↦ scalarCoefficient ℓ (fun y ↦ f (p, y)) k) := by
  have he : (fun p ↦ scalarCoefficient ℓ (fun y ↦ f (p, y)) k) =
      fun p ↦ ∫ z in fundamentalCell n,
        periodicLift (UnitAddTorus.mFourier (-k)) z * f (p, ℓ • z)
          ∂representativeMeasure n := by
    funext p
    exact coefficient_integral ℓ (hf.continuous.comp
      (continuous_const.prodMk continuous_id)) k
  rw [he]
  rw [← contDiffOn_univ]
  apply contDiffOn_compactParameterIntegral (U := univ) (V := univ)
    (f := fun q : E × Euclidean n ↦
      periodicLift (UnitAddTorus.mFourier (-k)) q.2 * f (q.1, ℓ • q.2))
    (μ := representativeMeasure n)
    isOpen_univ isOpen_univ (isCompact_fundamentalCell n) (subset_univ _)
  exact (((contDiff_periodicLift_mFourier (-k)).comp contDiff_snd).mul
    (hf.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ℓ)))).contDiffOn

/-- Differentiation in a physical spectator direction passes through the
actual source Fourier coefficient. Joint smoothness supplies domination on
a compact parameter neighborhood; no derivative identity is assumed
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem fderiv_scalarCoefficient_parameter_apply {f : E × Euclidean n → ℂ}
    (hf : ContDiff ℝ ∞ f) (ℓ : ℝ) (k : Fin n → ℤ) (p v : E) :
    fderiv ℝ (fun q ↦ scalarCoefficient ℓ (fun y ↦ f (q, y)) k) p v =
      scalarCoefficient ℓ (fun y ↦ fderiv ℝ (fun q ↦ f (q, y)) p v) k := by
  let g : E × Euclidean n → ℂ := fun q ↦
    periodicLift (UnitAddTorus.mFourier (-k)) q.2 * f (q.1, ℓ • q.2)
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_periodicLift_mFourier (-k)).comp contDiff_snd).mul
      (hf.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ℓ)))
  have hd : ContDiff ℝ ∞ (fun q : E × Euclidean n ↦
      fderiv ℝ (fun t ↦ f (t, q.2)) q.1 v) := by
    apply ContDiff.clm_apply _ contDiff_const
    exact ContDiff.fderiv
      (hf.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst (by simp)
  have he : (fun q ↦ scalarCoefficient ℓ (fun y ↦ f (q, y)) k) =
      fun q ↦ ∫ z in fundamentalCell n, g (q, z) ∂representativeMeasure n := by
    funext q
    exact coefficient_integral ℓ (hf.continuous.comp
      (continuous_const.prodMk continuous_id)) k
  rw [he, fderiv_compactParameterIntegral (U := univ) (V := univ)
    isOpen_univ isOpen_univ (isCompact_fundamentalCell n) (subset_univ _)
    hg.contDiffOn (mem_univ p)]
  rw [ContinuousLinearMap.integral_apply
    (integrableOn_parameterFDeriv (U := univ) (V := univ)
      isOpen_univ isOpen_univ (isCompact_fundamentalCell n) (subset_univ _)
      hg.contDiffOn (mem_univ p))]
  rw [coefficient_integral ℓ (f := fun y ↦ fderiv ℝ (fun q ↦ f (q, y)) p v)
    (hd.continuous.comp ((continuous_const (y := p)).prodMk continuous_id)) k]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    dsimp [g]
    rw [fderiv_const_mul (a := fun q ↦ f (q, ℓ • z))
      ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp) p)]
    rfl

end JanetCartan.FourierIntegral.SourceExpansion
