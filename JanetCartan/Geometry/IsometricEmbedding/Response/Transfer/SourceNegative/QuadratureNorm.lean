module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.Components
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Fourier
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Negative source norms for the same real quadratures

The real inverse in `app:ch_regular:eq:inverse-remainder` uses complexified
orthonormal components of real data. The original source estimate uses the
complex vector Fourier-Sobolev norm. Taking either real quadrature contracts
that norm with constant one, at every real order where the source belongs.

Conjugation reflects the Fourier variable. The proof retains this reflection,
uses the even Bessel weight and the same Lebesgue measure, and then applies
the Hilbert sum over the original Euclidean coordinates. There is no dimension
factor or loss in the negative source constant. Consumer: the original-source
input to the same fixed inverse before `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open JanetCartan JanetCartan.Pseudodifferential
namespace JanetCartan.ResponseTransfer.SourceNegative
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Scalar conjugation on the original L² space (`app:ch_regular_base:eq:negative-duality`). -/
private def conjugateScalarL2 : L2 →L[ℝ] L2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

/-- The literal conjugate representative for `app:ch_regular_base:eq:negative-duality`. -/
private theorem conjugateScalarL2_coe (f : L2) :
    conjugateScalarL2 f =ᵐ[volume] fun x ↦ star (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

/-- Conjugation reflects the frequency in `app:ch_regular_base:eq:negative-duality`. -/
private theorem fourier_conjugate_integral (f : E → ℂ) (ξ : E) :
    𝓕 (fun x ↦ star (f x)) ξ = star (𝓕 f (-ξ)) := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, inner_neg_right, neg_neg]
  change _ = (starRingEnd ℂ) (∫ v, (Real.fourierChar (inner ℝ v ξ) : ℂ) * f v)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp

/-- Extend the conjugation/reflection identity to actual L² classes by density
(`app:ch_regular_base:eq:negative-duality`). -/
private theorem fourier_conjugateScalarL2 (f : L2) :
    𝓕 (conjugateScalarL2 f) = conjugateScalarL2
      (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 f)) := by
  refine (SchwartzMap.denseRange_toLpCLM (F := ℂ)
    (p := 2) ENNReal.ofNat_ne_top).induction_on f ?_ ?_
  · exact isClosed_eq (continuous_fourier.comp conjugateScalarL2.continuous)
      (conjugateScalarL2.continuous.comp
        ((Lp.isometry_compMeasurePreserving (Measure.measurePreserving_neg volume)).continuous.comp
          continuous_fourier))
  intro g
  let f : L2 := g.toLp 2
  have hf : Integrable (f : E → ℂ) := g.integrable.congr (g.coeFn_toLp 2).symm
  have hc : Integrable (conjugateScalarL2 f : E → ℂ) :=
    (Complex.conjCLE.toContinuousLinearMap.integrable_comp hf).congr
      (conjugateScalarL2_coe f).symm
  change 𝓕 (conjugateScalarL2 f) = conjugateScalarL2
    (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 f))
  apply Lp.ext
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert _ hc,
    conjugateScalarL2_coe
      (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 f)),
    Lp.coeFn_compMeasurePreserving (𝓕 f) (Measure.measurePreserving_neg volume),
    (Measure.measurePreserving_neg (volume : Measure E)).quasiMeasurePreserving.ae
      (Localization.fourierTransform_coeFn_ae_integral_hilbert f hf)] with ξ hc hj hr hf
  rw [hc, Real.fourier_congr_ae (conjugateScalarL2_coe f) ξ,
    fourier_conjugate_integral, hj, hr]
  exact congrArg star hf.symm

/-- The even Bessel weight preserves the conjugation/reflection identity
(`app:ch_regular_base:eq:negative-duality`). -/
private theorem weightedFourier_conjugateScalarL2 (s : ℝ) (f : L2) :
    weightedL2Fourier s (conjugateScalarL2 f) =ᵐ[volume]
      fun ξ ↦ star (weightedL2Fourier s f (-ξ)) := by
  have he := fourier_conjugateScalarL2 f
  filter_upwards [conjugateScalarL2_coe
      (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 f)),
    Lp.coeFn_compMeasurePreserving (𝓕 f) (Measure.measurePreserving_neg volume)] with ξ hj hr
  simp only [weightedL2Fourier, he, hj, hr, Function.comp_apply,
    euclideanSobolevWeight, norm_neg, star_smul, star_trivial]

/-- Conjugation preserves the original source Sobolev domain
(`app:ch_regular:eq:inverse-remainder`). -/
private theorem memFourierSobolev_conjugateScalarL2 {s : ℝ} {f : L2}
    (hf : MemFourierSobolev s f) : MemFourierSobolev s (conjugateScalarL2 f) :=
  ((hf.comp_measurePreserving (Measure.measurePreserving_neg volume)).star).ae_eq
    (weightedFourier_conjugateScalarL2 s f).symm

/-- Conjugation preserves its Fourier-Sobolev norm exactly, including negative orders
(`app:ch_regular:eq:inverse-remainder`). -/
private theorem fourierSobolevNorm_conjugateScalarL2 (s : ℝ) (f : L2) :
    fourierSobolevNorm s (conjugateScalarL2 f) = fourierSobolevNorm s f := by
  unfold fourierSobolevNorm
  rw [eLpNorm_congr_ae (weightedFourier_conjugateScalarL2 s f)]
  change (eLpNorm (star (weightedL2Fourier s f ∘ Neg.neg)) 2 volume).toReal = _
  rw [eLpNorm_star, eLpNorm_comp_measurePreserving
    (aestronglyMeasurable_weightedL2Fourier s f) (Measure.measurePreserving_neg volume)]

/-- Scalar rotation commutes with the weighted Fourier representative
(`app:ch_response:eq:response-actual-solver-formula`). -/
private theorem weightedFourier_scalar_smul (s : ℝ) (c : ℂ) (f : L2) :
    weightedL2Fourier s (c • f) =ᵐ[volume] c • weightedL2Fourier s f := by
  filter_upwards [Lp.coeFn_smul c (𝓕 f)] with ξ hξ
  simp only [weightedL2Fourier, fourier_smul, hξ, Pi.smul_apply]
  exact smul_comm _ _ _

/-- Exact scalar homogeneity for the two original quadratures
(`app:ch_response:eq:response-actual-solver-formula`). -/
private theorem fourierSobolevNorm_scalar_smul (s : ℝ) (c : ℂ) (f : L2) :
    fourierSobolevNorm s (c • f) = ‖c‖ * fourierSobolevNorm s f := by
  unfold fourierSobolevNorm
  rw [eLpNorm_congr_ae (weightedFourier_scalar_smul s c f), eLpNorm_const_smul,
    ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]

/-- Included real part is the average with the conjugate, on the same L² class
(`app:ch_regular_base:eq:negative-duality`). -/
private theorem scalarRealPart_eq (f : L2) :
    (Complex.ofRealCLM.comp Complex.reCLM).compLp f =
      (2⁻¹ : ℂ) • (f + conjugateScalarL2 f) := by
  apply Lp.ext
  filter_upwards [(Complex.ofRealCLM.comp Complex.reCLM).coeFn_compLp f,
    Lp.coeFn_smul (2⁻¹ : ℂ) (f + conjugateScalarL2 f),
    Lp.coeFn_add f (conjugateScalarL2 f), conjugateScalarL2_coe f]
    with x hr hs ha hc
  simp only [hr, hs, ha, hc, Pi.smul_apply, Pi.add_apply]
  change ((f x).re : ℂ) = (2⁻¹ : ℂ) * (f x + star (f x))
  change ((f x).re : ℂ) = (2⁻¹ : ℂ) * (f x + (starRingEnd ℂ) (f x))
  rw [Complex.add_conj]
  push_cast
  ring

/-- Real part contracts the scalar Fourier norm without changing its constant
(`app:ch_regular:eq:inverse-remainder`). -/
private theorem scalarRealPart_fourierSobolevNorm_le {s : ℝ} {f : L2}
    (hf : MemFourierSobolev s f) :
    fourierSobolevNorm s ((Complex.ofRealCLM.comp Complex.reCLM).compLp f) ≤
      fourierSobolevNorm s f := by
  rw [scalarRealPart_eq, fourierSobolevNorm_scalar_smul]
  have h := fourierSobolevNorm_add_le hf (memFourierSobolev_conjugateScalarL2 hf)
  rw [fourierSobolevNorm_conjugateScalarL2] at h
  norm_num [norm_inv]
  linarith

/-- The same real part belongs to the original Sobolev domain
(`app:ch_regular:eq:inverse-remainder`). -/
private theorem scalarRealPart_memFourierSobolev {s : ℝ} {f : L2}
    (hf : MemFourierSobolev s f) :
    MemFourierSobolev s ((Complex.ofRealCLM.comp Complex.reCLM).compLp f) := by
  rw [scalarRealPart_eq]
  exact ((hf.add (memFourierSobolev_conjugateScalarL2 hf)).const_smul (2⁻¹ : ℂ)).ae_eq
    (weightedFourier_scalar_smul s (2⁻¹ : ℂ) _).symm

variable {I : Type*} [Fintype I]
local notation "VL2" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)

/-- The real inverse component is exactly the included real coordinate of the
original complex source (`app:ch_regular_base:eq:negative-duality`). -/
private theorem realComponentL2_realPart (f : VL2) (i : I) :
    ArbitraryAccuracy.realComponentL2 (EuclideanSpace.basisFun I ℝ) i (l2RealPart volume f) =
      (Complex.ofRealCLM.comp Complex.reCLM).compLp (finiteL2CoordinateIsometry volume f i) := by
  apply Lp.ext
  filter_upwards [ArbitraryAccuracy.realComponentL2_coeFn (EuclideanSpace.basisFun I ℝ) i
      (l2RealPart volume f), euclideanRealPart.coeFn_compLpL f,
    (Complex.ofRealCLM.comp Complex.reCLM).coeFn_compLp (finiteL2CoordinateIsometry volume f i),
    finiteL2Coordinates_apply_ae volume f i] with x ha hr hc hi
  change (l2RealPart volume f) x = euclideanRealPart (f x) at hr
  change (finiteL2CoordinateIsometry volume f i) x = f x i at hi
  simp only [ha, EuclideanSpace.basisFun_inner, hr, euclideanRealPart_apply, hc, hi]
  rfl

/-- Real part of the original vector source has the component Sobolev membership
used by `ArbitraryAccuracy.inverse_remainder_restrictionSobolev`
(`app:ch_regular:eq:inverse-remainder`). -/
theorem memComponentFourierSobolev_l2RealPart {s : ℝ} {f : VL2}
    (hf : MemVectorFourierSobolev s f) :
    ArbitraryAccuracy.MemComponentFourierSobolev (EuclideanSpace.basisFun I ℝ) s
      (l2RealPart volume f) := by
  intro i
  rw [realComponentL2_realPart]
  exact scalarRealPart_memFourierSobolev (hf i)

/-- Real part contracts the original vector Fourier-Sobolev norm with constant one.
The inverse's orthonormal components are exactly the source's Euclidean coordinates;
no dimension comparison enters `app:ch_regular:eq:inverse-remainder`. -/
theorem componentFourierSobolevNorm_l2RealPart_le {s : ℝ} {f : VL2}
    (hf : MemVectorFourierSobolev s f) :
    ArbitraryAccuracy.componentFourierSobolevNorm (EuclideanSpace.basisFun I ℝ) s
      (l2RealPart volume f) ≤ vectorFourierSobolevNorm s f := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨norm_nonneg _, ?_⟩
  rw [vectorFourierSobolevNorm, matrixFourierSobolevNorm_sq]
  apply Finset.sum_le_sum
  intro i _
  rw [realComponentL2_realPart]
  exact pow_le_pow_left₀ (fourierSobolevNorm_nonneg _ _)
    (scalarRealPart_fourierSobolevNorm_le (hf i)) 2

/-- Every unit rotation followed by real part has the SAME original vector
Fourier-Sobolev bound. In particular `c = 1` and `c = -Complex.I` supply both
literal quadratures in `app:ch_response:eq:response-actual-solver-formula` for
`ArbitraryAccuracy.inverse_remainder_restrictionSobolev.hsource`, with constant one. -/
theorem real_quadrature_fourierSobolev_bound {s : ℝ} {f : VL2}
    (hf : MemVectorFourierSobolev s f) (c : ℂ) (hc : ‖c‖ = 1) :
    ArbitraryAccuracy.MemComponentFourierSobolev (EuclideanSpace.basisFun I ℝ) s
      (l2RealPart volume (c • f)) ∧
    ArbitraryAccuracy.componentFourierSobolevNorm (EuclideanSpace.basisFun I ℝ) s
      (l2RealPart volume (c • f)) ≤ vectorFourierSobolevNorm s f := by
  have he (i : I) : finiteL2CoordinateIsometry volume (c • f) i =
      c • finiteL2CoordinateIsometry volume f i := by
    simp only [map_smul, PiLp.smul_apply]
  have hm : MemVectorFourierSobolev s (c • f) := by
    intro i
    rw [he]
    exact ((hf i).const_smul c).ae_eq (weightedFourier_scalar_smul s c _).symm
  refine ⟨memComponentFourierSobolev_l2RealPart hm,
    (componentFourierSobolevNorm_l2RealPart_le hm).trans_eq ?_⟩
  unfold vectorFourierSobolevNorm matrixFourierSobolevNorm
  congr 1
  ext i
  simp only [he, fourierSobolevNorm_scalar_smul, hc, one_mul]

end JanetCartan.ResponseTransfer.SourceNegative
