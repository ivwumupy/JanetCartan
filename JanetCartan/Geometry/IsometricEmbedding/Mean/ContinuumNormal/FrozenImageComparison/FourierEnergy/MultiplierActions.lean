module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.FourierEnergy.Symbols
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Fourier

/-!
# Fourier actions of the frozen image channel and its adjoint

The literal uncut complex channel from `FrozenImageComparison.Model` acts by
`uncutChannelMatrix` after the L² Fourier transform, and its Hilbert adjoint acts
by the conjugate transpose. These are the multiplier identifications needed for
`norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy`, the Plancherel step of
`paper-v2.tex`, `app:ch_background:prop:bg-frame`.

The scalar differentiated Bessel factors retain physical frequency `2πξ`.
Finite Hilbert coordinates assemble their actions without a positive-dimension
assumption or an assumed Fourier realization of the channel.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
open JanetCartan.ResponseTransfer.Complement
namespace JanetCartan.ContinuumNormal.FrozenImageComparison
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure E)

/-- The literal scalar factor has its defining differentiated Bessel symbol.
This supplies the entries in `fourier_uncutComplexChannel_ae`
(`app:ch_background:prop:bg-frame`, frozen image contribution). -/
private theorem fourier_imageDerivativeBesselL2Operator_ae (a : Fin n) (f : L²) :
    𝓕 (imageDerivativeBesselL2Operator a f) =ᵐ[volume]
      fun ξ ↦ imageDerivativeBesselSymbol a ξ * (𝓕 f) ξ := by
  have he : 𝓕 (imageDerivativeBesselL2Operator a f) =
      multiplicationOperator ((memLp_top_imageDerivativeBesselSymbol a).toLp _) (𝓕 f) := by
    change (Lp.fourierTransformₗᵢ E ℂ) ((Lp.fourierTransformₗᵢ E ℂ).symm _) = _
    exact (Lp.fourierTransformₗᵢ E ℂ).apply_symm_apply _
  rw [he]
  filter_upwards [multiplicationOperator_coeFn
    ((memLp_top_imageDerivativeBesselSymbol a).toLp _) (𝓕 f),
    (memLp_top_imageDerivativeBesselSymbol a).coeFn_toLp] with ξ hξ hm
  rw [hξ, hm]

/-- The differentiated Bessel symbol is purely imaginary, as used to identify
the scalar Hilbert adjoint in `fourier_uncutComplexChannel_adjoint_ae`
(`app:ch_background:prop:bg-frame`, Plancherel step). -/
private theorem star_imageDerivativeBesselSymbol (a : Fin n) (ξ : E) :
    star (imageDerivativeBesselSymbol a ξ) = - imageDerivativeBesselSymbol a ξ := by
  simp [imageDerivativeBesselSymbol]

/-- Plancherel turns the purely imaginary symbol into skew-adjointness of the
literal differentiated Bessel factor. This supplies the adjoint scalar entries
(`app:ch_background:prop:bg-frame`, Plancherel step). -/
private theorem adjoint_imageDerivativeBesselL2Operator (a : Fin n) :
    (imageDerivativeBesselL2Operator a).adjoint = -imageDerivativeBesselL2Operator a := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change inner ℂ (-imageDerivativeBesselL2Operator a f) g =
    inner ℂ f (imageDerivativeBesselL2Operator a g)
  rw [← Lp.inner_fourier_eq, ← Lp.inner_fourier_eq f]
  rw [FourierTransform.fourier_neg]
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourier_imageDerivativeBesselL2Operator_ae a f,
    fourier_imageDerivativeBesselL2Operator_ae a g,
    Lp.coeFn_neg (𝓕 (imageDerivativeBesselL2Operator a f))] with ξ hf hg hn
  simp only [hn, Pi.neg_apply, hf, hg, RCLike.inner_apply,
    map_neg, map_mul, starRingEnd_apply, star_imageDerivativeBesselSymbol]
  ring

/-- Finite scalar combinations give the entries of the frozen channel symbol,
for `fourier_uncutComplexChannel_ae` (`app:ch_background:prop:bg-frame`). -/
private theorem fourier_sum_smul_imageDerivativeBesselL2Operator_ae (c : Fin n → ℂ) (f : L²) :
    𝓕 ((∑ a, c a • imageDerivativeBesselL2Operator a) f) =ᵐ[volume]
      fun ξ ↦ (∑ a, c a * imageDerivativeBesselSymbol a ξ) * (𝓕 f) ξ := by
  classical
  have he : 𝓕 ((∑ a, c a • imageDerivativeBesselL2Operator a) f) =
      ∑ a, c a • 𝓕 (imageDerivativeBesselL2Operator a f) := by
    simp only [sum_apply, smul_apply, fourier_sum, fourier_smul]
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun a ↦ c a • 𝓕 (imageDerivativeBesselL2Operator a f)),
    ae_all_iff.mpr (fun a ↦ Lp.coeFn_smul (c a) (𝓕 (imageDerivativeBesselL2Operator a f))),
    ae_all_iff.mpr (fun a ↦ fourier_imageDerivativeBesselL2Operator_ae a f)] with ξ hs hc hd
  simp only [Finset.sum_apply] at hs
  rw [hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [hc a]
  simp only [Pi.smul_apply, smul_eq_mul, hd a, mul_assoc]

/-- The adjoint of each scalar entry has the conjugate symbol, for
`fourier_uncutComplexChannel_adjoint_ae` (`app:ch_background:prop:bg-frame`). -/
private theorem fourier_sum_smul_imageDerivativeBesselL2Operator_adjoint_ae (c : Fin n → ℂ) (f : L²) :
    𝓕 ((∑ a, c a • imageDerivativeBesselL2Operator a).adjoint f) =ᵐ[volume]
      fun ξ ↦ star (∑ a, c a * imageDerivativeBesselSymbol a ξ) * (𝓕 f) ξ := by
  classical
  have he : (∑ a, c a • imageDerivativeBesselL2Operator a).adjoint =
      ∑ a, (-star (c a)) • imageDerivativeBesselL2Operator a := by
    simp only [map_sum, map_smulₛₗ, adjoint_imageDerivativeBesselL2Operator, starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro a _
    exact smul_neg (star (c a)) (imageDerivativeBesselL2Operator a) |>.trans
      (neg_smul (star (c a)) (imageDerivativeBesselL2Operator a)).symm
  rw [he]
  filter_upwards [fourier_sum_smul_imageDerivativeBesselL2Operator_ae (fun a ↦ -star (c a)) f] with ξ hξ
  simpa only [star_sum, star_mul, star_imageDerivativeBesselSymbol,
    mul_neg, neg_mul, mul_comm] using hξ

/-- Finite Hilbert coordinates assemble the scalar Fourier actions into the
vector identity. Both frozen-channel action theorems consume this implication
with their proved scalar actions (`app:ch_background:prop:bg-frame`). -/
private theorem fourier_vectorMatrixL2Operator_ae
    (B : Fin n → Fin n → L² →L[ℂ] L²) (b : E → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j g, 𝓕 (B i j g) =ᵐ[volume] fun ξ ↦ b ξ i j * (𝓕 g) ξ)
    (f : C²) :
    (𝓕 (vectorMatrixL2Operator B f) : C²) =ᵐ[volume]
      fun ξ ↦ WithLp.toLp 2 ((b ξ).mulVec ((𝓕 f) ξ)) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  rw [coordinate_fourier, finiteL2CoordinateIsometry_vectorMatrixL2Operator]
  simp only [matrixOperator_apply, fourier_sum]
  have hc (j : Fin n) :
      (𝓕 (finiteL2CoordinateIsometry volume f j) : L²) =ᵐ[volume] fun ξ ↦ (𝓕 f) ξ j := by
    rw [← coordinate_fourier]
    exact finiteL2Coordinates_apply_ae volume (𝓕 f) j
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun j ↦ 𝓕 (B i j (finiteL2CoordinateIsometry volume f j))),
    ae_all_iff.mpr (fun j ↦ hB i j (finiteL2CoordinateIsometry volume f j)),
    ae_all_iff.mpr hc] with ξ hs hb hc
  simp only [Finset.sum_apply] at hs
  change _ = ∑ j, b ξ i j * (𝓕 f) ξ j
  rw [hs]
  apply Finset.sum_congr rfl
  intro j _
  rw [hb j, hc j]

/-- The literal uncut frozen complex channel is the multiplier with matrix
`uncutChannelMatrix`, retaining the physical frequency `2πξ` in every dimension.
This supplies the frozen image contribution in `app:ch_background:prop:bg-frame`
and the parent Fourier-energy identification. -/
theorem fourier_uncutComplexChannel_ae
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : C²) :
    (𝓕 (uncutComplexChannel A f) : C²) =ᵐ[volume]
      fun ξ ↦ uncutChannelAction A ξ ((𝓕 f) ξ) := by
  apply fourier_vectorMatrixL2Operator_ae
  intro i j g
  exact fourier_sum_smul_imageDerivativeBesselL2Operator_ae (fun a ↦ (A a i j : ℂ)) g

/-- The literal Hilbert adjoint of the uncut frozen complex channel has the
conjugate-transpose multiplier, with no Fourier-action premise. This is the
Plancherel input to `norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy`
(`app:ch_background:prop:bg-frame`, frozen image contribution). -/
theorem fourier_uncutComplexChannel_adjoint_ae
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : C²) :
    (𝓕 ((uncutComplexChannel A).adjoint f) : C²) =ᵐ[volume]
      fun ξ ↦ uncutChannelAdjointAction A ξ ((𝓕 f) ξ) := by
  rw [uncutComplexChannel, vectorMatrixL2Operator_adjoint]
  apply fourier_vectorMatrixL2Operator_ae
  intro i j g
  exact fourier_sum_smul_imageDerivativeBesselL2Operator_adjoint_ae (fun a ↦ (A a j i : ℂ)) g

end JanetCartan.ContinuumNormal.FrozenImageComparison
