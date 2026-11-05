module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.EuclideanEnergy

/-!
# Plancherel energy for the frozen Euclidean matrix multiplier

The frozen step of `app:ch_background:prop:bg-frame` pairs the measured datum
with a bounded matrix Fourier multiplier. Scalar Plancherel and the finite L²
coordinate isometry identify this pairing with the ordinary Fourier integral.
The same argument proves integrability of the quadratic integrand from the
entrywise L∞ bounds; no Fourier action or energy identity is assumed.

The final carrier identity consumes `re_inner_frozenMeasuredMultiplier` after
the separate identification of the carrier normal with this measured multiplier.
The frequency measure remains Euclidean Lebesgue volume, the symbol is evaluated
at `2πξ`, and the real quadratic form includes both Fourier components.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Matrix
open scoped ENNReal
namespace JanetCartan.ContinuumNormal.FrozenModel
open AmplitudeBound Pseudodifferential PeriodicLocalL2
variable {n : ℕ}

/-- Coordinate representatives of the ordinary Fourier integral, used in
`frozenEntry_pairing` for the frozen step of `app:ch_background:prop:bg-frame`. -/
private theorem frozenCoordinate_fourier_coeFn
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hf : Integrable (f : Euclidean n → EuclideanSpace ℂ (Fin n))) (i : Fin n) :
    (𝓕 (finiteL2CoordinateIsometry volume f i) : EuclideanL2 n ℂ) =ᵐ[volume]
      fun ξ ↦ (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) i := by
  have hc : finiteL2CoordinateIsometry volume f i =ᵐ[volume] fun x ↦ f x i :=
    finiteL2Coordinates_apply_ae volume f i
  have hi : Integrable (finiteL2CoordinateIsometry volume f i : Euclidean n → ℂ) :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).integrable_comp hf).congr hc.symm
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert _ hi] with ξ hξ
  rw [hξ, Real.fourier_congr_ae hc]
  have hp := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).integral_comp_comm
    ((Real.fourierIntegral_convergent_iff ξ).2 hf)
  simpa only [Real.fourier_eq, Circle.smul_def, map_smul, PiLp.proj_apply] using hp

/-- Scalar Plancherel and L² inner-product integrability for each matrix entry.
Consumer: `frozenMatrix_pairing` (`app:ch_background:prop:bg-frame`). -/
private theorem frozenEntry_pairing
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume)
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hf : Integrable (f : Euclidean n → EuclideanSpace ℂ (Fin n))) (i j : Fin n) :
    Integrable (fun ξ ↦ inner ℂ
      ((𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) i)
      (frozenSymbolEntry b i j ξ *
        (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) j)) ∧
    inner ℂ (finiteL2CoordinateIsometry volume f i)
        (fourierMultiplier ((hb i j).toLp (frozenSymbolEntry b i j))
          (finiteL2CoordinateIsometry volume f j)) =
      ∫ ξ, inner ℂ ((𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) i)
        (frozenSymbolEntry b i j ξ *
          (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) j) := by
  let a := (hb i j).toLp (frozenSymbolEntry b i j)
  let u := 𝓕 (finiteL2CoordinateIsometry volume f i)
  let v := multiplicationOperator a (𝓕 (finiteL2CoordinateIsometry volume f j))
  have he : (fun ξ ↦ inner ℂ (u ξ) (v ξ)) =ᵐ[volume]
      fun ξ ↦ inner ℂ ((𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) i)
        (frozenSymbolEntry b i j ξ *
          (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) j) := by
    filter_upwards [multiplicationOperator_coeFn a
      (𝓕 (finiteL2CoordinateIsometry volume f j)), (hb i j).coeFn_toLp,
      frozenCoordinate_fourier_coeFn f hf i, frozenCoordinate_fourier_coeFn f hf j]
      with ξ hv ha hi hj
    change inner ℂ ((𝓕 (finiteL2CoordinateIsometry volume f i)) ξ)
      (multiplicationOperator a (𝓕 (finiteL2CoordinateIsometry volume f j)) ξ) = _
    rw [hv, hi, hj]
    exact congrArg (fun c : ℂ ↦ inner ℂ
      ((𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) i)
      (c * (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ) j)) ha
  refine ⟨(L2.integrable_inner u v).congr he, ?_⟩
  rw [← Lp.inner_fourier_eq]
  have hF : 𝓕 (fourierMultiplier a (finiteL2CoordinateIsometry volume f j)) = v := by
    exact (Lp.fourierTransformₗᵢ (Euclidean n) ℂ).apply_symm_apply _
  change inner ℂ u (𝓕 (fourierMultiplier a (finiteL2CoordinateIsometry volume f j))) = _
  rw [hF, L2.inner_def]
  exact integral_congr_ae he

/-- The finite sum of scalar pairings supplies the complex integral and its
integrability. Consumers: the real energy and integrability theorems below
(`app:ch_background:prop:bg-frame`, frozen Plancherel step). -/
private theorem frozenMatrix_pairing
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume)
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hf : Integrable (f : Euclidean n → EuclideanSpace ℂ (Fin n))) :
    Integrable (fun ξ ↦ inner ℂ (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ)
      (WithLp.toLp 2 ((fun i j ↦ frozenSymbolEntry b i j ξ) *ᵥ
        𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ))) ∧
    inner ℂ f (frozenMatrixFourierMultiplier b hb f) =
      ∫ ξ, inner ℂ (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ)
        (WithLp.toLp 2 ((fun i j ↦ frozenSymbolEntry b i j ξ) *ᵥ
          𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ)) := by
  let F := 𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n))
  have he (ξ : Euclidean n) :
      inner ℂ (F ξ) (WithLp.toLp 2 ((fun i j ↦ frozenSymbolEntry b i j ξ) *ᵥ F ξ)) =
        ∑ i, ∑ j, inner ℂ (F ξ i) (frozenSymbolEntry b i j ξ * F ξ j) := by
    simp only [PiLp.inner_apply, Matrix.mulVec, dotProduct, inner_sum]
  have hi (i j : Fin n) : Integrable (fun ξ ↦
      inner ℂ (F ξ i) (frozenSymbolEntry b i j ξ * F ξ j)) :=
    (frozenEntry_pairing b hb f hf i j).1
  have hrow (i : Fin n) := integrable_finsetSum Finset.univ (fun j _ ↦ hi i j)
  have hsum := integrable_finsetSum Finset.univ (fun i _ ↦ hrow i)
  dsimp only [F] at he
  constructor
  · simpa only [he] using hsum
  · rw [← (finiteL2CoordinateIsometry volume).inner_map_map f
      (frozenMatrixFourierMultiplier b hb f)]
    simp only [frozenMatrixFourierMultiplier, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
      PiLp.inner_apply, matrixOperator_apply, inner_sum]
    have hp (i j : Fin n) := (frozenEntry_pairing b hb f hf i j).2
    simp_rw [hp]
    change (∑ i, ∑ j, ∫ ξ, inner ℂ (F ξ i) (frozenSymbolEntry b i j ξ * F ξ j)) = _
    calc
      _ = ∫ ξ, ∑ i, ∑ j, inner ℂ (F ξ i)
          (frozenSymbolEntry b i j ξ * F ξ j) := by
        rw [integral_finsetSum Finset.univ (fun i _ ↦ hrow i)]
        apply Finset.sum_congr rfl
        intro i _
        exact (integral_finsetSum Finset.univ (fun j _ ↦ hi i j)).symm
      _ = _ := integral_congr_ae (.of_forall fun ξ ↦ (he ξ).symm)

/-- The quadratic Fourier integrand in the frozen Plancherel step of
`app:ch_background:prop:bg-frame` is integrable. Its bound follows from the
entrywise L∞ hypotheses and the L² scalar multiplier construction. -/
theorem integrable_realifiedMatrixQuadraticForm_fourier
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume)
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hf : Integrable (f : Euclidean n → EuclideanSpace ℂ (Fin n))) :
    Integrable (fun ξ ↦ realifiedMatrixQuadraticForm (b ((2 * Real.pi) • ξ))
      (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ)) := by
  simpa only [realifiedMatrixQuadraticForm_eq_re_inner, frozenSymbolEntry] using!
    (frozenMatrix_pairing b hb f hf).1.re

/-- Plancherel identifies the actual bounded matrix multiplier's real quadratic
form with the Euclidean frozen energy (`app:ch_background:prop:bg-frame`).
Both real Fourier components and the physical frequency `2πξ` are retained. -/
theorem re_inner_frozenMatrixFourierMultiplier
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume)
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hf : Integrable (f : Euclidean n → EuclideanSpace ℂ (Fin n))) :
    (inner ℂ f (frozenMatrixFourierMultiplier b hb f)).re =
      euclideanFrozenEnergy b (f : Euclidean n → EuclideanSpace ℂ (Fin n)) := by
  rw [(frozenMatrix_pairing b hb f hf).2]
  have hr := integral_re (frozenMatrix_pairing b hb f hf).1
  change (∫ ξ, (inner ℂ (𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ)
    (WithLp.toLp 2 ((fun i j ↦ frozenSymbolEntry b i j ξ) *ᵥ
      𝓕 (f : Euclidean n → EuclideanSpace ℂ (Fin n)) ξ))).re) = _ at hr
  exact hr.symm.trans (integral_congr_ae (.of_forall fun ξ ↦
    (realifiedMatrixQuadraticForm_eq_re_inner _ _).symm))

/-- The two real measurement factors give the Euclidean Fourier energy for
every L² datum (`app:ch_background:prop:bg-frame`, frozen Plancherel step).
Continuity and compact support, hence in particular smooth compact support,
supply the L¹ hypothesis of the ordinary Fourier transform. -/
theorem re_inner_frozenMeasuredMultiplier
    (χ : Euclidean n → ℝ) (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (hc : Continuous χ) (hs : HasCompactSupport χ)
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume)
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    (inner ℂ f (frozenMeasuredMultiplier χ hχ b hb f)).re =
      euclideanFrozenEnergy b (fun x ↦ (χ x : ℂ) • f x) := by
  change (inner ℂ f (frozenMeasurementOperator χ hχ
    (frozenMatrixFourierMultiplier b hb (frozenMeasurementOperator χ hχ f)))).re = _
  rw [inner_frozenMeasurementOperator,
    re_inner_frozenMatrixFourierMultiplier b hb _
      (frozenMeasurementOperator_integrable χ hχ hc hs f)]
  exact euclideanFrozenEnergy_congr_ae b (frozenMeasurementOperator_coeFn χ hχ f)

end JanetCartan.ContinuumNormal.FrozenModel
