module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity.Basic

/-!
# The separated frozen amplitude is a measured Fourier multiplier

For the frozen step of `app:ch_background:prop:bg-frame`, the two measurement
factors in `app:ch_background:eq:bg-full-complex-amplitude` separate from the
matrix symbol. On smooth Euclidean tests, source integration gives the Fourier
transform of the measured input. Its rapid decay and the bounded symbol justify
the inverse Fourier integral. The existing literal PDO realization and compact
smooth density then identify the bounded operators on all complex Euclidean L².

The parent carrier Fourier identity supplies the separation and symbol bounds
from the frozen spectral construction, and the amplitude regularity from
`CarrierNormalRealization`. No operator identification is assumed here. All
measures are Euclidean Lebesgue volume; `frozenSymbolEntry` retains `k = 2πξ`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap ENNReal Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

open AmplitudeBound Pseudodifferential

variable {n : ℕ}

/-- Integral representative of a bounded scalar multiplier on inputs with
integrable Fourier transform, for `app:ch_background:prop:bg-frame`. The smooth
measured tests below supply both integrability hypotheses. -/
private theorem multiplier_ae_inverseIntegral
    (a : Euclidean n → ℂ) (ha : MemLp a ∞ volume)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n)))
    (u : Euclidean n → ℂ) (hfu : f =ᵐ[volume] u)
    (hu : Integrable u) (hFu : Integrable (𝓕 u)) :
    fourierMultiplier (ha.toLp a) f =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ a ξ * 𝓕 u ξ) := by
  let g := multiplicationOperator (ha.toLp a) (𝓕 f)
  have hF : (𝓕 f : Lp ℂ 2 (volume : Measure (Euclidean n))) =ᵐ[volume] 𝓕 u := by
    have h := fourierTransform_coeFn_ae_integral f (hu.congr hfu.symm)
    exact h.trans (Filter.Eventually.of_forall (Real.fourier_congr_ae hfu))
  have hg : (g : Euclidean n → ℂ) =ᵐ[volume] fun ξ ↦ a ξ * 𝓕 u ξ := by
    filter_upwards [multiplicationOperator_coeFn (ha.toLp a) (𝓕 f), ha.coeFn_toLp, hF]
      with ξ hm haξ hFξ
    exact hm.trans (by rw [haξ, hFξ])
  have hgi : Integrable (g : Euclidean n → ℂ) :=
    (hFu.mul_of_top_right ha).congr hg.symm
  have hi := fourierTransformInv_coeFn_ae_integral g hgi
  change (𝓕⁻ g : Lp ℂ 2 (volume : Measure (Euclidean n))) =ᵐ[volume] _
  exact hi.trans (Filter.Eventually.of_forall (Real.fourierInv_congr_ae hg))

/-- Source-first factorization of the separated amplitude in
`app:ch_background:eq:bg-full-complex-amplitude`, consumed by the test identity. -/
private theorem separated_fullAmplitudeOperator
    (χ : Euclidean n → ℝ) (a u : Euclidean n → ℂ) (x : Euclidean n) :
    fullAmplitudeOperator (fun x y ξ ↦ (χ x : ℂ) * (χ y : ℂ) * a ξ) u x =
      (χ x : ℂ) * 𝓕⁻ (fun ξ ↦ a ξ * 𝓕 (fun y ↦ (χ y : ℂ) * u y) ξ) x := by
  have hs : sourceAmplitudeTransform
      (fun x y ξ ↦ (χ x : ℂ) * (χ y : ℂ) * a ξ) u x =
      fun ξ ↦ (χ x : ℂ) * (a ξ * 𝓕 (fun y ↦ (χ y : ℂ) * u y) ξ) := by
    funext ξ
    simp only [sourceAmplitudeTransform, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [fullAmplitudeOperator, hs]
  simp only [Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  ring

/-- Test realization of the separated measured multiplier in
`app:ch_background:prop:bg-frame`, used to identify the frozen full amplitude. -/
theorem frozenMeasuredMultiplier_ae_matrixFullAmplitudeOperator
    (χ : Euclidean n → ℝ) (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (hχc : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume)
    (u : Euclidean n → EuclideanSpace ℂ (Fin n)) (hu : MemLp u 2 volume)
    (huc : ContDiff ℝ ∞ u) :
    frozenMeasuredMultiplier χ hχ b hb (hu.toLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2
        (matrixFullAmplitudeOperator
          (fun x y ξ i j ↦ (χ x : ℂ) * (χ y : ℂ) * frozenSymbolEntry b i j ξ)
          (fun y j ↦ u y j) x) := by
  let f := frozenMeasurementOperator χ hχ (hu.toLp u)
  have hf : f =ᵐ[volume] fun x ↦ (χ x : ℂ) • u x := by
    filter_upwards [frozenMeasurementOperator_coeFn χ hχ (hu.toLp u), hu.coeFn_toLp]
      with x hm hu
    exact hm.trans (by rw [hu])
  have hentry (i j : Fin n) :
      fourierMultiplier ((hb i j).toLp (frozenSymbolEntry b i j))
        (finiteL2CoordinateIsometry volume f j) =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ frozenSymbolEntry b i j ξ * 𝓕 (fun y ↦ (χ y : ℂ) * u y j) ξ) := by
    have hc : ContDiff ℝ ∞ (fun y ↦ (χ y : ℂ) * u y j) :=
      (Complex.ofRealCLM.contDiff.comp hχc).mul (by fun_prop)
    have hs : HasCompactSupport (fun y ↦ (χ y : ℂ) * u y j) :=
      (hχs.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right
    let s := hs.toSchwartzMap hc
    apply multiplier_ae_inverseIntegral _ (hb i j) _ s
    · filter_upwards [finiteL2Coordinates_apply_ae volume f j, hf] with x hx hfx
      exact hx.trans (by rw [hfx]; rfl)
    · exact s.integrable
    · exact (𝓕 s).integrable
  have hmatrix : frozenMatrixFourierMultiplier b hb f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j,
        𝓕⁻ (fun ξ ↦ frozenSymbolEntry b i j ξ * 𝓕 (fun y ↦ (χ y : ℂ) * u y j) ξ) x) := by
    apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
    intro i
    simp only [frozenMatrixFourierMultiplier,
      finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j ↦ fourierMultiplier ((hb i j).toLp (frozenSymbolEntry b i j))
        (finiteL2CoordinateIsometry volume f j)), ae_all_iff.mpr (hentry i)] with x hx he
    simp only [Finset.sum_apply] at hx
    rw [hx]
    exact Finset.sum_congr rfl (fun j _ ↦ he j)
  change frozenMeasurementOperator χ hχ (frozenMatrixFourierMultiplier b hb f) =ᵐ[volume] _
  filter_upwards [frozenMeasurementOperator_coeFn χ hχ
    (frozenMatrixFourierMultiplier b hb f), hmatrix] with x hx hm
  rw [hx, hm]
  apply PiLp.ext
  intro i
  simp only [PiLp.smul_apply, smul_eq_mul, matrixFullAmplitudeOperator,
    separated_fullAmplitudeOperator, Finset.mul_sum]

/-- The separated measured amplitude in
`app:ch_background:eq:bg-full-complex-amplitude` is the measured frozen
Euclidean multiplier on all complex L² data (`app:ch_background:prop:bg-frame`).
The symbol uses physical frequency `k = 2πξ` through `frozenSymbolEntry`.
The frozen spectral construction supplies separation and boundedness, and
`CarrierNormalRealization` supplies the full-amplitude budgets. -/
theorem vectorTwoPositionL2Operator_eq_frozenMeasuredMultiplier
    (hn : 0 < n) (R : ℝ)
    (χ : Euclidean n → ℝ) (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (hχc : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume)
    (A : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hA : ContDiff ℝ ∞ (Function.uncurry A))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ A ξ z i j))
    (B : ℝ)
    (hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ A ξ z i j) (2 * (n + 1)) B)
    (hsep : ∀ ξ x y i j,
      A ξ (pairedPosition x y) i j = (χ x : ℂ) * (χ y : ℂ) * frozenSymbolEntry b i j ξ) :
    vectorTwoPositionL2Operator hn R A hA hs B hB = frozenMeasuredMultiplier χ hχ b hb := by
  apply DFunLike.coe_injective
  apply FourierIntegral.denseRange_graphTestToLp.equalizer
    (vectorTwoPositionL2Operator hn R A hA hs B hB).continuous
    (frozenMeasuredMultiplier χ hχ b hb).continuous
  funext u
  have hc (j : Fin n) : ContDiff ℝ (n + 1) (fun y ↦ u.val y j) := by
    have h := u.property.1
    have hcu : ContDiff ℝ ∞ (fun y ↦ u.val y j) := by fun_prop
    exact hcu.of_le (by simp)
  have hcs (j : Fin n) : HasCompactSupport (fun y ↦ u.val y j) :=
    u.property.2.comp_left (g := fun z : EuclideanSpace ℂ (Fin n) ↦ z j) (by simp)
  have hleft := vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator
    hn R A hA hs B hB u.val (FourierIntegral.graphTest_memLp u) hc hcs
  have hright := frozenMeasuredMultiplier_ae_matrixFullAmplitudeOperator χ hχ hχc hχs b hb
    u.val (FourierIntegral.graphTest_memLp u) u.property.1
  apply Lp.ext
  have heq : (fun x y ξ ↦ A ξ (pairedPosition x y)) =
      (fun x y ξ i j ↦ (χ x : ℂ) * (χ y : ℂ) * frozenSymbolEntry b i j ξ) := by
    funext x y ξ i j
    exact hsep ξ x y i j
  rw [heq] at hleft
  exact hleft.trans hright.symm
end JanetCartan.ContinuumNormal.FrozenModel
