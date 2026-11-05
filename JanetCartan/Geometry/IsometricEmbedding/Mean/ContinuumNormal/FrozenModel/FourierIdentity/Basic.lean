module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.EuclideanEnergy
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers

/-!
# Interfaces for the frozen Euclidean Fourier identity

The frozen step of `app:ch_background:prop:bg-frame` uses a measured Euclidean
Fourier multiplier, with physical frequency `k = 2πξ`. These definitions reuse
the scalar Lebesgue Fourier multiplier and the literal vector L² coordinate
isometry. They do not assert an identification with the carrier normal.

`FourierIdentity.SeparatedAmplitude` is to identify the global PDO with the
measured multiplier. `FourierIdentity.MultiplierEnergy` is to identify its
quadratic form with `euclideanFrozenEnergy`. The final carrier assembly consumes
both deductions. The matrix bounds and amplitude separation are supplied by the
frozen spectral construction; the global normal equality is supplied by
`CarrierNormalRealization.exists_carrierL2Extension_globalNormal_of_primitiveNorms`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Matrix
open scoped ENNReal Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumRow

variable {n : ℕ}

/-- An entry of the real frozen symbol in Mathlib's unit-frequency coordinates
(`app:ch_background:eq:bg-real-symbol`). -/
def frozenSymbolEntry (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (ξ : Euclidean n) : ℂ :=
  (b ((2 * Real.pi) • ξ) i j : ℂ)

/-- Measurability and a uniform Frobenius bound supply the actual `L∞` entries
used by the frozen multiplier, without lattice sampling
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem frozenSymbolEntry_memLp
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, Measurable (fun k ↦ b k i j))
    (C : ℝ) (hC : ∀ k, ‖b k‖ ≤ C) (i j : Fin n) :
    MemLp (frozenSymbolEntry b i j) ∞ volume := by
  refine memLp_top_of_bound ?_ C ?_
  · exact (Complex.continuous_ofReal.measurable.comp
      ((hb i j).comp
        (continuous_id.const_smul (2 * Real.pi)).measurable)).aestronglyMeasurable
  · filter_upwards [] with ξ
    simp only [frozenSymbolEntry, Complex.norm_real]
    exact ((PiLp.norm_apply_le (WithLp.toLp 2 (b ((2 * Real.pi) • ξ) i)) j).trans
      (PiLp.norm_apply_le
        (WithLp.toLp 2 (fun l ↦ WithLp.toLp 2 (b ((2 * Real.pi) • ξ) l))) i)).trans (hC _)

/-- The matrix Fourier multiplier on literal complex Euclidean L², assembled
from the existing scalar multipliers (`app:ch_background:prop:bg-frame`). -/
def frozenMatrixFourierMultiplier
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume) :
    EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)) :=
  vectorMatrixL2Operator (fun i j ↦
    fourierMultiplier ((hb i j).toLp (frozenSymbolEntry b i j)))

/-- Multiplication by the real measurement on complex Euclidean L². The scalar
coefficient is included in ℂ, while the measure stays Lebesgue volume
(`app:ch_background:prop:bg-frame`, frozen step). -/
def frozenMeasurementOperator (χ : Euclidean n → ℝ)
    (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume) :
    EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)) :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ∞ 2 2
    (hχ.toLp (fun x ↦ (χ x : ℂ)))

/-- Literal action of the measurement multiplication used in the frozen
Fourier energy (`app:ch_background:prop:bg-frame`). -/
theorem frozenMeasurementOperator_coeFn (χ : Euclidean n → ℝ)
    (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    frozenMeasurementOperator χ hχ f =ᵐ[volume] fun x ↦ (χ x : ℂ) • f x := by
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ
    (E := EuclideanSpace ℂ (Fin n))).coeFn_holder (r := 2) (hχ.toLp _) f,
    hχ.coeFn_toLp] with x hx hχx
  exact hx.trans (congrArg (fun c : ℂ ↦ c • f x) hχx)

/-- A real measurement moves across the complex L² pairing unchanged
(`app:ch_background:prop:bg-frame`, frozen Plancherel step). -/
theorem inner_frozenMeasurementOperator (χ : Euclidean n → ℝ)
    (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (f g : EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    inner ℂ f (frozenMeasurementOperator χ hχ g) =
      inner ℂ (frozenMeasurementOperator χ hχ f) g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frozenMeasurementOperator_coeFn χ hχ f,
    frozenMeasurementOperator_coeFn χ hχ g] with x hf hg
  simp only [hf, hg, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- Complex inclusion commutes with the literal cell zero extension. This
fixes the representative used by the frozen Euclidean energy
(`app:ch_background:prop:bg-frame`). -/
theorem toEuclidean_l2ComplexInclusion (w : OutputL2 n) :
    toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w) =
      l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) w) := by
  have hp := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae
      ((euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL w))
  apply Lp.ext
  filter_upwards [toEuclidean_coe (𝕜 := ℂ) (l2ComplexInclusion volume w),
    toEuclidean_coe (𝕜 := ℝ) w,
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL
      (toEuclidean (𝕜 := ℝ) w), hp] with x hc hr hi hp
  change l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) w) x = _ at hi
  rw [hc, hi, hr]
  by_cases hx : x ∈ halfOpenCell n
  · simpa only [Set.indicator_of_mem hx, periodicLift, Function.comp_apply,
      l2ComplexInclusion]
      using hp hx
  · simp only [Set.indicator_of_notMem hx, map_zero]

/-- The input to the frozen multiplier is exactly the complex inclusion of
the measured real Euclidean zero extension (`app:ch_background:prop:bg-frame`). -/
theorem frozenMeasurementOperator_toEuclidean_coeFn (χ : Euclidean n → ℝ)
    (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume) (w : OutputL2 n) :
    frozenMeasurementOperator χ hχ
        (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w)) =ᵐ[volume]
      fun x ↦ euclideanComplexInclusion (χ x • toEuclidean (𝕜 := ℝ) w x) := by
  rw [toEuclidean_l2ComplexInclusion]
  filter_upwards [frozenMeasurementOperator_coeFn χ hχ
    (l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) w)),
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL
      (toEuclidean (𝕜 := ℝ) w)] with x hm hi
  change l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) w) x = _ at hi
  rw [hm, hi]
  ext i
  simp

/-- The measured Euclidean zero extension of a real torus test is the existing
physical source profile. This is the smooth-test input for the separated-amplitude
identification; the equality itself only needs equality of representatives
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem frozenMeasurementOperator_toEuclidean_eq_physicalSourceProfile
    (χ : Euclidean n → ℝ) (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (hχcell : ∀ x ∉ halfOpenCell n, χ x = 0)
    (w : OutputL2 n) (w₀ : Torus n → Euclidean n) (hw : w =ᵐ[volume] w₀) :
    frozenMeasurementOperator χ hχ
        (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w)) =ᵐ[volume]
      TestChartTransfer.physicalSourceProfile χ
        (fun z ↦ euclideanComplexInclusion (w₀ z)) := by
  have hp := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae hw)
  filter_upwards [frozenMeasurementOperator_toEuclidean_coeFn χ hχ w,
    toEuclidean_coe (𝕜 := ℝ) w, hp] with x hm he hp
  rw [hm, he]
  by_cases hx : x ∈ halfOpenCell n
  · rw [Set.indicator_of_mem hx]
    change euclideanComplexInclusion (χ x • w (torusQuotient x)) =
      χ x • euclideanComplexInclusion (w₀ (torusQuotient x))
    rw [hp hx, map_smul]
  · simp [Set.indicator_of_notMem hx, hχcell x hx,
      TestChartTransfer.physicalSourceProfile]

/-- The measured input is integrable for every L² datum when the measurement
is continuous and compactly supported. This discharges the ordinary Fourier
integral's `L¹` premise in the all-data energy formula, rather than assuming
integrability of an arbitrary L² representative (`app:ch_background:prop:bg-frame`). -/
theorem frozenMeasurementOperator_integrable (χ : Euclidean n → ℝ)
    (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (hc : Continuous χ) (hs : HasCompactSupport χ)
    (f : EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    Integrable (frozenMeasurementOperator χ hχ f :
      Euclidean n → EuclideanSpace ℂ (Fin n)) := by
  have hl := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hi := hl.integrable_smul_left_of_hasCompactSupport
      (Complex.continuous_ofReal.comp hc)
      (hs.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp))
  exact hi.congr (frozenMeasurementOperator_coeFn χ hχ f).symm

/-- The ordinary Euclidean energy is independent of almost-everywhere choices
of physical representatives (`app:ch_background:prop:bg-frame`). -/
theorem euclideanFrozenEnergy_congr_ae
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    {f g : Euclidean n → EuclideanSpace ℂ (Fin n)} (h : f =ᵐ[volume] g) :
    euclideanFrozenEnergy b f = euclideanFrozenEnergy b g := by
  unfold euclideanFrozenEnergy
  congr 1
  funext ξ
  rw [Real.fourier_congr_ae h]

/-- The measured frozen multiplier, retaining the measurement on both sides
(`app:ch_background:prop:bg-frame`). Its identification with the full PDO is a
separate proof obligation, not part of this definition. -/
def frozenMeasuredMultiplier (χ : Euclidean n → ℝ)
    (hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume)
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, MemLp (frozenSymbolEntry b i j) ∞ volume) :
    EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)) :=
  frozenMeasurementOperator χ hχ ∘L frozenMatrixFourierMultiplier b hb ∘L
    frozenMeasurementOperator χ hχ

/-- The real and imaginary quadratic forms are exactly the real part of the
complex matrix pairing. No symmetry or positivity is required for this algebraic
identity (`app:ch_background:prop:bg-frame`, frozen Plancherel step). -/
theorem realifiedMatrixQuadraticForm_eq_re_inner
    (M : Matrix (Fin n) (Fin n) ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    realifiedMatrixQuadraticForm M z =
      (inner ℂ z (WithLp.toLp 2 ((fun i j ↦ (M i j : ℂ)) *ᵥ z))).re := by
  simp only [realifiedMatrixQuadraticForm, dotProduct, Matrix.mulVec,
    PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum]
  change _ = Complex.reCLM (∑ i, (∑ j, (M i j : ℂ) * z j) * star (z i))
  simp only [Finset.sum_mul, map_sum, Complex.reCLM_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The same literal carrier test action identifies every admissible extension.
This uses the original `carrierMeasure` and its checked initial-test density,
so the eventual Fourier identity cannot depend on an existential choice
(`app:ch_background:prop:bg-frame`). -/
theorem carrierExtensions_eq_of_initialTests {N : ℕ} (d : CarrierData n N)
    (U W : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val)
    (hW : ∀ v : carrierInitialTestSpace n,
      W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val) : W = U := by
  apply DFunLike.coe_injective
  apply denseRange_carrierInitialTestToLp.equalizer W.continuous U.continuous
  funext v
  exact Lp.ext ((hW v).trans (hU v).symm)

/-- The published global normal realization reduces the real adjoint energy
to a Euclidean pairing of the complex zero extension. The reflected PDO already
contains both quadratures and factor four; no additional factor is inserted
(`app:ch_background:prop:bg-frame`, frozen Plancherel step).

In the carrier application `A` is the `vectorTwoPositionL2Operator` returned by
`exists_carrierL2Extension_globalNormal_of_primitiveNorms`. -/
theorem realQuadratureAdjoint_norm_sq_eq_euclidean_pairing
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (A : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hU : (realQuadratureChannel U).comp (realQuadratureChannel U).adjoint =
      realOutputCompression (transferOperator A)) (w : OutputL2 n) :
    ‖(realQuadratureChannel U).adjoint w‖ ^ 2 =
      (inner ℂ (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w))
        (A (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w)))).re := by
  rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ w (((realQuadratureChannel U).comp
    (realQuadratureChannel U).adjoint) w) = _
  rw [hU]
  change inner ℝ w (l2RealPart volume (transferOperator A (l2ComplexInclusion volume w))) = _
  rw [real_inner_comm, l2RealPart_inner, real_inner_comm, real_inner_eq_complex_re]
  change (inner ℂ (l2ComplexInclusion volume w)
    (toTorus (𝕜 := ℂ) (A (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w))))).re = _
  rw [← ContinuousLinearMap.adjoint_inner_left, toTorus_adjoint]
  rfl

end JanetCartan.ContinuumNormal.FrozenModel
