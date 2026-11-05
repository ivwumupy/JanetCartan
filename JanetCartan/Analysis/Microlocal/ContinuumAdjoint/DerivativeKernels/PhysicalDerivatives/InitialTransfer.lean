module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.Basic
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers

/-!
# Initial weak derivatives of partial radian synthesis

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-derivative-trade`, the initial letter is precisely the
radian multiplier `i⟪h,η⟫`. Its L² representative becomes the actual weak
coordinate derivative after `partialUnitaryInverse`.

The proof commutes bounded normalizations of the multiplier through the proved
parameter Fourier operator, applies its full Fourier factorization and exact
transverse dilation, and derives equality of tempered distributions. All
representatives use the original `carrierMeasure`. No positive-dimension or
smoothness hypothesis is needed. The consumer is the all-order physical
adjoint derivative construction.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure FourierTransform
open scoped SchwartzMap
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential
variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- Bounded transverse multipliers preserve a relation under parameter Fourier
transformation. This supplies the unbounded multiplier argument for
`hasCarrierL2CoordinateDerivative_partialInverse_initial`
(`app:ch_background:prop:bg-adjoint`). -/
private theorem parameterFourier_bounded_relation
    (a b : Euclidean (n - 1) → ℂ) (ha : MemLp a ⊤ volume) (hb : MemLp b ⊤ volume)
    (f g : IteratedCarrierL2 n)
    (h : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun η => a η * g z η) =ᵐ[volume] fun η => b η * f z η) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun η => a η * iteratedParameterFourier n g z η) =ᵐ[volume]
        fun η => b η * iteratedParameterFourier n f z η := by
  let A := AmplitudeBound.multiplicationOperator (ha.toLp a)
  let B := AmplitudeBound.multiplicationOperator (hb.toLp b)
  have hA (u : TransverseL2 n) : A u =ᵐ[volume] fun η => a η * u η := by
    filter_upwards [AmplitudeBound.multiplicationOperator_coeFn (ha.toLp a) u,
      ha.coeFn_toLp] with η hη haη
    exact hη.trans (by rw [haη])
  have hB (u : TransverseL2 n) : B u =ᵐ[volume] fun η => b η * u η := by
    filter_upwards [AmplitudeBound.multiplicationOperator_coeFn (hb.toLp b) u,
      hb.coeFn_toLp] with η hη hbη
    exact hη.trans (by rw [hbη])
  have he : A.compLp g = B.compLp f := by
    apply Lp.ext
    filter_upwards [h, A.coeFn_compLp g, B.coeFn_compLp f] with z hz ha hb
    rw [ha, hb]
    exact Lp.ext ((hA _).trans (hz.trans (hB _).symm))
  have he' : A.compLp (iteratedParameterFourier n g) =
      B.compLp (iteratedParameterFourier n f) := by
    rw [← iteratedParameterFourier_compLp, ← iteratedParameterFourier_compLp, he]
  filter_upwards [A.coeFn_compLp (iteratedParameterFourier n g),
    B.coeFn_compLp (iteratedParameterFourier n f)] with z ha hb
  have hz : A (iteratedParameterFourier n g z) = B (iteratedParameterFourier n f z) :=
    ha.symm.trans ((congrArg (fun u : IteratedCarrierL2 n => u z) he').trans hb)
  exact (hA _).symm.trans ((Filter.EventuallyEq.of_eq (congrArg
    (fun u : TransverseL2 n => (u : Euclidean (n - 1) → ℂ)) hz)).trans (hB _))

/-- Normalize the graph of a continuous multiplier by `1 + ‖m‖`, so both
coefficients are bounded. Cancelling the nowhere-zero normalization proves the
commutation used by the initial-coordinate transfer in
`app:ch_background:prop:bg-adjoint`, without a Fourier intertwining hypothesis. -/
private theorem parameterFourier_coordinate_relation
    (m : Euclidean (n - 1) → ℂ) (hm : Continuous m)
    (f g : IteratedCarrierL2 n)
    (h : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      g z =ᵐ[volume] fun η => m η * f z η) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      iteratedParameterFourier n g z =ᵐ[volume]
        fun η => m η * iteratedParameterFourier n f z η := by
  let a : Euclidean (n - 1) → ℂ := fun η => ((1 + ‖m η‖ : ℝ) : ℂ)⁻¹
  let b : Euclidean (n - 1) → ℂ := fun η => a η * m η
  have ha0 (η) : ((1 + ‖m η‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖m η‖))
  have hac : Continuous a := (Complex.continuous_ofReal.comp (continuous_const.add hm.norm)).inv₀ ha0
  have han (η) : ‖a η‖ = (1 + ‖m η‖)⁻¹ := by
    simp only [a, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 + ‖m η‖)]
  have ha : MemLp a ⊤ volume := memLp_top_of_bound hac.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun η => by rw [han]; exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (m η)]))
  have hb : MemLp b ⊤ volume := memLp_top_of_bound (hac.mul hm).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun η => by
      change ‖a η * m η‖ ≤ 1
      rw [norm_mul, han, ← div_eq_inv_mul]
      exact (div_le_one (by positivity)).mpr (by linarith))
  have hab : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun η => a η * g z η) =ᵐ[volume] fun η => b η * f z η := by
    filter_upwards [h] with z hz
    filter_upwards [hz] with η hη
    simp only [hη, b, mul_assoc]
  filter_upwards [parameterFourier_bounded_relation a b ha hb f g hab] with z hz
  filter_upwards [hz] with η hη
  apply mul_left_cancel₀ (inv_ne_zero (ha0 η))
  exact hη.trans (mul_assoc _ _ _)

set_option maxHeartbeats 800000 in
/-- The full Fourier symbol of the initial derivative after partial radian
synthesis, including the exact frequency dilation. This is the representative
identity used to prove the distributional conclusion of
`hasCarrierL2CoordinateDerivative_partialInverse_initial`
(`app:ch_background:eq:bg-derivative-trade`). -/
private theorem initialFourier_partialInverse_initial_ae
    (i : Fin (n - 1)) (f : CarrierVariable n → ℂ)
    (h0 : MemLp f 2 (carrierMeasure n))
    (h1 : MemLp (applyInitialCarrierDerivative
      (.initial (EuclideanSpace.basisFun (Fin (n - 1)) ℝ i)) f) 2 (carrierMeasure n)) :
    initialFourier n (partialUnitaryInverse n (h1.toLp _)) =ᵐ[carrierMeasure n]
      fun ξ => (2 * Real.pi * Complex.I) * (flatInitialCoordinates n ξ (Fin.natAdd 3 i) : ℂ) *
        initialFourier n (partialUnitaryInverse n (h0.toLp f)) ξ := by
  let g := applyInitialCarrierDerivative
    (.initial (EuclideanSpace.basisFun (Fin (n - 1)) ℝ i)) f
  let m : Euclidean (n - 1) → ℂ := fun η => Complex.I * (η i : ℂ)
  have hg (p : CarrierVariable n) : g p = m p.2 * f p := by
    simp only [g, m, applyInitialCarrierDerivative, EuclideanSpace.basisFun_inner]
  have hfib : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (carrierFubiniEquiv n (h1.toLp g)) z =ᵐ[volume]
        fun η => m η * (carrierFubiniEquiv n (h0.toLp f)) z η := by
    filter_upwards [carrierFubiniEquiv_toLp_coeFn h0,
      carrierFubiniEquiv_toLp_coeFn h1] with z hf hg'
    filter_upwards [hf, hg'] with η hfη hgη
    rw [hgη, hfη]
    exact hg _
  have hcoord (p : CarrierVariable n) :
      flatInitialCoordinates n p (Fin.natAdd 3 i) = p.2 i := by
    calc
      _ = inner ℝ (flatInitialCoordinates n (0, EuclideanSpace.basisFun (Fin (n - 1)) ℝ i))
          (flatInitialCoordinates n p) := by
        rw [flatInitialCoordinates_initialDirection, EuclideanSpace.basisFun_inner]
      _ = p.2 i := by
        change inner ℝ (flatInitialEquiv n (initialCoordinates n _))
          (flatInitialEquiv n (initialCoordinates n p)) = _
        rw [LinearIsometryEquiv.inner_map_map]
        simpa [initialCoordinates, MeasurableEquiv.prodCongr, WithLp.prod_inner_apply] using
          (EuclideanSpace.basisFun_inner (Fin (n - 1)) ℝ p.2 i)
  have hF := parameterFourier_coordinate_relation m (by fun_prop)
    (carrierFubiniEquiv n (h0.toLp f)) (carrierFubiniEquiv n (h1.toLp g)) hfib
  apply (ae_prod_iff_ae_ae (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
    (by fun_prop))).mpr
  filter_upwards [initialFourier_partialUnitaryInverse_coeFn (h0.toLp f),
    initialFourier_partialUnitaryInverse_coeFn (h1.toLp g), hF] with z hf hg' hFz
  have hscaled := (Measure.quasiMeasurePreserving_smul
    (volume : Measure (Euclidean (n - 1))) (by positivity : (2 * Real.pi : ℝ) ≠ 0)).ae hFz
  filter_upwards [hf, hg', hscaled] with ξ hfξ hgξ hFξ
  rw [hgξ, hfξ, hFξ]
  change (synthesisFactor n : ℂ) *
    (Complex.I * (((2 * Real.pi) • ξ) i : ℝ) *
      (iteratedParameterFourier n (carrierFubiniEquiv n (h0.toLp f))) z ((2 * Real.pi) • ξ)) = _
  simp only [hcoord (z, ξ)]
  simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.real_smul]
  ring

/-- Recover the distributional coordinate derivative from its actual full
Fourier representatives, on the original carrier measure. The consumer is
`hasCarrierL2CoordinateDerivative_partialInverse_initial`
(`app:ch_background:prop:bg-adjoint`). -/
private theorem carrierDerivative_of_initialFourier_ae
    (i : Fin (3 + (n - 1))) (f g : CarrierL2 n)
    (h : initialFourier n g =ᵐ[carrierMeasure n]
      fun ξ => (2 * Real.pi * Complex.I) * (flatInitialCoordinates n ξ i : ℂ) *
        initialFourier n f ξ) : HasCarrierL2CoordinateDerivative i f g := by
  have hp := (flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae h
  have hf := flatInitialL2Equiv_coeFn n (initialFourier n f)
  have hg := flatInitialL2Equiv_coeFn n (initialFourier n g)
  rw [flatInitialL2Equiv_initialFourier] at hf hg
  have he : (fun ξ => euclideanCoordinateDerivativeSymbol i ξ *
      (𝓕 (flatInitialL2Equiv n f)) ξ) =ᵐ[volume]
      (𝓕 (flatInitialL2Equiv n g) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (3 + (n - 1)))))) := by
    filter_upwards [hp, hf, hg] with ξ hp hf hg
    simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply] at hp hf hg
    rw [hf, hg]
    exact hp.symm
  have hdist : 𝓕 (euclideanCoordinateDerivative i (flatInitialL2Equiv n f)) =
      𝓕 ((flatInitialL2Equiv n g) : 𝓢'(EuclideanSpace ℝ (Fin (3 + (n - 1))), ℂ)) := by
    rw [fourier_euclideanCoordinateDerivative, Lp.fourier_toTemperedDistribution_eq]
    ext φ
    simp only [TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply
        (hasTemperateGrowth_euclideanCoordinateDerivativeSymbol i)]
    apply integral_congr_ae
    filter_upwards [he] with ξ hξ
    simp only [smul_eq_mul]
    rw [← hξ]
    ring
  have hi := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin (3 + (n - 1))), ℂ) => 𝓕⁻ T) hdist
  change euclideanCoordinateDerivative i (flatInitialL2Equiv n f) = _
  simpa only [fourierInv_fourier_eq] using hi

/-- Initial-coordinate transfer in `app:ch_background:prop:bg-adjoint`, with the
radian multiplier from `app:ch_background:eq:bg-derivative-trade`. The two L²
hypotheses suffice; no smoothness or Fourier derivative premise is required. -/
theorem hasCarrierL2CoordinateDerivative_partialInverse_initial
    (i : Fin (n - 1)) (f : CarrierVariable n → ℂ)
    (h0 : MemLp f 2 (carrierMeasure n))
    (h1 : MemLp (applyInitialCarrierDerivative
      (.initial (EuclideanSpace.basisFun (Fin (n - 1)) ℝ i)) f) 2 (carrierMeasure n)) :
    HasCarrierL2CoordinateDerivative (Fin.natAdd 3 i)
      (partialUnitaryInverse n (h0.toLp f))
      (partialUnitaryInverse n (h1.toLp (applyInitialCarrierDerivative
        (.initial (EuclideanSpace.basisFun (Fin (n - 1)) ℝ i)) f))) :=
  carrierDerivative_of_initialFourier_ae _ _ _
    (initialFourier_partialInverse_initial_ae i f h0 h1)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
