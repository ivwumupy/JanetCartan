module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives.Basic

/-!
# Fourier transport and all mixed carrier derivative multipliers

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
the full initial Fourier transform commutes with the ordered Euclidean
identification, retaining all `3 + (n - 1)` coordinates. Integral covariance
under `flatInitialEquiv` proves this on Schwartz functions; density extends it
to every L² class.

`flatInitialL2Equiv_initialFourier` discharges the Fourier-transport premise of
the physical weight comparison and the mixed weak-derivative characterization.
The two derivative multiplier theorems then describe actual distributional
coordinate derivatives and every word in `CarrierDerivativeIndex` on the
literal measure `(ds dv) dy`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.CarrierSobolev
open ContinuumRow Pseudodifferential

/-- The L² pullback used to prove `flatInitialL2Equiv_initialFourier`, for
`app:ch_background:prop:bg-adjoint`. -/
private abbrev flatPullback (n : ℕ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (E := ℂ) (p := 2) (flatInitialEquiv n).symm
    (flatInitialEquiv n).symm.measurePreserving

/-- The Schwartz representative of the pullback in
`app:ch_background:prop:bg-adjoint`; used by `flatPullback_fourier`. -/
private theorem flatPullback_schwartz (n : ℕ) (φ : 𝓢(InitialSpace n, ℂ)) :
    flatPullback n (φ.toLp 2) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (flatInitialEquiv n).symm.toContinuousLinearEquiv φ).toLp 2 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (φ.toLp 2)
      (flatInitialEquiv n).symm.measurePreserving,
    (flatInitialEquiv n).symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (φ.coeFn_toLp 2),
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (flatInitialEquiv n).symm.toContinuousLinearEquiv φ).coeFn_toLp 2] with x hx hφ hψ
  exact hx.trans (hφ.trans hψ.symm)

/-- L² covariance under the flattening isometry, for
`app:ch_background:prop:bg-adjoint`; used by `flatInitialL2Equiv_initialFourier`. -/
private theorem flatPullback_fourier (n : ℕ) (f : Lp ℂ 2 (volume : Measure (InitialSpace n))) :
    flatPullback n (𝓕 f) = 𝓕 (flatPullback n f) := by
  let p := fun f : Lp ℂ 2 (volume : Measure (InitialSpace n)) =>
    flatPullback n (𝓕 f) = 𝓕 (flatPullback n f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := InitialSpace n) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((flatPullback n).continuous.comp continuous_fourier)
      (continuous_fourier.comp (flatPullback n).continuous)
  intro φ
  change flatPullback n (𝓕 (φ.toLp 2)) = 𝓕 (flatPullback n (φ.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, flatPullback_schwartz, flatPullback_schwartz,
    SchwartzMap.toLp_fourier_eq]
  congr 1
  ext x
  exact (Real.fourier_comp_linearIsometry (flatInitialEquiv n).symm φ x).symm

/-- Factor the published coordinate change to identify its Fourier action,
for `app:ch_background:prop:bg-adjoint`. -/
private theorem flatInitialL2Equiv_factor (n : ℕ) (f : CarrierL2 n) :
    flatInitialL2Equiv n f = flatPullback n (initialL2Equiv n f) := by
  change Lp.compMeasurePreserving _ _ f =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
  rw [← Lp.compMeasurePreserving_comp_apply]
  rfl

/-- The full initial Fourier transform commutes with the ordered Euclidean
coordinate identification, for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse`. This supplies the transport premise of
the physical Sobolev weight comparison and mixed-derivative characterization. -/
theorem flatInitialL2Equiv_initialFourier (n : ℕ) (f : CarrierL2 n) :
    flatInitialL2Equiv n (initialFourier n f) = 𝓕 (flatInitialL2Equiv n f) := by
  rw [flatInitialL2Equiv_factor, flatInitialL2Equiv_factor]
  change flatPullback n ((initialL2Equiv n)
    ((initialL2Equiv n).symm (𝓕 (initialL2Equiv n f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, flatPullback_fourier]

/-- Pull the transported Fourier representative back to the literal carrier
measure, for the derivative multiplier in `app:ch_background:prop:bg-adjoint`. -/
private theorem initialFourier_flat_coeFn (n : ℕ) (f : CarrierL2 n) :
    (fun ξ => (𝓕 (flatInitialL2Equiv n f)) (flatInitialCoordinates n ξ)) =ᵐ[carrierMeasure n]
      initialFourier n f := by
  have h := (flatInitialCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (flatInitialL2Equiv_coeFn n (initialFourier n f))
  rw [flatInitialL2Equiv_initialFourier] at h
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using h

/-- A physical coordinate derivative multiplies the full initial Fourier
transform by `2π i` times its corresponding frequency, almost everywhere on
`(ds dv) dy`. This is the first-order identity needed for the mixed derivatives
in `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`. -/
theorem HasCarrierL2CoordinateDerivative.initialFourier_ae_eq
    {n : ℕ} {i : Fin (3 + (n - 1))} {f g : CarrierL2 n}
    (h : HasCarrierL2CoordinateDerivative i f g) :
    initialFourier n g =ᵐ[carrierMeasure n]
      (fun ξ => (2 * Real.pi * Complex.I) * (flatInitialCoordinates n ξ i : ℂ) *
        initialFourier n f ξ) := by
  have he := (flatInitialCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (HasEuclideanL2CoordinateDerivative.fourier_ae_eq h)
  filter_upwards [he, initialFourier_flat_coeFn n f, initialFourier_flat_coeFn n g]
    with ξ hξ hf hg
  change (2 * Real.pi * Complex.I) * (flatInitialCoordinates n ξ i : ℂ) *
    (𝓕 (flatInitialL2Equiv n f)) (flatInitialCoordinates n ξ) =
      (𝓕 (flatInitialL2Equiv n g)) (flatInitialCoordinates n ξ) at hξ
  rw [hf, hg] at hξ
  exact hξ.symm

/-- Product of the physical frequency multipliers along an ordered derivative
word, with empty product one, for `app:ch_background:prop:bg-adjoint`.
The recursion follows `HasCarrierL2Derivatives`: first take the indicated
coordinate derivative, then follow the remaining word. Its consumer is
`HasCarrierL2Derivatives.initialFourier_ae_eq`. -/
def carrierDerivativeSymbol {n : ℕ} :
    {s : ℕ} → CarrierDerivativeIndex n s → CarrierVariable n → ℂ
  | 0, _, _ => 1
  | _ + 1, none, _ => 1
  | _ + 1, some (i, w), ξ =>
      carrierDerivativeSymbol w ξ *
        ((2 * Real.pi * Complex.I) * (flatInitialCoordinates n ξ i : ℂ))

/-- The empty derivative word has symbol one, as required at order zero in
`app:ch_background:prop:bg-adjoint`. -/
@[simp] theorem carrierDerivativeSymbol_empty (n s : ℕ) (ξ : CarrierVariable n) :
    carrierDerivativeSymbol (.empty (3 + (n - 1)) s) ξ = 1 := by
  cases s <;> rfl

/-- Every actual mixed physical derivative has its full Fourier product
symbol, almost everywhere for the literal carrier measure, for
`app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`.
All three carrier coordinates and all `n - 1` transverse coordinates occur. -/
theorem HasCarrierL2Derivatives.initialFourier_ae_eq
    {n s : ℕ} {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) (w : CarrierDerivativeIndex n s) :
    initialFourier n (v w) =ᵐ[carrierMeasure n]
      (fun ξ => carrierDerivativeSymbol w ξ * initialFourier n f ξ) := by
  induction s generalizing f with
  | zero =>
    have hv := (hasCarrierL2Derivatives_zero_iff f v).mp h
    cases w
    simp only [hv, carrierDerivativeSymbol, one_mul]
    exact Filter.EventuallyEq.rfl
  | succ s ih =>
    obtain ⟨hv, hd⟩ := (hasCarrierL2Derivatives_succ_iff f v).mp h
    cases w with
    | none =>
      simp only [hv, carrierDerivativeSymbol, one_mul]
      exact Filter.EventuallyEq.rfl
    | some iw =>
      obtain ⟨i, w⟩ := iw
      filter_upwards [ih (hd i).2 w, (hd i).1.initialFourier_ae_eq] with ξ hw hi
      rw [hw, hi]
      exact (mul_assoc _ _ _).symm

end JanetCartan.CarrierSobolev
