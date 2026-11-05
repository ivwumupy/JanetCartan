module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Substitution
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.FiniteBand

/-!
# Absolute convergence after conic substitution

The second Fubini step in `app:ch_background:eq:bg-full-complex-amplitude`
is deduced from the original finite-band bounds. The inverse Jacobian cancels
in the integral of the norm at each spectator. Only measurability, chart
identities, and support remain as geometric inputs; no transformed size or
integrability estimate is postulated.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.ContinuumRow.TransportKernel
variable {n N : ℕ}

/-- The density measurability needed by conic Fubini follows from the primitive
coefficient functions, including arbitrary measurable real regularization.
Smooth primitive data supply these hypotheses
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem measurable_normalDensityEntry (d : CarrierData n N) (m : CarrierVariable n → ℝ) (x y : Torus n)
    (hm : Measurable m) (ha : Measurable (Function.uncurry d.angularCutoff))
    (hh : Measurable d.highCutoff)
    (hνx : Measurable (d.normalField (d.chartPoint x)))
    (hνy : Measurable (d.normalField (d.chartPoint y)))
    (hξx : Measurable (d.covector (d.chartPoint x)))
    (hξy : Measurable (d.covector (d.chartPoint y))) (i j : Fin n) :
    Measurable (fun u ↦ normalDensityEntry d m x y u i j) := by
  have hangular : Measurable (fun u : CarrierVariable n ↦
      d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2)) :=
    ha.comp (measurable_fst.prodMk (measurable_snd.norm.inv.smul measurable_snd))
  unfold normalDensityEntry reducedCovector tensorPairing
  fun_prop


/-- Primitive measurability of the density, inverse, Jacobian, and joint chart
image suffices for the transformed density. Smooth primitive data supply these
inputs (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem stronglyMeasurable_inverseDensityEntry (d : CarrierData n N) (m : CarrierVariable n → ℝ) (x y : Torus n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (i j : Fin n)
    (hd : Measurable (fun u ↦ normalDensityEntry d m x y u i j))
    (hU : Measurable (fun p : Euclidean 2 × Euclidean n ↦ U p.1 p.2))
    (hJ : Measurable (fun p : Euclidean 2 × Euclidean n ↦ (J p.1 p.2).det))
    (hI : MeasurableSet {p : Euclidean 2 × Euclidean n | p.2 ∈ Ψ p.1 '' D p.1}) :
    StronglyMeasurable (fun p : Euclidean 2 × Euclidean n ↦
      inverseDensityEntry d m x y e D Ψ U J p.1 p.2 i j) := by
  have hu := e.measurable.comp hU
  have hc : Measurable (fun p : Euclidean 2 × Euclidean n ↦
      chartCarrierVariable e p.1 (U p.1 p.2)) :=
    (hu.fst.prodMk measurable_fst).prodMk hu.snd
  have hr :=
    (((hJ.comp (measurable_fst.prodMk hU)).norm.inv.mul (hd.comp hc)).indicator hI).stronglyMeasurable
  convert hr using 1
  funext p
  by_cases hp : p.2 ∈ Ψ p.1 '' D p.1 <;>
    simp only [inverseDensityEntry, Set.indicator, Set.mem_ofPred_eq, hp,
      ↓reduceIte, Function.comp_apply, Pi.mul_apply, Pi.inv_apply, Real.norm_eq_abs]

private theorem measurable_phase_density (z : Euclidean n) (a : Euclidean 2 × Euclidean n → ℝ)
    (ha : StronglyMeasurable a) :
    AEStronglyMeasurable (fun p : Euclidean 2 × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ z p.2) * (a p : ℂ))
        (volume.prod volume) := by
  have hp : Continuous (fun p : Euclidean 2 × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ z p.2)) := by
    unfold NormalComparison.oscillatoryFactor
    fun_prop
  exact (hp.stronglyMeasurable.mul (Complex.continuous_ofReal.comp_stronglyMeasurable ha)).aestronglyMeasurable

private theorem transfer_integrable
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (hD : ∀ v, MeasurableSet (D v))
    (hΨ : ∀ v t, t ∈ D v → HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : ∀ v, InjOn (Ψ v) (D v))
    (hU : ∀ v t, t ∈ D v → U v (Ψ v t) = t)
    (hJ : ∀ v t, t ∈ D v → (J v t).det ≠ 0)
    (B : Euclidean 2 × Euclidean n → ℂ)
    (hB : Integrable B (volume.prod volume))
    (hs : ∀ v t, t ∉ D v → B (v,t) = 0)
    (hm : AEStronglyMeasurable (fun p : Euclidean 2 × Euclidean n ↦
      (Ψ p.1 '' D p.1).indicator
        (fun k ↦ |(J p.1 (U p.1 k)).det|⁻¹ • B (p.1, U p.1 k)) p.2)
      (volume.prod volume)) :
    Integrable (fun p : Euclidean 2 × Euclidean n ↦
      (Ψ p.1 '' D p.1).indicator
        (fun k ↦ |(J p.1 (U p.1 k)).det|⁻¹ • B (p.1, U p.1 k)) p.2)
      (volume.prod volume) := by
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hB.prod_right_ae] with v hv
    apply IntegrableOn.integrable_indicator _
      (measurable_image_of_fderivWithin (hD v) (hΨ v) (hinj v))
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (hD v) (hΨ v) (hinj v) _).mpr
    apply hv.integrableOn.congr_fun _ (hD v)
    intro t ht
    simp only [hU v t ht, smul_smul, mul_inv_cancel₀ (abs_ne_zero.mpr (hJ v t ht)), one_smul]
  · apply hB.integral_norm_prod_left.congr
    apply Filter.Eventually.of_forall
    intro v
    dsimp only
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D v)
      (fun t ht ↦ by simp [hs v t ht])]
    rw [NormalComparison.integral_eq_inverse_jacobian_integral
      (D v) (hD v) (Ψ v) (U v) (J v) (hΨ v) (hinj v) (hU v) (hJ v)]
    rw [← integral_indicator (measurable_image_of_fderivWithin (hD v) (hΨ v) (hinj v))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro k
    by_cases hk : k ∈ Ψ v '' D v
    · simp [hk, Real.norm_eq_abs]
    · simp [hk]

/-- Joint transformed integrability follows from finite-band bounds and the
genuine conic substitution. The remaining measurability premise carries no
size estimate; it follows from the primitive data via
`stronglyMeasurable_inverseDensityEntry`. This justifies the second Fubini step
in `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem integrable_transformed_phase_density {N : ℕ} (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    {x y : Torus n} (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (h : FiniteCarrierKernelBounds d m)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (i j : Fin n)
    (hD : ∀ v, MeasurableSet (D v))
    (hΨ : ∀ v t, t ∈ D v → HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : ∀ v, InjOn (Ψ v) (D v)) (hU : ∀ v t, t ∈ D v → U v (Ψ v t) = t)
    (hJ : ∀ v t, t ∈ D v → (J v t).det ≠ 0)
    (hsupp : ∀ v t, t ∉ D v →
      normalDensityEntry d m x y (chartCarrierVariable e v t) i j = 0)
    (hphase : ∀ v t, t ∈ D v →
      carrierPhase d x (chartCarrierVariable e v t) -
        carrierPhase d y (chartCarrierVariable e v t) =
          inner ℝ (d.chartPoint x - d.chartPoint y) (Ψ v t))
    (hm : AEStronglyMeasurable (fun p : Euclidean 2 × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (d.chartPoint x - d.chartPoint y) p.2) *
        (inverseDensityEntry d m x y e D Ψ U J p.1 p.2 i j : ℂ)) (volume.prod volume)) :
    Integrable (fun p : Euclidean 2 × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (d.chartPoint x - d.chartPoint y) p.2) *
        (inverseDensityEntry d m x y e D Ψ U J p.1 p.2 i j : ℂ)) (volume.prod volume) := by
  let B : Euclidean 2 × Euclidean n → ℂ := fun p ↦
    NormalComparison.oscillatoryFactor 1
      (carrierPhase d x (chartCarrierVariable e p.1 p.2) -
        carrierPhase d y (chartCarrierVariable e p.1 p.2)) *
      (normalDensityEntry d m x y (chartCarrierVariable e p.1 p.2) i j : ℂ)
  have hB : Integrable B (volume.prod volume) :=
    ((MeasurePreserving.id volume).prod he).integrable_comp_of_integrable
      ((integrable_spectator_iff _).mpr (integrable_phase_density h hx hy i j))
  have heq : (fun p : Euclidean 2 × Euclidean n ↦
      (Ψ p.1 '' D p.1).indicator
        (fun k ↦ |(J p.1 (U p.1 k)).det|⁻¹ • B (p.1, U p.1 k)) p.2) =
      (fun p : Euclidean 2 × Euclidean n ↦
        NormalComparison.oscillatoryFactor 1
          (inner ℝ (d.chartPoint x - d.chartPoint y) p.2) *
          (inverseDensityEntry d m x y e D Ψ U J p.1 p.2 i j : ℂ)) := by
    funext p
    by_cases hp : p.2 ∈ Ψ p.1 '' D p.1
    · obtain ⟨t, ht, heq⟩ := hp
      rcases p with ⟨v,k⟩
      dsimp only at *
      subst k
      simp only [Set.indicator_of_mem (mem_image_of_mem (Ψ v) ht),
        inverseDensityEntry, B, hU v t ht, hphase v t ht,
        Complex.real_smul, Complex.ofReal_mul]
      ring
    · simp [inverseDensityEntry, hp]
  rw [← heq]
  apply transfer_integrable D Ψ U J hD hΨ hinj hU hJ B hB
  · intro v t ht
    simp [B, hsupp v t ht]
  · rwa [heq]

/-- The full two-position kernel formula with both Fubini hypotheses proved.
Only primitive measurability, finite-band bounds, and the genuine chart conditions
remain; no transformed integrability assumption is needed
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedNormalEntry_eq_fullAmplitude_of_finiteBand (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (h : FiniteCarrierKernelBounds d m) {x y : Torus n}
    (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (i j : Fin n)
    (hD : ∀ v, MeasurableSet (D v))
    (hΨ : ∀ v t, t ∈ D v → HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : ∀ v, InjOn (Ψ v) (D v)) (hU : ∀ v t, t ∈ D v → U v (Ψ v t) = t)
    (hJ : ∀ v t, t ∈ D v → (J v t).det ≠ 0)
    (hsupp : ∀ v t, t ∉ D v →
      normalDensityEntry d m x y (chartCarrierVariable e v t) i j = 0)
    (hphase : ∀ v t, t ∈ D v →
      carrierPhase d x (chartCarrierVariable e v t) -
        carrierPhase d y (chartCarrierVariable e v t) =
          inner ℝ (d.chartPoint x - d.chartPoint y) (Ψ v t))
    (hd : Measurable (fun u ↦ normalDensityEntry d m x y u i j))
    (hUm : Measurable (fun p : Euclidean 2 × Euclidean n ↦ U p.1 p.2))
    (hJm : Measurable (fun p : Euclidean 2 × Euclidean n ↦ (J p.1 p.2).det))
    (hI : MeasurableSet {p : Euclidean 2 × Euclidean n | p.2 ∈ Ψ p.1 '' D p.1}) :
    regularizedNormalEntry d m x y i j =
      ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
          (fullAmplitudeEntry d m x y e D Ψ U J k i j : ℂ) := by
  apply regularizedNormalEntry_eq_fullAmplitude d m hx hy e he D Ψ U J i j
    hD hΨ hinj hU hJ hsupp hphase (integrable_phase_density h hx hy i j)
  apply integrable_transformed_phase_density d m hx hy h e he D Ψ U J i j
    hD hΨ hinj hU hJ hsupp hphase
  exact measurable_phase_density _ _
    (stronglyMeasurable_inverseDensityEntry d m x y e D Ψ U J i j hd hUm hJm hI)

end JanetCartan.ContinuumRow.TransportKernel
