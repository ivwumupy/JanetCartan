module
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationDensity
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakUniqueness
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

open MeasureTheory Set
open scoped ContDiff
open JanetCartan JanetCartan.Pseudodifferential JanetCartan.CarrierSobolev

/-!
# Quantitative bounds for the same uncut preparation density

For `app:ch_mean_pairs:eq:mean-density-recursion`, combine the existing
half-order multiplier estimate, full carrier Sobolev coordinates, weak-jet
uniqueness and the smooth Sobolev estimate. This proves global bounds on the
chosen smooth representative, with finite input order `k + (3 + (n - 1)) + 2`.
No initial-position cutoff is introduced. The representative remains the one
used by `preparationDensityCorrection`, and the radian synthesis factor is
retained exactly. The same corrected-positive inverse/adjoint must still
produce the raw input norms from smooth source norms.
-/

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean

private theorem vector_rep_bound (n r k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (u : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)))
      (f : Euclidean n → EuclideanSpace ℂ (Fin r)),
      MemVectorFourierSobolev ((k + n + 1 : ℕ) : ℝ) u →
      ContDiff ℝ ∞ f → f =ᵐ[volume] u →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤
        C * vectorFourierSobolevNorm ((k + n + 1 : ℕ) : ℝ) u := by
  obtain ⟨C, hC, hest⟩ := LocalSobolev.FiniteOrder.exists_smooth_jet_estimate
    n k (F := EuclideanSpace ℂ (Fin r))
  obtain ⟨B, hB, hweak⟩ := LocalSobolev.exists_vector_weakJet_nat n r (k + n + 1)
  refine ⟨C * B, mul_nonneg hC hB.le, ?_⟩
  intro u f hu hf he j hj x
  obtain ⟨J, hw, hm, hb⟩ := hweak u hu
  have hjet (l : ℕ) (hl : l ≤ k + n + 1) :
      iteratedFDeriv ℝ l f =ᵐ[volume] J l := by
    simpa only [Measure.restrict_univ] using
      (Mollification.hasWeakJetOn_of_contDiff volume
        (hf.of_le (by simp : (k + n + 1 : ℕ) ≤ (∞ : ℕ∞ω))) univ).ae_eq
        hw isOpen_univ (by simpa only [Measure.restrict_univ] using he) l hl
  have hmem (l : ℕ) (hl : l ≤ k + n + 1) :
      MemLp (iteratedFDeriv ℝ l f) 2 volume := (hm l hl).ae_eq (hjet l hl).symm
  have hsum : (∑ l ∈ Finset.range (k + n + 1 + 1),
      (eLpNorm (iteratedFDeriv ℝ l f) 2 volume).toReal) =
      ∑ l ∈ Finset.range (k + n + 1 + 1), (eLpNorm (J l) 2 volume).toReal := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [eLpNorm_congr_ae (hjet l (by have := Finset.mem_range.mp hl; omega))]
  calc
    _ ≤ C * ∑ l ∈ Finset.range (k + n + 1 + 1),
        (eLpNorm (iteratedFDeriv ℝ l f) 2 volume).toReal := hest f hf hmem j hj x
    _ ≤ C * (B * vectorFourierSobolevNorm ((k + n + 1 : ℕ) : ℝ) u) := by
      rw [hsum]
      exact mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

private theorem scalar_rep_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Lp ℂ 2 (volume : Measure (Euclidean n)))
      (f : Euclidean n → ℂ), MemFourierSobolev ((k + n + 1 : ℕ) : ℝ) u →
      ContDiff ℝ ∞ f → f =ᵐ[volume] u →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤
        C * fourierSobolevNorm ((k + n + 1 : ℕ) : ℝ) u := by
  let P := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 ↦ ℂ) 0).restrictScalars ℝ
  obtain ⟨C, hC, hb⟩ := vector_rep_bound n 1 k
  refine ⟨‖P‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro u f hu hf he j hj x
  let v := (finiteL2CoordinateIsometry volume).symm (WithLp.toLp 2 (fun _ : Fin 1 ↦ u))
  let g := fun x ↦ WithLp.toLp 2 (fun _ : Fin 1 ↦ f x)
  have hv : MemVectorFourierSobolev ((k + n + 1 : ℕ) : ℝ) v := by
    intro i
    simpa only [v, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply] using hu
  have hg : ContDiff ℝ ∞ g := by
    exact (contDiff_piLp 2).mpr (fun _ ↦ hf)
  have hge : g =ᵐ[volume] v := by
    have hcoord := finiteL2Coordinates_apply_ae volume v (0 : Fin 1)
    have hcoord' : u =ᵐ[volume] fun x ↦ v x 0 := by
      change finiteL2CoordinateIsometry volume v 0 =ᵐ[volume] _ at hcoord
      simpa only [v, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply] using hcoord
    filter_upwards [he, hcoord'] with x hx hy
    ext i
    fin_cases i
    exact hx.trans hy
  have hvnorm : vectorFourierSobolevNorm ((k + n + 1 : ℕ) : ℝ) v =
      fourierSobolevNorm ((k + n + 1 : ℕ) : ℝ) u := by
    simp [vectorFourierSobolevNorm, matrixFourierSobolevNorm, v,
      EuclideanSpace.norm_eq, Real.sqrt_sq (fourierSobolevNorm_nonneg _ _)]
  have hp : P ∘ g = f := rfl
  calc
    _ = ‖iteratedFDeriv ℝ j (P ∘ g) x‖ := by rw [hp]
    _ ≤ ‖P‖ * ‖iteratedFDeriv ℝ j g x‖ :=
      P.norm_iteratedFDeriv_comp_left hg.contDiffAt (by simp)
    _ ≤ ‖P‖ * (C * fourierSobolevNorm ((k + n + 1 : ℕ) : ℝ) u) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [hvnorm] using hb v g hv hg hge j hj x
    _ = _ := by ring

open JanetCartan.ContinuumRow

/-- The finite reserve used for the uncut preparation density includes every
carrier and initial variable, not just transverse Fourier moments
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem exists_carrierRepresentative_derivative_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : CarrierL2 n) (f : CarrierVariable n → ℂ),
      MemPhysicalSobolev (k + (3 + (n - 1)) + 1) u →
      ContDiff ℝ ∞ f → f =ᵐ[carrierMeasure n] u →
      ∀ j ≤ k, ∀ p, ‖iteratedFDeriv ℝ j f p‖ ≤
        C * physicalSobolevNorm (k + (3 + (n - 1)) + 1) u := by
  let L := (initialCoordinatesLinear n).trans (flatInitialEquiv n).toContinuousLinearEquiv
  obtain ⟨C, hC, hb⟩ := scalar_rep_bound (3 + (n - 1)) k
  refine ⟨C * (max 1 ‖L.toContinuousLinearMap‖) ^ k, by positivity, ?_⟩
  intro u f hu hf he j hj p
  let g := f ∘ L.symm
  have hg : ContDiff ℝ ∞ g := hf.comp L.symm.contDiff
  have hge : g =ᵐ[volume] flatInitialL2Equiv n u := by
    have he' := (flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae_eq_comp he
    exact he'.trans (flatInitialL2Equiv_coeFn n u).symm
  have hgb := (hb (flatInitialL2Equiv n u) g
    ((memPhysicalSobolev_iff_memFourierSobolev _ u).mp hu) hg hge j hj (L p)).trans
      (mul_le_mul_of_nonneg_left (fourierSobolevNorm_le_physicalSobolevNorm _ u hu) hC)
  have hpow : ‖L.toContinuousLinearMap‖ ^ j ≤ (max 1 ‖L.toContinuousLinearMap‖) ^ k :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  have hfg : g ∘ L.toContinuousLinearMap = f := by
    funext x
    exact congrArg f (L.symm_apply_apply x)
  calc
    _ = ‖iteratedFDeriv ℝ j (g ∘ L.toContinuousLinearMap) p‖ := by rw [hfg]
    _ = ‖(iteratedFDeriv ℝ j g (L p)).compContinuousLinearMap
        (fun _ ↦ L.toContinuousLinearMap)‖ := by
      rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hg p (by simp)]
      rfl
    _ ≤ ‖iteratedFDeriv ℝ j g (L p)‖ * ‖L.toContinuousLinearMap‖ ^ j := by
      simpa using (iteratedFDeriv ℝ j g (L p)).norm_compContinuousLinearMap_le
        (fun _ ↦ L.toContinuousLinearMap)
    _ ≤ (C * physicalSobolevNorm (k + (3 + (n - 1)) + 1) u) *
        (max 1 ‖L.toContinuousLinearMap‖) ^ k :=
      mul_le_mul hgb hpow (pow_nonneg (norm_nonneg _) _) (by
        exact mul_nonneg hC ENNReal.toReal_nonneg)
    _ = _ := by ring

open JanetCartan.UncutDensity JanetCartan.ContinuumAdjoint.DensityMultiplier

private theorem synthesis_ae_initialDensity {n N : ℕ} (d : CarrierData n N)
    (hρsmooth : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ContDiff ℝ ∞ d.highCutoff)
    (hlow : ∀ r ≤ 1, d.highCutoff r = 0)
    (hχ : ∀ r, |d.highCutoff r| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (c : ℝ) (u : CarrierL2 n) (hu : ∀ s : ℕ, MemRawSobolev s u) :
    let hρ' := fun z θ (_ : ‖θ‖ = 1) ↦
      (show ‖(d.angularCutoff z θ : ℂ)‖ ≤ A by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ z θ)
    let v := densitySynthesisL2 hρsmooth.continuous.measurable hχsmooth.continuous.measurable
      hA hρ' hχ (hlow 0 zero_le_one) u (carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu 1))
    (fun p ↦ (c * synthesisFactor n) * (v p).re) =ᵐ[carrierMeasure n] initialDensity d c u := by
  dsimp only
  let hm := hρsmooth.continuous.measurable
  let hχm := hχsmooth.continuous.measurable
  have hρ' : ∀ z θ, ‖θ‖ = 1 → ‖(d.angularCutoff z θ : ℂ)‖ ≤ A := by
    intro z θ _
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ z θ
  let hw := carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu 1)
  let v := densitySynthesisL2 hm hχm hA hρ' hχ (hlow 0 zero_le_one) u hw
  obtain ⟨h₂, he⟩ := realSynthesisL2_sobolev_coeFn d (n + 1) (by omega)
    hm hχm hA zero_le_one hρ hχ c u (hu _)
  have hfreq : densityFrequencyOutput 0 hm hχm hA hρ' hχ (hlow 0 zero_le_one) u hw =
      h₂.toLp _ := by
    apply Lp.ext
    filter_upwards [densityFrequencyOutput_coeFn 0 hm hχm hA hρ' hχ
      (hlow 0 zero_le_one) u hw, h₂.coeFn_toLp] with p hp hq
    simp only [etaBesselWeight, pow_zero, one_smul] at hp
    exact hp.trans hq.symm
  have hclass : realSynthesisL2 c (h₂.toLp _) =
      (c * synthesisFactor n) • Complex.reCLM.compLpL 2 (carrierMeasure n) v := by
    rw [realSynthesisL2, ← hfreq]
    rfl
  rw [hclass] at he
  filter_upwards [he, Lp.coeFn_smul (c * synthesisFactor n)
    (Complex.reCLM.compLpL 2 (carrierMeasure n) v), Complex.reCLM.coeFn_compLpL v]
    with p hp hq hr
  simpa only [hq, Pi.smul_apply, hr, Complex.reCLM_apply, smul_eq_mul] using hp

/-- The actual uncut density gains globally bounded jets from the full raw
Sobolev estimate. The finite shift is the full initial dimension plus two;
there is no spatial cutoff and no hypothesis assuming a synthesis bound
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem exists_initialDensityRepresentative_derivative_bound {n N : ℕ}
    (d : CarrierData n N)
    (hρsmooth : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hcρ : HasCompactSupport (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ContDiff ℝ ∞ d.highCutoff)
    (hlow : ∀ r ≤ 1, d.highCutoff r = 0)
    (hχ : ∀ r, |d.highCutoff r| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (c : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : CarrierL2 n), (∀ s : ℕ, MemRawSobolev s u) →
      ∀ (f : CarrierVariable n → ℝ), ContDiff ℝ ∞ f →
      f =ᵐ[carrierMeasure n] initialDensity d c u →
      ∀ j ≤ k, ∀ p, ‖iteratedFDeriv ℝ j f p‖ ≤
        C * rawSobolevNorm (k + (3 + (n - 1)) + 1 + 1) u := by
  let hm := hρsmooth.continuous.measurable
  let hχm := hχsmooth.continuous.measurable
  have hρ' : ∀ z θ, ‖θ‖ = 1 → ‖(d.angularCutoff z θ : ℂ)‖ ≤ A := by
    intro z θ _
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ z θ
  obtain ⟨B, hB, hb⟩ := exists_carrierRepresentative_derivative_bound n k
  obtain ⟨D, hD, hd⟩ := exists_densityOutputs_rawSobolev_bound
    (k + (3 + (n - 1)) + 1) hm hχm hA hρ' hχ (hlow 0 zero_le_one)
    hρsmooth hcρ hχsmooth hlow (χy := fun _ : CarrierVariable n ↦ (0 : ℝ))
    contDiff_const HasCompactSupport.zero
  let P := (c * synthesisFactor n) • Complex.reCLM
  refine ⟨‖P‖ * B * D, by positivity, ?_⟩
  intro u hu f hf he j hj p
  let hw := carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu 1)
  let v := densitySynthesisL2 hm hχm hA hρ' hχ (hlow 0 zero_le_one) u hw
  have hv (s : ℕ) : MemPhysicalSobolev s v := by
    obtain ⟨L, _, hL⟩ := exists_densityOutputs_rawSobolev_bound s hm hχm hA hρ'
      hχ (hlow 0 zero_le_one) hρsmooth hcρ hχsmooth hlow
      (χy := fun _ : CarrierVariable n ↦ (0 : ℝ)) contDiff_const HasCompactSupport.zero
    exact (hL u (hu (s + 1))).1.1
  obtain ⟨g, hg, hge⟩ := CurrentMean.exists_smooth_carrierRepresentative n v hv
  have hfg : f = P ∘ g := by
    let : (carrierMeasure n).IsOpenPosMeasure := by
      unfold carrierMeasure
      infer_instance
    apply Measure.eq_of_ae_eq (μ := carrierMeasure n) _ hf.continuous
      (P.continuous.comp hg.continuous)
    have hs := synthesis_ae_initialDensity d hρsmooth hχsmooth hlow hχ hA hρ c u hu
    filter_upwards [he, hs, hge] with x hx hy hz
    exact hx.trans (hy.symm.trans (by
      simp only [Function.comp_apply, P, smul_apply, Complex.reCLM_apply, smul_eq_mul, hz]
      rfl))
  have hgb := hb v g (hv _) hg hge j hj p
  have hnorm := (hd u (hu _)).1.2
  rw [hfg]
  calc
    _ ≤ ‖P‖ * ‖iteratedFDeriv ℝ j g p‖ :=
      P.norm_iteratedFDeriv_comp_left hg.contDiffAt (by simp)
    _ ≤ ‖P‖ * (B * (D * rawSobolevNorm (k + (3 + (n - 1)) + 1 + 1) u)) :=
      mul_le_mul_of_nonneg_left
        (hgb.trans (mul_le_mul_of_nonneg_left hnorm hB)) (norm_nonneg _)
    _ = _ := by ring

end JanetCartan.CurrentMean
