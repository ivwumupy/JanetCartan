module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Sobolev
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.RawAssembly
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Smooth uncut density representatives for preparation

For `app:ch_mean_pairs:eq:mean-density-recursion`, the full raw Sobolev
regularity of the SAME adjoint input yields a jointly smooth real density.
The half-order multiplier and partial inverse are the existing literal
Lebesgue operators. The exact `synthesisFactor` converts their unitary
normalization to the unprefactored radian synthesis in `UncutDensity`.

The representative agrees with literal synthesis at every initial position
for almost every carrier parameter. This stronger identity justifies
substitution of the transported footpoint, without pulling back a joint
a.e. equality along a graph. Carrier support is also recovered pointwise.

The actual corrected-positive inverse/adjoint producer must still supply
full raw regularity for its smooth sources. This file constructs the density
representative from that membership; it does not assume smoothness of an
arbitrary L² representative or a bound for preparation iterates.
-/

open MeasureTheory Set FourierTransform
open scoped ContDiff

@[expose] public noncomputable section

namespace JanetCartan.CurrentMean

open ContinuumRow CarrierSobolev Pseudodifferential

private theorem exists_smooth_scalarRepresentative {m : ℕ} (hm : 0 < m)
    (u : Lp ℂ 2 (volume : Measure (Euclidean m)))
    (hu : ∀ s : ℕ, MemFourierSobolev (s : ℝ) u) :
    ∃ f : Euclidean m → ℂ, ContDiff ℝ ∞ f ∧ f =ᵐ[volume] u := by
  let v : Lp (EuclideanSpace ℂ (Fin 1)) 2 (volume : Measure (Euclidean m)) :=
    (finiteL2CoordinateIsometry volume).symm (WithLp.toLp 2 (fun _ : Fin 1 ↦ u))
  have hv (s : ℕ) : MemVectorFourierSobolev (s : ℝ) v := by
    intro i
    simpa only [v, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply] using hu s
  have hfinite (k : ℕ) : ∃ f : Euclidean m → EuclideanSpace ℂ (Fin 1),
      ContDiff ℝ k f ∧ f =ᵐ[volume] v := by
    obtain ⟨J, hJ, hmJ, _⟩ := LocalSobolev.exists_vector_weakJet_nat_explicit
      m 1 (k + m + 1) v (hv _)
    exact LocalSobolev.FiniteOrder.exists_contDiff_ae_eq_of_weakJet hm hJ (Lp.memLp v) hmJ
  obtain ⟨f, hf, he⟩ := hfinite 0
  have hfs : ContDiff ℝ ∞ f := by
    apply contDiff_infty.mpr
    intro k
    obtain ⟨g, hg, hge⟩ := hfinite k
    have hfg := Measure.eq_of_ae_eq (he.trans hge.symm) hf.continuous hg.continuous
    rwa [hfg]
  refine ⟨fun x ↦ f x 0, (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 ↦ ℂ) 0).restrictScalars ℝ
    |>.contDiff.comp hfs, ?_⟩
  have hcoord : u =ᵐ[volume] fun x ↦ v x 0 := by
    have h := finiteL2Coordinates_apply_ae volume v (0 : Fin 1)
    change finiteL2CoordinateIsometry volume v 0 =ᵐ[volume] _ at h
    simpa only [v, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply] using h
  filter_upwards [he, hcoord] with x hx hy
  exact (congrArg (fun z : EuclideanSpace ℂ (Fin 1) ↦ z 0) hx).trans hy.symm

/-- All physical initial Sobolev orders give one smooth representative on
all carrier and initial variables. The coordinate and measure identifications
are the existing ones (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem exists_smooth_carrierRepresentative (n : ℕ) (u : CarrierL2 n)
    (hu : ∀ s : ℕ, MemPhysicalSobolev s u) :
    ∃ f : CarrierVariable n → ℂ, ContDiff ℝ ∞ f ∧ f =ᵐ[carrierMeasure n] u := by
  obtain ⟨f, hf, he⟩ := exists_smooth_scalarRepresentative (by omega : 0 < 3 + (n - 1))
    (flatInitialL2Equiv n u) (fun s ↦ (memPhysicalSobolev_iff_memFourierSobolev s u).mp (hu s))
  let L := (initialCoordinatesLinear n).trans (flatInitialEquiv n).toContinuousLinearEquiv
  refine ⟨fun p ↦ f (flatInitialCoordinates n p), hf.comp L.contDiff, ?_⟩
  have h := (flatInitialCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (he.trans (flatInitialL2Equiv_coeFn n u))
  filter_upwards [h] with p hp
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using hp

open UncutDensity ContinuumAdjoint.DensityMultiplier

/-- Construct a smooth representative of the actual uncut signed density
from full raw regularity and the original smooth masks. The multiplier's
Sobolev membership is proved and instantiated, not an extra input
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem exists_smooth_initialDensity {n N : ℕ} (d : CarrierData n N)
    (hρsmooth : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hcρ : HasCompactSupport (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ContDiff ℝ ∞ d.highCutoff)
    (hlow : ∀ r ≤ 1, d.highCutoff r = 0)
    (hχ : ∀ r, |d.highCutoff r| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (c : ℝ) (u : CarrierL2 n) (hu : ∀ s : ℕ, MemRawSobolev s u) :
    ∃ f : CarrierVariable n → ℝ, ContDiff ℝ ∞ f ∧
      f =ᵐ[carrierMeasure n] initialDensity d c u := by
  let hm := hρsmooth.continuous.measurable
  let hχm := hχsmooth.continuous.measurable
  have hρ' : ∀ z θ, ‖θ‖ = 1 → ‖(d.angularCutoff z θ : ℂ)‖ ≤ A := by
    intro z θ _
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ z θ
  let hw := carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu 1)
  let v := densitySynthesisL2 hm hχm hA hρ' hχ (hlow 0 zero_le_one) u hw
  have hv (s : ℕ) : MemPhysicalSobolev s v := by
    obtain ⟨L, _, hL⟩ := exists_densityOutputs_rawSobolev_bound s hm hχm hA hρ'
      hχ (hlow 0 zero_le_one) hρsmooth hcρ hχsmooth hlow
      (χy := fun _ : CarrierVariable n ↦ (0 : ℝ)) contDiff_const HasCompactSupport.zero
    exact (hL u (hu (s + 1))).1.1
  obtain ⟨g, hg, hge⟩ := exists_smooth_carrierRepresentative n v hv
  let f := fun p ↦ (c * synthesisFactor n) * (g p).re
  refine ⟨f, contDiff_const.mul (Complex.reCLM.contDiff.comp hg), ?_⟩
  obtain ⟨h₂, he⟩ := realSynthesisL2_sobolev_coeFn d (n + 1) (by omega)
    hm hχm hA zero_le_one hρ hχ c u (hu _)
  have hfreq : densityFrequencyOutput 0 hm hχm hA hρ' hχ (hlow 0 zero_le_one) u hw =
      h₂.toLp _ := by
    apply Lp.ext
    filter_upwards [densityFrequencyOutput_coeFn 0 hm hχm hA hρ' hχ
      (hlow 0 zero_le_one) u hw, h₂.coeFn_toLp] with p hp hq
    simp only [etaBesselWeight, pow_zero, one_smul] at hp
    exact hp.trans hq.symm
  have he' : (fun p ↦ (c * synthesisFactor n) * (v p).re) =ᵐ[carrierMeasure n]
      initialDensity d c u := by
    have hclass : realSynthesisL2 c (h₂.toLp _) =
        (c * synthesisFactor n) • Complex.reCLM.compLpL 2 (carrierMeasure n) v := by
      rw [realSynthesisL2, ← hfreq]
      rfl
    rw [hclass] at he
    filter_upwards [he, Lp.coeFn_smul (c * synthesisFactor n)
      (Complex.reCLM.compLpL 2 (carrierMeasure n) v), Complex.reCLM.coeFn_compLpL v]
      with p hp hq hr
    simpa only [hq, Pi.smul_apply, hr, Complex.reCLM_apply, smul_eq_mul] using hp
  filter_upwards [hge, he'] with p hp hq
  exact (congrArg (fun z : ℂ ↦ (c * synthesisFactor n) * z.re) hp).trans hq

/-- Absolute frequency integrability makes literal synthesis continuous
in every initial position (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem initialDensity_continuous_slice {n N : ℕ} (d : CarrierData n N)
    (c : ℝ) (u : CarrierVariable n → ℂ) (z : CarrierParameter)
    (hu : Integrable (fun η ↦ carrierDensitySymbol d (z,η) * u (z,η))) :
    Continuous (fun y ↦ initialDensity d c u (z,y)) := by
  have hfourier : Continuous (𝓕 (fun η ↦ carrierDensitySymbol d (z,η) * u (z,η))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hu
  simp only [initialDensity, radianInverseIntegral_eq_fourierInv, Real.fourierInv_eq_fourier_neg]
  apply continuous_const.mul (Complex.continuous_re.comp (hfourier.comp ?_))
  fun_prop

/-- A continuous representative agrees with literal synthesis at EVERY
initial position for almost every carrier parameter. This closes the
footpoint-evaluation obligation in `app:ch_mean_pairs:eq:mean-density-recursion`. -/
theorem initialDensity_ae_all_positions {n N : ℕ} (d : CarrierData n N)
    (s : ℕ) (hs : n - 1 < 2 * s)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχm : Measurable d.highCutoff) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A) (hχ : ∀ r, |d.highCutoff r| ≤ B)
    (c : ℝ) (u : CarrierL2 n) (hu : MemRawSobolev (s + 1) u)
    (f : CarrierVariable n → ℝ) (hf : Continuous f)
    (he : f =ᵐ[carrierMeasure n] initialDensity d c u) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      ∀ y, f (z,y) = initialDensity d c u (z,y) := by
  have hslice := integrable_slice_of_weighted_density s hs
    (memLp_weighted_densitySymbol d s hρm hχm hA hB hρ hχ u
      (carrierWeightedMem_of_memRawSobolev hu))
  filter_upwards [Measure.ae_ae_of_ae_prod he, hslice] with z hz hi
  have heq := Measure.eq_of_ae_eq hz
    (hf.comp (continuous_const.prodMk continuous_id)) (initialDensity_continuous_slice d c u z hi)
  exact congrFun heq

/-- The same transported mean is obtained after choosing the smooth
representative. Equality at every initial position precedes substitution of
the actual footpoint (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem measuredIncrement_eq_of_ae_all_positions {n N : ℕ} (d : CarrierData n N)
    (ψ : CarrierParameter → ℝ) {f g : CarrierVariable n → ℝ}
    (hfg : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter), ∀ y, f (z,y) = g (z,y)) :
    measuredIncrement d ψ f = measuredIncrement d ψ g := by
  funext x
  apply congrArg (fun v : Torus n → Euclidean n ↦ d.outputChart.indicator v x)
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with z hz
  rw [hz]

/-- The smooth density retains the original closed carrier support,
pointwise for every initial position, without any spatial cutoff
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem initialDensityRepresentative_zero_off_carrier {n N : ℕ} (d : CarrierData n N)
    (c : ℝ) (u : CarrierL2 n) {K : Set CarrierParameter} (hK : IsClosed K)
    (hsupp : ∀ z, z ∉ K → ∀ θ, d.angularCutoff z θ = 0)
    (f : CarrierVariable n → ℝ) (hf : Continuous f)
    (he : f =ᵐ[carrierMeasure n] initialDensity d c u) :
    ∀ z, z ∉ K → ∀ y, f (z,y) = 0 := by
  let : (carrierMeasure n).IsOpenPosMeasure := by
    unfold carrierMeasure
    infer_instance
  let V : Set (CarrierVariable n) := {p | p.1 ∉ K}
  have hV : IsOpen V := hK.isOpen_compl.preimage continuous_fst
  have hz : f =ᵐ[(carrierMeasure n).restrict V] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hV.measurableSet] with p hp hpV
    exact hp.trans (initialDensity_eq_zero_of_angular d c u p.1 (hsupp p.1 hpV) p.2)
  have heq := Measure.eqOn_open_of_ae_eq hz hV hf.continuousOn continuousOn_const
  exact fun z hz y ↦ heq hz

/-- Additivity of literal uncut synthesis on its actual regular domain,
with equality at every initial position before footpoint substitution
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem initialDensity_add_ae_all_positions {n N : ℕ} (d : CarrierData n N)
    (s : ℕ) (hs : n - 1 < 2 * s)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχm : Measurable d.highCutoff) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A) (hχ : ∀ r, |d.highCutoff r| ≤ B)
    (c : ℝ) (u v : CarrierL2 n) (hu : MemRawSobolev (s + 1) u)
    (hv : MemRawSobolev (s + 1) v) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter), ∀ y,
      initialDensity d c (u + v : CarrierL2 n) (z,y) =
        initialDensity d c u (z,y) + initialDensity d c v (z,y) := by
  have hi (w : CarrierL2 n) (hw : MemRawSobolev (s + 1) w) :=
    integrable_slice_of_weighted_density s hs
      (memLp_weighted_densitySymbol d s hρm hχm hA hB hρ hχ w
        (carrierWeightedMem_of_memRawSobolev hw))
  have he := initialDensity_congr d c (Lp.coeFn_add u v)
  have hz : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter), ∀ y,
      initialDensity d c (u + v : CarrierL2 n) (z,y) =
        initialDensity d c u (z,y) + initialDensity d c v (z,y) := by
    filter_upwards [he, hi u hu, hi v hv] with z hz hu hv
    intro y
    rw [hz]
    have hfourier : 𝓕 ((fun η ↦ carrierDensitySymbol d (z,η) * u (z,η)) +
        (fun η ↦ carrierDensitySymbol d (z,η) * v (z,η))) =
      𝓕 (fun η ↦ carrierDensitySymbol d (z,η) * u (z,η)) +
        𝓕 (fun η ↦ carrierDensitySymbol d (z,η) * v (z,η)) :=
      VectorFourier.fourierIntegral_add Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hu hv
    have hh := congrFun hfourier (-((2 * Real.pi)⁻¹ • y))
    simp only [initialDensity, radianInverseIntegral_eq_fourierInv, Real.fourierInv_eq_fourier_neg]
    have heq : (fun η ↦ carrierDensitySymbol d (z,η) * ((u : CarrierVariable n → ℂ) + v) (z,η)) =
        (fun η ↦ carrierDensitySymbol d (z,η) * u (z,η)) +
          (fun η ↦ carrierDensitySymbol d (z,η) * v (z,η)) := by
      funext η
      simp only [Pi.add_apply, mul_add]
    rw [heq, hh, Pi.add_apply, Complex.add_re, mul_add]
  exact hz

/-- Real scalar linearity retains the uncut signed density and holds at
every initial position for almost every carrier parameter
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem initialDensity_smul_ae_all_positions {n N : ℕ} (d : CarrierData n N)
    (c a : ℝ) (u : CarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter), ∀ y,
      initialDensity d c (a • u : CarrierL2 n) (z,y) = a * initialDensity d c u (z,y) := by
  have he := initialDensity_congr d c (Lp.coeFn_smul a u)
  have hz : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter), ∀ y,
      initialDensity d c (a • u : CarrierL2 n) (z,y) = a * initialDensity d c u (z,y) := by
    filter_upwards [he] with z hz
    intro y
    rw [hz]
    simp only [initialDensity, radianInverseIntegral, Pi.smul_apply]
    simp_rw [mul_smul_comm, smul_comm _ a, integral_smul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  exact hz

end JanetCartan.CurrentMean
