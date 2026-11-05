module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Chart
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.RadialFactor
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.RawSpace
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Literal vector components and the shared raw norm

For `app:ch_background:prop:bg-adjoint`, retain the literal vector contraction
and the actual torus-to-Lebesgue chart transfer. The component operators below
act on the existing Euclidean vector L² space and return the existing carrier
L² space. The finite sum uses the shared raw Sobolev norm.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow NormalComparison AmplitudeBound PeriodicLocalL2
open CarrierSobolev Pseudodifferential
variable {n N : ℕ}

/-- The literal normalized component, retaining the angular mask and full
normal field of `app:ch_background:eq:bg-T`. Only the frequency-only radial
factor is separated for the half-order estimates. -/
def carrierChartNormalizedComponent (d : CarrierData n N) (χ : Euclidean n → ℝ)
    (j : Fin n) : AdjointAmplitude n := fun z x η ↦
  (χ x * d.angularCutoff z (‖η‖⁻¹ • η) * ‖d.normalField x z‖ ^ 2 *
    reducedCovector d x (d.covector x z) j : ℝ)

/-- Exact normalization of the literal component for the raw adjoint estimate
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierChartComponent_eq_frequencyScale (d : CarrierData n N)
    (χ : Euclidean n → ℝ) (j : Fin n) :
    carrierChartComponent d χ j = frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
      (carrierChartNormalizedComponent d χ j) := by
  funext z x η
  simp only [carrierChartComponent, carrierChartAmplitude, carrierChartNormalizedComponent,
    frequencyScaleAmplitude, halfOrderRadialFactor, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- Compact measurement support makes the component integral absolutely
convergent for every L² datum (`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_chartAdjoint_L2 {φ : Euclidean n → ℝ} {a v : Euclidean n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : Continuous a) (hs : HasCompactSupport a)
    (hv : MemLp v 2) :
    Integrable (fun x ↦ oscillatoryFactor (-1) (φ x) * (a x * v x)) := by
  have hk : MemLp (fun x ↦ oscillatoryFactor (-1) (φ x) * a x) 2 :=
    ((CompactTransport.contDiff_oscillatoryFactor hφ (-1)).continuous.mul ha).memLp_of_hasCompactSupport hs.mul_left
  have hi : Integrable (fun x ↦ (oscillatoryFactor (-1) (φ x) * a x) * v x) :=
    hk.integrable_mul hv
  simpa only [mul_assoc] using hi

/-- Literal Haar-to-Lebesgue component decomposition on all Euclidean vector
L² representatives. Integrability is proved before extracting the finite sum;
no smoothness of the datum is needed (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierAdjointIntegral_eq_sum_chartAdjoint_L2
    (d : CarrierData n N) {K S : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hS : IsCompact S) (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (χ : Euclidean n → ℝ) (hχ : ∀ x ∉ K, χ x = 0)
    (hcut : ∀ x ∈ d.outputChart, d.measurementCutoff x = χ (centeredTorusRepresentative x))
    (v : Torus n → EuclideanSpace ℂ (Fin n))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2)
    (hw : ∀ x ∈ d.outputChart, f (centeredTorusRepresentative x) = v x)
    (ha : ∀ j, SmoothSupportedAdjointAmplitude S (carrierChartComponent d χ j))
    (hΦ : ∀ z η, ContDiff ℝ ∞ (fun x ↦ carrierChartPhase d z x η))
    (u : CarrierVariable n) :
    carrierAdjointIntegral d v u = ∑ j : Fin n,
      chartAdjoint (fun x ↦ carrierChartPhase d u.1 x u.2)
        (fun x ↦ carrierChartComponent d χ j u.1 x u.2)
        (finiteL2CoordinateIsometry volume f j) := by
  rw [carrierAdjointIntegral_eq_chartIntegral d hcell hchart hpoint χ hχ hcut v f hw u]
  have hi (j : Fin n) : Integrable (fun x ↦
      oscillatoryFactor (-1) (carrierChartPhase d u.1 x u.2) *
        (carrierChartComponent d χ j u.1 x u.2 * f x j)) :=
    integrable_chartAdjoint_L2 (hΦ u.1 u.2)
      (((ha j).smooth u.2).comp (contDiff_const.prodMk contDiff_id)).continuous
      (hS.of_isClosed_subset isClosed_closure ((ha j).tsupport_subset hS.isClosed u.1 u.2))
      ((Lp.memLp f).eval_piLp j)
  simp only [PiLp.inner_apply, euclideanComplexInclusion_apply, RCLike.inner_apply,
    Complex.conj_ofReal, mul_comm (f _ _), Finset.mul_sum]
  calc
    _ = ∑ j : Fin n, chartAdjoint (fun x ↦ carrierChartPhase d u.1 x u.2)
        (fun x ↦ carrierChartComponent d χ j u.1 x u.2) (fun x ↦ f x j) :=
      integral_finsetSum _ (fun j _ ↦ hi j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      unfold chartAdjoint
      apply integral_congr_ae
      filter_upwards [finiteL2Coordinates_apply_ae volume f j] with x hx
      change finiteL2CoordinateIsometry volume f j x = f x j at hx
      rw [hx]

/-- The shared full raw Sobolev norm has the triangle bound needed for the
finite component contraction (`app:ch_background:prop:bg-adjoint`). -/
theorem rawSobolevNorm_finsetSum {ι : Type*} (I : Finset ι) (s : ℕ)
    (f : ι → CarrierL2 n) (hf : ∀ i ∈ I, MemRawSobolev s (f i)) :
    MemRawSobolev s (∑ i ∈ I, f i) ∧
      rawSobolevNorm s (∑ i ∈ I, f i) ≤ ∑ i ∈ I, rawSobolevNorm s (f i) := by
  have hm : (∑ i ∈ I, f i) ∈ rawSobolevLevel n s :=
    (rawSobolevLevel n s).sum_mem hf
  refine ⟨hm, ?_⟩
  classical
  let F (i : ι) : rawSobolevLevel n s :=
    if hi : i ∈ I then ⟨f i, hf i hi⟩ else 0
  have hF (i : ι) (hi : i ∈ I) : (F i).val = f i := by simp [F, hi]
  have he : (∑ i ∈ I, F i).val = ∑ i ∈ I, f i := by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl hF
  rw [← he, ← norm_rawSobolevAnalysis, map_sum]
  exact (norm_sum_le I _).trans_eq (Finset.sum_congr rfl (fun i hi ↦ by
    rw [norm_rawSobolevAnalysis, hF i hi]))

/-- The actual finite component contraction, using the existing isometric
Euclidean vector coordinates (`app:ch_background:prop:bg-adjoint`). -/
def carrierComponentOperator
    (U : Fin n → Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n) :
    Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2 →L[ℂ] CarrierL2 n :=
  ∑ j, (U j).comp ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ Lp (α := Euclidean n) ℂ 2) j).comp
    (finiteL2CoordinateIsometry volume).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The finite contraction has the displayed component sum
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierComponentOperator_apply
    (U : Fin n → Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n)
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2) :
    carrierComponentOperator U f = ∑ j, U j (finiteL2CoordinateIsometry volume f j) := by
  simp [carrierComponentOperator]

/-- Finite component estimates give the actual vector-datum estimate in the
shared raw norm. The parent supplies every scalar estimate using
`exists_chartAdjoint_raw_bound`, so this implication is not an assumed
modified-operator estimate (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierComponentOperator_raw_bound
    (U : Fin n → Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n)
    (s : ℕ) (C : Fin n → ℝ) (H : ℝ) (hC : ∀ j, 0 ≤ C j) (hH : 0 ≤ H)
    (hU : ∀ j f, MemFourierSobolev s f → MemRawSobolev s (U j f) ∧
      rawSobolevNorm s (U j f) ≤ C j * (fourierSobolevNorm s f + H * ‖f‖))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2)
    (hf : MemVectorFourierSobolev s f) :
    MemRawSobolev s (carrierComponentOperator U f) ∧
      rawSobolevNorm s (carrierComponentOperator U f) ≤
        (∑ j, C j) * (vectorFourierSobolevNorm s f + H * ‖f‖) := by
  rw [carrierComponentOperator_apply]
  obtain ⟨hm, hb⟩ := rawSobolevNorm_finsetSum Finset.univ s
    (fun j ↦ U j (finiteL2CoordinateIsometry volume f j)) (fun j _ ↦ (hU j _ (hf j)).1)
  refine ⟨hm, hb.trans ?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  apply (hU j _ (hf j)).2.trans
  apply mul_le_mul_of_nonneg_left _ (hC j)
  apply add_le_add (fourierSobolevNorm_coordinate_le _ _ j)
  apply mul_le_mul_of_nonneg_left _ hH
  exact (PiLp.norm_apply_le (finiteL2CoordinateIsometry volume f) j).trans_eq
    ((finiteL2CoordinateIsometry volume).norm_map f)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
