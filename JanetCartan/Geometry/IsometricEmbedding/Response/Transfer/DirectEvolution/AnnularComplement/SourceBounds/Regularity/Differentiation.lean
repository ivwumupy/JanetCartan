module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Regularity.Integrand

/-!
# Differentiation of the literal inner source integral

The primitive producer is `contDiffOn_annularSourceIntegrand_localCarrierPhase`;
`elapsedAnnularSourceKernelObservation_regularity` instantiates it from the
original data. Every finite joint parameter/output derivative passes through the source
integral. Compactness of the original envelope support supplies integrability
and local domination. There is no frequency integrability hypothesis or compact
frequency cutoff. These are the qualitative inputs to the quantitative assembly
in `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Joint smoothness in `(c,x,ξ)` of each of the four literal kernels, from
primitive data on the supported phase chart. In particular, `(c,x)` is smooth
at every frequency (`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffOn_annularSourceKernelObservation_of_joint
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
  (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
  {U : Set P} (hU : IsOpen U)
  (hJ : ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
    annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
      (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ))
  {K : Set E} (hK : IsCompact K) (hs : ∀ c ∈ U, tsupport (a c) ⊆ K) :
    ContDiffOn ℝ ∞ (fun p : (P × E) × E =>
      annularSourceKernelObservation adj demod Θ A π (φ p.1.1) lam (a p.1.1) p.1.2 p.2)
      ((U ×ˢ univ) ×ˢ univ) := by
  have hJs : ∀ p ∈ (U ×ˢ (univ : Set E)) ×ˢ (univ : Set E), ∀ z ∉ K,
      annularSourceIntegrand adj demod Θ A π (φ p.1.1) lam (a p.1.1) p.1.2 p.2 z = 0 := by
    intro p hp z hz
    exact annularSourceIntegrand_eq_zero_of_source_eq_zero adj demod Θ A π _ lam _ _ _ _
      (image_eq_zero_of_notMem_tsupport (fun h => hz (hs p.1.1 hp.1.1 h)))
  apply ((contDiffOn_integral_parameterCompactSupport (μ := volume)
    ((hU.prod isOpen_univ).prod isOpen_univ) hJ hK hJs).const_smul
      (((2 * Real.pi) ^ n : ℂ)⁻¹)).congr
  intro p _
  exact annularSourceKernelObservation_eq_integral adj demod Θ A π _ lam _ _ _

omit [FiniteDimensional ℝ P] in
/-- At each unrestricted frequency, the actual external integrand jet is
source integrable. This includes the derivatives of the demodulator and derives
integrability from the original envelope (`app:ch_response:lem:energy-carrier-jets`). -/
theorem integrable_iteratedFDeriv_annularSourceIntegrand_of_joint
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
  (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
  {U : Set P} (hU : IsOpen U)
  (hJ : ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
    annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
      (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ))
  {K : Set E} (hK : IsCompact K) (hs : ∀ c ∈ U, tsupport (a c) ⊆ K)
    (k : ℕ) {c : P} (hc : c ∈ U) (x ξ : E) :
    Integrable (fun z => iteratedFDeriv ℝ k (fun p : P × E =>
      annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z) (c, x)) := by
  have hJξ : ContDiffOn ℝ ∞ (fun q : (P × E) × E =>
      annularSourceIntegrand adj demod Θ A π (φ q.1.1) lam (a q.1.1) q.1.2 ξ q.2)
      ((U ×ˢ univ) ×ˢ univ) :=
    hJ.comp ((contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd)
      (fun _ hp => ⟨⟨hp.1, mem_univ _⟩, hp.2⟩)
  apply integrable_parameterJet_of_compactSupport (μ := volume)
    (hU.prod isOpen_univ) hJξ hK _ k ⟨hc, mem_univ x⟩
  intro p hp z hz
  exact annularSourceIntegrand_eq_zero_of_source_eq_zero adj demod Θ A π _ lam _ _ _ _
    (image_eq_zero_of_notMem_tsupport (fun h => hz (hs p.1 hp.1 h)))

/-- Exact finite external derivative identity, including the physical Fourier
normalization. The right side differentiates the actual complete integrand;
no modified-amplitude bound or frequency integrability is assumed. Both Boolean
indices can be specialized to recover the four published literal kernels.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem iteratedFDeriv_annularSourceKernelObservation_of_joint
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
  (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
  {U : Set P} (hU : IsOpen U)
  (hJ : ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
    annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
      (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ))
  {K : Set E} (hK : IsCompact K) (hs : ∀ c ∈ U, tsupport (a c) ⊆ K)
    (k : ℕ) (v : Fin k → P × E) {c : P} (hc : c ∈ U) (x ξ : E) :
    iteratedFDeriv ℝ k (fun p : P × E =>
      annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ)
        (c, x) v =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
        iteratedFDeriv ℝ k (fun p : P × E =>
          annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z) (c, x) v := by
  have hJξ : ContDiffOn ℝ ∞ (fun q : (P × E) × E =>
      annularSourceIntegrand adj demod Θ A π (φ q.1.1) lam (a q.1.1) q.1.2 ξ q.2)
      ((U ×ˢ univ) ×ˢ univ) :=
    hJ.comp ((contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd)
      (fun _ hp => ⟨⟨hp.1, mem_univ _⟩, hp.2⟩)
  have hJs : ∀ p ∈ U ×ˢ (univ : Set E), ∀ z ∉ K,
      annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z = 0 := by
    intro p hp z hz
    exact annularSourceIntegrand_eq_zero_of_source_eq_zero adj demod Θ A π _ lam _ _ _ _
      (image_eq_zero_of_notMem_tsupport (fun h => hz (hs p.1 hp.1 h)))
  have hG := contDiffOn_integral_parameterCompactSupport (μ := volume)
    (hU.prod isOpen_univ) hJξ hK hJs
  simp_rw [annularSourceKernelObservation_eq_integral]
  rw [iteratedFDeriv_const_smul_apply'
    ((hG.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩)).of_le (by simp))]
  change ((2 * Real.pi) ^ n : ℂ)⁻¹ • (iteratedFDeriv ℝ k
    (fun p : P × E => ∫ z,
      annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z) (c, x) v) = _
  rw [iteratedFDeriv_integral_parameterCompactSupport (hU.prod isOpen_univ) hJξ hK hJs k
    ⟨hc, mem_univ x⟩,
    ContinuousMultilinearMap.integral_apply
      (integrable_iteratedFDeriv_annularSourceIntegrand_of_joint adj demod Θ A π φ lam a
        hU hJ hK hs k hc x ξ)]

omit [FiniteDimensional ℝ P] in
private theorem continuous_annular_externalJet_frequency
    {U : Set P} (hU : IsOpen U) {g : (P × E) × E → F}
    (hg : ContDiffOn ℝ ∞ g ((U ×ˢ univ) ×ˢ univ))
    (k : ℕ) (v : Fin k → P × E) {c : P} (hc : c ∈ U) (x : E) :
    Continuous (fun ξ => iteratedFDeriv ℝ k (fun p : P × E => g (p, ξ)) (c, x) v) := by
  have hj := contDiffOn_parameterIteratedFDeriv (hU.prod isOpen_univ) hg k
  have hjξ : Continuous (fun ξ : E =>
      iteratedFDeriv ℝ k (fun p : P × E => g (p, ξ)) (c, x)) := by
    rw [← continuousOn_univ]
    have hh := hj.continuousOn.comp
      (show ContinuousOn (fun ξ : E => ((c, x), ξ)) univ from
        (continuous_const.prodMk continuous_id).continuousOn)
      (fun ξ _ => ⟨⟨hc, mem_univ x⟩, mem_univ ξ⟩)
    exact hh
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P × E) F v).continuous.comp hjξ

/-- Every evaluated joint external derivative is continuous in frequency on the
whole frequency space. This is stronger than the measurability needed for the
annular Sobolev deduction (`app:ch_response:lem:energy-carrier-jets`). -/
theorem continuous_iteratedFDeriv_annularSourceKernelObservation_frequency_of_joint
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
  (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
  {U : Set P} (hU : IsOpen U)
  (hJ : ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
    annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
      (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ))
  {K : Set E} (hK : IsCompact K) (hs : ∀ c ∈ U, tsupport (a c) ⊆ K)
    (k : ℕ) (v : Fin k → P × E) {c : P} (hc : c ∈ U) (x : E) :
    Continuous (fun ξ => iteratedFDeriv ℝ k (fun p : P × E =>
      annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ)
        (c, x) v) := by
  have hG := contDiffOn_annularSourceKernelObservation_of_joint adj demod Θ A π φ lam a
    hU hJ hK hs
  exact continuous_annular_externalJet_frequency hU hG k v hc x

/-- Frequency strong measurability of all actual evaluated external jets,
without a frequency cutoff (`app:ch_response:lem:energy-carrier-jets`). -/
theorem stronglyMeasurable_iteratedFDeriv_annularSourceKernelObservation_frequency_of_joint
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
  (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
  {U : Set P} (hU : IsOpen U)
  (hJ : ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
    annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
      (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ))
  {K : Set E} (hK : IsCompact K) (hs : ∀ c ∈ U, tsupport (a c) ⊆ K)
    (k : ℕ) (v : Fin k → P × E) {c : P} (hc : c ∈ U) (x : E) :
    StronglyMeasurable (fun ξ => iteratedFDeriv ℝ k (fun p : P × E =>
      annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ)
        (c, x) v) :=
  (continuous_iteratedFDeriv_annularSourceKernelObservation_frequency_of_joint adj demod Θ A π φ
    lam a hU hJ hK hs k v hc x).stronglyMeasurable

/-- Frequency strong measurability of each original literal kernel, including
both demodulated observations (`app:ch_response:lem:energy-carrier-jets`). -/
theorem stronglyMeasurable_annularSourceKernelObservation_frequency_of_joint
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
  (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
  {U : Set P} (hU : IsOpen U)
  (hJ : ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
    annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
      (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ))
  {K : Set E} (hK : IsCompact K) (hs : ∀ c ∈ U, tsupport (a c) ⊆ K)
    {c : P} (hc : c ∈ U) (x : E) :
    StronglyMeasurable (fun ξ =>
      annularSourceKernelObservation adj demod Θ A π (φ c) lam (a c) x ξ) := by
  simpa using stronglyMeasurable_iteratedFDeriv_annularSourceKernelObservation_frequency_of_joint
    adj demod Θ A π φ lam a hU hJ hK hs
      0 (fun i => Fin.elim0 i) hc x

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
