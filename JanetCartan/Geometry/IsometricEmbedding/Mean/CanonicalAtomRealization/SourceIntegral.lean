module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.Integral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FullSuperposition
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Strain

/-!
# The original source after canonical superposition

The response in `app:ch_lag:eq:lag-recurrence` acts on the full cutoff strain
AFTER Fourier synthesis. Prove that this source is the integral of the SAME
atomic sources, and that both quadratures belong to the existing compact
smooth source domain. These feed the fixed-response interchange proved in
`Identification`, without assuming that the response commutes with integration.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CanonicalAtomRealization

open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- The full cutoff strain is linear in the physical differential, including
every entry and both quadratures (`app:ch_lag:eq:lag-recurrence`). -/
private def cutoffStrainDifferential {n N : ℕ} (F : Euclidean n → Euclidean N)
    (χ : Euclidean n → ℝ) (x : Euclidean n) :
    (Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N)) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun D := χ x • fun i j ↦ ∑ k,
        ((partialDeriv F x i k : ℂ) * D (EuclideanSpace.single j 1) k +
          D (EuclideanSpace.single i 1) k * (partialDeriv F x j k : ℂ))
      map_add' D E := by
        ext i j
        simp only [Pi.smul_apply, add_apply,
          PiLp.add_apply, mul_add, add_mul, Finset.sum_add_distrib, Matrix.add_apply]
        simp only [smul_add]
        abel
      map_smul' a D := by
        ext i j
        simp only [Matrix.smul_apply, Pi.smul_apply, smul_apply,
          PiLp.smul_apply, RingHom.id_apply, Complex.real_smul]
        simp only [mul_left_comm _ (a : ℂ), mul_assoc, ← mul_add, ← Finset.mul_sum] }

/-- Complex scaling of the same full strain retains both real quadratures
before applying the fixed real response (`app:ch_lag:eq:lag-recurrence`). -/
private theorem cutoffStrainDifferential_complex_smul {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ) (x : Euclidean n)
    (a : ℂ) (D : Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N)) :
    cutoffStrainDifferential F χ x (a • D) = a • cutoffStrainDifferential F χ x D := by
  ext i j
  simp only [cutoffStrainDifferential, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, Pi.smul_apply,
    smul_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
  simp only [mul_left_comm _ a, mul_assoc, ← mul_add, ← Finset.mul_sum]

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (τ : ℝ) (z : Euclidean 3)
    {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hshift : ∀ p ∈ X ×ˢ V, (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈ Ω)
    (hX : IsOpen X) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (χ : Euclidean n → ℝ) (hsrc : tsupport χ ⊆ X)

include hΩ hspace hphase hF hi hrank hα hnonzero hshift hX hV hceil hd hM hb hsrc

/-- The literal source after full Fourier synthesis is the integral of
the original atomic sources at every physical point, with the cutoff
applied after taking the complete strain. This closes the source identity
used to move the fixed response through the canonical integral
(`app:ch_lag:eq:lag-W0-definition`, `app:ch_lag:eq:lag-recurrence`). -/
theorem fullPrimaryWave_source_eq_integral (v : WideInput n J) (x : Euclidean n) :
    complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v) x =
      ∫ η, weightedWideDensity d v η •
        complexAtomicSource F χ
          (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
            (y, T.reference.spatialPatch z + τ • η)) x := by
  by_cases hx : x ∈ tsupport χ
  · have ha := contDiffOn_shiftedFullPrimaryAtom T Q F row col Φ Y r
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift
    have hint := integrable_wideSuperposition hceil
      (contDiffOn_parameterFDeriv hX hV ha).continuousOn hd hM hb v (hsrc hx)
    have he := (hasFDerivAt_wideSuperposition hX hV hceil ha hd hM hb v (hsrc hx)).fderiv
    change cutoffStrainDifferential F χ x
      (fderiv ℝ (fullPrimaryWave T Q F row col Φ Y τ r z d v) x) = _
    rw [fullPrimaryWave, he, wideSuperposition,
      ← (cutoffStrainDifferential F χ x).integral_comp_comm hint]
    apply integral_congr_ae
    filter_upwards [] with η
    rw [cutoffStrainDifferential_complex_smul]
    rfl
  · simp [complexAtomicSource, image_eq_zero_of_notMem_tsupport hx]

/-- Both quadratures of the SAME superposed source belong to the response's
existing compact smooth source domain. Smoothness is proved for arbitrary
Hilbert data; no membership premise is added to the current map
(`app:ch_response:thm:response-compatible-choice`, `app:ch_lag:eq:lag-recurrence`). -/
theorem fullPrimaryWave_source_quadratures_mem
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (v : WideInput n J) :
    tensorFieldRealPart (complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v)) ∈
      compactSmoothSources (tsupport χ) ∧
    tensorFieldImagPart (complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v)) ∈
      compactSmoothSources (tsupport χ) := by
  have hzero : (0 : Euclidean (n - 1)) ∈ V :=
    hceil (Metric.mem_closedBall_self (by positivity))
  have hXU : X ⊆ U := fun x hx ↦ hspace _ (hshift (x, 0) ⟨hx, hzero⟩)
  exact cutoff_strain_quadratures_mem hχ hc hX (hF.mono hXU)
    (contDiffOn_fullPrimaryWave T Q F row col Φ Y r hΩ hspace hphase hF hi hrank hα hnonzero
      τ z hshift hX hV hceil hd hM hb v) hsrc

/-- Integrability of the full atomic source is proved on the unchanged
Fourier density. The proof uses the bounded finite-dimensional strain map
after the already established derivative interchange
(`app:ch_lag:eq:lag-recurrence`). -/
theorem fullPrimaryWave_source_integrable (v : WideInput n J) (x : Euclidean n) :
    Integrable (fun η ↦ weightedWideDensity d v η • complexAtomicSource F χ
      (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
        (y, T.reference.spatialPatch z + τ • η)) x) := by
  by_cases hx : x ∈ tsupport χ
  · have ha := contDiffOn_shiftedFullPrimaryAtom T Q F row col Φ Y r
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift
    have hint := integrable_wideSuperposition hceil
      (contDiffOn_parameterFDeriv hX hV ha).continuousOn hd hM hb v (hsrc hx)
    apply ((cutoffStrainDifferential F χ x).integrable_comp hint).congr
    filter_upwards [] with η
    rw [cutoffStrainDifferential_complex_smul]
    rfl
  · simp [complexAtomicSource, image_eq_zero_of_notMem_tsupport hx]

/-- The original whole-source map is complex linear on the raw Hilbert
space, proved from its literal full-strain integral. This lets the SAME
algebraic fixed response act on arbitrary raw data, without identifying it
with an unproved integral of responses
(`app:ch_lag:eq:lag-recurrence`, `app:ch_mean_pairs:defn:mean-canonical`). -/
def fullPrimaryWave_sourceLinearMap :
    WideInput n J →ₗ[ℂ] (Euclidean n → Matrix (Fin n) (Fin n) ℂ) where
  toFun v := complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v)
  map_add' v w := by
    funext x
    simp only [fullPrimaryWave_source_eq_integral T Q F row col Φ Y r hΩ hspace hphase
      hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc, Pi.add_apply]
    rw [← integral_add
      (fullPrimaryWave_source_integrable T Q F row col Φ Y r hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc v x)
      (fullPrimaryWave_source_integrable T Q F row col Φ Y r hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc w x)]
    apply integral_congr_ae
    filter_upwards [wideDensity_add hd hb v w] with η hη
    rw [hη, add_smul]
  map_smul' a v := by
    funext x
    change complexAtomicSource _ _ (fullPrimaryWave _ _ _ _ _ _ _ _ _ _ _ (a • v)) x = _
    simp only [fullPrimaryWave_source_eq_integral T Q F row col Φ Y r hΩ hspace hphase
      hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc, Pi.smul_apply,
      RingHom.id_apply]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [wideDensity_smul hd hb a v] with η hη
    rw [hη, mul_smul]

/-- The whole-source linear map retains the full unprojected cutoff strain
(`app:ch_lag:eq:lag-recurrence`). -/
@[simp] theorem fullPrimaryWave_sourceLinearMap_apply (v : WideInput n J) :
    fullPrimaryWave_sourceLinearMap T Q F row col Φ Y r hΩ hspace hphase hF hi hrank hα hnonzero
      τ z hshift hX hV hceil hd hM hb χ hsrc v =
      complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v) := rfl

end JanetCartan.CanonicalAtomRealization
