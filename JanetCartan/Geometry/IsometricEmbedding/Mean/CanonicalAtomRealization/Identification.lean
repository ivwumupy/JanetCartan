module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.ResponseIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.WholeSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.FullPrimarySource

/-!
# Identifying whole-source and corrected-atom constructions

For `app:ch_lag:eq:lag-recurrence`, prove the literal response-integral
interchange for the actual full primary source. Then identify the whole-source
corrected displacement and its physical derivative with the previously
constructed atomwise integral. The original source cutoff, spatial chart,
response, carrier and smooth-band density are retained. The source-norm bound
is the order-zero instance of the fixed-response producer's tame estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces

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

include hΩ hspace hphase hF hi hrank hα hnonzero hshift hX hV hsrc

/-- The actual shifted complete atomic source is jointly smooth on the
whole physical space, retaining the original source cutoff
(`app:ch_lag:eq:lag-recurrence`). -/
theorem contDiffOn_shiftedFullPrimarySource (hχ : ContDiff ℝ ∞ χ) :
    ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n - 1) ↦ complexAtomicSource F χ
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
          (y, T.reference.spatialPatch z + τ • p.2)) p.1) (univ ×ˢ V) := by
  have hw := contDiffOn_shiftedFullPrimaryAtom T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift
  have hs := contDiffOn_jointComplexStrain hU (hX.prod hV)
    (fun p hp ↦ hspace _ (hshift p hp)) hF hw
  intro p hp
  by_cases hx : p.1 ∈ tsupport χ
  · exact ((hχ.contDiffAt.comp p contDiffAt_fst).smul
      (hs.contDiffAt ((hX.prod hV).mem_nhds ⟨hsrc hx, hp.2⟩))).contDiffWithinAt
  · apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℂ))).congr_of_eventuallyEq
    have he : (fun q : Euclidean n × Euclidean (n - 1) ↦ χ q.1) =ᶠ[𝓝 p] (fun _ ↦ 0) :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto (continuous_fst.tendsto p)
    filter_upwards [he] with q hq
    simp only [complexAtomicSource, hq, zero_smul]

variable (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {d₀ : ℕ} (e : (ℝ × (Fin d₀ → ℝ)) ≃L[ℝ] Euclidean n)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))

include hceil hd hM hb hχ hc

/-- The whole-source response identity needs the source bound only on the
observation set. The entire source cutoff may extend beyond that set into
the original raw chart (`app:ch_lag:eq:lag-recurrence`). -/
theorem fullPrimaryWave_response_eq_integral_on_observation
    {L : Set (Euclidean n)}
    (hB : ∀ i j : Fin n, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ L,
        ‖tensorComponentResponse e (tsupport χ) B i j u x‖ ≤
          C * ‖ofTest s volume u.val‖)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ L) :
    complexifyResponse B
      (complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v)) x =
      wideSuperposition (fun p : Euclidean n × Euclidean (n - 1) ↦
        fullPrimaryResponse T Q F row col Φ Y χ B τ r
          (z, T.reference.spatialPatch z + τ • p.2) p.1) d v x := by
  have he := fullPrimaryWave_source_eq_integral T Q F row col Φ Y r hΩ hspace hphase
    hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc v
  rw [show complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v) =
      (fun y ↦ ∫ ξ, weightedWideDensity d v ξ • complexAtomicSource F χ
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
          (y, T.reference.spatialPatch z + τ • ξ)) y) from funext he]
  apply complexifyResponse_wideIntegral hV hceil hd hM hb e hc B x
  · intro i j
    obtain ⟨s, C, hC, hCb⟩ := hB i j
    exact ⟨s, C, hC, fun u ↦ hCb u x hx⟩
  · exact contDiffOn_shiftedFullPrimarySource T Q F row col Φ Y r hΩ hspace hphase
      hF hi hrank hα hnonzero τ z hshift hX hV χ hsrc hχ
  · intro ξ _
    exact tsupport_smul_subset_left _ _

variable
    (hB : ∀ i j : Fin n, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ X,
        ‖tensorComponentResponse e (tsupport χ) B i j u x‖ ≤
          C * ‖ofTest s volume u.val‖)
include hB

/-- Applying the SAME response after the full cutoff strain equals the
integral of the actual atomic responses. The finite source-norm estimate
belongs to the fixed-inverse producer; the source identity, admission and
integral interchange are proved here (`app:ch_lag:eq:lag-recurrence`). -/
theorem fullPrimaryWave_response_eq_integral
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ X) :
    complexifyResponse B
      (complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v)) x =
      wideSuperposition (fun p : Euclidean n × Euclidean (n - 1) ↦
        fullPrimaryResponse T Q F row col Φ Y χ B τ r
          (z, T.reference.spatialPatch z + τ • p.2) p.1) d v x :=
  fullPrimaryWave_response_eq_integral_on_observation T Q F row col Φ Y r hΩ hspace hphase
    hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc hχ hc e B hB v hx

variable (hresponse : ContDiffOn ℝ ∞
    (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
include hresponse

/-- The manuscript's whole-source corrected wave is the integral of its
SAME corrected atoms, pointwise on the original physical chart
(`app:ch_lag:eq:lag-recurrence`). -/
theorem wholeSourceCorrectedWave_eq_correctedWideWave
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ X) :
    wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v x =
      correctedWideWave T Q F row col Φ Y χ B τ r z (T.reference.spatialPatch z) d v x := by
  rw [correctedWideWave_eq_canonical_sub_responseIntegral T Q F row col Φ Y χ B τ r z
    (T.reference.spatialPatch z) hΩ hspace hphase hF hi hrank hα hnonzero hresponse
    hshift hceil hd hM hb v hx]
  change fullPrimaryWave T Q F row col Φ Y τ r z d v x -
    complexifyResponse B (complexAtomicSource F χ
      (fullPrimaryWave T Q F row col Φ Y τ r z d v)) x = _
  rw [fullPrimaryWave_response_eq_integral T Q F row col Φ Y r hΩ hspace hphase
    hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc hχ hc e B hB v hx]
  rfl

/-- Identifying the two fields on the open chart identifies their actual
physical derivatives and their unchanged carrier demodulator
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem wholeSourceCorrectedDerivative_eq_correctedWideDerivative
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ X) :
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B τ z d v x =
      correctedWideDerivative T Q F row col Φ Y χ B τ r z (T.reference.spatialPatch z) d v x := by
  have he : wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v =ᶠ[𝓝 x]
      correctedWideWave T Q F row col Φ Y χ B τ r z (T.reference.spatialPatch z) d v := by
    filter_upwards [hX.mem_nhds hx] with y hy
    exact wholeSourceCorrectedWave_eq_correctedWideWave T Q F row col Φ Y r hΩ hspace hphase
      hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc hχ hc e B hB hresponse v hy
  unfold wholeSourceCorrectedDerivative correctedWideDerivative
  rw [he.fderiv_eq, phase_on_carrier]

/-- The derivative of the actual whole-source construction has the literal
corrected-atom integral, with the original band count, masks and Lebesgue
measure (`app:ch_waves:eq:individual-representation`). -/
theorem wholeSourceCorrectedDerivative_eq_integral (hτ : τ ≠ 0)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ X) :
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B τ z d v x =
      rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, ξ)))
        (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x := by
  rw [wholeSourceCorrectedDerivative_eq_correctedWideDerivative T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc
    hχ hc e B hB hresponse v hx]
  exact correctedWideDerivative_eq_integral T Q F row col Φ Y χ B τ r z
    (T.reference.spatialPatch z) hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift
    hτ hX hV hceil hd hM hb v hx

end JanetCartan.CanonicalAtomRealization

