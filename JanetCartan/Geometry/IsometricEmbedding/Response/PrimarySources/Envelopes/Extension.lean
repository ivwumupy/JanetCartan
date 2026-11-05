module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Frobenius
public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic

/-!
# A compact extension of the complete primary strain amplitude

For `app:ch_response:cor:current-atoms`, use the existing cutoff extension on
the literal `fullPrimaryStrainAmplitude`. The same cutoff is fixed before the
scalar, frequency and carrier. Agreement holds on a neighborhood of the entire
source support, so all spatial jets are preserved. Remodulation gives the full
linearized metric, without replacing it by a projected or principal strain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponsePrimarySources
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSourceExtension ResponseTransfer SourceNegative

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart)

/-- One fixed cutoff extension of the complete demodulated primary strain.
This is the envelope used in `app:ch_response:cor:current-atoms`. -/
def fullStrainEnvelope (τ : ℝ) (c : Euclidean 3 × Euclidean (n - 1)) :
    Euclidean n → Matrix (Fin n) (Fin n) ℂ :=
  χ.zeroExtend (fun x : chart ↦ fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x, c))

/-- The extension is literal cutoff multiplication; it retains every cubic
residual term (`app:ch_response:eq:response-graded-source`). -/
theorem fullStrainEnvelope_eq (τ : ℝ) (c : Euclidean 3 × Euclidean (n - 1)) :
    fullStrainEnvelope T Q F row col Φ Y r χ τ c =
      fun x ↦ χ.toFun x • fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x, c) :=
  χ.zeroExtend_restrict (fun x ↦ fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x, c))

/-- A fixed compact support works for all scalars, frequencies and carrier
labels (`app:ch_response:eq:response-graded-source`). -/
theorem tsupport_fullStrainEnvelope_subset (τ : ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) :
    tsupport (fullStrainEnvelope T Q F row col Φ Y r χ τ c) ⊆ tsupport χ.toFun :=
  χ.tsupport_zeroExtend_subset _

/-- Compactness of the same envelope, before any quantitative estimate
(`app:ch_response:eq:response-graded-source`). -/
theorem hasCompactSupport_fullStrainEnvelope (τ : ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) :
    HasCompactSupport (fullStrainEnvelope T Q F row col Φ Y r χ τ c) :=
  χ.hasCompactSupport_zeroExtend _

/-- The extension agrees with the entire amplitude near each source point,
preserving all local derivatives (`app:ch_response:cor:current-atoms`). -/
theorem fullStrainEnvelope_eventuallyEq (τ : ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) {x : Euclidean n} (hx : x ∈ core) :
    fullStrainEnvelope T Q F row col Φ Y r χ τ c =ᶠ[𝓝 x]
      fun y ↦ fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (y, c) :=
  χ.zeroExtend_eventuallyEq
    (fun y ↦ fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (y, c)) hx

/-- All spatial jets on the source core are those of the complete original
amplitude (`app:ch_response:cor:current-atoms`). -/
theorem iteratedFDeriv_fullStrainEnvelope_eq (τ : ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) (j : ℕ)
    {x : Euclidean n} (hx : x ∈ core) :
    iteratedFDeriv ℝ j (fullStrainEnvelope T Q F row col Φ Y r χ τ c) x =
      iteratedFDeriv ℝ j
        (fun y ↦ fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (y, c)) x :=
  ((fullStrainEnvelope_eventuallyEq T Q F row col Φ Y r χ τ c hx).iteratedFDeriv ℝ j).self_of_nhds

omit χ in
/-- Remodulation is exactly the full original strain, with the physical
frequency `τ⁻¹` (`app:ch_response:cor:current-atoms`). -/
theorem carrier_smul_fullPrimaryStrainAmplitude (τ : ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) (x : Euclidean n) :
    carrier τ⁻¹ (fun y ↦ phase T Q y c.2) x •
        fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x, c) =
      WKB.complexLinearizedMetric F
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2)) x := by
  simp only [fullPrimaryStrainAmplitude, carrier, smul_smul, ← Complex.exp_add,
    Complex.ofReal_mul, Complex.ofReal_inv]
  have he : Complex.I * ((τ : ℂ)⁻¹ * (phase T Q x c.2 : ℂ)) +
      -Complex.I * (phase T Q x c.2 : ℂ) / (τ : ℂ) = 0 := by ring
  rw [he, Complex.exp_zero, one_smul]

/-- The cutoff full strain is the literal modulated source on its entire
original support (`app:ch_response:eq:response-graded-source`). -/
theorem cutoff_fullPrimaryStrain_eq_modulatedSource
    (χsrc : Euclidean n → ℝ) (hs : tsupport χsrc ⊆ core)
    (τ : ℝ) (c : Euclidean 3 × Euclidean (n - 1)) :
    (fun x ↦ χsrc x • WKB.complexLinearizedMetric F
      (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2)) x) =
      modulatedSource χsrc (fun y ↦ phase T Q y c.2)
        (fullStrainEnvelope T Q F row col Φ Y r χ τ c) τ⁻¹ := by
  funext x
  by_cases hx : χsrc x = 0
  · simp [modulatedSource, hx]
  · have he := (fullStrainEnvelope_eventuallyEq T Q F row col Φ Y r χ τ c
      (hs (subset_tsupport χsrc hx))).self_of_nhds
    simp only [modulatedSource, he,
      carrier_smul_fullPrimaryStrainAmplitude T Q F row col Φ Y r τ c x]

/-- A globally extended phase gives the same source whenever it preserves
the actual phase on the full source support. The phase construction must prove
this agreement (`app:ch_response:thm:response-literal-transfer`). -/
theorem cutoff_fullPrimaryStrain_eq_modulatedSource_of_phase_eq
    (χsrc φ : Euclidean n → ℝ) (hs : tsupport χsrc ⊆ core)
    (τ : ℝ) (c : Euclidean 3 × Euclidean (n - 1))
    (hφ : EqOn φ (fun y ↦ phase T Q y c.2) (tsupport χsrc)) :
    (fun x ↦ χsrc x • WKB.complexLinearizedMetric F
      (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2)) x) =
      modulatedSource χsrc φ (fullStrainEnvelope T Q F row col Φ Y r χ τ c) τ⁻¹ := by
  rw [cutoff_fullPrimaryStrain_eq_modulatedSource T Q F row col Φ Y r χ χsrc hs τ c]
  funext x
  by_cases hx : χsrc x = 0
  · simp [modulatedSource, hx]
  · simp only [modulatedSource, carrier, hφ (subset_tsupport χsrc hx)]

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω,
      nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)

include hΩ hspace hphase hF hi hrank hα hnonzero

/-- Smoothness of the actual compact strain envelope follows from the
retained leading outputs, with no assumed envelope regularity
(`app:ch_response:eq:response-graded-source`). -/
theorem contDiff_fullStrainEnvelope (hchart : IsOpen chart) (τ : ℝ)
    (c : Euclidean 3 × Euclidean (n - 1))
    (hmap : MapsTo (fun x ↦ (x, c)) chart Ω) :
    ContDiff ℝ ∞ (fullStrainEnvelope T Q F row col Φ Y r χ τ c) :=
  χ.contDiff_zeroExtend_restrict hchart
    ((contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F row col Φ Y r τ
      hΩ hspace hphase hF hi hrank hα hnonzero).comp
        (contDiffOn_id.prodMk contDiffOn_const) hmap)

/-- Actual Lebesgue L² membership of the same Frobenius tensor envelope,
derived from its proved smoothness and fixed compact support
(`app:ch_response:eq:response-graded-source`). -/
theorem memLp_fullStrainEnvelope (hchart : IsOpen chart) (τ : ℝ)
    (c : Euclidean 3 × Euclidean (n - 1))
    (hmap : MapsTo (fun x ↦ (x, c)) chart Ω) :
    MemLp (fullStrainEnvelope T Q F row col Φ Y r χ τ c) 2 volume :=
  (contDiff_fullStrainEnvelope T Q F row col Φ Y r χ
    hΩ hspace hphase hF hi hrank hα hnonzero hchart τ c hmap).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_fullStrainEnvelope T Q F row col Φ Y r χ τ c)

end JanetCartan.ResponsePrimarySources
