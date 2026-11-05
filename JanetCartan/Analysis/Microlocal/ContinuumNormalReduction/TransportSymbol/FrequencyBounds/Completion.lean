module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.HighFrequency
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A fixed smooth low-frequency completion

The completion after `app:ch_background:eq:bg-symbol` uses the fixed scalar
mask `smoothTransition (|k|² - 1)`. Smoothness of the homogeneous amplitude
away from zero is deduced from primitive regularity and a relative conic chart
buffer. No regularity at the vertex of the homogeneous cone is required.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Removing the high cutoff preserves all primitive regularity on the
nonzero input chart (`app:ch_background:eq:bg-symbol`). -/
theorem PrimitiveRegularity.homogeneous {a : Coefficients n N}
    {J : InputVariables n → ℝ} {W : Set (InputVariables n)}
    (h : PrimitiveRegularity a J W) : PrimitiveRegularity (homogeneousCoefficients a) J W :=
  { h with high := contDiff_const }

/-- The homogeneous density is smooth on an open region with a relative
chart buffer. This allows the closure of its support to meet the cone vertex
outside that region. Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem extendedDensity_contDiffOn_of_relative_buffer
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω U : Set (Variables n × Euclidean 2)} {W L : Set (InputVariables n)}
    (hΩ : IsOpen Ω) (h : PrimitiveRegularity a J W) (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ L)
    (hbuffer : closure (F '' L) ∩ U ⊆ Ω) :
    ContDiffOn ℝ ∞ (extendedDensity a J u Ω) U := by
  intro p hp
  by_cases hpΩ : p ∈ Ω
  · have hd := ((inputDensity_contDiffOn h).comp (inverseCoordinates_contDiffOn hu)
        hmap).contDiffAt (hΩ.mem_nhds hpΩ)
    apply (hd.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hΩ.mem_nhds hpΩ] with q hq
    exact indicator_of_mem hq _
  · have hnot : p ∉ tsupport (extendedDensity a J u Ω) := by
      intro hsupport
      exact hpΩ (hbuffer ⟨closure_mono
        (support_extendedDensity_subset a J u F hmap hright hs) hsupport, hp⟩)
    exact (contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hnot)).contDiffWithinAt

/-- Primitive smoothness and the relative conic buffer imply smoothness of
the literal homogeneous spectator integral away from `k = 0`.
Source: `app:ch_background:eq:bg-symbol`. -/
theorem homogeneousAmplitude_contDiffOn_punctured
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {W L : Set (InputVariables n)}
    (hΩ : IsOpen Ω) (h : PrimitiveRegularity a J W) (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ L)
    (hbuffer : closure (F '' L) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    {K : Set (Euclidean 2)} (hK : IsCompact K) :
    ContDiffOn ℝ ∞ (amplitude (homogeneousCoefficients a) J u Ω K)
      {p | p.2.2 ≠ 0} := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply contDiffOn_compactParameterIntegral
    (isOpen_ne_fun continuous_snd.snd continuous_const) isOpen_univ hK (subset_univ K)
  have hd := extendedDensity_contDiffOn_of_relative_buffer
    (homogeneousCoefficients a) J u F hΩ h.homogeneous hu hmap hright
    (fun p hp h₁ h₂ h₃ _ ↦ hs p hp h₁ h₂ h₃) hbuffer
  exact hd.mono (fun p hp ↦ hp.1)

/-- Fixed output-frequency cutoff used to complete the homogeneous amplitude
in `app:ch_background:eq:bg-symbol`. It is independent of `R`. -/
def completionCutoff (k : Euclidean n) : ℝ := Real.smoothTransition (‖k‖ ^ 2 - 1)

/-- The fixed completion cutoff is smooth even at zero.
Source: `app:ch_background:eq:bg-symbol`. -/
theorem completionCutoff_contDiff : ContDiff ℝ ∞ (completionCutoff (n := n)) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.norm_sq ℝ).sub contDiff_const)

/-- The fixed completion vanishes on a whole neighborhood of zero.
Source: `app:ch_background:eq:bg-symbol`. -/
theorem completionCutoff_eq_zero {k : Euclidean n} (hk : ‖k‖ ≤ 1) :
    completionCutoff k = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have := norm_nonneg k
  nlinarith

/-- The completion equals the homogeneous amplitude above a fixed frequency.
Source: `app:ch_background:eq:bg-symbol`. -/
theorem completionCutoff_eq_one {k : Euclidean n} (hk : 2 ≤ ‖k‖) :
    completionCutoff k = 1 := by
  apply Real.smoothTransition.one_of_one_le
  nlinarith

/-- Fixed low-frequency completion of the literal full homogeneous amplitude;
its diagonal completes `d₀` in `app:ch_background:eq:bg-symbol`. -/
def completedAmplitude (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : Variables n) : Matrix (Fin n) (Fin n) ℝ :=
  completionCutoff p.2.2 • amplitude (homogeneousCoefficients a) J u Ω K p

/-- Multiplication by the fixed cutoff completes every punctured smooth
amplitude. The actual input is produced by
`homogeneousAmplitude_contDiffOn_punctured`, from the primitive chart buffer.
Source: `app:ch_background:eq:bg-symbol`. -/
theorem completedAmplitude_contDiff
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hf : ContDiffOn ℝ ∞ (amplitude (homogeneousCoefficients a) J u Ω K)
      {p | p.2.2 ≠ 0}) :
    ContDiff ℝ ∞ (completedAmplitude a J u Ω K) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2.2 = 0
  · apply (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℝ))).congr_of_eventuallyEq
    have hopen : IsOpen {q : Variables n | ‖q.2.2‖ < 1} :=
      isOpen_lt continuous_snd.snd.norm continuous_const
    filter_upwards [hopen.mem_nhds (by simp [hp] : p ∈ {q : Variables n | ‖q.2.2‖ < 1})]
      with q hq
    simp only [completedAmplitude, completionCutoff_eq_zero hq.le, zero_smul]
  · exact ((completionCutoff_contDiff.comp (contDiff_snd.snd)).contDiffAt).smul
      (hf.contDiffAt ((isOpen_ne_fun continuous_snd.snd continuous_const).mem_nhds hp))

/-- The discrepancy with the actual high-cutoff amplitude is zero above a
fixed geometric radius. The regularization parameter is absent.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem amplitude_eq_completed_of_large_frequency
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (p : Variables n) (hp : max 2 (2 * C) ≤ ‖p.2.2‖) :
    amplitude a J u Ω K p = completedAmplitude a J u Ω K p := by
  rw [completedAmplitude, completionCutoff_eq_one ((le_max_left _ _).trans hp), one_smul]
  exact amplitude_eq_homogeneous_of_large_frequency a J u Ω K hhigh hC hcomparison p
    ((le_max_right _ _).trans hp)

/-- The smooth completion discrepancy has bounded frequency support, with
all physical variables and the literal spectator measure retained.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem tsupport_completion_discrepancy_subset
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖) :
    tsupport (fun p ↦ amplitude a J u Ω K p - completedAmplitude a J u Ω K p) ⊆
      {p | ‖p.2.2‖ ≤ max 2 (2 * C)} := by
  apply closure_minimal _ (isClosed_le continuous_snd.snd.norm continuous_const)
  intro p hp
  by_contra h
  exact hp (sub_eq_zero.mpr (amplitude_eq_completed_of_large_frequency
    a J u Ω K hhigh hC hcomparison p (not_le.mp h).le))

/-- Smoothness of the discrepancy follows from `amplitude_contDiff` and
`homogeneousAmplitude_contDiffOn_punctured`; these two actual producers use
primitive regularity and chart buffers, never a symbol bound.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem completion_discrepancy_contDiff
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (ha : ContDiff ℝ ∞ (amplitude a J u Ω K))
    (hh : ContDiffOn ℝ ∞ (amplitude (homogeneousCoefficients a) J u Ω K)
      {p | p.2.2 ≠ 0}) :
    ContDiff ℝ ∞ (fun p ↦ amplitude a J u Ω K p - completedAmplitude a J u Ω K p) :=
  ha.sub (completedAmplitude_contDiff a J u Ω K hh)

/-- Every derivative of the completion discrepancy is supported in the same
fixed frequency ball. Source: the bounded-frequency smoothing term following
`app:ch_background:eq:bg-symbol`. -/
theorem tsupport_iteratedFDeriv_completion_discrepancy_subset
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖) (j : ℕ) :
    tsupport (iteratedFDeriv ℝ j
      (fun p ↦ amplitude a J u Ω K p - completedAmplitude a J u Ω K p)) ⊆
      {p | ‖p.2.2‖ ≤ max 2 (2 * C)} :=
  (tsupport_iteratedFDeriv_subset j).trans
    (tsupport_completion_discrepancy_subset a J u Ω K hhigh hC hcomparison)

/-- Full assembly from primitive data: a smooth fixed completion and a smooth
bounded-frequency discrepancy. `Lhi` is the original high-cutoff support buffer;
`Lhom` is the conic mask buffer, whose closure may meet zero frequency. These
are geometric obligations of the parent construction, not amplitude estimates.
Source: `app:ch_background:eq:bg-symbol` and `app:ch_background:prop:bg-frame`. -/
theorem completedAmplitude_and_discrepancy_of_primitive_inputs
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {W Lhi Lhom : Set (InputVariables n)}
    (hΩ : IsOpen Ω) (h : PrimitiveRegularity a J W) (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hshi : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Lhi)
    (hclosed : IsClosed (F '' Lhi)) (hbufferhi : F '' Lhi ⊆ Ω)
    (hshom : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Lhom)
    (hbufferhom : closure (F '' Lhom) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    {K : Set (Euclidean 2)} (hK : IsCompact K)
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖) :
    ContDiff ℝ ∞ (completedAmplitude a J u Ω K) ∧
    ContDiff ℝ ∞ (fun p ↦ amplitude a J u Ω K p - completedAmplitude a J u Ω K p) ∧
    ∀ j : ℕ, tsupport (iteratedFDeriv ℝ j
      (fun p ↦ amplitude a J u Ω K p - completedAmplitude a J u Ω K p)) ⊆
      {p | ‖p.2.2‖ ≤ max 2 (2 * C)} := by
  have hh := homogeneousAmplitude_contDiffOn_punctured a J u F hΩ h hu hmap hright
    hshom hbufferhom hK
  have ha := amplitude_contDiff a J u F hΩ h hu hmap hright hshi hclosed hbufferhi hK
  exact ⟨completedAmplitude_contDiff a J u Ω K hh,
    completion_discrepancy_contDiff a J u Ω K ha hh,
    tsupport_iteratedFDeriv_completion_discrepancy_subset a J u Ω K hhigh hC hcomparison⟩

end JanetCartan.ContinuumNormalReduction.TransportSymbol
