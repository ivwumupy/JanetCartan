module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Displacement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CanonicalSuperposition

/-!
# The literal corrected atom on the canonical raw input

For `app:ch_mean_pairs:defn:mean-canonical`, integrate the SAME retained
corrected atoms against the original smooth-band Lebesgue density. Differentiate
this integral before identifying its amplitude. The fixed response's joint
regularity is the input of `CorrectedAtoms.JointRegularity`, supplied by the
response producer; neither a raw-to-smooth map nor its representation is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalAtomRealization

open RawPrimary RawInputPartition CorrectedAtoms
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary.AmplitudeGrades.Polynomial

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) (ζ : Euclidean (n - 1))

/-- The canonical corrected displacement on the original `X_K`, with its
half weights and detector/high-pass masks still inside the Lebesgue density
(`app:ch_mean_pairs:defn:mean-canonical`). -/
def correctedWideWave (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  wideSuperposition
    (fun p : Euclidean n × Euclidean (n - 1) ↦
      fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r (z, ζ + τ • p.2) p.1) d v

/-- The actual demodulated PHYSICAL derivative of the constructed corrected
displacement (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
def correctedWideDerivative (d : Euclidean (n - 1) → ℂ) (v : WideInput n J)
    (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ :=
  Complex.exp (-Complex.I * (phase T Q x ζ / τ : ℝ)) •
    RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
      (fderiv ℝ (correctedWideWave T Q F row col Φ Y χ B τ r z ζ d v) x)

/-- The explicit shifted corrected kernel in
`app:ch_waves:eq:individual-representation`. It retains the original phase
and subtracts the derivative of the same fixed response. -/
def correctedWideKernel (p : Euclidean n × Euclidean (n - 1)) :
    Matrix (Fin N) (Fin n) ℂ :=
  Complex.exp (Complex.I *
    (rawPrimaryPhaseDifference (fun x η ↦ phase T Q x η) ζ τ p.1 p.2 : ℝ)) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (p.1, (z, ζ + τ • p.2))

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    {O : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hshift : ∀ p ∈ O ×ˢ V, (p.1, (z, ζ + τ • p.2)) ∈ Ω)

include hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift

/-- Joint smoothness of the literal shifted corrected atom follows from
the retained raw geometry and the SAME response's joint regularity
(`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_shiftedCorrectedAtom :
    ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n - 1) ↦ fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r
        (z, ζ + τ • p.2) p.1) (O ×ˢ V) := by
  have hc := contDiffOn_fullCorrectedPrimaryAtom_joint T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero τ hresponse
  have hm : ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n - 1) ↦ (p.1, (z, ζ + τ • p.2))) (O ×ˢ V) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk
      (contDiffOn_const.add (contDiffOn_snd.const_smul τ)))
  simpa only [Function.comp_def] using hc.comp hm hshift

/-- Finite-band smoothness of the actual corrected displacement is proved
for every Hilbert datum, without differentiating that datum
(`app:ch_waves:thm:individual`, `app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_correctedWideWave (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    ContDiffOn ℝ ∞ (correctedWideWave T Q F row col Φ Y χ B τ r z ζ d v) O :=
  contDiffOn_wideSuperposition hO hV hceil
    (contDiffOn_shiftedCorrectedAtom T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift) hd hM hb v

/-- Separate the actual canonical raw wave from the integral of its SAME
atomic responses (`app:ch_lag:eq:lag-W0-definition`). To identify this with
`app:ch_lag:eq:lag-recurrence`, the fixed-response producer must additionally
justify moving its response through this integral on the admitted source
space. `fullPrimaryWave_response_eq_integral` in `Identification` supplies that
step from the fixed response's existing source-norm bound. -/
theorem correctedWideWave_eq_canonical_sub_responseIntegral
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ O) :
    correctedWideWave T Q F row col Φ Y χ B τ r z ζ d v x =
      canonicalWideWave F τ (fun p ↦ phase T Q p.1 p.2)
        (fun p ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (p.1, (z, p.2))))
        (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (z, p.2))) ζ d v x -
      wideSuperposition (fun p ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r
        (z, ζ + τ • p.2) p.1) d v x := by
  have hm : ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n - 1) ↦ (p.1, (z, ζ + τ • p.2))) (O ×ˢ V) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk
      (contDiffOn_const.add (contDiffOn_snd.const_smul τ)))
  have hw := (contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero).comp hm hshift
  have hrsp := hresponse.comp hm hshift
  have hiraw := integrable_wideSuperposition hceil hw.continuousOn hd hM hb v hx
  have hiresp := integrable_wideSuperposition hceil hrsp.continuousOn hd hM hb v hx
  change (∫ η, weightedWideDensity d v η •
      (fullPrimaryAtom T Q F row col Φ Y τ r z (x, ζ + τ • η) -
        fullPrimaryResponse T Q F row col Φ Y χ B τ r (z, ζ + τ • η) x)) = _
  simp_rw [smul_sub]
  exact integral_sub hiraw hiresp

/-- Differentiating the literal corrected Fourier integral gives its
pointwise demodulated matrix representation, with the original Lebesgue
measure and unchanged smooth-band density
(`app:ch_waves:eq:individual-representation`, `main:eq:canonical-identity`). -/
theorem correctedWideDerivative_eq_integral (hτ : τ ≠ 0)
    (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J)
    {x : Euclidean n} (hx : x ∈ O) :
    correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v x =
      rawPrimaryDemodulatedIntegral (fun y η ↦ phase T Q y η)
        (fun y η ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, η)))
        ζ τ volume (weightedWideDensity d v) x := by
  have ha := contDiffOn_shiftedCorrectedAtom T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift
  have hint := integrable_wideSuperposition hceil
    (contDiffOn_parameterFDeriv hO hV ha).continuousOn hd hM hb v hx
  have hderiv := (hasFDerivAt_wideSuperposition hO hV hceil ha hd hM hb v hx).fderiv
  unfold correctedWideDerivative correctedWideWave
  rw [hderiv, wideSuperposition,
    ← (RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N).integral_comp_comm hint,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  by_cases hη : η ∈ Metric.closedBall 0 ((2 : ℝ) ^ J)
  · have hp := hshift (x, η) ⟨hx, hceil hη⟩
    have hrsp := ((hresponse.contDiffAt (hΩ.mem_nhds hp)).comp x
      (f := fun y : Euclidean n ↦ (y, (z, ζ + τ • η)))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    rw [fullCorrectedDerivativeAmplitude_eq_demodulated T Q F row col Φ Y χ B r
      hΩ hspace hphase hF hi hrank hα hnonzero hτ hp hrsp]
    let D : Matrix (Fin N) (Fin n) ℂ := fun i j ↦ partialDeriv
      (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r (z, ζ + τ • η)) x j i
    change Complex.exp (-Complex.I * (phase T Q x ζ / τ : ℝ)) •
        (weightedWideDensity d v η • D) =
      Complex.exp (Complex.I *
        (rawPrimaryPhaseDifference (fun y ξ ↦ phase T Q y ξ) ζ τ x η : ℝ)) •
        (weightedWideDensity d v η •
          (Complex.exp (-Complex.I * (phase T Q x (ζ + τ • η) / τ : ℝ)) • D))
    have he : Complex.exp (Complex.I *
        (rawPrimaryPhaseDifference (fun y ξ ↦ phase T Q y ξ) ζ τ x η : ℝ)) *
        Complex.exp (-Complex.I * (phase T Q x (ζ + τ • η) / τ : ℝ)) =
        Complex.exp (-Complex.I * (phase T Q x ζ / τ : ℝ)) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [rawPrimaryPhaseDifference, sub_div, Complex.ofReal_sub]
      ring
    simp only [smul_smul]
    congr 1
    rw [← he]
    ring
  · have hη' : (2 : ℝ) ^ J ≤ ‖η‖ := le_of_lt (by simpa using hη)
    rw [wideDensity_eq_zero_of_ceiling_le d v hη']
    simp

/-- The representation is the existing smooth-band superposition of the
explicit corrected kernel, without changing its frequency grouping
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem correctedWideDerivative_eq_superposition (hτ : τ ≠ 0)
    (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J)
    {x : Euclidean n} (hx : x ∈ O) :
    correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v x =
      wideSuperposition (correctedWideKernel T Q F row col Φ Y χ B τ r z ζ) d v x := by
  rw [correctedWideDerivative_eq_integral T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v hx]
  unfold rawPrimaryDemodulatedIntegral wideSuperposition correctedWideKernel
  congr 1
  funext η
  exact smul_comm _ _ _

/-- The corrected Fourier kernel is jointly smooth on the original buffered
product. This uses `CorrectedAtoms` for both actual derivative amplitudes
(`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem contDiffOn_correctedWideKernel (hτ : τ ≠ 0) (hzero : (0 : Euclidean (n - 1)) ∈ V) :
    ContDiffOn ℝ ∞ (correctedWideKernel T Q F row col Φ Y χ B τ r z ζ) (O ×ˢ V) := by
  have ha := contDiffOn_fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hresponse
  have hmap : ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n - 1) ↦ (p.1, (z, ζ + τ • p.2))) (O ×ˢ V) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk
      (contDiffOn_const.add (contDiffOn_snd.const_smul τ)))
  have hs := (contDiffOn_fullPhase T Q hphase).comp hmap hshift
  have hs₀ : ContDiffOn ℝ ∞ (fun p : Euclidean n × Euclidean (n - 1) ↦ phase T Q p.1 ζ)
      (O ×ˢ V) := by
    apply (contDiffOn_fullPhase T Q hphase).comp
      (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_const))
    intro p hp
    simpa only [smul_zero, add_zero] using hshift (p.1, 0) ⟨hp.1, hzero⟩
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((hs.sub hs₀).div_const τ))).cexp).smul (ha.comp hmap hshift)

/-- Every finite-band corrected derivative is smooth for arbitrary raw
Hilbert data. Domination and all derivative interchanges come from compact
frequency support, rather than an assumed smooth output
(`app:ch_mean_pairs:eq:mean-current-raw`). -/
theorem contDiffOn_correctedWideDerivative (hτ : τ ≠ 0)
    (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    ContDiffOn ℝ ∞ (correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v) O := by
  have hzero : (0 : Euclidean (n - 1)) ∈ V :=
    hceil (Metric.mem_closedBall_self (by positivity))
  apply (contDiffOn_wideSuperposition hO hV hceil
    (contDiffOn_correctedWideKernel T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hzero) hd hM hb v).congr
  intro x hx
  exact correctedWideDerivative_eq_superposition T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v hx

/-- Additivity is pointwise for the physical derivative, although raw `L²`
representatives are additive only almost everywhere
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem correctedWideDerivative_add (hτ : τ ≠ 0)
    (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v w : WideInput n J)
    {x : Euclidean n} (hx : x ∈ O) :
    correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d (v + w) x =
      correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v x +
        correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d w x := by
  have he (u : WideInput n J) := correctedWideDerivative_eq_superposition
    T Q F row col Φ Y χ B τ r z ζ hΩ hspace hphase hF hi hrank hα hnonzero
    hresponse hshift hτ hO hV hceil hd hM hb u hx
  rw [he, he, he]
  exact wideSuperposition_add hceil
    (contDiffOn_correctedWideKernel T Q F row col Φ Y χ B τ r z ζ hΩ hspace hphase
      hF hi hrank hα hnonzero hresponse hshift hτ
      (hceil (Metric.mem_closedBall_self (by positivity)))).continuousOn hd hM hb v w hx

/-- The original complex quadratures give real homogeneity on the raw
Hilbert space used by the canonical adjoint
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem correctedWideDerivative_real_smul (hτ : τ ≠ 0)
    (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (a : ℝ) (v : WideInput n J) {x : Euclidean n} (hx : x ∈ O) :
    correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d (a • v) x =
      a • correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v x := by
  have he (u : WideInput n J) := correctedWideDerivative_eq_superposition
    T Q F row col Φ Y χ B τ r z ζ hΩ hspace hphase hF hi hrank hα hnonzero
    hresponse hshift hτ hO hV hceil hd hM hb u hx
  rw [he, he]
  have hscale (E : Type) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
      [IsScalarTower ℝ ℂ E] (u : E) : (a : ℂ) • u = a • u :=
    IsScalarTower.algebraMap_smul ℂ a u
  simpa only [hscale] using
    wideSuperposition_smul (correctedWideKernel T Q F row col Φ Y χ B τ r z ζ) hd hb (a : ℂ) v x

/-- The same corrected field also has the shared `RawInputRealization`
annular formula, using its EXISTING isometric two-shell refinement. The
original smooth bands and their quadratures are still grouped together
(`app:ch_waves:eq:B-bounds`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem correctedWideDerivative_eq_refinedIntegral (hτ : τ ≠ 0)
    (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J)
    {x : Euclidean n} (hx : x ∈ O) :
    correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v x =
      rawPrimaryDemodulatedIntegral (fun y η ↦ phase T Q y η)
        (fun y η ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, η)))
        ζ τ volume (RawInputRealization.density
          (fun i : RefinedIndex J ↦ weightedRadialBand d i.1.val) (wideRefinement n J v)) x := by
  rw [correctedWideDerivative_eq_integral T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v hx]
  apply integral_congr_ae
  filter_upwards [weightedWideDensity_eq_refined hd hM hb v] with η hη
  rw [hη]

/-- The quantitative amplitude profiles bound the constructed derivative
with the original `K^(n/2)` Fourier cost and no band-count factor.
The raw and response profile producers supply `hraw` and `hresp` for their
literal amplitudes; no bound on the desired map is assumed
(`app:ch_waves:eq:raw-physical-bound`, `app:ch_response:cor:current-atoms`). -/
theorem norm_correctedWideDerivative_rounded_le (hτ : τ ≠ 0)
    (hO : IsOpen O) (hV : IsOpen V) (hn : 1 ≤ n) {K : ℝ} (hK : 1 ≤ K)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ cutoffCount K) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    {Craw Cresp : ℝ} (hraw₀ : 0 ≤ Craw) (hresp₀ : 0 ≤ Cresp)
    (v : WideInput n (cutoffCount K)) {x : Euclidean n} (hx : x ∈ O)
    (hraw : ∀ η ∈ Metric.closedBall 0 (4 * K),
      ‖fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, ζ + τ • η))‖ ≤ Craw)
    (hresp : ∀ η ∈ Metric.closedBall 0 (4 * K),
      ‖fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ
        (x, (z, ζ + τ • η))‖ ≤ Cresp) :
    ‖correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v x‖ ≤
      ((Craw + Cresp) * (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2))) *
        K ^ ((n : ℝ) / 2) * ‖v‖ := by
  rw [correctedWideDerivative_eq_superposition T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v hx]
  apply norm_wideSuperposition_rounded_le hn hK _ hd hM hb (add_nonneg hraw₀ hresp₀)
  intro η hη
  simp only [correctedWideKernel, norm_smul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hraw η hη) (hresp η hη))

end JanetCartan.CanonicalAtomRealization
