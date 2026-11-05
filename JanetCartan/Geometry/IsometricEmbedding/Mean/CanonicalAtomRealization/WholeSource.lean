module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SourceIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SmoothMap

/-!
# The canonical map with the response after the whole source

Construct the literal order of operations in `app:ch_lag:eq:lag-recurrence`:
Fourier synthesis, complete cutoff strain, then the SAME fixed response. Source
admission is proved in `SourceIntegral`. The original ambient response's reduced
solver regularity supplies smoothness for every such source. The construction
is independent of the response-integral interchange, proved in `Identification`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CanonicalAtomRealization

open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open CurrentMean AmplitudeBound

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (χ : Euclidean n → ℝ)

/-- The manuscript's corrected field: apply the fixed response only AFTER
synthesizing the complete raw wave and its full cutoff strain
(`app:ch_lag:eq:lag-recurrence`). -/
def wholeSourceCorrectedWave
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (τ : ℝ) (z : Euclidean 3) (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  complexCorrectedAtom F χ B (fullPrimaryWave T Q F row col Φ Y τ r z d v)

/-- The literal demodulated physical derivative of the whole-source
corrected field (`app:ch_mean_pairs:defn:mean-canonical`). -/
def wholeSourceCorrectedDerivative
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (τ : ℝ) (z : Euclidean 3) (d : Euclidean (n - 1) → ℂ) (v : WideInput n J)
    (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ :=
  Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
    RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
      (fderiv ℝ (wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v) x)

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
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
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ ξ, ‖d ξ‖ ≤ M)
    (hsrc : tsupport χ ⊆ X)

/-- The whole-source response is linear on the original raw Hilbert space.
This uses the proved source map, without moving the response inside any
integral (`app:ch_lag:eq:lag-recurrence`). -/
def wholeSourceResponseLinearMap
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) :
    WideInput n J →ₗ[ℝ] (Euclidean n → EuclideanSpace ℂ (Fin N)) :=
  ((complexifyResponse B).comp
    (fullPrimaryWave_sourceLinearMap T Q F row col Φ Y r hΩ hspace hphase hF hi hrank hα hnonzero
      τ z hshift hX hV hceil hd hM hb χ hsrc)).restrictScalars ℝ

/-- Restrict the original raw wave to its validity chart and subtract the
whole-source response. These are the SAME physical values, including at
zero raw input (`app:ch_mean_pairs:defn:mean-canonical`). -/
def wholeSourceCorrectedWaveLinearMap
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) :
    WideInput n J →ₗ[ℝ] (X → EuclideanSpace ℂ (Fin N)) := by
  let W : WideInput n J →ₗ[ℝ] (X → EuclideanSpace ℂ (Fin N)) :=
    { toFun v x := fullPrimaryWave T Q F row col Φ Y τ r z d v x
      map_add' v w := by
        funext x
        exact fullPrimaryWave_add T Q F row col Φ Y r hΩ hspace hphase hF hi hrank hα hnonzero
          τ z hshift hceil hd hM hb v w x.property
      map_smul' a v := by
        funext x
        have hscale (E : Type) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
            [IsScalarTower ℝ ℂ E] (u : E) : (a : ℂ) • u = a • u :=
          IsScalarTower.algebraMap_smul ℂ a u
        simpa only [hscale, Pi.smul_apply, RingHom.id_apply] using
          fullPrimaryWave_smul T Q F row col Φ Y r τ z hd hb (a : ℂ) v x }
  let res : (Euclidean n → EuclideanSpace ℂ (Fin N)) →ₗ[ℝ] (X → EuclideanSpace ℂ (Fin N)) :=
    { toFun f x := f x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact W - res.comp (wholeSourceResponseLinearMap T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc B)

/-- The linear map retains exactly the full corrected field on its physical
chart (`app:ch_lag:eq:lag-recurrence`). -/
@[simp] theorem wholeSourceCorrectedWaveLinearMap_apply
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (v : WideInput n J) (x : X) :
    wholeSourceCorrectedWaveLinearMap T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc B v x =
      wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v x := rfl

variable (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
    (η : Euclidean n → ℝ)
    (Tresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Fin n → ℝ))
    (Sresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hS : ∀ h : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
      DifferentiableAt ℝ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) x)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (hSsmooth : ∀ h : compactSmoothSources (tsupport χ),
      ContDiffOn ℝ ∞ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) chart)

local notation "B₀" => ambientExtension F (Subtype.val Q) η Tresp Sresp
  (compactSmoothSources (tsupport χ)) Ξ hS

include hΩ hspace hphase hF hi hrank hα hnonzero hshift hX hV hceil hd hM hb hsrc
  hχ hc hchart hchartU hSsmooth

/-- The actual ambient response to the WHOLE canonical source is smooth
by source admission and the SAME reduced solver's chart regularity.
This applies the existing ambient producer to arbitrary Hilbert data
(`app:ch_response:prop:response-ambient`, `app:ch_lag:eq:lag-recurrence`). -/
theorem contDiff_wholeSourceResponse (v : WideInput n J) :
    ContDiff ℝ ∞ (complexifyResponse B₀
      (complexAtomicSource F χ (fullPrimaryWave T Q F row col Φ Y τ r z d v))) := by
  obtain ⟨hr, him⟩ := fullPrimaryWave_source_quadratures_mem T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc hχ hc v
  exact contDiff_complexify_ambientExtension F Q.1 η Tresp Sresp
    (compactSmoothSources (tsupport χ)) Ξ hS _ hr him hchart (hF.mono hchartU)
    hr.1.contDiffOn him.1.contDiffOn (fun x hx ↦ hi x (hchartU hx))
    (fun x hx ↦ hrank x (hchartU hx)) (hSsmooth ⟨_, hr⟩) (hSsmooth ⟨_, him⟩)

/-- Finite-band smoothness of the manuscript's actual corrected field,
with the response applied after the complete superposition
(`app:ch_lag:eq:lag-recurrence`). -/
theorem contDiffOn_wholeSourceCorrectedWave (v : WideInput n J) :
    ContDiffOn ℝ ∞ (wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d v) X := by
  have hraw := contDiffOn_fullPrimaryWave T Q F row col Φ Y r hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb v
  have hresp := contDiff_wholeSourceResponse T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
    hchart hchartU hSsmooth v
  exact hraw.sub hresp.contDiffOn

/-- Smoothness of the literal demodulated derivative follows by physical
differentiation of the actual whole-source corrected field
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem contDiffOn_wholeSourceCorrectedDerivative (v : WideInput n J) :
    ContDiffOn ℝ ∞ (wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v) X := by
  have hraw := contDiffOn_wholeSourceCorrectedWave T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
    hchart hchartU hSsmooth v
  have hzero : (0 : Euclidean (n - 1)) ∈ V :=
    hceil (Metric.mem_closedBall_self (by positivity))
  have hp : ContDiffOn ℝ ∞ (fun x ↦ T.carrier Q x z) X := by
    have hm : ContDiffOn ℝ ∞
        (fun x : Euclidean n ↦ (x, (z, T.reference.spatialPatch z))) X :=
      contDiffOn_id.prodMk contDiffOn_const
    have hs : ∀ x ∈ X, (x, (z, T.reference.spatialPatch z)) ∈ Ω := by
      intro x hx
      simpa only [smul_zero, add_zero] using hshift (x, 0) ⟨hx, hzero⟩
    simpa only [Function.comp_def, fullPrimaryPhase_on_carrier] using
      (contDiffOn_fullPhase T Q hphase).comp hm hs
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (hp.div_const τ))).cexp).smul
    ((RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N).contDiff.comp_contDiffOn
      (hraw.fderiv_of_isOpen hX (m := ∞) (by simp)))

/-- Local physical differentiation of the already constructed whole-source
map preserves real linearity (`app:ch_mean_pairs:defn:mean-canonical`). -/
private def wholeSourceDerivativeAt (x : X) :
    WideInput n J →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ := by
  let W := wholeSourceCorrectedWaveLinearMap T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc B₀
  have hW (v : WideInput n J) :
      DifferentiableAt ℝ (wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d v) x :=
    ((contDiffOn_wholeSourceCorrectedWave T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth v).contDiffAt (hX.mem_nhds x.property)).differentiableAt (by simp)
  refine
    { toFun v := wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v x
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    have he : wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d (v + w) =ᶠ[𝓝 x.val]
        wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d v +
          wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d w := by
      filter_upwards [hX.mem_nhds x.property] with y hy
      exact congrFun (W.map_add v w) ⟨y, hy⟩
    unfold wholeSourceCorrectedDerivative
    rw [he.fderiv_eq, fderiv_add (hW v) (hW w), map_add, smul_add]
  · intro a v
    have he : wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d (a • v) =ᶠ[𝓝 x.val]
        a • wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d v := by
      filter_upwards [hX.mem_nhds x.property] with y hy
      exact congrFun (W.map_smul a v) ⟨y, hy⟩
    unfold wholeSourceCorrectedDerivative
    rw [he.fderiv_eq, fderiv_const_smul (hW v) a, map_smul]
    exact smul_comm _ _ _

variable (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : tsupport ψ ⊆ X)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)

include hψ hψX hcell hbox

/-- The supplied slice cutoff and existing periodization extend the SAME
whole-source corrected derivative smoothly to the torus. Finite-band
regularity holds for arbitrary raw Hilbert data
(`app:ch_mean_pairs:eq:mean-current-raw`). -/
theorem isSmoothPeriodic_cutWholeSourceCorrectedDerivative (v : WideInput n J) :
    IsSmoothPeriodic (fun x ↦ ψ (centeredTorusRepresentative x) •
      wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v (centeredTorusRepresentative x)) := by
  have hD := contDiffOn_wholeSourceCorrectedDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
    hchart hchartU hSsmooth v
  have hh := preparationMatrixExtension_regular ψ hψ hX hψX hcell hbox
    (fun p ↦ wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v p.1)
    (hD.comp contDiffOn_fst (fun _ hp ↦ hp.1))
  exact ⟨hh.1.comp (continuous_id.prodMk (continuous_const (y := 0))),
    hh.2.comp (contDiff_id.prodMk (contDiff_const (c := 0)))⟩

/-- The canonical raw-to-smooth map constructed with the manuscript's
actual order: complete raw source, then the fixed ambient response. It uses
the original Hilbert input and the original carrier. The relation to the
atomwise integral is not assumed in this construction
(`app:ch_mean_pairs:defn:mean-canonical`). -/
def smoothWholeSourceCanonicalDerivative :
    WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) where
  toFun v := ⟨fun x _ ↦ ψ (centeredTorusRepresentative x) •
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v (centeredTorusRepresentative x),
    fun _ ↦ isSmoothPeriodic_cutWholeSourceCorrectedDerivative T Q F row col Φ Y r χ
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
      hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox v⟩
  map_add' v w := by
    apply Subtype.ext
    funext x u
    by_cases hx : centeredTorusRepresentative x ∈ tsupport ψ
    · let D := wholeSourceDerivativeAt T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
        hchart hchartU hSsmooth ⟨centeredTorusRepresentative x, hψX hx⟩
      change ψ _ • D (v + w) = ψ _ • D v + ψ _ • D w
      rw [map_add, smul_add]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  map_smul' a v := by
    apply Subtype.ext
    funext x u
    by_cases hx : centeredTorusRepresentative x ∈ tsupport ψ
    · let D := wholeSourceDerivativeAt T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
        hchart hchartU hSsmooth ⟨centeredTorusRepresentative x, hψX hx⟩
      change ψ _ • D (a • v) = a • (ψ _ • D v)
      rw [map_smul]
      exact smul_comm _ _ _
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Evaluation retains the literal physical derivative of the whole-source
corrected wave (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
@[simp] theorem smoothWholeSourceCanonicalDerivative_apply (v : WideInput n J) (x : Torus n) :
    (smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox v).val x () =
      ψ (centeredTorusRepresentative x) •
        wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v (centeredTorusRepresentative x) := rfl

/-- On the measurement plateau the constructed map is precisely the
uncut demodulated derivative of `W₀ - B(χ Dγ W₀)`, with the fixed response
applied to the WHOLE source (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem smoothWholeSourceCanonicalDerivative_eq_physical (v : WideInput n J) (x : Torus n)
    (hx : ψ (centeredTorusRepresentative x) = 1) :
    (smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox v).val x () =
      Complex.exp (-Complex.I * (T.carrier Q (centeredTorusRepresentative x) z / τ : ℝ)) •
        RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
          (fderiv ℝ (complexCorrectedAtom F χ B₀ (fullPrimaryWave T Q F row col Φ Y τ r z d v))
            (centeredTorusRepresentative x)) := by
  rw [smoothWholeSourceCanonicalDerivative_apply, hx, one_smul]
  rfl

/-- The original real raw adjoint and `Q₀` feed the literal whole-source
corrected field in the existing canonical constructor. No new inverse,
raw space, or sample normalization is selected
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem smoothCanonicalDerivative_wholeSource_eq_physical
    (A : WideInput n J →L[ℝ] ContinuumRow.OutputL2 n)
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : ContinuumRow.OutputL2 n) (x : Torus n)
    (hx : ψ (centeredTorusRepresentative x) = 1) :
    (CanonicalChange.smoothCanonicalDerivative (fun _ : Unit ↦ A)
      (fun _ ↦ smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
        hchart hchartU hSsmooth ψ hψ hψX hcell hbox) Q₀ e).val x () =
      Complex.exp (-Complex.I * (T.carrier Q (centeredTorusRepresentative x) z / τ : ℝ)) •
        RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
          (fderiv ℝ (complexCorrectedAtom F χ B₀
            (fullPrimaryWave T Q F row col Φ Y τ r z d (A.adjoint (Q₀ e))))
            (centeredTorusRepresentative x)) :=
  smoothWholeSourceCanonicalDerivative_eq_physical T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
    hchart hchartU hSsmooth ψ hψ hψX hcell hbox (A.adjoint (Q₀ e)) x hx

/-- The measured cross term uses the constructed whole-source derivative
and the supplied original background. This is the literal component used
by `CanonicalChange.smoothCanonicalResponse_eq_measured_cross`
(`main:eq:canonical-identity`). -/
theorem wholeSourceSmoothCrossResponse_eq_physical
    (base : SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (v : WideInput n J) (x : Torus n) (hx : ψ (centeredTorusRepresentative x) = 1) :
    (CanonicalChange.smoothRawCrossResponse base C hC
      (fun _ : Unit ↦ smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
        hchart hchartU hSsmooth ψ hψ hψX hcell hbox) () v).val x () =
      C x ((2 : ℝ) • mixedHermitianTensor (base.val x ())
        (Complex.exp (-Complex.I * (T.carrier Q (centeredTorusRepresentative x) z / τ : ℝ)) •
          RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
            (fderiv ℝ (complexCorrectedAtom F χ B₀ (fullPrimaryWave T Q F row col Φ Y τ r z d v))
              (centeredTorusRepresentative x)))) := by
  rw [CanonicalChange.smoothRawCrossResponse_apply,
    smoothWholeSourceCanonicalDerivative_eq_physical T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox v x hx]

end JanetCartan.CanonicalAtomRealization
