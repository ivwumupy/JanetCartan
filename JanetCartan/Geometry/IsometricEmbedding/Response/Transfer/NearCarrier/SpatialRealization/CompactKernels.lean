module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ForwardRegularized.Admissibility
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.CompactIntegral

/-!
# Compact kernels for spatial transfer

The analytic inputs to the spatial derivative step in
`app:ch_response:eq:direct-envelope-profile` follow from joint smoothness and
compact carriers. The amplitude is the full selected matrix amplitude, including
both physical masks. These lemmas are consumed by the forward and reverse
regularization constructors; no bound on a graph derivative is an input.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral
variable {n r : ℕ}

/-- The complete oscillatory matrix kernel, in output × (frequency × source)
order, for `app:ch_response:eq:direct-envelope-profile`. -/
def amplitudeKernel (Ω : (Euclidean n) → (Euclidean n) → (Euclidean n) → ℂ) (A : FullAmplitude n r)
    (u : (Euclidean n) → (Fin r → ℂ)) (x : (Euclidean n)) (p : (Euclidean n) × (Euclidean n)) : (Fin r → ℂ) :=
  Ω x p.2 p.1 • (A x p.2 p.1).mulVec (u p.2)

variable {X Y F : Set (Euclidean n)} {Ω : (Euclidean n) → (Euclidean n) → (Euclidean n) → ℂ} {A : FullAmplitude n r} {u : (Euclidean n) → (Fin r → ℂ)}

/-- Joint kernel smoothness for the compact integral used in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem smooth_amplitudeKernel
    (hΩ : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ Ω p.1 p.2.1 p.2.2))
    (hA : ForwardAmplitudeAdmissible X Y F A) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ amplitudeKernel Ω A u p.1 p.2) := by
  have hperm : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ (p.1, p.2.2, p.2.1)) :=
    contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)
  exact (hΩ.comp hperm).smul
    ((ReverseDerivative.matrixAction.contDiff.comp (hA.smooth.comp hperm)).clm_apply
      (hu.comp contDiff_snd.snd))

/-- The full kernel vanishes off the original source/frequency carriers.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem amplitudeKernel_eq_zero_off_carrier (hA : ForwardAmplitudeAdmissible X Y F A)
    (x : (Euclidean n)) (p : (Euclidean n) × (Euclidean n)) (hp : p ∉ F ×ˢ Y) : amplitudeKernel Ω A u x p = 0 := by
  have h : p.2 ∉ Y ∨ p.1 ∉ F := by tauto
  simp [amplitudeKernel, hA.support x p.2 p.1 (Or.inr h)]

/-- Compact carriers give absolute integrability of the literal product kernel
in `app:ch_response:eq:direct-envelope-profile`. -/
theorem integrable_amplitudeKernel
    (hΩ : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ Ω p.1 p.2.1 p.2.2))
    (hA : ForwardAmplitudeAdmissible X Y F A) (hY : IsCompact Y) (hF : IsCompact F)
    (hu : ContDiff ℝ ∞ u) (x : (Euclidean n)) :
    Integrable (amplitudeKernel Ω A u x) (volume.prod volume) :=
  GraphDifferentiation.integrable_section (U := univ) (hF.prod hY)
    (smooth_amplitudeKernel hΩ hA hu).continuous.continuousOn
    (fun z _ p hp ↦ amplitudeKernel_eq_zero_off_carrier hA z p hp) (mem_univ x)

/-- Every source/frequency section of the actual output derivative is
integrable; this discharges the derivative-integrability field of both spatial
regularizations (`app:ch_response:eq:direct-envelope-profile`). -/
theorem integrable_amplitudeKernel_fderiv
    (hΩ : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ Ω p.1 p.2.1 p.2.2))
    (hA : ForwardAmplitudeAdmissible X Y F A) (hY : IsCompact Y) (hF : IsCompact F)
    (hu : ContDiff ℝ ∞ u) (x : (Euclidean n)) :
    Integrable (fun p ↦ fderiv ℝ (fun z ↦ amplitudeKernel Ω A u z p) x)
      (volume.prod volume) := by
  apply GraphDifferentiation.integrable_section (U := univ) (hF.prod hY)
    (contDiffOn_parameterFDeriv isOpen_univ isOpen_univ
      (smooth_amplitudeKernel hΩ hA hu).contDiffOn).continuousOn
    _ (mem_univ x)
  intro z hz p hp
  exact GraphDifferentiation.fderiv_section_eq_zero
    (f := fun p ↦ amplitudeKernel Ω A u p.1 p.2) isOpen_univ
    (fun w _ q hq ↦ amplitudeKernel_eq_zero_off_carrier hA w q hq) hz hp

/-- Compactness supplies a local integrable majorant for the actual kernel
Fréchet derivatives. No domination hypothesis remains in this result.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem locally_dominated_amplitudeKernel_fderiv
    (hΩ : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ Ω p.1 p.2.1 p.2.2))
    (hA : ForwardAmplitudeAdmissible X Y F A) (hY : IsCompact Y) (hF : IsCompact F)
    (hu : ContDiff ℝ ∞ u) (x : (Euclidean n)) :
    ∃ s ∈ 𝓝 x, ∃ bound : (Euclidean n) × (Euclidean n) → ℝ, Integrable bound (volume.prod volume) ∧
      ∀ᵐ p ∂(volume.prod volume), ∀ z ∈ s,
        ‖fderiv ℝ (fun w ↦ amplitudeKernel Ω A u w p) z‖ ≤ bound p := by
  classical
  obtain ⟨a, ha, _, C, hC⟩ := exists_bound_parameterFDeriv
    (U := (univ : Set (Euclidean n))) isOpen_univ isOpen_univ (hF.prod hY) (subset_univ _)
    (smooth_amplitudeKernel hΩ hA hu).contDiffOn (mem_univ x)
  refine ⟨Metric.ball x a, Metric.ball_mem_nhds x ha,
    (F ×ˢ Y).indicator (fun _ ↦ C), ?_, Filter.Eventually.of_forall ?_⟩
  · exact (integrable_indicator_iff (hF.prod hY).measurableSet).mpr
      (integrableOn_const (μ := volume.prod volume) (C := C)
        ((hF.prod hY).measure_lt_top (μ := volume.prod volume)).ne)
  · intro p z hz
    by_cases hp : p ∈ F ×ˢ Y
    · simpa only [indicator_of_mem hp] using hC z (Metric.ball_subset_closedBall hz) p hp
    · rw [indicator_of_notMem hp]
      have he : (fun w ↦ amplitudeKernel Ω A u w p) = fun _ ↦ 0 :=
        funext fun w ↦ amplitudeKernel_eq_zero_off_carrier hA w p hp
      simp [he]

/-- The actual iterated kernel integral is smooth. Compact supports discharge
all Fubini and differentiation hypotheses in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem smooth_amplitudeIntegral
    (hΩ : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ Ω p.1 p.2.1 p.2.2))
    (hA : ForwardAmplitudeAdmissible X Y F A) (hY : IsCompact Y) (hF : IsCompact F)
    (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x ↦ ∫ δ, ∫ y, Ω x y δ • (A x y δ).mulVec (u y)) := by
  let μ : Measure ((Euclidean n) × (Euclidean n)) := volume.prod volume
  let : IsFiniteMeasure (μ.restrict (F ×ˢ Y)) :=
    isFiniteMeasure_restrict.mpr (hF.prod hY).measure_lt_top.ne
  have he : (fun x ↦ ∫ δ, ∫ y, Ω x y δ • (A x y δ).mulVec (u y)) =
      fun x ↦ ∫ p in F ×ˢ Y, amplitudeKernel Ω A u x p ∂μ := by
    funext x
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp ↦ amplitudeKernel_eq_zero_off_carrier hA x p hp),
      integral_prod _ (integrable_amplitudeKernel hΩ hA hY hF hu x)]
    rfl
  rw [he]
  exact contDiffOn_univ.mp (contDiffOn_compactParameterIntegral
    (U := (univ : Set (Euclidean n))) isOpen_univ isOpen_univ (hF.prod hY) (subset_univ _)
    (smooth_amplitudeKernel hΩ hA hu).contDiffOn)

/-- The full output mask gives compact support to the actual integral in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem compactSupport_amplitudeIntegral
    (hA : ForwardAmplitudeAdmissible X Y F A) (hX : IsCompact X) :
    HasCompactSupport (fun x ↦ ∫ δ, ∫ y, Ω x y δ • (A x y δ).mulVec (u y)) := by
  apply hX.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hX.isClosed
  intro x hx
  by_contra hn
  exact hx (by simp [hA.support x _ _ (Or.inl hn)])

/-- All Schwartz pairings of the literal normalized graph are integrable,
from compact smooth amplitudes (`app:ch_response:eq:direct-envelope-profile`). -/
theorem integrable_amplitudeIntegral_pairing
    (hΩ : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ Ω p.1 p.2.1 p.2.2))
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    (hu : ContDiff ℝ ∞ u) (c : ℂ) (φ : 𝓢((Euclidean n), ℂ)) :
    Integrable (fun x ↦ φ x • (c • ∫ δ, ∫ y, Ω x y δ • (A x y δ).mulVec (u y))) :=
  (φ.continuous.smul ((smooth_amplitudeIntegral hΩ hA hY hF hu).continuous.const_smul c)).integrable_of_hasCompactSupport
      (((compactSupport_amplitudeIntegral hA hX).comp_left (smul_zero c)).smul_left)

end JanetCartan.ResponseTransfer.SpatialRealization
