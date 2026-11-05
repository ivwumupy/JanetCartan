module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Coefficients
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Kernels

/-!
# Smooth compact regularizations of reverse amplitudes

The frequency cutoff avoids the zero covector, where a homogeneous phase need
not be smooth. These facts supply the compact integrands used by the reverse
weak pairing in `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- A smooth cutoff supported away from zero extends an admissible amplitude
to a globally smooth function of all three variables. Consumed by the compact
frequency reverse pairing. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.contDiff_frequencyCut
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : (0 : E) ∉ tsupport χ) :
    ContDiff ℝ ∞ (fun p : (E × E) × E ↦ frequencyCutFullAmplitude χ C p.1.1 p.1.2 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hη : p.2 = 0
  · have hz : p.2 ∉ tsupport χ := hη ▸ hχ0
    have he := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto
      (continuous_snd.tendsto p)
    apply (contDiffAt_const (c := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    change χ q.2 = 0 at hq
    simp [frequencyCutFullAmplitude, hq]
  · exact (hχ.contDiffAt.comp p contDiffAt_snd).smul (hC.smooth p hη)

/-- The regularized full amplitude has compact support in both physical
positions and frequency. This is the support input for absolute integrability,
not an assumed integrability premise.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.hasCompactSupport_frequencyCut
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (χ : E → ℂ) (hχ : HasCompactSupport χ) :
    HasCompactSupport
      (fun p : (E × E) × E ↦ frequencyCutFullAmplitude χ C p.1.1 p.1.2 p.2) := by
  apply (hK.prod hχ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (hK.isClosed.prod (isClosed_tsupport _))
  intro p hp
  have hne : C p.1.1 p.1.2 p.2 ≠ 0 := by
    intro hz
    exact hp (by simp [frequencyCutFullAmplitude, hz])
  have hχne : χ p.2 ≠ 0 := by
    intro hz
    exact hp (by simp [frequencyCutFullAmplitude, hz])
  exact ⟨hC.support (subset_tsupport _ hne), subset_tsupport χ hχne⟩

/-- At a nonzero frequency the two-position amplitude is globally smooth in
physical coordinates. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem ReverseAmplitudeAdmissible.contDiff_physical
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (η : E) (hη : η ≠ 0) : ContDiff ℝ ∞ (fun p : E × E ↦ C p.1 p.2 η) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  exact (hC.smooth (p, η) hη).comp p (contDiffAt_id.prodMk contDiffAt_const)

/-- The compact frequency cutoff makes the reverse oscillatory amplitude
smooth even though the phase is only smooth away from zero. This supplies the
actual integrand, retaining its masks and the conjugate oscillation, for the
weak integration by parts. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem ReverseAmplitudeAdmissible.contDiff_reverseOscillatory_frequencyCut
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : (0 : E) ∉ tsupport χ) :
    ContDiff ℝ ∞ (fun p : (E × E) × E ↦ star (graphOscillation S p.1.1 p.1.2 p.2) •
      frequencyCutFullAmplitude χ C p.1.1 p.1.2 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hη : p.2 = 0
  · have hz : p.2 ∉ tsupport χ := hη ▸ hχ0
    have he := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto
      (continuous_snd.tendsto p)
    apply (contDiffAt_const (c := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    change χ q.2 = 0 at hq
    simp [frequencyCutFullAmplitude, hq]
  · have hs := (hS p.1.1 p.2 hη).comp p (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have he : ContDiffAt ℝ ∞ (fun q : (E × E) × E ↦
        star (graphOscillation S q.1.1 q.1.2 q.2)) p := by
      simp_rw [star_graphOscillation]
      exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((contDiffAt_fst.snd.inner ℝ contDiffAt_snd).sub hs))).cexp
    exact he.smul ((hC.contDiff_frequencyCut χ hχ hχ0).contDiffAt)

/-- Compact support of the reverse oscillatory amplitude, independent of any
regularity of the phase at the zero covector.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.hasCompactSupport_reverseOscillatory_frequencyCut
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (S : E → E → ℝ) (χ : E → ℂ) (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun p : (E × E) × E ↦ star (graphOscillation S p.1.1 p.1.2 p.2) •
      frequencyCutFullAmplitude χ C p.1.1 p.1.2 p.2) := by
  apply (hC.hasCompactSupport_frequencyCut hK χ hχ).mono
  intro p hp hz
  apply hp
  change frequencyCutFullAmplitude χ C p.1.1 p.1.2 p.2 = 0 at hz
  change star (graphOscillation S p.1.1 p.1.2 p.2) •
    frequencyCutFullAmplitude χ C p.1.1 p.1.2 p.2 = 0
  rw [hz, smul_zero]

/-- Frequency cutoffs commute with the explicit reverse first output amplitude.
This connects output integration by parts with source transfer at fixed frequency.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseFirstOutputAmplitude_frequencyCutFullAmplitude
    (χ : E → ℂ) (C : FullAmplitude n r) (i : Fin n) :
    reverseFirstOutputAmplitude (frequencyCutFullAmplitude χ C) i =
      frequencyCutFullAmplitude χ (reverseFirstOutputAmplitude C i) := by
  funext x y η
  have hd : partialDeriv (fun z ↦ χ η • C x z η) y i =
      χ η • partialDeriv (fun z ↦ C x z η) y i := by
    have h := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun z ↦ C x z η) (χ η)) y
    exact congrArg (fun L : E →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
      L (EuclideanSpace.single i 1)) h
  simp only [reverseFirstOutputAmplitude, frequencyCutFullAmplitude, hd, smul_add]
  rw [smul_comm (Complex.I * (η i : ℂ))]

end JanetCartan.FourierIntegral
