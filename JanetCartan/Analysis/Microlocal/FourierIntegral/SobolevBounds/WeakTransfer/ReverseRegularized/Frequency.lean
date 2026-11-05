module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Source
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Realization

/-!
# Frequency integration of reverse source transfer

Compactness and smoothness of the cutoff oscillatory amplitude supply absolute
integrability before the source-transfer identity is integrated in frequency.
This is the source side of the literal adjoint weak pairing; output integration
by parts is a separate obligation of the parent construction.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Absolute integrability in frequency and source follows from the published
smooth compact reverse oscillatory amplitude. Consumed by frequency integration
of source transfer, with the original physical coordinates and Lebesgue measures.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.integrable_reverseOscillatory_frequencyCut_mulVec
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχ0 : (0 : E) ∉ tsupport χ)
    (v : E → Fin r → ℂ) (hv : Continuous v) (y : E) :
    Integrable (fun p : E × E ↦ star (graphOscillation S p.2 y p.1) •
      (frequencyCutFullAmplitude χ C p.2 y p.1).mulVec (v p.2))
      (volume.prod volume) := by
  let a := fun q : (E × E) × E ↦ star (graphOscillation S q.1.1 q.1.2 q.2) •
    frequencyCutFullAmplitude χ C q.1.1 q.1.2 q.2
  have ha : Continuous a :=
    (hC.contDiff_reverseOscillatory_frequencyCut S hS χ hχ hχ0).continuous
  have has : HasCompactSupport a :=
    hC.hasCompactSupport_reverseOscillatory_frequencyCut hK S χ hχs
  have hs : HasCompactSupport (fun p : E × E ↦ (a ((p.2, y), p.1)).mulVec (v p.2)) := by
    apply HasCompactSupport.intro
      (has.image (continuous_snd.prodMk continuous_fst.fst))
    intro p hp
    have hz : a ((p.2, y), p.1) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hp ⟨((p.2, y), p.1), hm, rfl⟩
    simp [hz]
  have hc : Continuous (fun p : E × E ↦ (a ((p.2, y), p.1)).mulVec (v p.2)) := by
    have hac := ha.comp ((continuous_snd.prodMk (continuous_const (y := y))).prodMk
      continuous_fst)
    unfold Matrix.mulVec dotProduct
    fun_prop
  simpa only [a, Matrix.smul_mulVec] using hc.integrable_of_hasCompactSupport hs

/-- The source integral is integrable in frequency, with no integrability
hypothesis. This permits addition and finite sums in the reverse source-transfer
formula. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.integrable_integral_reverseOscillatory_frequencyCut
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχ0 : (0 : E) ∉ tsupport χ)
    (v : E → Fin r → ℂ) (hv : Continuous v) (y : E) :
    Integrable (fun η ↦ ∫ x, star (graphOscillation S x y η) •
      (frequencyCutFullAmplitude χ C x y η).mulVec (v x)) :=
  (hC.integrable_reverseOscillatory_frequencyCut_mulVec hK S hS χ hχ hχs hχ0 v hv y).integral_prod_left

/-- Frequency-integrated source transfer for the literal reverse operator.
The actual inverse, homogeneity, and smoothness premises are precisely those of
the fixed-frequency source identity. Compact smooth cutoff amplitudes provide
all integrability, and the cutoff vanishes near zero frequency. Consumed by the
parent's output weak pairing assembly.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.reverseGraphOperator_reverseFirstOutputAmplitude
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hhom : ∀ p ∈ K, ∀ η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 p.1] (fun z ↦ t * S z η))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχ0 : (0 : E) ∉ tsupport χ) (i : Fin n) (y : E) (u : graphTestSpace n r) :
    reverseGraphOperator S (frequencyCutFullAmplitude χ (FourierIntegral.reverseFirstOutputAmplitude C i))
        (fun x ↦ (u.val x).ofLp) y =
      reverseGraphOperator S (frequencyCutFullAmplitude χ (FourierIntegral.adjointTransferRemainder S i C))
        (fun x ↦ (u.val x).ofLp) y +
      ∑ j, reverseGraphOperator S (frequencyCutFullAmplitude χ (FourierIntegral.adjointTransferDatum S i j C))
        (fun x ↦ ((graphTestPartialDeriv j u).val x).ofLp) y := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).toContinuousLinearMap
  have hu : ContDiff ℝ ∞ (fun x ↦ (u.val x).ofLp) := L.contDiff.comp u.property.1
  have hus : HasCompactSupport (fun x ↦ (u.val x).ofLp) :=
    u.property.2.comp_left L.map_zero
  have huj (j : Fin n) : Continuous (fun x ↦ ((graphTestPartialDeriv j u).val x).ofLp) :=
    (L.contDiff.comp (graphTestPartialDeriv j u).property.1).continuous
  have hcut : ReverseAmplitudeAdmissible K (frequencyCutFullAmplitude χ C) := by
    refine ⟨fun p _ ↦ (hC.contDiff_frequencyCut χ hχ hχ0).contDiffAt, ?_⟩
    exact (tsupport_smul_subset_right _ _).trans hC.support
  have ht (η : E) :
      (∫ x, star (graphOscillation S x y η) •
        (frequencyCutFullAmplitude χ (FourierIntegral.reverseFirstOutputAmplitude C i) x y η).mulVec
          ((u.val x).ofLp)) =
      (∫ x, star (graphOscillation S x y η) •
        (frequencyCutFullAmplitude χ (FourierIntegral.adjointTransferRemainder S i C) x y η).mulVec
          ((u.val x).ofLp)) +
      ∑ j, ∫ x, star (graphOscillation S x y η) •
        (frequencyCutFullAmplitude χ (FourierIntegral.adjointTransferDatum S i j C) x y η).mulVec
          (((graphTestPartialDeriv j u).val x).ofLp) := by
    by_cases hη : η = 0
    · subst η
      simp [frequencyCutFullAmplitude, image_eq_zero_of_notMem_tsupport hχ0]
    · simpa only [reverseFirstOutputAmplitude_frequencyCutFullAmplitude,
        adjointTransferRemainder_frequencyCutFullAmplitude,
        adjointTransferDatum_frequencyCutFullAmplitude, graphTestPartialDeriv_coordinates] using
        hcut.integral_reverseFirstOutputAmplitude S hS hinv hhom _ hu hus y η hη i
  have hR := (hC.adjointTransferRemainder S hS hinv i).integrable_integral_reverseOscillatory_frequencyCut
    hK S hS χ hχ hχs hχ0 _ hu.continuous y
  have hP (j : Fin n) :=
    (hC.adjointTransferDatum S hS hinv i j).integrable_integral_reverseOscillatory_frequencyCut
      hK S hS χ hχ hχs hχ0 _ (huj j) y
  simp only [reverseGraphOperator]
  simp_rw [ht]
  rw [integral_add hR (integrable_finsetSum Finset.univ (fun j _ ↦ hP j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hP j), smul_add, Finset.smul_sum]

end JanetCartan.FourierIntegral
