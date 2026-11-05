module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.PhaseLocality

/-!
# Reverse source transfer from primitive phase data

This discharges the coefficient smoothness and mixed differentiability premises
of `integral_reverseFirstOutputAmplitude_transfer` from the shared admissibility
predicate. The remaining compact frequency integration is a separate step.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`.
-/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Source transfer at every nonzero frequency, using only primitive phase
smoothness, homogeneity on the common support, and the actual inverse gap.
Smoothness of the inverse-weighted coefficient is proved by admissibility
closure. Consumed by frequency integration in the reverse weak pairing.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem integral_reverseFirstOutputAmplitude_smooth_supported
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    {F : Set E} (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (hinv : SupportedMixedInvertibility S (K ×ˢ F))
    (hhom : SupportedPhaseHomogeneity S (K ×ˢ F))
    (u : E → Fin r → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (y η : E) (hη : η ≠ 0) (i : Fin n) :
    (∫ x, star (graphOscillation S x y η) •
      (FourierIntegral.reverseFirstOutputAmplitude C i x y η).mulVec (u x)) =
      (∫ x, star (graphOscillation S x y η) •
        (FourierIntegral.adjointTransferRemainder S i C x y η).mulVec (u x)) +
      ∑ j, ∫ x, star (graphOscillation S x y η) •
        (FourierIntegral.adjointTransferDatum S i j C x y η).mulVec (partialDeriv u x j) := by
  have hphase : ContDiff ℝ ∞ (fun x ↦ S x η) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hS x η hη).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hsupport (x : E) (hx : C x y η ≠ 0) : ((x, y), η) ∈ K ×ˢ F := by
    have hm : ((x, y), η) ∈ Function.support
        (fun p : (E × E) × E ↦ C p.1.1 p.1.2 p.2) := hx
    exact ⟨hC.support (subset_tsupport _ hm), by
      by_contra hηF
      exact hx (hfreq x y η hηF)⟩
  refine integral_reverseFirstOutputAmplitude_transfer S C u y η i hphase
    (hC.contDiff_physical η hη) ?_ hu hus ?_ ?_ ?_
  · intro j
    have hc : ContDiff ℝ ∞ (fun p : E × E ↦
        FourierIntegral.adjointTransferDatum S i j C p.1 p.2 η) :=
      (hC.adjointTransferDatum_of_supported S hfreq hF hF0 (Set.Subset.refl _)
        (fun p _ hη ↦ hS p.1.1 p.2 hη) hinv i j).contDiff_physical η hη
    simpa only [Function.comp_def, id_eq] using
      hc.comp (contDiff_id.prodMk (contDiff_const (c := y)))
  · intro x _ j
    have hs := (hS x η hη).comp ((x, η), x)
      (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    have hd : ContDiffAt ℝ ∞
        (fun q : E × E ↦ partialDeriv (fun z ↦ S z q.2) q.1 j) (x, η) :=
      (hs.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const
    exact (hd.comp η (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  · intro x hx
    exact hhom ((x, y), η) (hsupport x hx) hη
  · intro x hx
    exact hinv ((x, y), η) (hsupport x hx)

/-- Frequency-integrated source transfer for the literal reverse operator.
The actual inverse, homogeneity, and smoothness premises are precisely those of
the fixed-frequency source identity. Compact smooth cutoff amplitudes provide
all integrability, and the cutoff vanishes near zero frequency. Consumed by the
parent's output weak pairing assembly.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraphOperator_reverseFirstOutputAmplitude_smooth_supported
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    {F : Set E} (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (hinv : SupportedMixedInvertibility S (K ×ˢ F))
    (hhom : SupportedPhaseHomogeneity S (K ×ˢ F))
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
  have hcutF : ∀ x y η, η ∉ F → frequencyCutFullAmplitude χ C x y η = 0 := by
    intro x y η hη
    simp [frequencyCutFullAmplitude, hfreq x y η hη]
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
        integral_reverseFirstOutputAmplitude_smooth_supported hcut S hS hF hF0 hcutF hinv hhom _ hu hus y η hη i
  have hR := (hC.adjointTransferRemainder_of_supported S hfreq hF hF0 (Set.Subset.refl _)
    (fun p _ hη ↦ hS p.1.1 p.2 hη) hinv i).integrable_integral_reverseOscillatory_frequencyCut
    hK S hS χ hχ hχs hχ0 _ hu.continuous y
  have hP (j : Fin n) :=
    (hC.adjointTransferDatum_of_supported S hfreq hF hF0 (Set.Subset.refl _)
      (fun p _ hη ↦ hS p.1.1 p.2 hη) hinv i j).integrable_integral_reverseOscillatory_frequencyCut
      hK S hS χ hχ hχs hχ0 _ (huj j) y
  simp only [reverseGraphOperator]
  simp_rw [ht]
  rw [integral_add hR (integrable_finsetSum Finset.univ (fun j _ ↦ hP j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hP j), smul_add, Finset.smul_sum]


/-- Compact-frequency reverse weak pairing in the exact source test space and
complex Hilbert fiber of `fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings`.
All integrability obligations follow from smoothness and compact supports. The
phase is smooth only away from zero, and its homogeneity and actual mixed inverse
gap are required only on the common physical support. The already reversed `C`
retains every physical mask and is transferred without further conjugation.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraphOperator_frequencyCut_weak_pairing_smooth_supported
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    {F : Set E} (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (hinv : SupportedMixedInvertibility S (K ×ˢ F))
    (hhom : SupportedPhaseHomogeneity S (K ×ˢ F))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχ0 : (0 : E) ∉ tsupport χ)
    (i : Fin n) (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)) :
    (∫ y, partialDeriv φ y i • WithLp.toLp 2
      (reverseGraphOperator S (frequencyCutFullAmplitude χ C) (fun x ↦ (u.val x).ofLp) y)) =
      -((∫ y, φ y • WithLp.toLp 2
          (reverseGraphOperator S (frequencyCutFullAmplitude χ (adjointTransferRemainder S i C))
            (fun x ↦ (u.val x).ofLp) y)) +
        ∑ j, ∫ y, φ y • WithLp.toLp 2
          (reverseGraphOperator S (frequencyCutFullAmplitude χ (adjointTransferDatum S i j C))
            (fun x ↦ ((graphTestPartialDeriv j u).val x).ofLp) y)) := by
  have hR := reverseGraphOperator_frequencyCut_integrable_pairing
    (hC.adjointTransferRemainder_of_supported S hfreq hF hF0 (Set.Subset.refl _)
      (fun p _ hη ↦ hS p.1.1 p.2 hη) hinv i) hK hS hχ hχs hχ0 u φ
  have hP (j : Fin n) := reverseGraphOperator_frequencyCut_integrable_pairing
    (hC.adjointTransferDatum_of_supported S hfreq hF hF0 (Set.Subset.refl _)
      (fun p _ hη ↦ hS p.1.1 p.2 hη) hinv i j) hK hS hχ hχs hχ0
      (graphTestPartialDeriv j u) φ
  rw [reverseGraphOperator_frequencyCut_output_weak_pairing hC hK hS hχ hχs hχ0]
  simp_rw [reverseGraphOperator_reverseFirstOutputAmplitude_smooth_supported hC hK S hS hF hF0 hfreq hinv hhom
    χ hχ hχs hχ0 i _ u, WithLp.toLp_add, WithLp.toLp_sum, smul_add, Finset.smul_sum]
  rw [integral_add hR (integrable_finsetSum Finset.univ (fun j _ ↦ hP j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hP j)]


end JanetCartan.FourierIntegral.SupportedSobolev
