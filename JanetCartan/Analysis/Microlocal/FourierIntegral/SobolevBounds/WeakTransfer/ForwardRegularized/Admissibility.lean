module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Source
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.FrequencyCutoff

/-!
# Qualitative admissibility of forward transfer amplitudes

The predicate used for `hR` and `hP` in
`fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings` records only
primitive smoothness and support. The frequency carrier is closed and avoids
zero; it need not be compact. This encodes the fixed low-frequency cutoff that
the manuscript includes in every homogeneous construction. Thus the phase may be nonlinear homogeneous and
smooth only away from zero. Every physical mask remains in the full amplitude.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Primitive smoothness and fixed carriers, for the forward weak-transfer
consumer. Compactness of the physical carriers is supplied separately when
integrating. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
structure ForwardAmplitudeAdmissible (X Y F : Set (Euclidean n)) (A : FullAmplitude n r) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ A p.1 p.2.1 p.2.2)
  support : ∀ x y η, x ∉ X ∨ y ∉ Y ∨ η ∉ F → A x y η = 0

namespace ForwardRegularized

/-- Joint smoothness of an output derivative of the full amplitude, used in
the remainder branch of `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem smooth_outputPartial {A : FullAmplitude n r}
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ A p.1 p.2.1 p.2.2)) (i : Fin n) :
    ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦
      partialDeriv (fun z ↦ A z p.2.1 p.2.2) p.1 i) := by
  have h : ContDiff ℝ ∞ (fun q : ((Euclidean n) × ((Euclidean n) × (Euclidean n))) × (Euclidean n) ↦ A q.2 q.1.2.1 q.1.2.2) :=
    hA.comp (contDiff_snd.prodMk (contDiff_fst.snd.fst.prodMk contDiff_fst.snd.snd))
  exact (h.fderiv contDiff_fst (by simp)).clm_apply contDiff_const

/-- Joint smoothness of a source derivative, with all output and frequency
spectators retained (`app:ch_regular_base:eq:graph-derivative-transfer`). -/
theorem smooth_sourcePartial {A : FullAmplitude n r}
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ A p.1 p.2.1 p.2.2)) (j : Fin n) :
    ContDiff ℝ ∞ (fun p : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦
      partialDeriv (fun z ↦ A p.1 z p.2.2) p.2.1 j) := by
  have h : ContDiff ℝ ∞ (fun q : ((Euclidean n) × ((Euclidean n) × (Euclidean n))) × (Euclidean n) ↦ A q.1.1 q.2 q.1.2.2) :=
    hA.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd.snd))
  exact (h.fderiv contDiff_snd.fst (by simp)).clm_apply contDiff_const

/-- The actual mixed phase entry is smooth wherever the phase is smooth.
This only uses a neighborhood of a nonzero covector in the forward transfer
construction (`app:ch_regular_base:eq:graph-derivative-transfer`). -/
theorem smoothAt_mixedPhaseEntry {S : (Euclidean n) → (Euclidean n) → ℝ} {x η : (Euclidean n)}
    (hS : ContDiffAt ℝ ∞ (Function.uncurry S) (x, η)) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun p : (Euclidean n) × (Euclidean n) ↦ mixedPhaseMatrix S p.1 p.2 i j) (x, η) := by
  have hx : ContDiffAt ℝ ∞
      (fun p : (Euclidean n) × (Euclidean n) ↦ partialDeriv (fun z ↦ S z p.2) p.1 i) (x, η) := by
    have h : ContDiffAt ℝ ∞ (fun q : ((Euclidean n) × (Euclidean n)) × (Euclidean n) ↦ S q.2 q.1.2) ((x, η), x) :=
      hS.comp ((x, η), x) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    exact (h.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const
  have h : ContDiffAt ℝ ∞
      (fun q : ((Euclidean n) × (Euclidean n)) × (Euclidean n) ↦ partialDeriv (fun z ↦ S z q.2) q.1.1 i) ((x, η), η) :=
    hx.comp ((x, η), η) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (h.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const

private theorem partial_eq_zero_off_closed {K : Set (Euclidean n)} (hK : IsClosed K)
    {a : (Euclidean n) → Matrix (Fin r) (Fin r) ℂ} (hs : ∀ x ∉ K, a x = 0)
    {x : (Euclidean n)} (hx : x ∉ K) (i : Fin n) : partialDeriv a x i = 0 := by
  have he : a =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with z hz using hs z hz
  have h : fderiv ℝ a x = 0 := by
    rw [he.fderiv_eq (𝕜 := ℝ)]
    simp
  exact congrArg (fun L : (Euclidean n) →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
    L (EuclideanSpace.single i 1)) h

end ForwardRegularized

namespace ForwardAmplitudeAdmissible
variable {X Y F : Set (Euclidean n)} {A : FullAmplitude n r}

/-- Physical derivatives preserve all three closed carriers, including the
frequency gap (`app:ch_regular_base:eq:graph-derivative-transfer`). -/
theorem outputPartial (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (i : Fin n) :
    ForwardAmplitudeAdmissible X Y F
      (fun x y η ↦ partialDeriv (fun z ↦ A z y η) x i) := by
  refine ⟨ForwardRegularized.smooth_outputPartial hA.smooth i, ?_⟩
  intro x y η h
  rcases h with hx | hy | hη
  · exact ForwardRegularized.partial_eq_zero_off_closed hX
      (fun z hz ↦ hA.support z y η (Or.inl hz)) hx i
  · have he : (fun z ↦ A z y η) = fun _ ↦ 0 :=
      funext fun z ↦ hA.support z y η (Or.inr (Or.inl hy))
    simp [he, partialDeriv]
  · have he : (fun z ↦ A z y η) = fun _ ↦ 0 :=
      funext fun z ↦ hA.support z y η (Or.inr (Or.inr hη))
    simp [he, partialDeriv]

/-- Source derivatives preserve the complete physical and frequency carriers.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem sourcePartial (hA : ForwardAmplitudeAdmissible X Y F A)
    (hY : IsClosed Y) (j : Fin n) :
    ForwardAmplitudeAdmissible X Y F
      (fun x y η ↦ partialDeriv (fun z ↦ A x z η) y j) := by
  refine ⟨ForwardRegularized.smooth_sourcePartial hA.smooth j, ?_⟩
  intro x y η h
  rcases h with hx | hy | hη
  · have he : (fun z ↦ A x z η) = fun _ ↦ 0 :=
      funext fun z ↦ hA.support x z η (Or.inl hx)
    simp [he, partialDeriv]
  · exact ForwardRegularized.partial_eq_zero_off_closed hY
      (fun z hz ↦ hA.support x z η (Or.inr (Or.inl hz))) hy j
  · have he : (fun z ↦ A x z η) = fun _ ↦ 0 :=
      funext fun z ↦ hA.support x z η (Or.inr (Or.inr hη))
    simp [he, partialDeriv]

/-- Datum-branch admissibility follows from primitive phase smoothness away
from zero. No regularity at zero is imposed on the phase.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphTransferDatum (hA : ForwardAmplitudeAdmissible X Y F A)
    (hF : IsClosed F) (hF0 : (0 : (Euclidean n)) ∉ F) (S : (Euclidean n) → (Euclidean n) → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (i j : Fin n) : ForwardAmplitudeAdmissible X Y F (FourierIntegral.graphTransferDatum S i j A) := by
  refine ⟨contDiff_iff_contDiffAt.mpr (fun p ↦ ?_), ?_⟩
  · by_cases hη : p.2.2 = 0
    · have hz : p.2.2 ∉ F := hη ▸ hF0
      have he : (fun q : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦ FourierIntegral.graphTransferDatum S i j A q.1 q.2.1 q.2.2)
          =ᶠ[𝓝 p] fun _ ↦ 0 := by
        filter_upwards [(continuous_snd.snd.isOpen_preimage _ hF.isOpen_compl).mem_nhds hz]
          with q hq
        simp [FourierIntegral.graphTransferDatum, hA.support q.1 q.2.1 q.2.2
          (Or.inr (Or.inr hq))]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((ForwardRegularized.smoothAt_mixedPhaseEntry (hS _ _ hη) i j).comp p
          (contDiffAt_fst.prodMk contDiffAt_snd.snd))).smul hA.smooth.contDiffAt
  · intro x y η h
    simp [FourierIntegral.graphTransferDatum, hA.support x y η h]

/-- Remainder-branch closure supplies the exact `hR` premise of the finite
weak-transfer consumer. Both position derivatives and every mask are retained.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphTransferRemainder (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F) (hF0 : (0 : (Euclidean n)) ∉ F)
    (S : (Euclidean n) → (Euclidean n) → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (i : Fin n) : ForwardAmplitudeAdmissible X Y F (graphTransferRemainder S i A) := by
  have hx := hA.outputPartial hX i
  have hy (j) := (hA.sourcePartial hY j).graphTransferDatum hF hF0 S hS i j
  refine ⟨hx.smooth.add (ContDiff.sum (fun j _ ↦ (hy j).smooth)), ?_⟩
  intro x y η h
  change _ + ∑ j, FourierIntegral.graphTransferDatum S i j
    (fun x y η ↦ partialDeriv (fun z ↦ A x z η) y j) x y η = 0
  rw [hx.support x y η h]
  simp only [(hy _).support x y η h, Finset.sum_const_zero, add_zero]

/-- Smooth frequency cutoffs preserve the qualitative admissibility predicate.
Source: the regularization in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem frequencyCut (hA : ForwardAmplitudeAdmissible X Y F A)
    {χ : (Euclidean n) → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ForwardAmplitudeAdmissible X Y F (frequencyCutFullAmplitude χ A) := by
  refine ⟨(hχ.comp contDiff_snd.snd).smul hA.smooth, ?_⟩
  intro x y η h
  simp [frequencyCutFullAmplitude, hA.support x y η h]

end ForwardAmplitudeAdmissible
end JanetCartan.FourierIntegral
