module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Cutoff

/-!
# Reverse source transfer from primitive phase data

This discharges the coefficient smoothness and mixed differentiability premises
of `integral_reverseFirstOutputAmplitude_transfer` from the shared admissibility
predicate. The remaining compact frequency integration is a separate step.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`.
-/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Source transfer at every nonzero frequency, using only primitive phase
smoothness, homogeneity on the common support, and the actual inverse gap.
Smoothness of the inverse-weighted coefficient is proved by admissibility
closure. Consumed by frequency integration in the reverse weak pairing.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.integral_reverseFirstOutputAmplitude
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hhom : ∀ p ∈ K, ∀ η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 p.1] (fun z ↦ t * S z η))
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
  have hsupport (x : E) (hx : C x y η ≠ 0) : (x, y) ∈ K := by
    have hm : ((x, y), η) ∈ Function.support
        (fun p : (E × E) × E ↦ C p.1.1 p.1.2 p.2) := hx
    exact hC.support (subset_tsupport _ hm)
  refine integral_reverseFirstOutputAmplitude_transfer S C u y η i hphase
    (hC.contDiff_physical η hη) ?_ hu hus ?_ ?_ ?_
  · intro j
    have hc : ContDiff ℝ ∞ (fun p : E × E ↦
        FourierIntegral.adjointTransferDatum S i j C p.1 p.2 η) :=
      (hC.adjointTransferDatum S hS hinv i j).contDiff_physical η hη
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
    exact hhom (x, y) (hsupport x hx) η hη
  · intro x hx
    exact hinv (x, y) (hsupport x hx) η hη

end JanetCartan.FourierIntegral
