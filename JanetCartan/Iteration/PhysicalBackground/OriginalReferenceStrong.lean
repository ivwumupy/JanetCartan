module

public import JanetCartan.Iteration.PhysicalBackground.ActualReference
import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.InitializedProofCache

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev PositiveBackground CoerciveInverse

/- Native StrongReference bound for the literal selected augmented row at
zero density. The inferred conclusion keeps the exact `SelectedBoundary.rMeasure`
and all original cutoffs; it does not assert the bound at an arbitrary radius.
Cfull is fixed before σ. Consumer: the original pre-σ raw half-budget in
`app:ch_background:prop:bg-current`. -/
proof_from originalReferenceRow_strong
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = PhysicalSeed.OriginalBoundary.b hn)
    (k : (j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount) ×
        Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (PhysicalSeed.OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter
          (PhysicalSeed.OriginalBoundary.D hn)) →
      (l : Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
        ((p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ PhysicalSeed.OriginalBoundary.centers hn
        ⟨(p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) →
      { ε : ℝ // 0 < ε })
    (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ)
      (PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
        p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra)) :=
  let H := JanetCartan.PhysicalNormalInverse.StrongSourceGap.reference_uncorrected_raw
    hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
      incidenceCap hinc aExtra σ hσ (fun _ _ ↦ 0)
      (by intro i; exact contDiffOn_const)
      (by intro i q _hq; norm_num)
      (by intro i q _hq; constructor <;> norm_num)
      (by intro i; change cNorm _ _ (0 : (Euclidean (n - 1) × Euclidean 3) → ℝ) ≤ 1
          rw [cNorm_zero]
          norm_num)
      (by rfl)
  H.2

end JanetCartan.PhysicalBackground
end
