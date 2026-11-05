module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Geometry

/-!
# Leading-wave reconstruction with the canonical normal completion

Specialize `app:ch_waves:eq:reconstruction` to the actual canonical normal
completion. Its smoothness and normal-space membership discharge the auxiliary
normal-field hypotheses in `reconstruction_half_strain`, giving the actual
stress projection in `app:ch_waves:eq:exact-half-strain`.

These deductions are local to an open domain and require a smooth immersion of
full normal rank and a smooth covector field there. The leading-wave consumer
must supply those geometric and analytic inputs; no phase, carrier, or transport
existence is asserted here.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set
open JanetCartan.AmbientResponse

namespace JanetCartan.LeadingWave

/-- The actual correction in `app:ch_waves:eq:reconstruction` is normal.
This supplies the normal-space premise of `reconstruction_half_strain`. -/
theorem normalCorrection_canonical_mem_normalSpace {n N : ℕ}
    (F : Euclidean n → Euclidean N) (u : Euclidean n → Euclidean n)
    (x : Euclidean n) :
    normalCorrection F (canonicalNormalCompletion F) u x ∈ normalSpace F x := by
  exact canonicalNormalCompletion_mem_normalSpace F x (symmCovariantDeriv F u x)

/-- The actual normal correction in `app:ch_waves:eq:reconstruction` is smooth
on the open full-normal-rank immersion domain. This supplies the smoothness
premise of `reconstruction_half_strain` without assuming a smooth normal field. -/
theorem contDiffOn_normalCorrection_canonical {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s) :
    ContDiffOn ℝ ∞ (normalCorrection F (canonicalNormalCompletion F) u) s := by
  exact contDiffOn_canonicalNormalCompletion hs hF
    (contDiffOn_symmCovariantDeriv hs hF hu himm) himm hrank

/-- The ambient field in `app:ch_waves:eq:reconstruction`, using the actual
canonical completion, is smooth on the stated open immersion domain. -/
theorem contDiffOn_reconstruction_canonical {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s) :
    ContDiffOn ℝ ∞ (reconstruction F (canonicalNormalCompletion F) u) s := by
  exact (contDiffOn_tangentLift hs hF hu himm).add
    (contDiffOn_normalCorrection_canonical hs hF hu himm hrank)

/-- The exact projected half-strain identity
`app:ch_waves:eq:exact-half-strain` for the canonical reconstruction. All
auxiliary smooth-normal-field premises are discharged from local smoothness,
immersion, and full normal rank. -/
theorem reconstruction_canonical_half_strain {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s) :
    EqOn (fun x ↦ (1 / 2 : ℝ) •
      linearizedMetric F (reconstruction F (canonicalNormalCompletion F) u) x)
      (fun x ↦ ProjectedStressFrame.stressProjection F x (symmCovariantDeriv F u x)) s := by
  intro x hx
  calc
    _ = symmCovariantDeriv F u x -
        normalPairing F (normalCorrection F (canonicalNormalCompletion F) u) x :=
      reconstruction_half_strain hs hF hu himm
        (contDiffOn_normalCorrection_canonical hs hF hu himm hrank)
        (fun y _ ↦ normalCorrection_canonical_mem_normalSpace F u y) hx
    _ = _ := (ProjectedStressFrame.stressProjection_eq_sub_completion
      (hrank x hx) (symmCovariantDeriv F u x)).symm

end JanetCartan.LeadingWave
