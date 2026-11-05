module

public import JanetCartan.Iteration.PhysicalSampling.SourceCap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.IncidenceScaling

/-!
# The original detector fits the preselected scalar full geometry

The SAME original selector already accepts a prescribed angular-width cap.
Impose the scalar width in that cap before selecting the one original source
family. The original detector is neither partitioned nor replaced. Its positive
incidence representative changes only the length of the central covector; the
normalized direction is identical (`app:ch_background:defn:bg-row`,
`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section

open Set Metric NormedSpace

namespace JanetCartan.PhysicalSampling

open ContinuumRow.CanonicalConic Sampling

/-- Angular-width caps compare the actual closed direction sets even when the
selector uses its original positively rescaled incidence representative. -/
theorem closedDirections_subset_of_angular_cap {n : ℕ}
    (ηoriginal ηscalar : Euclidean (n - 1)) (roriginal rscalar : ℝ)
    (hdirection : normalize ηoriginal = normalize ηscalar)
    (hwidth : angularWidth ηoriginal roriginal ≤ angularWidth ηscalar rscalar) :
    closedDirections ηoriginal roriginal ⊆ closedDirections ηscalar rscalar := by
  intro θ hθ
  refine ⟨hθ.1, ?_⟩
  rw [← hdirection]
  exact closedBall_subset_closedBall (by linarith) hθ.2

/-- The literal unchanged detector satisfies exactly the support premise of
`exists_retained_scalarNormalFamily`, using the new pre-selection width cap.
This is not a post-selection shrinking of either the angular mask or the source. -/
theorem originalConicDetector_support_of_angular_cap {n : ℕ}
    {ηoriginal ηscalar : Euclidean (n - 1)} {roriginal rscalar cap : ℝ}
    (hηoriginal : ηoriginal ≠ 0) (hroriginal : 0 < roriginal)
    (hdirection : normalize ηoriginal = normalize ηscalar)
    (horiginal : angularWidth ηoriginal roriginal ≤ cap)
    (hcap : cap ≤ angularWidth ηscalar rscalar)
    {η : Euclidean (n - 1)} (hη : originalConicDetector hηoriginal hroriginal η ≠ 0) :
    normalize η ∈ closedDirections ηscalar rscalar :=
  closedDirections_subset_of_angular_cap _ _ _ _ hdirection (horiginal.trans hcap)
    (originalConicDetector_support hηoriginal hroriginal hη)

/-- A single positive user cap simultaneously enforces the scalar plateau,
carrier plateau and the original detector direction support. Further minima
with the strong inverse/raw-wave cap preserve every constraint. -/
theorem exists_common_scalar_source_cap {n : ℕ}
    (χ : ContDiffBump (0 : Euclidean n))
    {ηscalar : Euclidean (n - 1)} (hηscalar : ηscalar ≠ 0)
    {rscalar carrierCap sliceCap : ℝ} (hrscalar : 0 < rscalar)
    (hcarrierCap : 0 < carrierCap) (hsliceCap : 0 < sliceCap) :
    ∃ cap > (0 : ℝ), cap ≤ χ.rIn ∧ cap ≤ carrierCap ∧ cap ≤ sliceCap ∧
      cap ≤ angularWidth ηscalar rscalar := by
  let cap := min χ.rIn (min carrierCap (min sliceCap (angularWidth ηscalar rscalar)))
  refine ⟨cap, lt_min χ.rIn_pos (lt_min hcarrierCap
    (lt_min hsliceCap (angularWidth_spec hηscalar hrscalar).1)),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

end JanetCartan.PhysicalSampling
