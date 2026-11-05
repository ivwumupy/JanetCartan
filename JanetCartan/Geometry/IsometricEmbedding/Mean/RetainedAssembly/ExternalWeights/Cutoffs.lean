module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.ExternalWeights.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.ContinuousDensity
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# External cutoffs chosen on the supplied retained masks

The compact/open construction in `app:ch_background:prop:bg-positive` takes
place before the source mean, immersion, initial scalar, raw input, or density.
It can retain an additional prescribed compact plateau at that selection
point. Once a caller has selected a cutoff, the `fixedCutoff_*` deductions
use precisely that function. In particular no fixed seed weight is silently
replaced by a cutoff centered at a different incidence root.

Consumers: `PositiveBackground.uncorrectedDensity_core_cancellation` and the
same-family mean/source assembly in `RetainedAssembly.NormalizedMeanSource`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RetainedAssembly.ExternalWeights
open ContinuumRow CanonicalCarrier CanonicalConic

variable {n N : ℕ}

/-- Choose a smooth cutoff near the ENTIRE original detector projection,
preserving a prescribed compact plateau `K₀` at the original selection point.
The containment `houter` and radius inequalities are outputs of
`RetainedRowGeometry.exists_common_geometry_in_cell`; no compactness or
plateau of the detector projection is assumed
(`app:ch_background:prop:bg-positive`). -/
theorem exists_externalCutoff_in_retained_cell
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a rm am : ℝ}
    (hηb : ηb ≠ 0) (hrm : 0 < rm) (ham : 0 < am)
    (hamr : am ≤ rm) (hrmr : rm ≤ r) (hama : am ≤ a)
    {E : Set (Euclidean n × CarrierParameter)} (hE : IsOpen E)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ E)
    {K₀ : Set CarrierParameter} (hK₀ : IsCompact K₀)
    (hK₀E : K₀ ⊆ carrierNeighborhood E) :
    ∃ χ : CarrierParameter → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ carrierNeighborhood E ∧
      K₀ ∪ maskCarrierProjection zRoot ηb rm am ⊆ interior {z | χ z = 1} := by
  have hK := hK₀.union (maskCarrierProjection_compact (zRoot := zRoot) hηb hrm ham)
  have hKE := union_subset hK₀E
    (maskCarrierProjection_subset_carrierNeighborhood (ηb := ηb) ham hamr hrmr hama houter)
  obtain ⟨V, hV, hKV, hVE, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK (carrierNeighborhood_open hE) hKE
  obtain ⟨L, _hL, hLc, hKL, hLV⟩ := exists_compact_closed_between hK hV hKV
  obtain ⟨χ, hχ, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV hLc hLV
  have hs : tsupport χ = closure V := by rw [tsupport, hχsupport]
  refine ⟨χ, hχ, fun z ↦ hχrange (mem_range_self z),
    (show IsCompact (tsupport χ) from hs.symm ▸ hVc), hs.symm ▸ hVE, ?_⟩
  exact hKL.trans (interior_mono (fun z hz ↦ (hχone z).mp hz))

/-- A previously selected cutoff is kept literally. Its geometric plateau,
as constructed above, covers the full original angular mask. This is exactly
the `hχ` input of `PositiveBackground.uncorrectedDensity_core_cancellation`
(`app:ch_background:eq:bg-density-twice`). -/
theorem fixedCutoff_one_of_angularMask
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {rm am : ℝ}
    (hηb : ηb ≠ 0) (hrm : 0 < rm) (ham : 0 < am)
    (χ : CarrierParameter → ℝ)
    (hplateau : maskCarrierProjection zRoot ηb rm am ⊆ interior {z | χ z = 1})
    {z : CarrierParameter} {η : Euclidean (n - 1)}
    (h : angularMask zRoot (NormedSpace.normalize ηb) ham
      (angularWidth_spec hηb hrm).1 z η ≠ 0) : χ z = 1 := by
  obtain ⟨hs, hv, _⟩ := angularMask_nonzero zRoot (NormedSpace.normalize ηb) ham
    (angularWidth_spec hηb hrm).1 h
  apply interior_subset (hplateau ?_)
  rw [maskCarrierProjection_eq hηb hrm ham]
  exact ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩

/-- Exact absorption for every original initial position and every raw input,
with factor four and the supplied data's unchanged high-pass mask. The
geometric plateau is used to prove the identity
(`app:ch_background:eq:bg-density-four`, `eq:bg-density-twice`). -/
theorem fixedCutoff_sq_mul_initialDensity
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {rm am : ℝ}
    (hηb : ηb ≠ 0) (hrm : 0 < rm) (ham : 0 < am)
    (χ : CarrierParameter → ℝ)
    (hplateau : maskCarrierProjection zRoot ηb rm am ⊆ interior {z | χ z = 1})
    (d : CarrierData n N)
    (hd : d.angularCutoff = angularMask zRoot (NormedSpace.normalize ηb) ham
      (angularWidth_spec hηb hrm).1)
    (f : CarrierVariable n → ℂ) (p : CarrierVariable n) :
    χ p.1 ^ 2 * UncutDensity.initialDensity d 4 f p = UncutDensity.initialDensity d 4 f p := by
  apply UncutDensity.externalWeight_mul_initialDensity
  intro z η h
  rw [hd] at h
  exact fixedCutoff_one_of_angularMask hηb hrm ham χ hplateau h

/-- The SAME fixed cutoff also absorbs a continuous representative of this
uncut density at every point, hence at every actual transport footpoint
(`app:ch_background:eq:bg-density-twice`). -/
theorem fixedCutoff_sq_mul_continuousDensity
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {rm am : ℝ}
    (hηb : ηb ≠ 0) (hrm : 0 < rm) (ham : 0 < am)
    (χ : CarrierParameter → ℝ) (hχ : Continuous χ)
    (hplateau : maskCarrierProjection zRoot ηb rm am ⊆ interior {z | χ z = 1})
    (d : CarrierData n N)
    (hd : d.angularCutoff = angularMask zRoot (NormedSpace.normalize ηb) ham
      (angularWidth_spec hηb hrm).1)
    (f : CarrierVariable n → ℂ) {v : CarrierVariable n → ℝ} (hv : Continuous v)
    (heq : UncutDensity.initialDensity d 4 f =ᵐ[carrierMeasure n] v)
    (p : CarrierVariable n) : χ p.1 ^ 2 * v p = v p := by
  apply PositiveBackground.externalWeight_mul_continuousRepresentative d χ hχ _ 4 f hv heq p
  intro z η h
  rw [hd] at h
  exact fixedCutoff_one_of_angularMask hηb hrm ham χ hplateau h

end JanetCartan.RetainedAssembly.ExternalWeights
