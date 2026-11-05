module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.PuncturedSupport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalLabels

/-!
# The actual retained detector projection

For `app:ch_background:prop:bg-positive`, project the entire original conic
mask onto its carrier labels. Its radial variable is unbounded, but its
carrier projection is exactly the existing compact `carrierSupport`.
`RetainedRowGeometry.exists_common_geometry_in_cell` supplies `houter` below;
its incidence root need not be the scalar/ODE center. The original working
cylinder supplies the scalar-domain containment, without identifying centers.
The consumer is `ExternalWeights.exists_externalCutoff_in_retained_cell`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.RetainedAssembly.ExternalWeights
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction.TransportSymbol FullPhaseCharts.ActualComparison
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow.LeadingPrimitive
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry

variable {n : ℕ}

/-- The literal projection of the full conic detector support, including all
nonzero radial frequencies (`app:ch_background:prop:bg-positive`). -/
def maskCarrierProjection (zRoot : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a : ℝ) : Set CarrierParameter :=
  (fun p : InputVariables n ↦ p.2.1) '' conicMaskSupport zRoot ηb r a

/-- The projection is the original closed carrier support, not a support
chosen for a new detector (`app:ch_background:defn:bg-row`). -/
theorem maskCarrierProjection_eq {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) :
    maskCarrierProjection zRoot ηb r a = carrierSupport zRoot (r := a) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact hp.2.1
  · intro z hz
    refine ⟨((0, 0), (z, ηb)), ?_, rfl⟩
    exact ⟨⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩,
      hz, hηb, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hηb),
      mem_closedBall_self (half_pos (angularWidth_spec hηb hr).1).le⟩

/-- Compactness follows from the actual masks even though the full conic
support is radially unbounded (`app:ch_background:prop:bg-positive`). -/
theorem maskCarrierProjection_compact {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) :
    IsCompact (maskCarrierProjection zRoot ηb r a) := by
  rw [maskCarrierProjection_eq hηb hr ha]
  exact carrierSupport_compact zRoot

/-- The same compact projection in the original three Euclidean scalar
labels (`app:ch_background:prop:bg-positive`). -/
theorem euclidean_maskCarrierProjection_compact
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) :
    IsCompact (parameter '' maskCarrierProjection zRoot ηb r a) :=
  (maskCarrierProjection_compact hηb hr ha).image parameter.continuous

/-- The open zero-position carrier slice of the supplied retained cell
(`app:ch_background:prop:bg-positive`). -/
def carrierNeighborhood (E : Set (Euclidean n × CarrierParameter)) : Set CarrierParameter :=
  (fun z ↦ ((0 : Euclidean n), z)) ⁻¹' E

/-- Openness uses the existing cell, with no reselection of scalar charts
(`app:ch_background:prop:bg-positive`). -/
theorem carrierNeighborhood_open {E : Set (Euclidean n × CarrierParameter)} (hE : IsOpen E) :
    IsOpen (carrierNeighborhood E) :=
  hE.preimage (continuous_const.prodMk continuous_id)

/-- The retained outer coefficient-domain containment puts the entire
original detector projection in the supplied carrier neighborhood. The
radius inequalities are exported by `exists_common_geometry_in_cell`
(`app:ch_background:prop:bg-positive`, `app:ch_background:eq:bg-Psi`). -/
theorem maskCarrierProjection_subset_carrierNeighborhood
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a rm am : ℝ}
    (ham : 0 < am) (hamr : am ≤ rm) (hrm : rm ≤ r) (hama : am ≤ a)
    {E : Set (Euclidean n × CarrierParameter)}
    (houter : coefficientDomain zRoot r (6 * a) ⊆ E) :
    maskCarrierProjection zRoot ηb rm am ⊆ carrierNeighborhood E := by
  rintro _ ⟨p, hp, rfl⟩
  apply houter
  exact ⟨mem_ball_self (by linarith),
    closedBall_subset_ball (by linarith) hp.2.1.1,
    closedBall_subset_ball (by linarith) hp.2.1.2⟩

/-- The same retained working-ball geometry places its carrier neighborhood
strictly inside the ORIGINAL scalar domain centered at `zCell`. The root used
in `maskCarrierProjection` is unrestricted. This instantiates the label-range
producer rather than assuming a cutoff plateau
(`app:ch_background:prop:bg-positive`, `app:ch_waves:eq:joint-tame`). -/
theorem carrierNeighborhood_subset_original_scalar_domain
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (zCell : Euclidean 3)
    {L σ τ : ℝ} (hL : 0 < L) (hσ : 0 < σ)
    {E : Set (Euclidean n × CarrierParameter)}
    (hgraph : MapsTo (carrierGraph T) E
      (ball ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) σ))
    (hworking : closedBall ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) (2 * σ) ⊆
      (coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zCell, T.reference.spatialPatch zCell)) (L / 64))) :
    carrierNeighborhood E ⊆ parameter ⁻¹' ball zCell (L / 8) := by
  intro z hz
  have h := (densityCoordinates_mem_original_cylinder T zCell hσ hgraph hworking hz).2
  change ((adaptedCoordinates T.data.adapted (0 : Euclidean n)).2, parameter z) ∈
    closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64) at h
  have hd := (max_le_iff.mp (show
    max (dist (adaptedCoordinates T.data.adapted (0 : Euclidean n)).2 0)
      (dist (parameter z) zCell) ≤ L / 64 by simpa only [mem_closedBall, Prod.dist_eq] using h)).2
  exact (mem_ball.mpr (hd.trans_lt (by linarith)))

end JanetCartan.RetainedAssembly.ExternalWeights
