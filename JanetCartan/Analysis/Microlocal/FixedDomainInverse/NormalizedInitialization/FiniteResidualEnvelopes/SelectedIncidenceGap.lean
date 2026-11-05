module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.IncidenceSourceGap
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectedConstruction.FullSource.Supports
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.PrimaryGradientBand

/-!
# The supplied signed source gap for the exact selected multiplier

The physical source momentum and the actual doubled frequency collar are
pulled through the same orthogonal coordinate permutation. The radius change
inside the multiplier is positive and changes neither normalized direction.
The supplied positive or negative incidence capture therefore produces exactly
the geometric hypothesis used by `SelectedInactive`, on the same selected
family and with one coefficient margin before all histories and accuracies.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open ActualCarriers CurrentFullPhase HamiltonPhase FrozenMenu LeadingWave.FullModulation
open CompatibleResponse ResponseTransfer.RetainedFactors NormedSpace
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAssembly RegularSector.FinitePdo
variable {d : ℕ} {P : Patch (d+1)} {Uref : Set (Euclidean (d+1))} {hUref : IsOpen Uref}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Coeff" => Fin (d+1) → MetricTensor (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
  {Aref : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}

private theorem primaryCoordinates_normalized_dist
    (i : Fin (d+1)) (v w : E) :
    dist (NormedSpace.normalize (primaryCoordinateChange i v)) (NormedSpace.normalize (primaryCoordinateChange i w)) =
      dist (NormedSpace.normalize v) (NormedSpace.normalize w) := by
  have hn (z : E) : NormedSpace.normalize (primaryCoordinateChange i z) =
      primaryCoordinateChange i (NormedSpace.normalize z) := by
    simp only [NormedSpace.normalize,norm_primaryCoordinateChange,map_smul]
  rw [hn,hn,dist_eq_norm,← map_sub,norm_primaryCoordinateChange,← dist_eq_norm]

/-- The actual selected endpoint/retarded multiplier has exactly the supplied
physical angular gap, for either sign of the full source phase. Its original
`2*threshold` collar and the same coordinate map are retained
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem selected_signed_source_angular_gap
    (T : PatchQuantitativeFamily P Uref hUref)
    (f : ActualMaskFamily Ω x RQ Aref K₀ M) (p : f.centers)
    {threshold : ℝ} (ht : 0 < threshold) (negative : Bool)
    (Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q Uref ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
    (y ξ : E) (c : Par)
    (hy : ((primaryCoordinateChange (f.chart p).index).symm y,c.2) ∈ phaseDomain T)
    (hξ : ξ ∈ tsupport (selectedEndpointMultiplier f p threshold))
    {gap : ℝ}
    (hgap : ∀ η ∈ tsupport (conicMask (f.angularMask p)),
      gap ≤ dist (NormedSpace.normalize (if negative then
        -phaseGradient T Q ((primaryCoordinateChange (f.chart p).index).symm y) c.2
        else phaseGradient T Q ((primaryCoordinateChange (f.chart p).index).symm y) c.2))
        (NormedSpace.normalize η)) :
    gap ≤ dist (NormedSpace.normalize (gradient (fun z ↦ if negative then
      -(T.fullSourcePhaseInCoordinates (f.chart p).index Q z c)
      else T.fullSourcePhaseInCoordinates (f.chart p).index Q z c) y)) (NormedSpace.normalize ξ) := by
  let e := primaryCoordinateChange (f.chart p).index
  let η := e.symm ξ
  let g := if negative then -phaseGradient T Q (e.symm y) c.2
    else phaseGradient T Q (e.symm y) c.2
  have hg : gradient (fun z ↦ if negative then
      -(T.fullSourcePhaseInCoordinates (f.chart p).index Q z c)
      else T.fullSourcePhaseInCoordinates (f.chart p).index Q z c) y = e g := by
    have hh := T.fullSourcePhaseInCoordinates_gradient (f.chart p).index Q (x := y) (c := c) hy
    cases negative
    · exact hh
    · change (InnerProductSpace.toDual ℝ E).symm
        (fderiv ℝ (-(fun z ↦ T.fullSourcePhaseInCoordinates (f.chart p).index Q z c)) y) =
          e (-phaseGradient T Q (e.symm y) c.2)
      have hfd : fderiv ℝ
          (-(fun z : E ↦ T.fullSourcePhaseInCoordinates (f.chart p).index Q z c)) y =
          -fderiv ℝ (fun z : E ↦ T.fullSourcePhaseInCoordinates (f.chart p).index Q z c) y :=
        fderiv_neg
      rw [hfd]
      calc
        _ = -(InnerProductSpace.toDual ℝ E).symm
            (fderiv ℝ (fun z ↦ T.fullSourcePhaseInCoordinates (f.chart p).index Q z c) y) :=
          map_neg (InnerProductSpace.toDual ℝ E).symm _
        _ = e (-phaseGradient T Q (e.symm y) c.2) := by
          change -gradient (fun z ↦ T.fullSourcePhaseInCoordinates (f.chart p).index Q z c) y = _
          rw [hh,map_neg]
  have hη : η ∈ tsupport (dilatedConicMask (f.angularMask p) (2*threshold)) :=
    selectedEndpointMultiplier_incidence_support f p threshold (by
      simpa only [η,e,ContinuousLinearEquiv.apply_symm_apply] using hξ)
  have hcut : (2*threshold)⁻¹ • η ∈ tsupport (conicMask (f.angularMask p)) :=
    tsupport_comp_subset_preimage (conicMask (f.angularMask p))
      (continuous_id.const_smul ((2*threshold)⁻¹)) hη
  have hphysical : gap ≤ dist (NormedSpace.normalize g) (NormedSpace.normalize η) := by
    have hh := hgap _ hcut
    simpa only [normalize_smul_of_pos (inv_pos.mpr (by positivity : 0 < 2*threshold))] using hh
  calc
    gap ≤ dist (NormedSpace.normalize g) (NormedSpace.normalize η) := hphysical
    _ = dist (NormedSpace.normalize (e g)) (NormedSpace.normalize (e η)) :=
      (primaryCoordinates_normalized_dist (f.chart p).index g η).symm
    _ = _ := by rw [hg]; simp only [η,ContinuousLinearEquiv.apply_symm_apply]

/-- A fixed cutoff from the ORIGINAL supplied signed incidence selector
has the precise gap for the original selected multiplier and coordinate
phase. The same coefficient margin works at every derivative order and
accuracy; the actual history constructor attains it once by increasing its
common initial threshold (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_selected_signed_incidence_cutoff_and_gap
    (T : PatchQuantitativeFamily P Uref hUref)
    (f : ActualMaskFamily Ω x RQ Aref K₀ M) (p : f.centers)
    {X : Set E} {Csrc V : Set Par}
    (hX : IsCompact X) (hXne : X.Nonempty) (hCsrc : IsCompact Csrc)
    (hsource : X ×ˢ Csrc ⊆ domain T) (hV : IsOpen V)
    (negative : Bool) {margin : ℝ} (hmargin : 0 < margin)
    (hcapture : ∀ Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q Uref ∧
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold}, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < margin →
      ∀ y ∈ X, ∀ c ∈ Csrc, ∀ scale : ℝ, 0 < scale →
        scale • (if negative then -phaseGradient T Q y c.2 else phaseGradient T Q y c.2)
          ∈ tsupport (conicMask (f.angularMask p)) → c ∈ V) :
    ∃ χ : Par → ℝ, ContDiff ℝ ∞ χ ∧ (∀ c, χ c ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ margin ∧ δ ≤ T.family.threshold ∧
    ∃ gap : ℝ, 0 < gap ∧
      ∀ Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q Uref ∧
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold}, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
      ∀ threshold : ℝ, 0 < threshold → ∀ y : E,
        (primaryCoordinateChange (f.chart p).index).symm y ∈ X →
      ∀ c ∈ Csrc, c ∈ tsupport (fun c ↦ 1-χ c) →
      ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
        gap ≤ dist (NormedSpace.normalize (gradient (fun z ↦ if negative then
          -(T.fullSourcePhaseInCoordinates (f.chart p).index Q z c)
          else T.fullSourcePhaseInCoordinates (f.chart p).index Q z c) y)) (NormedSpace.normalize ξ) := by
  have hchoose : ∃ χ : Par → ℝ, ContDiff ℝ ∞ χ ∧ (∀ c, χ c ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ margin ∧ δ ≤ T.family.threshold ∧
      ∃ gap : ℝ, 0 < gap ∧
        ∀ Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q Uref ∧
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold}, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
        ∀ y ∈ X, ∀ c ∈ Csrc, c ∈ tsupport (fun c ↦ 1-χ c) →
        ∀ η ∈ tsupport (conicMask (f.angularMask p)),
          gap ≤ dist (NormedSpace.normalize (if negative then -phaseGradient T Q y c.2
            else phaseGradient T Q y c.2)) (NormedSpace.normalize η) := by
    cases negative
    · exact @exists_full_source_incidence_cutoff_and_gap d P Uref hUref T X Csrc V
        hX hXne hCsrc hsource hV (f.angularMask p) margin hmargin hcapture
    · exact @exists_negative_full_source_incidence_cutoff_and_gap d P Uref hUref T X Csrc V
        hX hXne hCsrc hsource hV (f.angularMask p) margin hmargin hcapture
  obtain ⟨χ,hχ,hrange,hcompact,hsχ,δ,hδ,hδm,hδT,gap,hgap,hseparate⟩ := hchoose
  refine ⟨χ,hχ,hrange,hcompact,hsχ,δ,hδ,hδm,hδT,gap,hgap,?_⟩
  intro Q hQ threshold ht y hy c hc hinactive ξ hξ
  have hdomFull : ((primaryCoordinateChange (f.chart p).index).symm y,c) ∈ domain T :=
    hsource (a := ((primaryCoordinateChange (f.chart p).index).symm y,c)) ⟨hy,hc⟩
  have hdom : ((primaryCoordinateChange (f.chart p).index).symm y,c.2) ∈ phaseDomain T := hdomFull
  have hsep := hseparate Q hQ ((primaryCoordinateChange (f.chart p).index).symm y) hy c hc hinactive
  have hfinal := @selected_signed_source_angular_gap d P Uref hUref Ω x RQ M Aref K₀
    T f p threshold ht negative Q y ξ c hdom hξ gap hsep
  exact hfinal

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
