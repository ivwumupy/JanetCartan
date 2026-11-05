module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CappedLocalChart
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.RetainedCollars
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.Selection

/-!
# One finite original incidence family before reference selection

A fixed coefficient cap controls the actual stationary branches. Apply the
original finite pencil selection and retained algebraic collars to the same
charts, source masks and full parameter incidences. All family choices precede
the common reference and its history. The later admission must use this family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu
open Characteristic Characteristic.AlgebraicChart Characteristic.RootFamily
open Characteristic.ResidualCoordinates Characteristic.AlgebraicSymbols
open Characteristic.EvolutionIntegral Characteristic.AmplitudeBounds
open Characteristic.ConicPhase Characteristic.EvolutionIntegral.KernelIdentification
open FiniteMasks FiniteMasks.ActualFamily
open HamiltonPhase CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ArbitraryAccuracy
variable {d : ℕ} {ι : Type*} [Finite ι] {K : Set (Euclidean (d + 1))}
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (P : ι → Patch (d + 1)) (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
local notation "E" => Euclidean (d + 1)
local notation "TC" => Characteristic.TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "FrozenZero" =>
  Subtype (fun ξ : E ↦ ξ ∈ K ∧ determinant (cubeStress (d + 1)) ξ = 0)

open FullSourceStationary

/-- Select the protected finite family before the reference by applying
the actual source-incidence stationary construction at the fixed coefficient
cap. The same algebraic collars and original parameter supports are retained
for supplied-family operator continuations; no family is independently identified
(`app:ch_regular_base:thm:sector`, `app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_actualMaskFamily_with_full_source_incidence_radii_of_coefficient_cap
    (hframe : ∀ j, closedBall (0 : E) (T j).data.localReference.stateRadius ⊆ U)
    (Csrc : ι → Set Param) (hCsrc : ∀ j, IsCompact (Csrc j))
    (hcsrc : ∀ j c, c ∈ Csrc j →
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius)
    (Xsrc : ι → Set E) (hXsrc : ∀ j, IsCompact (Xsrc j))
    (hsource : ∀ j, Xsrc j ×ˢ Csrc j ⊆ LeadingWave.FullModulation.domain (T j))
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hKprimary : ∀ j, closedBall x RQ ⊆ ball 0 (T j).physicalRadius)
    (hK : IsCompact K) (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant (cubeStress (d + 1)) ξ = 0 →
      fderiv ℝ (determinant (cubeStress (d + 1))) ξ ≠ 0)
    {M aperture gap radius : ℝ} (hM : 0 ≤ M) (hAp : 0 < aperture) (hgap : 0 < gap)
    (hApξ : ∀ ξ ∈ K, ∀ i, |ξ i| < aperture)
    {coefficientCap : ℝ} (hcoefficientCap : 0 ≤ coefficientCap) :
    ∃ f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K M, (∀ p : f.centers,
      let c := f.chart p
      let ξ := p.val.val
      c.bufferRadius ≤ c.targetRadius ∧ c.maskRadius ≤ c.bufferRadius / 4 ∧
      RootBuffer c.index c.row c.col (cubeStress (d + 1)) ξ c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap ∧
      MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
        (closedBall x RQ) ∧
    ∃ evolutionTime speedGap rootSize rootCost,
      LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost ∧
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
      a < c.coefficientRadius ∧ b < min c.coefficientRadius c.rootRadius ∧
      let KA := closedBall (cubeStress (d + 1)) a
      let Kη := closedBall (coordinateSplit c.index ξ).2 b
      let x' := (physicalCoordinates c.index).symm x
      IsCompact KA ∧ IsCompact Kη ∧
      KA ⊆ ball (cubeStress (d + 1)) c.coefficientRadius ∧
      Kη ⊆ ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius) ∧
      (∀ p ∈ ball (cubeStress (d + 1)) c.coefficientRadius ×ˢ
        ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius),
        ContDiffAt ℝ ∞ c.root p) ∧
      (∀ p ∈ KA ×ˢ Kη, ContDiffAt ℝ ∞ c.root p) ∧
    ∃ bound > (0 : ℝ),
      (∀ p ∈ KA ×ˢ Kη,
        ‖coefficientRootPencil (coordinateSplit c.index) c.root p‖ ≤ bound ∧
        ‖pencil p.1 ((coordinateSplit c.index).symm (1, 0))‖ ≤ bound ∧
        (coefficientRootPencil (coordinateSplit c.index) c.root p).det = 0 ∧
        c.minorGap ≤ |(coefficientRootPencil (coordinateSplit c.index) c.root p).adjugate c.row c.col| ∧
        c.transportGap ≤ |minorTransportCoefficient
          (coefficientRootPencil (coordinateSplit c.index) c.root p)
          (pencil p.1 ((coordinateSplit c.index).symm (1, 0))) c.row c.col|) ∧
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      (∀ p ∈ minorCoefficientClass c.row c.col bound c.minorGap c.transportGap,
        ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det|) ∧
      (minorCoefficientClass c.row c.col bound c.minorGap c.transportGap ×ˢ
        closedBall (0 : ℝ) ε ⊆ minorComplementDomain c.row c.col) ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ c.coefficientRadius ∧
      f.coefficientRadius ≤ a' ∧
    ∃ V : Set E, IsOpen V ∧ ξ ∈ V ∧ V ⊆ c.angularNeighborhood ∧
      tsupport (f.angularMask p) ⊆ V ∧
      (∀ ζ ∈ V, ∀ t : ℝ, 0 < t → t • ζ ∈ V) ∧
    ∃ Λ > (0 : ℝ),
      (∀ ζ ∈ V,
        let ζ' := (physicalCoordinates c.index).symm ζ
        0 < c.radialSection (spatialPart ζ') ∧
        spatialPart (normalizeCovector c.radialSection ζ') ∈ Kη ∧
        ‖normalizeCovector c.radialSection ζ'‖ ≤ Λ ∧
        ∀ A ∈ closedBall (cubeStress (d + 1)) a',
          |normalizeCovector c.radialSection ζ' 0 -
            c.root (A, spatialPart (normalizeCovector c.radialSection ζ'))| ≤ ε) ∧
      ∀ Q : E → Coeff, MapsTo Q Ω (closedBall (cubeStress (d + 1)) a') →
        (∀ β : E → ℂ, tsupport β ⊆ V →
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹' Ω) ε (β ∘ physicalCoordinates c.index) ∧
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹'
              (rootPhysicalPosition (coordinateSplit c.index) '' tsupport c.sourceMask))
            ε (β ∘ physicalCoordinates c.index) ∧
          (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
            (normalizeCovector c.radialSection '' tsupport (β ∘ physicalCoordinates c.index)) ⊆
            complementDomain c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col (fieldDomain (coordinateSplit c.index) Ω c.radialSection
                (coordinateSplit c.index ξ).2 c.coefficientRadius)) ∧
        (ContDiffOn ℝ ∞ Q Ω → ∀ ζ ∈ V,
          let ζ' := normalizeCovector c.radialSection ((physicalCoordinates c.index).symm ζ)
          (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') y) ∧
          ∀ m, cNorm (closedBall x' RQ) m
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') ≤ C m * (1 + cNorm (closedBall x RQ) m Q))) ∧
    ∃ τ : f.centers → ℝ, (∀ center, 0 < τ center) ∧
    ∀ center : f.centers,
      let chart := f.chart center
      let ξ := center.val.val
      chart.maskRadius ≤ τ center ∧
      Icc (0 : ℝ) (3 * chart.maskRadius / 4) ⊆ Ioo (-2 * τ center) (2 * τ center) ∧
    ∃ εcarrier > (0 : ℝ), εcarrier ≤ chart.rootRadius ∧ 4 * εcarrier ≤ chart.targetRadius ∧
    let z := ((coordinateSplit chart.index x).1, ((coordinateSplit chart.index x).2,
      (coordinateSplit chart.index ξ).2))
    MapsTo (primaryCoordinateChange chart.index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (elapsedPhysicalBox z (εcarrier / 2)) ∧
    ∀ j : ι,
    ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      (∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius) ∧
    ∃ δ > (0 : ℝ), δ ≤ (T j).family.threshold ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
          scale • LeadingWave.FullModulation.phaseGradient (T j) Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.conicMask (f.angularMask center)) → c ∈ V) ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
        ∀ L : ℝ, 0 < L →
          scale • LeadingWave.FullModulation.phaseGradient (T j) Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.dilatedConicMask (f.angularMask center) L) → c ∈ V) ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ InvBound > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z εcarrier O
      let U₀ := elapsedPhysicalBox z (εcarrier / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture gap radius ⊆ O ∧
      (∀ c ∈ closure V, primaryCoordinateChange chart.index ((T j).reference.covector (0, c.2)) ∈ O) ∧
      ∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 4 Q.1 ≤ coefficientCap →
        cNorm (closedBall x RQ) 4 Q.1 ≤ coefficientCap →
        cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) chart.targetRadius ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) chart.targetRadius) m (twoTimePhase C) ≤
          chart.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q.1)) →
      a ≤ chart.rootRadius →
      closedBall z chart.rootRadius ⊆ fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius →
      (∀ w ∈ fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius,
        ∀ t : ℝ, 0 < t → fieldRoot (coordinateSplit chart.index) Q.1 chart.root (w.1, (w.2.1, t • w.2.2)) =
          t * fieldRoot (coordinateSplit chart.index) Q.1 chart.root w) →
      (∀ v ∈ C.target, twoTimeState Φ (C.symm v) ∈
          fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius ∧
        (twoTimeState Φ (C.symm v)).1 = v.1) →
      (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C)
        (twoTimePhaseDifferential (fieldRoot (coordinateSplit chart.index) Q.1 chart.root) Φ C v) v) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase chart.radialSection C) ((T j).fullSourcePhaseInCoordinates chart.index Q))
          ((Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ (T j).fullSourcePhaseInCoordinates chart.index Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            ((T j).fullSourcePhaseInCoordinates chart.index Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            ((T j).fullSourcePhaseInCoordinates chart.index Q) (p, κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ (T j).fullSourcePhaseInCoordinates chart.index Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
              ((T j).fullSourcePhaseInCoordinates chart.index Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ InvBound) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈ fullSourceSignedCarrier z εcarrier (closure V) O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain chart.radialSection C.target := by
  classical
  have hlocal (p : FrozenZero) :=
    PatchQuantitativeFamily.exists_localChart_with_full_source_incidence_radii_of_coefficient_cap
      P T hframe Csrc hCsrc hcsrc Xsrc hXsrc hsource hΩ x hRQ hKΩ hKprimary
      (fun hz ↦ hKzero (hz ▸ p.property.1)) p.property.2
      (hregular p.val p.property.1 p.property.2) hM hAp hgap (radius := radius)
      (hApξ p.val p.property.1) hcoefficientCap
  choose α hα τ hτ hmasks using hlocal
  have hc (p : FrozenZero) := hmasks p 1 zero_lt_one
  choose charts hcb hcm hcap hmaskτ hinterval hroot hsourceMask
    evolutionTime speedGap rootSize rootCost hprotection
    εcarrier hεcarrier hεL hεb hstationary using hc
  have hcollars (p : FrozenZero) := exists_algebraic_collar_on_retained_localChart
    hΩ hRQ hKΩ (charts p) (hroot p) (hsourceMask p)
  choose a ha b hb hac hbc hKA hKη hKAopen hKηopen hHopen hH bound hbound hprimitive
    ε hε δ hδ C hC hgapAlgebraic hdomain a' ha' ha'a ha'c
    V hV hcenter hVc hVcone Λ hΛ hcollar hbudgets using hcollars
  have hnormalize : ContinuousOn (NormedSpace.normalize : E → E) {ζ : E | ζ ≠ 0} := by
    intro ζ hζ
    exact ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hζ)).smul
      continuousAt_id).continuousWithinAt
  let Vn : FrozenZero → Set E := fun p ↦ V p ∩
    ({ζ : E | ζ ≠ 0} ∩ NormedSpace.normalize ⁻¹'
      ball (NormedSpace.normalize p.val) (α p))
  have hVn (p : FrozenZero) : IsOpen (Vn p) :=
    (hV p).inter (hnormalize.isOpen_inter_preimage isOpen_ne isOpen_ball)
  have hcenterVn (p : FrozenZero) : p.val ∈ Vn p := by
    change p.val ∈ V p ∧ p.val ≠ 0 ∧
      NormedSpace.normalize p.val ∈ ball (NormedSpace.normalize p.val) (α p)
    refine ⟨hcenter p, ?_, mem_ball_self (hα p)⟩
    intro hz
    exact hKzero (hz ▸ p.property.1)
  obtain ⟨s, χ, ε₀, hε₀, δ₀, hδ₀, hχ, hrange, hcompact, hsupp, hsum, hstable⟩ :=
    exists_finite_pencil_masks (cubeStress (d + 1)) hK Vn hVn (by
      intro ξ hξ hp
      exact ⟨⟨ξ, hξ, hp⟩, hcenterVn ⟨ξ, hξ, hp⟩⟩)
  let chart : ∀ p : s, LocalChart Ω x RQ (cubeStress (d + 1)) p.val.val M := fun p ↦ charts p.val
  have hsuppV (p : s) : tsupport (χ p) ⊆ V p.val := fun ζ hζ ↦ (hsupp p hζ).1
  have hsuppAngular (p : s) : tsupport (χ p) ∩ sphere (0 : E) 1 ⊆
      closedBall (NormedSpace.normalize p.val.val) (α p.val) := by
    intro ζ hζ
    have hn : ‖ζ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hζ.2
    have hball := (hsupp p hζ.1).2.2
    simp only [mem_preimage, NormedSpace.normalize_eq_self_of_norm_eq_one hn] at hball
    exact ball_subset_closedBall hball
  obtain ⟨ε₁, hε₁, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : s ↦ (0 : ℝ)) (y := fun p ↦ a' p.val) (fun p ↦ ha' p.val)
  let z : s → RootState (Euclidean d) := fun p ↦
    ((coordinateSplit (chart p).index x).1, ((coordinateSplit (chart p).index x).2,
      (coordinateSplit (chart p).index p.val.val).2))
  let Wphysical : Set E := ball x RQ ∩ ⋂ p : s,
    (chart p).physicalNeighborhood ∩ primaryCoordinateChange (chart p).index ⁻¹'
      elapsedPhysicalBox (z p) (εcarrier p.val / 2)
  have hWphysical : IsOpen Wphysical := isOpen_ball.inter
    (isOpen_iInter_of_finite fun p ↦ (chart p).isOpen_physicalNeighborhood.inter
      ((isOpen_elapsedPhysicalBox _ _).preimage (primaryCoordinateChange (chart p).index).continuous))
  have hxWphysical : x ∈ Wphysical := by
    refine ⟨mem_ball_self hRQ, mem_iInter.mpr fun p ↦
      ⟨(chart p).center_mem_physicalNeighborhood, ?_⟩⟩
    change primaryCoordinateChange (chart p).index x ∈
      elapsedPhysicalBox (z p) (εcarrier p.val / 2)
    constructor <;> exact mem_ball_self (half_pos (hεcarrier p.val))
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hWphysical x hxWphysical
  have hball : closedBall x (4 * (r / 8)) ⊆ Wphysical :=
    (closedBall_subset_ball (by linarith : 4 * (r / 8) < r)).trans hrW
  have hsupp' (p : s) : tsupport (χ p) ⊆ (chart p).angularNeighborhood :=
    (hsuppV p).trans (hVc p.val)
  obtain ⟨angular, L, hL, hang, hangp, _⟩ := exists_common_physical_radial_masks
    (fun p : s ↦ p.val.val) chart χ hsupp'
  obtain ⟨input, output, hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, _⟩ :=
    exists_common_physical_masks x (show 0 < r / 8 by positivity)
  have hphysical (p : s) : MapsTo (primaryCoordinateChange (chart p).index)
      (tsupport input ∪ tsupport output) (elapsedPhysicalBox (z p) (εcarrier p.val / 2)) := by
    intro y hy
    have hyball : y ∈ closedBall x (4 * (r / 8)) := by
      rcases hy with hy | hy
      · exact closedBall_subset_closedBall (by linarith : 3 * (r / 8) ≤ 4 * (r / 8))
          (ball_subset_closedBall (his hy))
      · exact closedBall_subset_closedBall (by linarith : 2 * (r / 8) ≤ 4 * (r / 8))
          (ball_subset_closedBall (hos hy))
    exact (mem_iInter.mp (hball hyball).2 p).2
  have hsmall' (p : s) : min ε₀ ε₁ ≤ a' p.val :=
    (min_le_right _ _).trans (by simpa using (hsmall p).le)
  refine ⟨⟨s, chart, χ, angular, min ε₀ ε₁, δ₀, r / 8, L, input, output,
    lt_min hε₀ hε₁, hδ₀, by positivity, hL,
    (fun p ↦ (hsmall' p).trans (ha'c p.val)),
    (fun y hy ↦ hKΩ (ball_subset_closedBall (hball hy).1)),
    (fun y hy ↦ ball_subset_closedBall (hball hy).1),
    (fun p y hy ↦ (mem_iInter.mp (hball hy).2 p).1),
    hχ, hrange, hcompact, hsupp', hsum, hang, hangp,
    hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, ?_⟩, ?_,
    (fun p ↦ τ p.val), (fun p ↦ hτ p.val), ?_⟩
  · intro Q X hQ
    exact hstable Q X fun y hy ↦ (hQ y hy).trans (min_le_left _ _)
  · intro p
    exact ⟨hcb p.val, hcm p.val, hroot p.val, hsourceMask p.val,
      evolutionTime p.val, speedGap p.val, rootSize p.val, rootCost p.val, hprotection p.val,
      a p.val, ha p.val, b p.val, hb p.val, hac p.val, hbc p.val,
      hKA p.val, hKη p.val, hKAopen p.val, hKηopen p.val,
      hHopen p.val, hH p.val, bound p.val, hbound p.val, hprimitive p.val,
      ε p.val, hε p.val, δ p.val, hδ p.val, C p.val, hC p.val,
      hgapAlgebraic p.val, hdomain p.val, a' p.val, ha' p.val, ha'a p.val, ha'c p.val,
      hsmall' p, V p.val, hV p.val, hcenter p.val, hVc p.val, hsuppV p,
      hVcone p.val, Λ p.val, hΛ p.val, hcollar p.val, hbudgets p.val⟩
  · intro p
    refine ⟨hmaskτ p.val, hinterval p.val, εcarrier p.val, hεcarrier p.val,
      hεL p.val, hεb p.val, hphysical p, ?_⟩
    intro j
    obtain ⟨Vj, hVj, hVKj, hparamj, δj, hδj, hδjT, hcapturej, hrest⟩ := hstationary p.val j
    have hcapture := hcapturej (χ p) (hsuppAngular p)
    refine ⟨Vj, hVj, hVKj, hparamj, δj, hδj, hδjT, hcapture, ?_, hrest⟩
    intro Q hQ y hy c hc scale hscale L hL hinc
    have hs := tsupport_comp_subset_preimage (conicMask (χ p))
      (continuous_id.const_smul L⁻¹) hinc
    apply hcapture Q hQ y hy c hc (L⁻¹ * scale) (mul_pos (inv_pos.mpr hL) hscale)
    simpa only [mem_preimage, Pi.smul_apply, id_eq, smul_smul] using hs

end JanetCartan.RegularSector.FiniteAlgebraic
