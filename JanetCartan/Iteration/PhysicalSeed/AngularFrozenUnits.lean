module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.FrozenUnits
public import JanetCartan.Iteration.PhysicalSeed.AngularNormalComparison
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Retain both caps through the same original FrozenUnits construction

Replay the genuine original continuation on the one stronger selected tuple.
The additional angular certificate is retained, never recovered from a forgotten
weak choice. Consumer: the same original source inverse and
`PhysicalSampling.exists_original_scalar_sampling_bounds`
(`new:sec:order-of-choices`, `app:ch_background:prop:bg-inverse`).
-/

set_option warningAsError true
set_option maxRecDepth 4000
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSeed.AngularFrozenUnits
open ContinuumRow ContinuumRow.NormalizedSelection
open ContinuumNormal.SourceDensityLimitRealization
open ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference ProjectedStressFrame
open PositiveReference.FlowConstruction RetainedRowGeometry
open NullTransport ActualFlow FlowAmplitude CarrierSobolev GeometricProfile
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement
open NormalizedBackground.SourceGeometry Pseudodifferential AmplitudeBound PeriodicLocalL2


declare_angular_retained exists_frozen_units_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_prescribed_measured_frozen_units
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have selectedResult := JanetCartan.PhysicalSeed.AngularNormalComparison.exists_normal_comparison_with_angular_cap hD hn H hUH hbounded T I Ω hΩ
    zCell ρc Rc M τlead row col hKΩ hpatchStrong hM hτeq hΩscale
    hRc hτ hτR hbuffer hphysical c₀ htrans R V hR hRphysical hRU hV hVP hflow
    L Mforward hL hMforward hforward hRtime hlabel hcover hcap aExtra
  choose cell hcell centers εcover hεcover hcover' hdomain hgram
    t r a r' a' ht hr ha hr' ha' hlocal hηb htnorm hdir hExtraCap
    hgeometry hmask hAngularExtraCap b hb hbcell hbH hbhalf hba hsampling
    δ hδ Dc p₀ q₀ ρ τ W Bi It A ε gap Qc Ωi βphase cJphase Vphase Lphase Gphase hconic
    χinitial rMeasure hrMeasure hMeasureCell hrb hrH hrhalf hra
    χcoeff hχcoeff hχrange hχcompact hχsupport hχplateau
    σ₀ hσ₀ hσ₀1 coeff Cimage Cbound Lbound hCimage hCbound hLbound
    hcoeff hzero hformula hjets hmeasured hcorrected
    Cnorm Cpdo hCnorm hCpdo Bhigh hBhigh densityCap hdensityCap hcapMeasured hcap8
    current hcurrent hcarriers hnormal using selectedResult
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let _z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let _ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let _rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let _coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  have hconicProjection := fun i ↦ (hconic i).2.2.2.2
  choose hρ hτi hW hKiW hBi hWBi hBiDom hDc hfoot hsupport hIt hIIt
    hsegT hseg _hend hε hfreq hgap _hQc _hΩi _hQcΩi _hQradius _hne _hscale hselectedJoint using hconicProjection
  have hselected := fun i F hF hi hrank hlow hsmall ↦
    (hselectedJoint i F hF hi hrank hlow hsmall).2
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, hAngularExtraCap, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, Dc, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi, βphase, cJphase, Vphase, Lphase, Gphase, hconic,
    χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    σ₀, hσ₀, hσ₀1, coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound,
    hcoeff, hzero, hformula, hjets, hmeasured, hcorrected,
    Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, densityCap, hdensityCap,
    hcapMeasured, hcap8, current, hcurrent, hcarriers, ?_, hnormal⟩
  intro σ hσ i
  obtain ⟨_, _, _, _, hiσ, hrankσ, hsmall, _⟩ := hcurrent σ hσ i
  have hQ := (current σ hσ i).frame_eq
  have hlow : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
      (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < (family i).family.threshold :=
    hQ ▸ (current σ hσ i).Q.2.2
  have hsmall' : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
      (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < δ := hQ ▸ hsmall
  have hadmitted := hselected i (sourceDilation H.map σ) (contDiff_sourceDilation H.contDiff).contDiffOn
    hiσ hrankσ hlow hsmall'
  have hframe : (⟨projectedStress (sourceDilation H.map σ),
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU (contDiff_sourceDilation H.contDiff).contDiffOn
        hiσ hrankσ), hlow⟩ : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (family i).family.threshold}) = (current σ hσ i).Q :=
    Subtype.ext hQ.symm
  rw [hframe] at hadmitted
  obtain ⟨hkernel, houtput, hrange, _hcurrentHalf, _hcurrentLow, _hbufferCurrent, hshell, _hupper⟩ := hadmitted.1
  have hfrozen := hadmitted.2.2
  have hi : IsImmersionOn H.map U := isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1)
    (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUH hx)
  apply unitCarrierOutput_on_original_seed_of_source_geometry
    (hD.2.2.2.2.1 i.1.1.1.1 i.2).1 (family i)
    (hΩ i.1.1.1.1 i.2 (selected i)) (hKΩ i.1.1.1.1 i.2 (selected i))
    (hpatchStrong i.1.1.1.1 i.2 (selected i))
    (hRc i.1.1.1.1 i.2 (selected i)) (hτ i.1.1.1.1 i.2 (selected i))
    (hτR i.1.1.1.1 i.2 (selected i)) (hbuffer i.1.1.1.1 i.2 (selected i))
    H.contDiff hi hrank (hphysical i.1.1.1.1 i.2) (seed i)
    (htrans i.1.1.1.1 i.2 (selected i)) (fun x _ ↦ H.inducedMetric_eq_one x)
    (hL i.1.1.1.1 i.2 (selected i)) (hMforward i.1.1.1.1 i.2 (selected i))
    (hR i.1.1.1.1 i.2 (selected i)) (hforward i.1.1.1.1 i.2 (selected i))
    (hRphysical i.1.1.1.1 i.2 (selected i)) (hRU i.1.1.1.1 i.2 (selected i))
    (hRtime i.1.1.1.1 i.2 (selected i)) (hV i.1.1.1.1 i.2 (selected i))
    (hVP i.1.1.1.1 i.2 (selected i)) (hflow i.1.1.1.1 i.2 (selected i))
    (hlabel i.1.1.1.1 i.2 (selected i)) (Dc i) ((hDc i).trans inter_subset_left)
    (hηb i) (hr i) (hr' i) (ha' i) (hgeometry i).2.2.1 (hgeometry i).2.2.2.1
    (hgeometry i).2.2.2.2.1 (hlocal i) (hgeometry i).2.1 (current σ hσ i).Q
    hσ.1 (hσ.2.trans (hcap8.trans (by norm_num))) (current σ hσ i).frame_eq hkernel
    (p₀ i) (q₀ i) (hρ i) (hτi i) (hW i) (hKiW i) (hBi i) (hWBi i) (hBiDom i)
    houtput hrange hshell (hIt i) (hIIt i) (hsegT i) (hseg i) (A i) (hgap i) (hε i)
    (fun p hp ↦ hfreq i p (hWBi i (hKiW i hp))) (hfoot i)
    hfrozen.2.2.2.2.2.1
    (fun p hp ↦ hfrozen.2.2.2.2.2.2.1 p (hWBi i (hKiW i hp))) (hsupport i)

end JanetCartan.PhysicalSeed.AngularFrozenUnits
