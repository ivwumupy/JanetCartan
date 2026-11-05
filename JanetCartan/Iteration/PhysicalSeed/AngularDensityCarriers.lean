module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.DensityCarriers
public import JanetCartan.Iteration.PhysicalSeed.AngularMeasured
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Retain both caps through the same original DensityCarriers construction

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

namespace JanetCartan.PhysicalSeed.AngularDensityCarriers
open ContinuumRow ContinuumRow.NormalizedSelection
open ContinuumNormal.SourceDensityLimitRealization
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


declare_angular_retained exists_density_carriers_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_prescribed_measured_density_carriers
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have selectedResult := JanetCartan.PhysicalSeed.AngularMeasured.exists_measured_row_with_angular_cap hD H hUH hbounded T I Ω hΩ
    zCell ρc Rc M τlead row col hKΩ hpatchStrong hM hτeq hΩscale
    hRc hτ hτR hbuffer hphysical c₀ htrans R V hR hRphysical hRU hV hVP hflow
    L Mforward hL hMforward hforward hRtime hlabel hcover hcap aExtra
  choose cell hcell centers εcover hεcover hcover' hdomain hgram
    t r a r' a' ht hr ha hr' ha' hlocal hηb htnorm hdir hExtraCap
    hgeometry hmask hAngularExtraCap b hb hbcell hbH hbhalf hba hsampling
    δ hδ hconic χinitial rMeasure hrMeasure hMeasureCell hrb hrH hrhalf hra
    χcoeff hχcoeff hχrange hχcompact hχsupport hχplateau
    σ₀ hσ₀ hσ₀1 coeff Cimage Cbound Lbound hCimage hCbound hLbound
    hcoeff hzero hformula hjets hmeasured hcorrected using selectedResult
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  choose Dc p₀ q₀ ρ τ W Bi It A ε gap Qc Ωi βphase cJphase Vphase Lphase Gphase hfixedGeometry horigin hcompact hcone hρ hτi hW hKiW hBi hWBi
    hBiDom hDc hfoot hsupport hIt hIIt hsegT hseg hend hε hfreq hgap
    hQc hΩi hQcΩi hQradius hne hscale hselectedJoint using hconic
  have hselected := fun i F hF hi hrank hlow hsmall ↦
    (hselectedJoint i F hF hi hrank hlow hsmall).2
  have densityResult := exists_finite_seed_source_density_carriers_with_normalized_actions H
    (fun i : ι ↦ D.patches i.1.1.1.1 i.2) hUH hbounded family
    (fun i ↦ (hD.2.2.2.2.1 i.1.1.1.1 i.2).1)
    (fun i ↦ Ω i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hΩ i.1.1.1.1 i.2 (selected i))
    (fun i ↦ zCell i.1.1.1.1 i.2 (selected i))
    (fun i ↦ ρc i.1.1.1.1 i.2 (selected i))
    (fun i ↦ Rc i.1.1.1.1 i.2 (selected i))
    (fun i ↦ M i.1.1.1.1 i.2 (selected i))
    (fun i ↦ τlead i.1.1.1.1 i.2 (selected i))
    (fun i ↦ L i.1.1.1.1 i.2 (selected i))
    (fun i ↦ Mforward i.1.1.1.1 i.2 (selected i)) rowi coli
    (fun i ↦ hKΩ i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hpatchStrong i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hRc i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hM i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hτeq i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hL i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hΩscale i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hbuffer i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hphysical i.1.1.1.1 i.2) seed
    (fun i ↦ htrans i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hMforward i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hforward i.1.1.1.1 i.2 (selected i))
    (fun i ↦ R i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hR i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hRphysical i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hRU i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hRtime i.1.1.1.1 i.2 (selected i))
    (fun i ↦ V i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hV i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hVP i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hflow i.1.1.1.1 i.2 (selected i))
    (fun i ↦ hlabel i.1.1.1.1 i.2 (selected i))
    Dc (fun i ↦ (hDc i).trans inter_subset_left) z ηb hηb r a r' a' hr hr' ha' hlocal
    (fun i ↦ (hgeometry i).2.2.1) (fun i ↦ (hgeometry i).2.2.2.1)
    (fun i ↦ (hgeometry i).2.2.2.2.1) (fun i ↦ (hgeometry i).2.2.2.2.2)
    hsupport (fun i ↦ (hgeometry i).2.1)
    p₀ q₀ ρ τ hρ hτi W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg
    A ε gap hε hgap hfreq (fun _ ↦ δ) (fun _ ↦ hδ)
    (fun i F hF hi hrank hlow hsmall ↦ (hselected i F hF hi hrank hlow hsmall).1)
  choose Cnorm Cpdo hCnorm hCpdo Bhigh hBhigh densityCap hdensityCap hcap8
    current hcurrent hcarriers using densityResult
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, hAngularExtraCap, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, Dc, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi, βphase, cJphase, Vphase, Lphase, Gphase, ?_,
    χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    σ₀, hσ₀, hσ₀1, coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound,
    hcoeff, hzero, hformula, hjets, ?_⟩
  · intro i
    exact ⟨hfixedGeometry i, horigin i, hcompact i, hcone i, hρ i, hτi i, hW i, hKiW i, hBi i, hWBi i, hBiDom i, hDc i,
      hfoot i, hsupport i, hIt i, hIIt i, hsegT i, hseg i, hend i,
      hε i, hfreq i, hgap i, hQc i, hΩi i, hQcΩi i, hQradius i,
      hne i, hscale i, hselectedJoint i⟩
  · dsimp only
    refine ⟨hmeasured, hcorrected, Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh,
      min densityCap σ₀, lt_min hdensityCap hσ₀, min_le_right _ _,
      (min_le_left _ _).trans hcap8,
      (fun σ hσ ↦ current σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩),
      (fun σ hσ i ↦ hcurrent σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩ i), ?_⟩
    intro σ hσ
    exact hcarriers σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩

end JanetCartan.PhysicalSeed.AngularDensityCarriers
