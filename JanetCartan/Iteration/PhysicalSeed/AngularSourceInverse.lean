module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.Inverse
public import JanetCartan.Iteration.PhysicalSeed.AngularSourceGap
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Retain both caps through the same original SourceInverse construction

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
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSeed.AngularSourceInverse
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



declare_angular_retained exists_source_inverse_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_prescribed_measured_source_inverse
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have selectedResult := JanetCartan.PhysicalSeed.AngularSourceGap.exists_source_gap_with_angular_cap hD hn H hUH hbounded T I Ω hΩ
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
    current hcurrent hcarriers hunit hseedGap hsourceGap hnormal using selectedResult
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let _seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let _rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let _coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, hAngularExtraCap, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, Dc, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi, βphase, cJphase, Vphase, Lphase, Gphase, hconic,
    χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    σ₀, hσ₀, hσ₀1, coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound,
    hcoeff, hzero, hformula, hjets, hmeasured, hcorrected,
    Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, densityCap, hdensityCap,
    hcapMeasured, hcap8, current, hcurrent, hcarriers, hunit,
    hseedGap, ?_⟩
  refine ⟨?_, hnormal⟩
  obtain ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG,
    sourceCap, hsourceCap, hcapSource, hcapMeasured', hcapOne, hsource⟩ := hsourceGap
  let ψ := innerCutoff (n := n) hrInner hInnerCell
  let γsource := NormalAugmentation.globalGap g Mlimit / 2
  have hγsource : 0 < γsource := half_pos hG
  obtain ⟨capElliptic, hcapElliptic, _hcapEllipticOne, helliptic⟩ :=
    NormalizedBackground.exists_normalized_row_elliptic_profile_estimates_with_exterior
      (ι := ι) H (by omega) hrMeasure hrhalf hχcoeff hχsupport hχplateau ψ
      (innerCutoff_smooth hrInner hInnerCell)
  let Qhigh := fun p ↦ ∑ i, Bhigh i p
  have hQhigh (p : ℕ) : 0 ≤ Qhigh p := Finset.sum_nonneg fun i _ ↦ (hBhigh i p).le
  obtain ⟨Cell, hCell, hest⟩ :=
    helliptic Cpdo (fun i ↦ (hCpdo i).le) Qhigh hQhigh γsource hγsource
  let cap := min sourceCap capElliptic
  have hcap : 0 < cap := lt_min hsourceCap hcapElliptic
  have hcS : cap ≤ sourceCap := min_le_left _ _
  have hcE : cap ≤ capElliptic := min_le_right _ _
  refine ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG,
    cap, hcap, hcS.trans hcapSource, hcS.trans hcapMeasured', hcS.trans hcapOne,
    Cell, hCell, ?_⟩
  intro v hv hpos hinterval hvnorm
  obtain ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior, hsourceDensity⟩ :=
    hsource v hv hpos hinterval hvnorm
  refine ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior, ?_⟩
  intro σ hσ cσ e
  have hσsource : σ ∈ Ioc (0 : ℝ) sourceCap := ⟨hσ.1, hσ.2.trans hcS⟩
  have hσdensity : σ ∈ Ioc (0 : ℝ) densityCap := ⟨hσ.1, hσsource.2.trans hcapSource⟩
  obtain ⟨Vop, huniq, hactions, hnorm, hlocal, hnormalGap, hgapRow⟩ := hsourceDensity σ hσsource
  refine ⟨Vop, huniq, hactions, hnorm, hlocal, hnormalGap, hgapRow, ?_⟩
  intro Arow Erow _Q₀
  have hgapE := CoerciveInverse.normalOperator_gap Arow hgapRow
  have hE := CoerciveInverse.isInvertible_of_gap Erow hγsource hgapE
  refine ⟨hE, CoerciveInverse.inverse_isSelfAdjoint Erow
    (CoerciveInverse.normalOperator_isSelfAdjoint Arow) hγsource hgapE,
    hE.self_comp_inverse, hE.inverse_comp_self,
    CoerciveInverse.norm_inverse_le Erow hγsource hgapE,
    CoerciveInverse.comp_rightInverse Arow hγsource hgapRow, ?_, ?_⟩
  · intro f
    refine ⟨ContinuumInverse.canonical_rightInverse_norm_sq_le Arow hγsource hgapRow f, ?_, ?_⟩
    · rw [CoerciveNormal.rightInverse_exterior_eq]
      exact hexterior _
    · have heq : physicalRow (imageChannel (coeff σ)
          (FixedCutoffs.periodic hrMeasure hMeasureCell 1) (FixedCutoffs.periodic hrMeasure hMeasureCell 2))
          (fun i ↦ restrictCarrier (FixedCutoffs.periodic hrMeasure hMeasureCell 1) (Vop i))
          (CoerciveInverse.rightInverse Arow f).fst +
          exteriorChannel ψ (CoerciveInverse.rightInverse Arow f).snd = f := by
        simpa only [Arow, ψ, augmentedRow_apply] using
          CoerciveInverse.apply_rightInverse Arow hγsource hgapRow f
      have hae := Lp.coeFn_add
        (physicalRow (imageChannel (coeff σ)
          (FixedCutoffs.periodic hrMeasure hMeasureCell 1) (FixedCutoffs.periodic hrMeasure hMeasureCell 2))
          (fun i ↦ restrictCarrier (FixedCutoffs.periodic hrMeasure hMeasureCell 1) (Vop i))
          (CoerciveInverse.rightInverse Arow f).fst)
        (exteriorChannel ψ (CoerciveInverse.rightInverse Arow f).snd)
      rw [heq] at hae
      filter_upwards [hae, hexterior (CoerciveInverse.rightInverse Arow f).snd] with x hx hext
      intro hxcore
      change f x = (physicalRow (imageChannel (coeff σ)
        (FixedCutoffs.periodic hrMeasure hMeasureCell 1) (FixedCutoffs.periodic hrMeasure hMeasureCell 2))
        (fun i ↦ restrictCarrier (FixedCutoffs.periodic hrMeasure hMeasureCell 1) (Vop i))
        (CoerciveInverse.rightInverse Arow f).fst) x +
        (exteriorChannel ψ (CoerciveInverse.rightInverse Arow f).snd) x at hx
      have hz : exteriorChannel ψ (CoerciveInverse.rightInverse Arow f).snd x = 0 := hext hxcore
      rw [hz, add_zero] at hx
      exact hx.symm
  · intro _S densityProfile
    obtain ⟨hsupport, hb, hlow, Vanalytic, hanalytic, _hmatching⟩ :=
      hcarriers σ hσdensity v hv hpos hinterval hvnorm
    have _hopEq : Vanalytic = Vop := huniq Vanalytic (fun i ↦ (hanalytic i).2.2.1)
    subst Vanalytic
    have hprofile (p : ℕ) : 0 ≤ densityProfile p := Finset.sum_nonneg fun i _ ↦ cNorm_nonneg _ _ _
    have hmono : Monotone densityProfile := fun p q hpq ↦
      Finset.sum_le_sum fun _ _ ↦ cNorm_mono_order hpq
    let amp := fun i ↦ fullReflectedMatrixAmplitude
      (coefficientsOfCarrier (e i) (FixedCutoffs.physical (ha' i) 1))
      (symbolJacobian (family i) (cσ i).Q)
      (symbolInverse (family i) (cσ i).Q (z i) (ηb i) (r i) (6 * a i))
      (symbolDomain (family i) (cσ i).Q (z i) (ηb i) (r i) (6 * a i))
      (closedBall (spectatorCenter (z i)) (a' i / 2))
    have hs (i : ι) : ∀ ξ j k, SupportedInCenteredBox (4 * a' i) (fun q ↦ amp i ξ q j k) :=
      fullReflectedMatrixAmplitude_supportedInCenteredBox _ _ _ _ _ (4 * a' i) (hsupport i)
    have hhigh : ∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ q ↦ amp i ξ q l j) p (Qhigh p * (1 + densityProfile p)) := by
      intro i p _ l j ξ is his q
      apply ((hanalytic i).2.2.2.2.2.2.2.1 p l j ξ is his q).trans
      apply mul_le_mul
      · exact Finset.single_le_sum (fun k _ ↦ (hBhigh k p).le) (Finset.mem_univ i)
      · exact add_le_add (le_refl (1 : ℝ)) (Finset.single_le_sum
          (fun k _ ↦ cNorm_nonneg
            (closedBall ((0 : Euclidean (n - 1)), zCell k.1.1.1.1 k.2 (selected k))
              (L k.1.1.1.1 k.2 (selected k) / 8)) p (v k)) (Finset.mem_univ i))
      · exact add_nonneg zero_le_one (cNorm_nonneg _ _ _)
      · exact hQhigh p
    have hnormaleq (i : ι) : carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator (by omega) (4 * a' i) (amp i) (hb i) (hs i) (Cpdo i)
            (fun l j ξ is his ↦ hlow i l j ξ is (his.trans (Nat.le_succ _))))) :=
      (hanalytic i).2.2.2.2.2.2.1
    exact hest σ ⟨hσ.1, hσ.2.trans hcE⟩ (coeff σ)
      (hformula σ ⟨hσ.1, hσsource.2.trans hcapMeasured'⟩) densityProfile hprofile hmono amp hb hlow hhigh
      (fun i ↦ 4 * a' i) Cpdo hs (fun i l j ξ is his ↦ hlow i l j ξ is (his.trans (Nat.le_succ _)))
      Vop hnormaleq hgapRow

end JanetCartan.PhysicalSeed.AngularSourceInverse
