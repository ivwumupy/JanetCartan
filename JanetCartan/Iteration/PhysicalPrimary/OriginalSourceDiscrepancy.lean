module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutEquation
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverSources
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceDiscrepancyTemplate

/-!
# The actual smooth source discrepancy of the original uncut inverse

The native current retains one smooth real-linear realization of its normalized
source on compact real tests. Apply that SAME native realization to the compact
smooth realization of chi3*Inv(h), then subtract that realization. No second
chi2, new inverse, angular-source identity, or output cutoff is introduced.
The forcing representative and its local a.e. identification remain explicit
for the physical-core consumer; no global smoothness of zeroExtend(h) is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open Set MeasureTheory Filter Metric
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy
open LocalSobolev SmallSupport FixedDomainInverse
open RegularSector.Realization RegularSector.FiniteAssembly
open CharacteristicTransport.CompleteResidual

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "RH" => Lp E 2 (volume : Measure E)

/-- Put the actual compact smooth chi3*Inv representative into the fixed real
sector test space used by the native AR. -/
def supportedSourceTest {W : Set E} {x : E} (χ₃ : ContDiffBump x)
    (Inv : LocalL2 W E →L[ℝ] LocalL2 W E)
    (z : smoothSource W E →ₗ[ℝ] (E → E))
    (hz : ∀ h, ContDiff ℝ ∞ (z h) ∧
      z h =ᵐ[volume.restrict W] bumpL2 (p := 2) le_rfl χ₃ (Inv h) ∧
      tsupport (z h) ⊆ tsupport (χ₃ : E → ℝ) ∧ W.indicator (z h) = z h) :
    smoothSource W E →ₗ[ℝ] realSectorTestSpace d (d+1) :=
  z.codRestrict (realSectorTestSpace d (d+1)) fun h ↦
    mem_realSectorTestSpace (hz h).1
      (χ₃.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (hz h).2.2.1)

/-- The real test class is the SAME global zero extension of chi3*Inv(h).
No independent source representative or extra cutoff is selected. -/
theorem supportedSourceTest_toLp {W : Set E} (hW : MeasurableSet W)
    {x : E} (χ₃ : ContDiffBump x)
    (Inv : LocalL2 W E →L[ℝ] LocalL2 W E)
    (z : smoothSource W E →ₗ[ℝ] (E → E))
    (hz : ∀ h, ContDiff ℝ ∞ (z h) ∧
      z h =ᵐ[volume.restrict W] bumpL2 (p := 2) le_rfl χ₃ (Inv h) ∧
      tsupport (z h) ⊆ tsupport (χ₃ : E → ℝ) ∧ W.indicator (z h) = z h)
    (h : smoothSource W E) :
    realSectorTestToLp (supportedSourceTest χ₃ Inv z hz h) =
      zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (Inv h)) := by
  apply Lp.ext
  have hi := (ae_eq_restrict_iff_indicator_ae_eq hW).mp (hz h).2.1
  rw [(hz h).2.2.2] at hi
  exact (realSectorTestToLp_coeFn (supportedSourceTest χ₃ Inv z hz h)).trans
    (hi.trans (zeroExtend_coeFn hW (bumpL2 (p := 2) le_rfl χ₃ (Inv h))).symm)

/-- The full native source-minus-identity discrepancy, as ONE real-linear map
on smooth sources. AR is native and is not replaced by the identity. -/
def sourceDiscrepancy {W : Set E} {x : E} (χ₃ : ContDiffBump x)
    (Inv : LocalL2 W E →L[ℝ] LocalL2 W E)
    (z : smoothSource W E →ₗ[ℝ] (E → E))
    (hz : ∀ h, ContDiff ℝ ∞ (z h) ∧
      z h =ᵐ[volume.restrict W] bumpL2 (p := 2) le_rfl χ₃ (Inv h) ∧
      tsupport (z h) ⊆ tsupport (χ₃ : E → ℝ) ∧ W.indicator (z h) = z h)
    (AR : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → E)) :
    smoothSource W E →ₗ[ℝ] (E → E) :=
  AR.comp (supportedSourceTest χ₃ Inv z hz) - z

theorem sourceDiscrepancy_apply {W : Set E} {x : E} (χ₃ : ContDiffBump x)
    (Inv : LocalL2 W E →L[ℝ] LocalL2 W E)
    (z : smoothSource W E →ₗ[ℝ] (E → E))
    (hz : ∀ h, ContDiff ℝ ∞ (z h) ∧
      z h =ᵐ[volume.restrict W] bumpL2 (p := 2) le_rfl χ₃ (Inv h) ∧
      tsupport (z h) ⊆ tsupport (χ₃ : E → ℝ) ∧ W.indicator (z h) = z h)
    (AR : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → E))
    (h : smoothSource W E) :
    sourceDiscrepancy χ₃ Inv z hz AR h = AR (supportedSourceTest χ₃ Inv z hz h) - z h := rfl

/-- Global smoothness uses the native AR smooth packet and the actual smooth
inverse-source realization, not mere L2 equality. -/
theorem sourceDiscrepancy_contDiff {W : Set E} {x : E} (χ₃ : ContDiffBump x)
    (Inv : LocalL2 W E →L[ℝ] LocalL2 W E)
    (z : smoothSource W E →ₗ[ℝ] (E → E))
    (hz : ∀ h, ContDiff ℝ ∞ (z h) ∧
      z h =ᵐ[volume.restrict W] bumpL2 (p := 2) le_rfl χ₃ (Inv h) ∧
      tsupport (z h) ⊆ tsupport (χ₃ : E → ℝ) ∧ W.indicator (z h) = z h)
    (AR : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → E))
    (hAR : ∀ u, ContDiff ℝ ∞ (AR u)) (h : smoothSource W E) :
    ContDiff ℝ ∞ (sourceDiscrepancy χ₃ Inv z hz AR h) :=
  (hAR (supportedSourceTest χ₃ Inv z hz h)).sub (hz h).1

/-- Exact global a.e. agreement with native source minus the identity applied to
the SAME chi3*Inv(h). This is the full native angular/source discrepancy;
quantitative tails remain separate. -/
theorem sourceDiscrepancy_ae {W : Set E} (hW : MeasurableSet W)
    {x : E} (χ₃ : ContDiffBump x)
    (Inv : LocalL2 W E →L[ℝ] LocalL2 W E)
    (z : smoothSource W E →ₗ[ℝ] (E → E))
    (hz : ∀ h, ContDiff ℝ ∞ (z h) ∧
      z h =ᵐ[volume.restrict W] bumpL2 (p := 2) le_rfl χ₃ (Inv h) ∧
      tsupport (z h) ⊆ tsupport (χ₃ : E → ℝ) ∧ W.indicator (z h) = z h)
    (A : RH →L[ℝ] RH)
    (AR : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → E))
    (hAR : ∀ u, AR u =ᵐ[volume] A (realSectorTestToLp u))
    (h : smoothSource W E) :
    sourceDiscrepancy χ₃ Inv z hz AR h =ᵐ[volume]
      (A - 1) (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (Inv h))) := by
  let Z := supportedSourceTest χ₃ Inv z hz
  let u := zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (Inv h))
  have hZ : realSectorTestToLp (Z h) = u := supportedSourceTest_toLp hW χ₃ Inv z hz h
  have hzGlobal : z h =ᵐ[volume] u := by
    have hi := (ae_eq_restrict_iff_indicator_ae_eq hW).mp (hz h).2.1
    rw [(hz h).2.2.2] at hi
    exact hi.trans (zeroExtend_coeFn hW
      (bumpL2 (p := 2) le_rfl χ₃ (Inv h))).symm
  have ha : AR (Z h) =ᵐ[volume] A u := by
    simpa only [hZ] using hAR (Z h)
  filter_upwards [ha, hzGlobal, Lp.coeFn_sub (A u) u] with y hy hz' hs
  simp only [sub_apply, one_apply_eq_self]
  change AR (Z h) y - z h y = (A u - u) y
  exact (congrArg₂ (· - ·) hy hz').trans hs.symm

/-- Upgrade the actual weak equation on the *open* original core, using the
explicit smooth representative of the local forcing on W and the ONE smooth
representative of the source-minus-identity term.  No assertion is made about
the smoothness of an arbitrary zero extension (`app:ch_regular:eq:exact-physical`). -/
theorem pointwise_core_of_ae_discrepancy
    {W V : Set E} (hW : MeasurableSet W) (hV : IsOpen V) (hVW : V ⊆ W)
    {Q : E → Fin (d + 1) → MetricTensor (d + 1)} {B : E → MetricTensor (d + 1)}
    (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B)
    {v f δ : E → E} (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f) (hδ : ContDiff ℝ ∞ δ)
    {h : LocalL2 W E} (hrep : h =ᵐ[volume.restrict W] f)
    {u : RH} {A : RH →L[ℝ] RH} (hδrep : δ =ᵐ[volume] (A - 1) u)
    (hphysical : physicalWeakApply
      (fun y j ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single j 1)) B
      (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp))
      =ᵐ[volume.restrict V] fun y ↦
        (l2ComplexInclusion volume (zeroExtend hW h + A u - u) y).ofLp) :
    EqOn (physicalWeakApply
      (fun y j ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single j 1)) B
      (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (f y + δ y)).ofLp) V := by
  let C := fun y j ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single j 1)
  have hC (a j k : Fin (d + 1)) : ContDiff ℝ ∞ (fun y ↦ C y a j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp
      (ActualCarriers.contDiff_pencil.comp (hQ.prodMk contDiff_const))
  have hBc (j k : Fin (d + 1)) : ContDiff ℝ ∞ (fun y ↦ B y j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp hB
  let P : EuclideanSpace ℂ (Fin (d + 1)) →L[ℝ] (Fin (d + 1) → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℂ)).toContinuousLinearMap
  let I : E →L[ℝ] EuclideanSpace ℂ (Fin (d + 1)) := euclideanComplexInclusion
  have hv' : ContDiff ℝ ∞ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp) :=
    P.contDiff.comp (I.contDiff.comp hv)
  have hright : ContDiff ℝ ∞ (fun y ↦ (euclideanComplexInclusion (f y + δ y)).ofLp) :=
    P.contDiff.comp (I.contDiff.comp (hf.add hδ))
  have hleft : Continuous (physicalWeakApply C B (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp))) := by
    apply continuous_pi
    intro j
    apply Continuous.add
    · apply continuous_finsetSum
      intro a _
      apply continuous_finsetSum
      intro k _
      exact (hC a j k).continuous.smul ((continuous_apply k).comp
        ((hv'.continuous_fderiv (by simp)).clm_apply continuous_const))
    · apply continuous_finsetSum
      intro k _
      exact (hBc j k).continuous.smul ((continuous_apply k).comp hv'.continuous)
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hV hleft.continuousOn hright.continuous.continuousOn
  apply hphysical.trans
  let h₀ := zeroExtend hW h
  let e := (A - 1) u
  have he : h₀ + A u - u = h₀ + e := by
    simp only [e, sub_apply, one_apply_eq_self, add_sub_assoc]
  have hf₀ : h₀ =ᵐ[volume.restrict V] f := by
    filter_upwards [ae_restrict_of_ae (zeroExtend_coeFn hW h),
      ae_restrict_of_ae_restrict_of_subset hVW hrep, ae_restrict_mem hV.measurableSet]
      with y hy hf' hyV
    exact hy.trans ((indicator_of_mem (hVW hyV) _).trans hf')
  change (fun y ↦ (l2ComplexInclusion volume (h₀ + A u - u) y).ofLp) =ᵐ[volume.restrict V] _
  rw [he]
  filter_upwards [ae_restrict_of_ae (euclideanComplexInclusion.coeFn_compLpL (h₀ + e)),
    ae_restrict_of_ae (Lp.coeFn_add h₀ e), hf₀, ae_restrict_of_ae hδrep] with y hy hs hf' he'
  change l2ComplexInclusion volume (h₀ + e) y = euclideanComplexInclusion ((h₀ + e) y) at hy
  change (h₀ + e) y = h₀ y + e y at hs
  change δ y = e y at he'
  change (l2ComplexInclusion volume (h₀ + e) y).ofLp = _
  rw [hy, hs, hf', ← he']

open CorrectedAtoms PrimarySourceAdmission

/-- On the actual admitted tensor class the local source and its globally
smooth forcing are both canonical.  This is the identical admission inside
`OriginalFullResponse.apply`, using the full smooth Q and the supplied source
mask, not a second chi2 or a new extension (`app:ch_response:eq:response-full-map`). -/
theorem compact_tensor_forcing_spec (W S : Set E)
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (η : E → ℝ)
    (hQ : ContDiff ℝ ∞ Q) (hη : ContDiff ℝ ∞ η) :
    let src := cutoffStressSmoothSource (S := S) (W := W) Q η isOpen_univ
      (fun i ↦ (contDiff_pi.mp hQ i).contDiffOn) hη (subset_univ S)
    ∀ t : compactSmoothSources S,
      ContDiff ℝ ∞ (euclideanCutoffStressSource Q η t) ∧
        (src t : LocalL2 W E) =ᵐ[volume.restrict W] euclideanCutoffStressSource Q η t := by
  intro src t
  exact ⟨contDiff_euclideanCutoffStressSource Q η isOpen_univ
      (fun i ↦ (contDiff_pi.mp hQ i).contDiffOn) hη (subset_univ S) t,
    cutoffStressSmoothSource_coeFn Q η isOpen_univ
      (fun i ↦ (contDiff_pi.mp hQ i).contDiffOn) hη (subset_univ S) t⟩

/-- Cancel only the measured stress multiplier which is already one on the
whole admitted tensor support.  Consequently the actual smooth correction in
the core equation is exactly the full source-minus-identity term, not a cutoff
commutator (`app:ch_response:eq:response-full-identity`). -/
theorem compact_tensor_forcing_eq_stress (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (η : E → ℝ) {S : Set E} (hη : ∀ x ∈ S, η =ᶠ[nhds x] fun _ ↦ (1 : ℝ))
    (t : compactSmoothSources S) : euclideanCutoffStressSource Q η t =
      fun x ↦ WithLp.toLp 2 (AmbientResponse.stressSource Q t x) := by
  have hp := AmbientResponse.cutoffSource_stressSource_eq Q η t
    (fun x hx ↦ (hη x (t.property.2.2 (subset_tsupport _ hx))).eq_of_nhds)
  funext x
  exact congrArg (WithLp.toLp 2) (congrFun hp x)

end JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy

construct_original_source_discrepancy
retain_original_tensor_forcing
derive_original_tensor_core_equation

end
