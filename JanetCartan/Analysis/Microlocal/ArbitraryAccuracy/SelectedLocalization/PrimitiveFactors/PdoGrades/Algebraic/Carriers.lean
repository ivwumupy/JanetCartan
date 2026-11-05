module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.SelectedInverse
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Geometry

/-!
# The actual angular carrier of the selected algebraic inverse

Restrict a supplied compact normalized frequency buffer to the closed support
of the original angular lift. The original complement certificate at the
retained radial threshold supplies the inverse domain on this compact set.
An auxiliary dilation tests that certificate; it never changes the operator
or its fixed cutoff. Consumer: branch three of `CompleteFactor`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers CompatibleResponse
open RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The original angular lift in the selected physical coordinates, before
the radial collar (`app:ch_regular_base:eq:complement-symbol`). -/
def selectedAlgebraicAngularLift (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) (ξ : E) : ℂ :=
  radialSourceCutoff (f.angularMask p) (physicalCoordinates (f.chart p).index ξ)

/-- Positive scaling does not change the selected angular lift
(`app:ch_regular:eq:high-amplitude`). -/
theorem selectedAlgebraicAngularLift_smul (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) {t : ℝ} (ht : 0 < t) (ξ : E) :
    selectedAlgebraicAngularLift f p (t • ξ) = selectedAlgebraicAngularLift f p ξ := by
  simp only [selectedAlgebraicAngularLift, map_smul, radialSourceCutoff_smul _ _ ht]

/-- Every normalized selected multiplier support lies in the SAME angular
closed support. This includes the cutoff shoulder and every source scale
(`app:ch_regular:eq:high-amplitude`). -/
theorem tsupport_selectedEndpointMultiplier_normalized_subset
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold ρ : ℝ} (ht : 0 < threshold) (hρ : 0 < ρ) :
    tsupport (fun ξ ↦ selectedEndpointMultiplier f p threshold (ρ • ξ)) ⊆
      tsupport (selectedAlgebraicAngularLift f p) := by
  have he : (fun ξ ↦ selectedEndpointMultiplier f p threshold (ρ • ξ)) =
      fun ξ ↦ (1 - FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
        ((2*threshold)⁻¹ • physicalCoordinates (f.chart p).index (ρ • ξ)) : ℂ) *
          selectedAlgebraicAngularLift f p ξ := by
    funext ξ
    simp only [selectedEndpointMultiplier, dilatedConicMask, conicMask,
      radialSourceCutoff_smul _ _ (inv_pos.mpr (by positivity : 0 < 2*threshold)),
      map_smul, radialSourceCutoff_smul _ _ hρ, selectedAlgebraicAngularLift,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  rw [he]
  exact tsupport_mul_subset_right

/-- Any nonzero point in the original angular closed support can be tested
in the closed support of the multiplier at its original fixed threshold.
The dilation is only an argument of the existing domain certificate
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem exists_smul_mem_selectedEndpointMultiplier_tsupport
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (ht : 0 < threshold) {ξ : E} (hξ : ξ ≠ 0)
    (hs : ξ ∈ tsupport (selectedAlgebraicAngularLift f p)) :
    ∃ t : ℝ, 0 < t ∧ t • ξ ∈ tsupport (selectedEndpointMultiplier f p threshold) := by
  let t := 6 * threshold / ‖ξ‖
  have ht' : 0 < t := div_pos (by positivity) (norm_pos_iff.mpr hξ)
  have hlarge : 2 < ‖(2*threshold)⁻¹ • physicalCoordinates (f.chart p).index (t • ξ)‖ := by
    rw [norm_smul, norm_physicalCoordinates, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 2*threshold)),
      Real.norm_of_nonneg ht'.le]
    dsimp [t]
    field_simp
    nlinarith
  have he : (fun η ↦ selectedEndpointMultiplier f p threshold (t • η)) =ᶠ[𝓝 ξ]
      selectedAlgebraicAngularLift f p := by
    filter_upwards [(by fun_prop : Continuous (fun η : E ↦
      ‖(2*threshold)⁻¹ • physicalCoordinates (f.chart p).index (t • η)‖)).continuousAt.eventually
      (lt_mem_nhds hlarge)] with η hη
    change (conicMask (f.angularMask p)
      ((2*threshold)⁻¹ • physicalCoordinates (f.chart p).index (t • η)) : ℂ) = _
    rw [conicMask_eq_radial hη.le]
    simp only [radialSourceCutoff_smul _ _ (inv_pos.mpr (by positivity : 0 < 2*threshold)),
      map_smul, radialSourceCutoff_smul _ _ ht', selectedAlgebraicAngularLift]
  refine ⟨t, ht', ?_⟩
  apply tsupport_comp_subset_preimage (selectedEndpointMultiplier f p threshold)
    (show Continuous (fun η : E ↦ t • η) by fun_prop)
  by_contra hn
  exact (notMem_tsupport_iff_eventuallyEq.mpr
    (he.symm.trans (notMem_tsupport_iff_eventuallyEq.mp hn))) hs

/-- The actual angular closed support lies in the selected positive-section
cone; no new spectral margin is assumed (`complement-symbol`). -/
theorem selectedAlgebraicAngularLift_positive_section
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {ξ : E} (hξ : ξ ≠ 0) (hs : ξ ∈ tsupport (selectedAlgebraicAngularLift f p)) :
    0 < (f.chart p).radialSection (spatialPart ξ) := by
  have hp : physicalCoordinates (f.chart p).index ξ ≠ 0 :=
    fun he ↦ hξ ((physicalCoordinates (f.chart p).index).injective (he.trans (map_zero _).symm))
  have hn := normalize_mem_tsupport_of_radialSourceCutoff hp
    (tsupport_comp_subset_preimage (radialSourceCutoff (f.angularMask p))
      (physicalCoordinates (f.chart p).index).continuous
      (tsupport_comp_subset Complex.ofReal_zero
        (fun ξ ↦ radialSourceCutoff (f.angularMask p)
          (physicalCoordinates (f.chart p).index ξ)) hs))
  have hc := (f.chart p).smul_mem_angularNeighborhood (f.angularMask_support p hn)
    (norm_pos_iff.mpr hp)
  rw [NormedSpace.norm_smul_normalize] at hc
  simpa only [LocalChart.angularNeighborhood, mem_preimage, split_physicalCoordinates]
    using hc.1

/-- Compact actual direction sets discharge the earlier supplied-carrier
inverse interface. `hdom` is the complement-domain output of
`exists_finite_physical_evolution_and_algebraic_inverse` evaluated on constant
fields at `2 * f.radialThreshold`. The SAME retained `RootBuffer` and family
are used. Profiles precede `Q,L,ρ,threshold`; the unchanged doubled threshold
is visible in `selectedEndpointMultiplier`. This proves the inverse factor
on every actual normalized multiplier support, not the complete physical
symbol (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_selected_conicBminus_actual_joint_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A : Coeff, A ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A)
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A) c.root) c.row c.col
          (normalizedRootDomain c))
    (J : Set E) (hJ : IsCompact J) (hzero : (0 : E) ∉ J)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (Rstar : ℕ) (L ρ : ℝ), 1 ≤ L → 0 < ρ →
      ∀ Q : E → Coeff, ContDiffOn ℝ ∞ Q Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
      ∀ p : f.centers, ∀ threshold : ℝ, 0 < threshold →
      ∀ v : E × E, physicalCoordinates (f.chart p).index v.1 ∈ closedBall x RQ →
        v.2 ∈ J → v.2 ∈ tsupport
          (fun ξ ↦ selectedEndpointMultiplier f p threshold (ρ • ξ)) → ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          conicBminus (f.chart p).radialSection (f.chart p).index Q
            (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
            (f.chart p).row (f.chart p).col w.1 (ρ • w.2)) v‖ ≤ ρ⁻¹ * C k * L ^ k := by
  let Jp := fun p ↦ J ∩ tsupport (selectedAlgebraicAngularLift f p)
  have hJp p : IsCompact (Jp p) := hJ.inter_right (isClosed_tsupport _)
  have hpos p ξ (hξ : ξ ∈ Jp p) : (f.chart p).radialSection (spatialPart ξ) ≠ 0 :=
    (selectedAlgebraicAngularLift_positive_section f p
      (fun he ↦ hzero (he ▸ hξ.1)) hξ.2).ne'
  have hcomp p A' (hA' : A' ∈ closedBall A₀ f.coefficientRadius) ξ (hξ : ξ ∈ Jp p) :
      ((physicalCoordinates (f.chart p).index).symm x,
        normalizeCovector (f.chart p).radialSection ξ) ∈
      complementDomain (f.chart p).index (fun _ : E ↦ A')
        (fieldRoot (coordinateSplit (f.chart p).index) (fun _ : E ↦ A') (f.chart p).root)
        (f.chart p).row (f.chart p).col (normalizedRootDomain (f.chart p)) := by
    obtain ⟨t, ht, hs⟩ := exists_smul_mem_selectedEndpointMultiplier_tsupport f p
      (zero_lt_one.trans_le f.radialThreshold_ge_one) (fun he ↦ hzero (he ▸ hξ.1)) hξ.2
    have hx : physicalCoordinates (f.chart p).index
        ((physicalCoordinates (f.chart p).index).symm x) ∈ Ω := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hKΩ (mem_closedBall_self hRQ)
    have hd := hdom p A' hA' (a := ((physicalCoordinates (f.chart p).index).symm x,
      normalizeCovector (f.chart p).radialSection (t • ξ))) ⟨hx, t • ξ, hs, rfl⟩
    simpa only [normalizeCovector_pos_smul _ _ ht] using hd
  obtain ⟨C, hC, hb⟩ := exists_selected_conicBminus_joint_profile f hΩ hKΩ hc
    Jp hJp hpos hcomp A hA
  refine ⟨C, hC, ?_⟩
  intro Rstar L ρ hL hρ Q hQ hQr hQp p threshold ht v hv hJv hs k
  exact hb Rstar L ρ hL hρ Q hQ hQr hQp p v hv
    ⟨hJv, tsupport_selectedEndpointMultiplier_normalized_subset f p ht hρ hs⟩ k

/-- Joint smoothness in coefficients and the full normalized covector on
the actual angular carrier. The domain input is the retained producer's
constant-field certificate at `2 * f.radialThreshold`. This is consumed by
the compact first-jet construction of `coefficientConicPhysicalAction`, and
does not postulate any derivative bound (`high-amplitude`). -/
theorem contDiffAt_selected_coefficientConicBminus_of_retained_domain
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hRQ : 0 ≤ RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (A' : Coeff) (hA' : A' ∈ closedBall A₀ f.coefficientRadius)
    (hdom : let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (ξ : E) (hξ : ξ ≠ 0) (hs : ξ ∈ tsupport (selectedAlgebraicAngularLift f p)) :
    ContDiffAt ℝ ∞ (coefficientConicBminus (f.chart p).radialSection (f.chart p).index
      (f.chart p).row (f.chart p).col (f.chart p).root) (A', ξ) := by
  let c := f.chart p
  have hpos := (selectedAlgebraicAngularLift_positive_section f p hξ hs).ne'
  obtain ⟨t, ht, hts⟩ := exists_smul_mem_selectedEndpointMultiplier_tsupport f p
    (zero_lt_one.trans_le f.radialThreshold_ge_one) hξ hs
  have hx : physicalCoordinates c.index ((physicalCoordinates c.index).symm x) ∈ Ω := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hKΩ (mem_closedBall_self hRQ)
  have hd := hdom (a := ((physicalCoordinates c.index).symm x,
    normalizeCovector c.radialSection (t • ξ))) ⟨hx, t • ξ, hts, rfl⟩
  simp only [normalizeCovector_pos_smul _ _ ht] at hd
  have hroot : ContDiffAt ℝ ∞ c.root (A', spatialPart (normalizeCovector c.radialSection ξ)) :=
    (hc.2 (A', spatialPart (normalizeCovector c.radialSection ξ))
      ⟨closedBall_subset_closedBall (f.coefficientRadius_le p) hA',
        ball_subset_closedBall hd.1.2⟩).1
  have hn := (contDiffAt_normalizeCovector c.radialSection hpos).comp (A', ξ) contDiffAt_snd
  have hbase : ContDiffAt ℝ ∞ (coefficientBminus c.index c.row c.col c.root)
      (A', normalizeCovector c.radialSection ξ) :=
    contDiffAt_coefficientBminus c.index c.row c.col c.root
      (p := (A', normalizeCovector c.radialSection ξ)) hroot hd.2
  have hb := hbase.comp (A', ξ) (contDiffAt_fst.prodMk hn)
  have hscalar : ContDiffAt ℝ ∞ (fun v : Coeff × E ↦ c.radialSection (spatialPart v.2)) (A', ξ) :=
    (c.radialSection.contDiff.comp ((coordinateSplit 0).contDiff.comp contDiff_snd).snd).contDiffAt
  exact (hscalar.inv hpos).smul hb

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
