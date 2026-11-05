module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.AmplitudeSupport

/-!
# Radial geometry of the selected comparable carriers

The actual doubled multiplier gives a positive spatial radius even after
normalization and closure. Its section radii have common positive lower and
finite upper bounds. Radial dilation connects these bounds to the original
`bufferedJetSet` used in `ElapsedGrades/Amplitudes`, preserving both times and
position. The residual support alternative handles unused parts of the joint
carrier. Analytic transfer of the original seminorms is a separate obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.ConicAmplitude
open Characteristic.UniformEvolution Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.KernelIdentification
open Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "V" => ℝ × JointVariables E

private theorem selected_elapsed_local_radial_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (c C a b₀ : ℝ) (ha : 0 < a) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ threshold, f.radialThreshold ≤ threshold → ∀ χout : E → ℂ,
      ∀ w ∈ elapsedComparableCarrier χout (selectedEndpointMultiplier f p threshold)
        univ c C a b₀,
        (f.chart p).radialSection (spatialPart w.2) ∈ Icc lo hi ∧
        spatialPart w.2 ∈ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          ((f.chart p).bufferRadius / 2) := by
  let ℓ := (f.chart p).radialSection
  let η₀ := (coordinateSplit (f.chart p).index p.val.val).2
  let ε := retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius
  have hε := retainedRadius_bounds (f.chart p).targetRadius_pos (f.chart p).bufferRadius_pos
  have hεpos : 0 < ε := hε.1
  obtain ⟨aperture, hAp, hsupport⟩ :=
    exists_selectedEndpointMultiplier_retained_frequency_domain f p hρb hsrcρ
  let B := (aperture / 2) * ‖ℓ‖
  have hB : 0 ≤ B := mul_nonneg (half_pos hAp).le (norm_nonneg _)
  let δ := (a / (16 * annulusFactor c C)) / (B + 1)
  have hδ : 0 < δ := div_pos (div_pos ha
    (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (two_le_annulusFactor c C))))
      (by linarith)
  let D := 1 + ‖η₀‖ + ε / 2
  have hD : 0 < D := by dsimp only [D]; positivity
  let H := 4 * max 1 (4 * annulusFactor c C * b₀)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨δ / D, (1 + ‖ℓ‖) * H, div_pos hδ hD, mul_pos (by positivity) hH, ?_⟩
  intro threshold hthreshold χout w hw
  have hcone : ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      |ξ 0| ≤ B * ‖spatialPart ξ‖ := by
    intro ξ hξ
    have hs := hsupport threshold hthreshold hξ
    calc
      _ ≤ (aperture / 2) * ℓ (spatialPart ξ) := hs.1.2.le
      _ ≤ (aperture / 2) * (‖ℓ‖ * ‖spatialPart ξ‖) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (ℓ.le_opNorm _)) (half_pos hAp).le
      _ = _ := by dsimp [B]; ring
  have hsp := elapsedComparableCarrier_spatial_lower_bound χout
    (selectedEndpointMultiplier f p threshold) univ hB hcone hw
  have hne : spatialPart w.2 ≠ 0 := norm_pos_iff.mp (hδ.trans_le hsp)
  have hclosure : spatialPart w.2 ∈ closure (angularCone ℓ η₀ (ε / 4)) := by
    apply spatialPartCLM.continuous.closure_preimage_subset
    apply closure_mono (s := {ξ : E | ∃ ρ : ℝ, 1 ≤ ρ ∧
      ρ • ξ ∈ elapsedFrequencyCarrier (selectedEndpointMultiplier f p threshold) univ})
      (t := spatialPart ⁻¹' angularCone ℓ η₀ (ε / 4)) ?_ hw.2.2
    rintro ξ ⟨ρ, hρ, hξ⟩
    have hs := (hsupport threshold hthreshold hξ.1).1.1
    have hh := smul_mem_angularCone hs (inv_pos.mpr (zero_lt_one.trans_le hρ))
    simpa only [spatialPart_smul, inv_smul_smul₀ (zero_lt_one.trans_le hρ).ne',
      mem_preimage, ℓ, η₀, ε] using hh
  have hang : spatialPart w.2 ∈ angularCone ℓ η₀ (ε / 2) :=
    closure_angularCone_subset (by linarith [hε.1]) ⟨hclosure, hne⟩
  have hn : ‖(ℓ (spatialPart w.2))⁻¹ • spatialPart w.2‖ ≤ ‖η₀‖ + ε / 2 := by
    have ht := dist_triangle ((ℓ (spatialPart w.2))⁻¹ • spatialPart w.2) η₀ 0
    rw [dist_zero_right, dist_zero_right] at ht
    linarith [show dist ((ℓ (spatialPart w.2))⁻¹ • spatialPart w.2) η₀ < ε / 2 from hang.2]
  have hnorm : ‖spatialPart w.2‖ ≤ ℓ (spatialPart w.2) * D := by
    calc
      _ = ℓ (spatialPart w.2) * ‖(ℓ (spatialPart w.2))⁻¹ • spatialPart w.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hang.1,
          ← mul_assoc, mul_inv_cancel₀ hang.1.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hn.trans (by dsimp [D]; linarith)) hang.1.le
  have hlo : δ / D ≤ ℓ (spatialPart w.2) := (div_le_iff₀ hD).mpr (hsp.trans hnorm)
  have hhi : ℓ (spatialPart w.2) ≤ (1 + ‖ℓ‖) * H := by
    have hn' : ‖spatialPart w.2‖ ≤ H := (norm_spatialPart_le w.2).trans hw.2.1.2
    have hl := (le_abs_self (ℓ (spatialPart w.2))).trans (ℓ.le_opNorm _)
    nlinarith [mul_le_mul_of_nonneg_left hn' (norm_nonneg ℓ)]
  exact ⟨⟨hlo, hhi⟩, hang.1, ball_subset_ball (by linarith [hε.2.2]) hang.2⟩

/-- Uniform positive and finite section radii on the EXACT joint carriers
constructed by `exists_selected_elapsed_comparable_carriers`. The actual
multiplier supplies both the temporal cone (hence the spatial lower bound)
and the angular margin, including normalization and closure. The constants
precede threshold, amplitude, accuracy, `L`, `ρ`, and every shell. Consumer:
the original retained amplitude profiles in `ElapsedGrades/Amplitudes`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_elapsed_radial_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (c C a b₀ : ℝ) (ha : 0 < a) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ threshold, f.radialThreshold ≤ threshold → ∀ output : E → ℝ,
      ∀ p, ∀ w ∈ Comparable.comparableJointCarrier c C a b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a b₀),
        (f.chart p).radialSection (spatialPart w.2.1) ∈ Icc lo hi ∧
        spatialPart w.2.1 ∈ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          ((f.chart p).bufferRadius / 2) := by
  classical
  choose lo hi hlo hhi hbound using fun p ↦
    selected_elapsed_local_radial_bounds f p (hρb p) (hsrcρ p) c C a b₀ ha
  let D := 1 + ∑ p, (lo p)⁻¹
  have hD : 0 < D := by
    have := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) ↦ (inv_pos.mpr (hlo p)).le)
    dsimp only [D]; linarith
  have hlower p : D⁻¹ ≤ lo p := by
    have hp : (lo p)⁻¹ ≤ ∑ j, (lo j)⁻¹ := Finset.single_le_sum
      (fun j _ ↦ (inv_pos.mpr (hlo j)).le) (Finset.mem_univ p)
    have hh : (lo p)⁻¹ ≤ D := by dsimp only [D]; linarith
    simpa only [one_div, inv_inv] using (one_div_le_one_div_of_le (inv_pos.mpr (hlo p)) hh)
  have hupper p : hi p ≤ 1 + ∑ j, hi j := by
    have hp := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ (hhi j).le)
      (Finset.mem_univ p)
    linarith
  refine ⟨D⁻¹, 1 + ∑ p, hi p, inv_pos.mpr hD, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) ↦ (hhi p).le)
    linarith
  · intro threshold hthreshold output p w hw
    have hb := hbound p threshold hthreshold (endpointOutputMask f p output) _ hw.2
    exact ⟨⟨(hlower p).trans hb.1.1, hb.1.2.trans (hupper p)⟩, hb.2⟩

/-- Radial dilation into the SAME retained band, with explicit two-sided
bounds. Its base is literally `w.1`, so both original times and position are
preserved. Consumer: transferring the original amplitude profile after
`selected_normalizedResidual_jet_carrier_or_eq_zero`
(`app:ch_regular:eq:high-amplitude`). -/
theorem selected_bufferedJetSet_radial_dilation
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    (ε lo hi ra rb : ℝ) (hlo : 0 < lo) (hra : 0 < ra) (hab : ra ≤ rb)
    {w : SymbolBudgets.TwoTimePoint d} (hw : w ∈ bufferedJetSet ℓ z ε lo hi) :
    let t := ra / ℓ w.2
    0 < t ∧ t ∈ Icc (ra / hi) (ra / lo) ∧ ℓ (t • w.2) = ra ∧
      (w.1, t • w.2) ∈ bufferedJetSet ℓ z ε ra rb := by
  intro t
  obtain ⟨hbase, ⟨⟨r, η⟩, ⟨hr, hη, hℓη⟩, he⟩⟩ := hw
  change ℓ η = 1 at hℓη
  change r • η = w.2 at he
  have hrpos : 0 < r := hlo.trans_le hr.1
  have hrad : ℓ w.2 = r := by rw [← he, map_smul, hℓη, smul_eq_mul, mul_one]
  have ht : t • w.2 = ra • η := by
    dsimp only [t]
    rw [hrad, ← he, smul_smul, div_mul_cancel₀ _ hrpos.ne']
  refine ⟨by dsimp only [t]; rw [hrad]; exact div_pos hra hrpos, ?_, ?_, ?_⟩
  · dsimp only [t]
    rw [hrad]
    exact ⟨div_le_div_of_nonneg_left hra.le hrpos hr.2,
      div_le_div_of_nonneg_left hra.le hlo hr.1⟩
  · rw [ht, map_smul, hℓη, smul_eq_mul, mul_one]
  · exact ⟨hbase, (ra, η), ⟨⟨le_rfl, hab⟩, hη, hℓη⟩, ht.symm⟩

/-- A uniformly bounded positive radial dilation into the ORIGINAL retained
`ra, rb` band for every nonzero derivative of the actual normalized residual.
The radii `ra, rb` are the retained outputs of
`exists_finite_direct_operator_bounds`; no inclusion of the undilated carrier
in their band is assumed. The map fixes both original times and position.
The local residual support and angular positivity are the same producer's
retained fields. Unused parts of the joint carrier give zero derivatives.
Consumer: the `Qb` profile in `CompleteFactor.hprimitiveMasks`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:complete-residual`). -/
theorem exists_selected_elapsed_retained_radial_dilations
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (c C a b₀ : ℝ) (ha : 0 < a)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p) :
    ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ threshold, f.radialThreshold ≤ threshold → ∀ output : E → ℝ,
      ∀ p, ∀ v : V, v.2 ∈ Comparable.comparableJointCarrier c C a b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a b₀) →
      let lc := f.chart p
      let e := coordinateSplit lc.index
      let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
      let t := ra p / lc.radialSection (spatialPart v.2.2.1)
      0 < t ∧ t ∈ Icc tlo thi ∧ lc.radialSection (t • spatialPart v.2.2.1) = ra p ∧
      ∀ (angular : Euclidean d → ℝ),
        (∀ η ∈ tsupport angular, 0 < lc.radialSection η) →
        ∀ F : T → Matrix (Fin q) (Fin q) ℂ,
        tsupport F ⊆ closedBall (z.1, z) (lc.bufferRadius / 2) →
        ∀ ρ : ℝ, 0 < ρ → ∀ m : ℕ,
        let W₂ := collared lc.radialSection 1 angular F
        let b := fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) • W₂ (t, (s, (y, η)))
        ((elapsedJointCoordinates v).1, t • spatialPart v.2.2.1) ∈
          bufferedJetSet lc.radialSection z (lc.bufferRadius / 2) (ra p) (rb p) ∨
          iteratedFDeriv ℝ m (normalizedElapsedSymbol ρ b) v = 0 := by
  classical
  obtain ⟨lo, hi, hlo, hhi, hbound⟩ := exists_selected_elapsed_radial_bounds f hρb hsrcρ c C a b₀ ha
  let D := 1 + ∑ p, (ra p)⁻¹
  let H := 1 + ∑ p, ra p
  have hD : 0 < D := by
    have := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) ↦ (inv_pos.mpr (hra p)).le)
    dsimp only [D]; linarith
  have hH : 0 < H := by
    have := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) ↦ (hra p).le)
    dsimp only [H]; linarith
  have hlower p : D⁻¹ ≤ ra p := by
    have hp : (ra p)⁻¹ ≤ ∑ j, (ra j)⁻¹ := Finset.single_le_sum
      (fun j _ ↦ (inv_pos.mpr (hra j)).le) (Finset.mem_univ p)
    have hh : (ra p)⁻¹ ≤ D := by dsimp only [D]; linarith
    simpa only [one_div, inv_inv] using (one_div_le_one_div_of_le (inv_pos.mpr (hra p)) hh)
  have hupper p : ra p ≤ H := by
    have hp := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ (hra j).le)
      (Finset.mem_univ p)
    dsimp only [H]; linarith
  refine ⟨D⁻¹ / hi, H / lo, div_pos (inv_pos.mpr hD) hhi, div_pos hH hlo, ?_⟩
  intro threshold hthreshold output p v hv lc e z t
  have hr := (hbound threshold hthreshold output p v.2 hv).1
  have hrad : 0 < lc.radialSection (spatialPart v.2.2.1) := hlo.trans_le hr.1
  have ht : 0 < t := div_pos (hra p) hrad
  have htrange : t ∈ Icc (D⁻¹ / hi) (H / lo) := by
    refine ⟨?_, ?_⟩
    · exact (div_le_div_of_nonneg_right (hlower p) hhi.le).trans
        (div_le_div_of_nonneg_left (hra p).le hrad hr.2)
    · exact (div_le_div_of_nonneg_left (hra p).le hlo hr.1).trans
        (div_le_div_of_nonneg_right (hupper p) hlo.le)
  refine ⟨ht, htrange, ?_, ?_⟩
  · simp only [map_smul, smul_eq_mul, t, div_mul_cancel₀ _ hrad.ne']
  · intro angular hang F hF ρ hρ m W₂ b
    have hs := selected_normalizedResidual_jet_carrier_or_eq_zero f p angular hang F hF
      hρ lo hi v hr m
    rcases hs with hs | hs
    · exact Or.inl (selected_bufferedJetSet_radial_dilation lc.radialSection z
        (lc.bufferRadius / 2) lo hi (ra p) (rb p) hlo (hra p) (hab p) hs).2.2.2
    · exact Or.inr hs

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
