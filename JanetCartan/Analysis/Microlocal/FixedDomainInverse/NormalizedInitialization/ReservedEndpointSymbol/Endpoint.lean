module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.ShellWeights

/-!
# Reserved grades of the same selected endpoint symbol

The literal masked source, the original time coefficient and the supplied
endpoint amplitude retain their common derivative reserve under the existing
graded bilinear calculus. Both orientations and both frequency weights are
kept. The original retained seminorm certificate is substituted in the parent
`ReservedEndpointSymbol` producer, using the coefficient profile of the same
normalized inverse (`app:ch_regular:eq:high-amplitude`,
`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius Topology
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FinitePdo RegularSector.FinitePdo.RetainedConstruction
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EndpointPdoBounds RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelDecay ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- Full endpoint grades from the original coefficient profile and the
reserved seminorms of the SAME supplied `W₁`. The parent producer derives
these seminorms from the retained initializer certificate. Fixed masks use
scale one, so no derivative reserve is spent on their products. The compact
carrier may be the actual normalized annular support, and both orientations
retain order minus one (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_selected_endpoint_symbol_grades_of_reserved_seminorms
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (Jpdo : f.centers → Set V) (hJpdo : ∀ p, IsCompact (Jpdo p))
    (hpos : ∀ p, ∀ v ∈ Jpdo p, v.1.1 ∈ tsupport (endpointOutputMask f p output))
    {a : ℝ} (ha : 0 < a) (hfreq : ∀ p, ∀ v ∈ Jpdo p, a ≤ ‖v.2.1‖)
    (AQ DW : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) (hDW : ∀ m, 0 ≤ DW m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (Rreserve : ℕ) (L ρ : ℝ), 1 ≤ L → 1 ≤ ρ →
      ∀ Q : E → Fin (d+1) → MetricTensor (d+1), ContDiffOn ℝ ∞ Q Ω →
      (∀ m, cNorm (closedBall x RQ) m Q ≤ AQ m * L ^ (m-Rreserve)) →
      ∀ W : f.centers → TwoTimeAmplitude d (d+1),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p))) →
      (∀ p m, BoundedTwoTimeOrderSeminorm 1 (J p) m (W p) ∧
        twoTimeOrderSeminorm 1 (J p) m (W p) ≤ DW m * L ^ (m-Rreserve)) →
      ∀ p backward,
      let A := orientedMaskedPDOAmplitude backward
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold Q (W p))
      (∀ v ∈ Jpdo p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ⁻¹ * D m * L ^ (m-Rreserve)) ∧
      (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l,
        ∀ z ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p), ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low l))⁻¹ * D m * L ^ (m-Rreserve)) := by
  classical
  have hzero p (v : V) (hv : v ∈ Jpdo p) : v.2.1 ≠ 0 := by
    intro hz
    have := hfreq p v hv
    rw [hz, norm_zero] at this
    linarith
  obtain ⟨S, hS, hsource⟩ := exists_selected_source_symbol_grades f threshold ht hft
    output ho hoc hout Jpdo hJpdo hzero
  obtain ⟨G, hG, hdiag⟩ := exists_selected_endpoint_diagonal_reserved_weighted_grades f threshold ht
    hbuffer hmask ra rb hcoverage ha DW hDW
  let Cq := fun m ↦ ∑ p, timeCoefficientCost (f.chart p).index m * AQ m
  have hCq m : 0 ≤ Cq m := Finset.sum_nonneg fun p _ ↦
    mul_nonneg (timeCoefficientCost_pos _ _).le (hAQ m)
  let D := derivativeConvolution (derivativeConvolution S Cq) G
  have hD : ∀ m, 0 ≤ D m := derivativeConvolution_nonneg
    (derivativeConvolution_nonneg hS hCq) hG
  refine ⟨D, hD, ?_⟩
  intro Rreserve L ρ hL hρ Q hQ hQbound W J hW hb p backward A
  let o := endpointOutputMask f p output
  let i := chartInputMask f p
  let β := selectedEndpointMultiplier f p threshold
  let src := orientedMaskedPDOAmplitude false o i (selectedSourceSymbol f p (2*threshold))
  let q := fun y ↦ (coefficient (f.chart p).index Q y 0).map Complex.ofReal
  let endpoint := orientedMaskedPDOAmplitude false o i (selectedEndpointSymbol f p threshold Q (W p))
  have he y z ξ : endpoint y z ξ = (src y z ξ * q y) *
      W p (y 0) (y 0) (spatialPart y) (spatialPart ξ) :=
    selectedEndpointAmplitude_eq_source_product f p hft hout Q (W p) y z ξ
  have hsrc y z ξ : src y z ξ = β ξ • ((o y * i z) • (1 : Mat)) :=
    selectedSourceAmplitude_eq_multiplier_masks f p hft hout y z ξ
  have hos : ContDiff ℝ ∞ o := (endpointOutputMask_properties f p ho hoc hout).1
  have his : ContDiff ℝ ∞ i := (chartPhysicalMasks_properties f p).2.1
  have hβ : ContDiff ℝ ∞ β := (selectedEndpointMultiplier_bounds f p threshold).1
  have hqb {y : E} (hy : y ∈ tsupport o) :
      y ∈ closedBall ((physicalCoordinates (f.chart p).index).symm x) (2*f.physicalRadius) :=
    (endpointOutputMask_properties f p ho hoc hout).2.2 hy
  have hqs {y : E} (hy : y ∈ tsupport o) : ContDiffAt ℝ ∞ q y :=
    (contDiffOn_timeCoefficient (f.chart p).index hQ).contDiffAt
      ((hΩ.preimage (physicalCoordinates (f.chart p).index).continuous).mem_nhds
        (hball (selectedEndpoint_physical_ball_mapsTo f p (hqb hy))))
  have hqbound {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
      (P : U →L[ℝ] E) (hP : ‖P‖ ≤ 1) (v : U) (hv : P v ∈ tsupport o) (m : ℕ) :
      ‖iteratedFDeriv ℝ m (q ∘ P) v‖ ≤ Cq m * L ^ (m-Rreserve) := by
    apply (endpointCoefficient_jet_le f p hΩ hball Q hQ P hP (hqb hv) m).trans
    have hc : timeCoefficientCost (f.chart p).index m * AQ m ≤ Cq m :=
      Finset.single_le_sum (fun p _ ↦ mul_nonneg (timeCoefficientCost_pos (f.chart p).index m).le (hAQ m))
        (Finset.mem_univ p)
    exact (mul_le_mul_of_nonneg_left (hQbound m) (timeCoefficientCost_pos _ _).le).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (by positivity))
  have hsourcej (v : V) (hv : v ∈ Jpdo p) m :
      ‖iteratedFDeriv ℝ m (fun w : V ↦ src w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
        S m * L^(m-Rreserve) := by
    have hh := (hsource 1 ρ le_rfl hρ p false).1 v hv m
    simp only [one_pow, mul_one] at hh
    exact hh.trans (le_mul_of_one_le_right (hS m) (one_le_pow₀ hL))
  have hsourcep (ξ : E) (z : E × E) m :
      ‖iteratedFDeriv ℝ m (fun w : E × E ↦ src w.1 w.2 (ρ • ξ)) z‖ ≤
        S m * L^(m-Rreserve) := by
    have hh := (hsource 1 ρ le_rfl hρ p false).2 ξ z m
    simp only [one_pow, mul_one] at hh
    exact hh.trans (le_mul_of_one_le_right (hS m) (one_le_pow₀ hL))
  have hsj : ContDiff ℝ ∞ (fun w : V ↦ src w.1.1 w.1.2 (ρ • w.2.1)) := by
    simp only [hsrc]
    exact (hβ.comp (contDiff_snd.fst.const_smul ρ)).smul
      (((hos.comp contDiff_fst.fst).mul (his.comp contDiff_fst.snd)).smul contDiff_const)
  have hsp (ξ : E) : ContDiff ℝ ∞ (fun w : E × E ↦ src w.1 w.2 (ρ • ξ)) := by
    simp only [hsrc]
    exact (((hos.comp contDiff_fst).mul (his.comp contDiff_snd)).smul
      (contDiff_const (c := (1 : Mat)))).const_smul (β (ρ • ξ))
  have hwj : ContDiff ℝ ∞ (fun w : V ↦ W p
      (w.1.1 0) (w.1.1 0) (spatialPart w.1.1) (spatialPart (ρ • w.2.1))) := by
    have h := (hW p).comp (endpointJointDiagonal (d := d) ρ).contDiff
    change ContDiff ℝ ∞ (fun w : V ↦ W p (w.1.1 0) (w.1.1 0)
      (spatialPart w.1.1) (ρ • spatialPart w.2.1)) at h
    simpa only [spatialPart_smul] using h
  have hwp (ξ : E) : ContDiff ℝ ∞ (fun w : E × E ↦ W p
      (w.1 0) (w.1 0) (spatialPart w.1) (spatialPart (ρ • ξ))) := by
    have h := (hW p).comp
      (((diagonalLinear (d := d)).contDiff.comp
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : E × E → E))).add
        (contDiff_const (c := (((0, 0, 0), spatialPart (ρ • ξ)) : SymbolBudgets.TwoTimePoint d))))
    change ContDiff ℝ ∞ (fun w : E × E ↦ SymbolBudgets.jointAmplitude (W p)
      (diagonalPoint (spatialPart (ρ • ξ)) w.1)) at h
    simpa only [diagonalPoint_eq, SymbolBudgets.jointAmplitude] using h
  have hjoint (v : V) (hv : v ∈ Jpdo p) m :
      ‖iteratedFDeriv ℝ m (fun w : V ↦ endpoint w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
        ρ⁻¹ * D m * L^(m-Rreserve) := by
    by_cases hζ : ρ • v.2.1 ∈ tsupport β
    · let P : V →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp
        (ContinuousLinearMap.fst ℝ (E × E) (E × E × E))
      have hP : ‖P‖ ≤ 1 := by
        apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
        exact (mul_le_mul (ContinuousLinearMap.norm_fst_le ℝ _ _)
          (ContinuousLinearMap.norm_fst_le ℝ _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      have hqp : ContDiffAt ℝ ∞ (q ∘ P) v := (hqs (hpos p v hv)).comp v P.contDiff.contDiffAt
      have hprod j := norm_iteratedFDeriv_endpoint_product_reserved_le (hsj.contDiffAt) hqp hS hCq
        (S := 1) (T := 1) zero_le_one zero_le_one hL Rreserve
        (by simpa only [one_mul] using hsourcej v hv)
        (by simpa only [one_mul] using hqbound (U := V) P hP v (show P v ∈ tsupport o from hpos p v hv)) j
      have hh := norm_iteratedFDeriv_endpoint_product_reserved_le (hsj.contDiffAt.mul hqp) hwj.contDiffAt
        (derivativeConvolution_nonneg hS hCq) hG (S := 1) zero_le_one (by positivity) hL Rreserve
        (by simpa only [one_mul] using hprod)
        ((hdiag Rreserve L ρ hL hρ W hW hb p).1 v (hqb (hpos p v hv)) (hfreq p v hv) hζ) m
      simpa only [he, one_mul, Nat.add_zero, D, P, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', Function.comp_def] using hh
    · have hn : ∀ᶠ w : V in 𝓝 v, ρ • w.2.1 ∉ tsupport β :=
        (continuous_snd.fst.const_smul ρ).continuousAt.preimage_mem_nhds
          ((isClosed_tsupport β).isOpen_compl.mem_nhds hζ)
      have hz : (fun w : V ↦ endpoint w.1.1 w.1.2 (ρ • w.2.1)) =ᶠ[𝓝 v] 0 := by
        filter_upwards [hn] with w hw
        simp [he, hsrc, image_eq_zero_of_notMem_tsupport hw]
      rw [(hz.iteratedFDeriv ℝ m).eq_of_nhds]
      simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (hD m)) (by positivity)
  have hphysical low l ξ (hξ : ξ ∈ normalizedGraphCarrier ρ low l)
      (z : E × E) (hz : z ∈ tsupport o ×ˢ tsupport i) m :
      ‖iteratedFDeriv ℝ m (fun w : E × E ↦ endpoint w.1 w.2 (ρ • ξ)) z‖ ≤
        (max 1 (branchRadius low l))⁻¹ * D m * L^(m-Rreserve) := by
    by_cases hζ : ρ • ξ ∈ tsupport β
    · let P := ContinuousLinearMap.fst ℝ E E
      have hqp : ContDiffAt ℝ ∞ (q ∘ P) z := (hqs hz.1).comp z P.contDiff.contDiffAt
      have hprod j := norm_iteratedFDeriv_endpoint_product_reserved_le (hsp ξ).contDiffAt hqp hS hCq
        (S := 1) (T := 1) zero_le_one zero_le_one hL Rreserve
        (by simpa only [one_mul] using hsourcep ξ z)
        (by simpa only [one_mul] using hqbound (U := E × E) P (ContinuousLinearMap.norm_fst_le ℝ E E) z (show P z ∈ tsupport o from hz.1)) j
      have hh := norm_iteratedFDeriv_endpoint_product_reserved_le ((hsp ξ).contDiffAt.mul hqp)
        (hwp ξ).contDiffAt (derivativeConvolution_nonneg hS hCq) hG
        (S := 1) zero_le_one (by positivity) hL Rreserve
        (by simpa only [one_mul] using hprod)
        ((hdiag Rreserve L ρ hL hρ W hW hb p).2 low l ξ hξ z (hqb hz.1) hζ) m
      simpa only [he, one_mul, Nat.add_zero, D, P, ContinuousLinearMap.coe_fst',
        Function.comp_def] using hh
    · have he0 : (fun w : E × E ↦ endpoint w.1 w.2 (ρ • ξ)) = 0 := by
        funext w
        simp [he, hsrc, image_eq_zero_of_notMem_tsupport hζ]
      rw [he0]
      simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (hD m)) (by positivity)
  cases backward
  · exact ⟨hjoint, hphysical⟩
  · have he' y z ξ : A y z ξ = (endpoint y z ξ).conjTranspose := rfl
    constructor
    · intro v hv m
      simpa only [he', FourierIntegral.norm_iteratedFDeriv_transport_conjTranspose] using hjoint v hv m
    · intro low l ξ hξ z hz m
      simpa only [he', FourierIntegral.norm_iteratedFDeriv_transport_conjTranspose] using
        hphysical low l ξ hξ z hz m

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
