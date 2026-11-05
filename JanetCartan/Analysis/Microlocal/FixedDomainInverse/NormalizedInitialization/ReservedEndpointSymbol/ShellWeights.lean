module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.Products

/-!
# Reserved shell grades of the retained endpoint amplitude

Retain the coefficient reserve in the literal diagonal restriction of the
same two-time amplitude. The selected frequency coverage and temporal cone
supply both frequency weights without changing the natural slow-scale
exponent. The consumer is the `Q₀W₁` endpoint symbol in
`app:ch_regular_base:eq:energy-complete-residual` and the near-carrier input
of `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FinitePdo RegularSector.FinitePdo.RetainedConstruction
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EndpointPdoBounds RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Noncomparable
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "T" => SymbolBudgets.TwoTimePoint d

private theorem reserved_shell_inverse_le {R t c : ℝ} (hR : 0 < R) (ht : 0 < t)
    (h : t ≤ c * R) : R⁻¹ ≤ t⁻¹ * c := by
  rw [inv_mul_eq_div, le_div_iff₀ ht]
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hR).mpr h

/-- Convert the SAME retained diagonal amplitude's seminorms to the two
frequency weights required by `CompleteFactor`. The geometric hypotheses
are the exact outputs of the selected finite construction: diagonal coverage
and the buffer radii used by `exists_selectedEndpointMultiplier_temporal_cone`.
The original reserve remains in both conclusions; the coefficient and mask
product is performed by the reserved endpoint theorem.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`. -/
theorem exists_selected_endpoint_diagonal_reserved_weighted_grades
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (threshold : ℝ) (ht : 1 ≤ threshold)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    {a : ℝ} (ha : 0 < a) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m) :
    ∃ G : ℕ → ℝ, (∀ m, 0 ≤ G m) ∧
      ∀ (Rreserve : ℕ) (L ρ : ℝ), 1 ≤ L → 1 ≤ ρ →
      ∀ W : f.centers → TwoTimeAmplitude d (d+1),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p))) →
      (∀ p m, BoundedTwoTimeOrderSeminorm 1 (J p) m (W p) ∧
        twoTimeOrderSeminorm 1 (J p) m (W p) ≤ D m * L ^ (m-Rreserve)) →
      ∀ p,
      (∀ v : V, v.1.1 ∈ closedBall ((physicalCoordinates (f.chart p).index).symm x)
        (2*f.physicalRadius) → a ≤ ‖v.2.1‖ →
        ρ • v.2.1 ∈ tsupport (selectedEndpointMultiplier f p threshold) → ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ W p
          (w.1.1 0) (w.1.1 0) (spatialPart w.1.1) (spatialPart (ρ • w.2.1))) v‖ ≤
          ρ⁻¹ * G m * L ^ (m-Rreserve)) ∧
      (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z : E × E,
        z.1 ∈ closedBall ((physicalCoordinates (f.chart p).index).symm x)
          (2*f.physicalRadius) →
        ρ • ξ ∈ tsupport (selectedEndpointMultiplier f p threshold) → ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ W p
          (w.1 0) (w.1 0) (spatialPart w.1) (spatialPart (ρ • ξ))) z‖ ≤
          (max 1 (branchRadius low l))⁻¹ * G m * L ^ (m-Rreserve)) := by
  classical
  choose C hC hcone using fun p ↦
    exists_selectedEndpointMultiplier_temporal_cone f p (hbuffer p) (hmask p)
  let c := 1 + ∑ p, C p
  have hc : 1 ≤ c := le_add_of_nonneg_right (Finset.sum_nonneg fun p _ ↦ hC p)
  have hCc p : C p + 1 ≤ c := by
    have := Finset.single_le_sum (fun p _ ↦ hC p) (Finset.mem_univ p)
    change C p + 1 ≤ 1 + (∑ p, C p)
    linarith
  let κ := 2*c*max 1 a⁻¹
  have hk : 1 ≤ κ := by
    have hh : 1 ≤ max 1 a⁻¹ := le_max_left _ _
    dsimp [κ]
    nlinarith
  have hcκ : 2*c ≤ κ := le_mul_of_one_le_right (by linarith) (le_max_left _ _)
  have hcaκ : c / a ≤ κ := by
    have hh : c*a⁻¹ ≤ c*max 1 a⁻¹ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    dsimp [κ]
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (by linarith : 0 ≤ c) (le_max_left 1 a⁻¹ |>.trans' zero_le_one)]
  let G := fun m ↦ κ * D m * κ ^ m
  have hG m : 0 ≤ G m := mul_nonneg (mul_nonneg (zero_le_one.trans hk) (hD m))
    (pow_nonneg (zero_le_one.trans hk) _)
  refine ⟨G, hG, ?_⟩
  intro Rreserve L ρ hL hρ W J hW hb p
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  have hJ : IsCompact (J p) := isCompact_bufferedJetSet _ _ _ _ _
  have hrepr ζ (hζ : ζ ∈ tsupport (selectedEndpointMultiplier f p threshold)) :
      ∃ R : ℝ, 1 ≤ R ∧ ∃ η : Euclidean d,
        spatialPart ζ = R • η ∧ ‖ζ‖ ≤ c * R ∧
        MapsTo (diagonalPoint η)
          (closedBall ((physicalCoordinates (f.chart p).index).symm x) (2*f.physicalRadius)) (J p) := by
    obtain ⟨R, hR, η, he, hn, hm⟩ := (hcoverage p).selectedEndpoint_mapsTo f p ζ hζ
    refine ⟨R, hR, η, he, ?_, hm⟩
    exact (norm_le_spatial_of_cone (hcone p threshold (zero_lt_one.trans_le ht) ζ hζ)).trans
      (mul_le_mul (hCc p) hn (norm_nonneg _) (by linarith))
  constructor
  · intro v hv hav hζ m
    obtain ⟨R, hR, η, he, hn, hm⟩ := hrepr _ hζ
    have hRp : 0 < R := zero_lt_one.trans_le hR
    have hρR : ρ ≤ κ * R := by
      have hh : ρ*a ≤ c*R :=
        (mul_le_mul_of_nonneg_left hav hρp.le).trans (by simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hρp] using hn)
      have hh' : ρ ≤ (c/a)*R := by
        apply (le_div_iff₀ ha).mpr at hh
        convert hh using 1; ring
      exact hh'.trans (mul_le_mul_of_nonneg_right hcaκ hRp.le)
    have hη : (ρ/R) • spatialPart v.2.1 = η := by
      calc
        _ = R⁻¹ • spatialPart (ρ • v.2.1) := by rw [spatialPart_smul, smul_smul]; congr 1; ring
        _ = η := by rw [he, smul_smul, inv_mul_cancel₀ hRp.ne', one_smul]
    have hvJ : endpointJointDiagonal (ρ/R) v ∈ J p := by
      change ((v.1.1 0, v.1.1 0, spatialPart v.1.1), (ρ/R) • spatialPart v.2.1) ∈ J p
      rw [hη]
      simpa only [diagonalPoint_eq] using hm hv
    have hratio : max 1 |ρ/R| ≤ κ := by
      rw [abs_of_pos (div_pos hρp hRp)]
      exact max_le hk ((div_le_iff₀ hRp).mpr hρR)
    have hjet := norm_iteratedFDeriv_endpointJointDiagonal_le hJ (W p) (hW p) hR (hb p m).1 hvJ
    simp only [pow_one] at hjet
    apply hjet.trans
    have hi := reserved_shell_inverse_le hRp hρp hρR
    calc
      _ ≤ (ρ⁻¹ * κ) * (D m * L^(m-Rreserve)) * κ^m :=
        mul_le_mul (mul_le_mul hi (hb p m).2
          (twoTimeOrderSeminorm_nonneg _ _ _ _) (by positivity))
          (pow_le_pow_left₀ (by positivity) hratio m) (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (hD m) (by positivity)))
      _ = _ := by dsimp [G]; ring
  · intro low l ξ hξ z hz hζ m
    obtain ⟨R, hR, η, he, hn, hm⟩ := hrepr _ hζ
    have hRp : 0 < R := zero_lt_one.trans_le hR
    have hlo : branchRadius low l / 2 ≤ ‖ρ • ξ‖ := by
      have hh := ((mem_normalizedGraphCarrier_iff hρp.ne' low l ξ).mp hξ).1
      cases low <;> simp only [graphLower, Bool.false_eq_true, ↓reduceIte] at hh ⊢
      · linarith [branchRadius_pos false l]
      · exact hh
    have hweight : max 1 (branchRadius low l) ≤ κ*R := by
      apply max_le
      · exact hR.trans (le_mul_of_one_le_left hRp.le hk)
      · have hh : branchRadius low l ≤ 2*c*R := by linarith
        exact hh.trans (mul_le_mul_of_nonneg_right hcκ hRp.le)
    have hjet := norm_iteratedFDeriv_endpointPhysicalDiagonal_le hJ (W p) (hW p)
      hR (hb p m).1 η (hm hz)
    simp only [pow_one] at hjet
    rw [← he] at hjet
    apply hjet.trans
    calc
      _ ≤ ((max 1 (branchRadius low l))⁻¹ * κ) * (D m * L^(m-Rreserve)) :=
        mul_le_mul (reserved_shell_inverse_le hRp (by positivity) hweight) (hb p m).2
          (twoTimeOrderSeminorm_nonneg _ _ _ _) (by positivity)
      _ ≤ (max 1 (branchRadius low l))⁻¹ * G m * L^(m-Rreserve) := by
        dsimp [G]
        have hp : 1 ≤ κ^m := one_le_pow₀ hk
        nlinarith [mul_nonneg (by positivity : 0 ≤ (max 1 (branchRadius low l))⁻¹)
          (mul_nonneg (mul_nonneg (zero_le_one.trans hk) (hD m))
            (pow_nonneg (zero_le_one.trans hL) (m-Rreserve)))]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
