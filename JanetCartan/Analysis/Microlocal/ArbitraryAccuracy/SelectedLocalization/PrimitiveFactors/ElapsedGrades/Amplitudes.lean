module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Profiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.AmplitudeGrades
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhaseGrades

/-!
# Joint elapsed grades of the retained conic amplitudes

The normalized symbol is pulled back by the actual elapsed coordinate map,
so elapsed time is differentiated along with both physical positions and the
covectors. The order of each of the three selected amplitudes is preserved.
Consumer: `hprimitiveMasks` in
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.AmplitudeBounds
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open EvolutionIntegratedLocalization FourierIntegral FourierIntegral.PrimitiveProfiles
open FiniteChain.Graph
variable {d q : ℕ}
local notation "V" => ℝ × JointVariables (Euclidean (d+1))

/-- Joint elapsed substitution costs a fixed linear-map norm and no derivatives.
The original spatial order `-o` remains the factor `ρ⁻ᵒ`. This consumes the
actual conic seminorm, which is produced for the selected amplitudes by
`exists_selected_amplitude_order_profile`, rather than assuming elapsed grades
(`app:ch_regular:eq:high-amplitude`). -/
theorem normalizedElapsedSymbol_grade_of_twoTimeOrderSeminorm
    {J : Set (SymbolBudgets.TwoTimePoint d)} (hJ : IsCompact J)
    (b : TwoTimeAmplitude d q) (hb : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b))
    {o m : ℕ} {ρ L D : ℝ} (hρ : 1 ≤ ρ)
    (hfinite : BoundedTwoTimeOrderSeminorm o J m b)
    (hgrade : twoTimeOrderSeminorm o J m b ≤ D * L ^ m)
    {p : V} (hp : elapsedJointCoordinates p ∈ J) :
    ‖iteratedFDeriv ℝ m (normalizedElapsedSymbol ρ b) p‖ ≤
      (ρ ^ o)⁻¹ * (D * ‖elapsedJointCoordinates (d := d)‖ ^ m) * L ^ m := by
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hn : ContDiff ℝ ∞ (normalizedField ρ (SymbolBudgets.jointAmplitude b)) :=
    hb.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ))
  have he : normalizedElapsedSymbol ρ b =
      normalizedField ρ (SymbolBudgets.jointAmplitude b) ∘ elapsedJointCoordinates := by
    funext w
    simp [normalizedElapsedSymbol, normalizedField,
      SymbolBudgets.jointAmplitude, elapsedJointCoordinates, spatialPart_smul]
  have hc : cNorm J m (twoTimeOrderField o ρ b) =
      ρ ^ o * cNorm J m (normalizedField ρ (SymbolBudgets.jointAmplitude b)) := by
    exact (cNorm_smul (ρ ^ o) (hn.of_le (by simp))).trans
      (by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρpos.le _)])
  have hnorm : cNorm J m (normalizedField ρ (SymbolBudgets.jointAmplitude b)) ≤
      (ρ ^ o)⁻¹ * (D * L ^ m) := by
    have hh := (cNorm_twoTimeOrderField_le hfinite hρ).trans hgrade
    rw [hc] at hh
    exact (le_inv_mul_iff₀ (pow_pos hρpos o)).mpr hh
  rw [he, (elapsedJointCoordinates (d := d)).iteratedFDeriv_comp_right hn p (by simp)]
  apply ((iteratedFDeriv ℝ m (normalizedField ρ (SymbolBudgets.jointAmplitude b))
    (elapsedJointCoordinates p)).norm_compContinuousLinearMap_le
      (fun _ ↦ elapsedJointCoordinates)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ ((ρ ^ o)⁻¹ * (D * L ^ m)) * ‖elapsedJointCoordinates (d := d)‖ ^ m :=
      mul_le_mul_of_nonneg_right
        ((norm_iteratedFDeriv_le_cNorm hJ (hn.of_le (by simp)) hp le_rfl).trans hnorm)
        (pow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- A single profile bounds the joint elapsed symbols of the SAME finite family
before choosing coefficients, slow scale `L`, or frequency `ρ`. The order of
`W₀` is zero; those of `W₁` and the full retained `PW₁` are minus one.
The only analytic inputs are the smoothness and original seminorm bounds
retained by `exists_finite_direct_operator_bounds`. The carrier inclusion is
left explicit for the protected-geometry assembly. Consumer: the normalized
symbol component of `CompleteFactor.hprimitiveMasks`
(`app:ch_regular:eq:initial-coefficient-profile`, `app:ch_regular:eq:high-amplitude`). -/
theorem exists_selected_normalizedElapsedSymbol_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (ra rb : f.centers → ℝ) (cost : f.centers → ℕ → ℝ)
    (hcost : ∀ p m, 0 < cost p m) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (Rstar : ℕ), 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j - Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      let W := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
      (∀ p j, ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude (W p j))) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p j (v : V), elapsedJointCoordinates v ∈ J p → ∀ m,
        ‖iteratedFDeriv ℝ m (normalizedElapsedSymbol ρ (W p j)) v‖ ≤
          (ρ ^ (if j=0 then 0 else 1 : ℕ))⁻¹ * D m * L ^ m := by
  obtain ⟨D, hD, hprofile⟩ := exists_selected_amplitude_order_profile f ra rb cost hcost A hA
  refine ⟨fun m ↦ D m * ‖elapsedJointCoordinates (d := d)‖ ^ m,
    fun m ↦ mul_nonneg (hD m) (pow_nonneg (norm_nonneg _) _), ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQ hB Φ C angular J W hW hbudget p j v hv m
  have hb := hprofile Rstar hRstar L hL Q B hQ hB Φ C angular hbudget p j m
  exact normalizedElapsedSymbol_grade_of_twoTimeOrderSeminorm
    (isCompact_bufferedJetSet _ _ _ _ _) (W p j) (hW p j) hρ hb.1 hb.2 hv

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
