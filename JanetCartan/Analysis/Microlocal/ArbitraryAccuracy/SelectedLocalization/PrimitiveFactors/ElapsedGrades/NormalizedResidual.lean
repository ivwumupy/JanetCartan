module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.NormalizedResidual.RadialTransfer
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.ResidualCarriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputJets

/-!
# Normalized grades of the actual selected direct residual

The fixed compact carrier is the exact comparable carrier for both orientations,
times the support of the elapsed cutoff. Every nonzero residual jet is transferred
to the original retained band. Both coefficients are localized by the existing
chart output plateau, and the same `W₀`, `W₁`, and full physical `PW₁` are used.
The profile precedes the current coefficients, slow scale, frequency and accuracy.
Consumers: `CompleteFactor.hprimitiveMasks` and
`exists_selected_elapsed_comparable_profiles.hbudget`.
Source: `app:ch_regular:eq:initial-coefficient-profile`,
`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`, and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open Characteristic Characteristic.AmplitudeBounds Characteristic.ConicAmplitude
open Characteristic.ConicPhase Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral.KernelIdentification Characteristic.UniformEvolution
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral FiniteChain.Graph
open FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "V" => ℝ × JointVariables E
local notation "Mat" => MetricTensor (d+1)

/-- Construct the normalized residual profile on the actual compact carrier,
including the comparable time slab and the output-jet carrier. The only analytic
inputs after the coefficient profiles are the smoothness, support, physical
column identity and ORIGINAL conic seminorms retained by
`RegularSector.FiniteAssembly.exists_finite_direct_operator_bounds`.

In particular no quantitative bound for `selectedBufferedAmplitude` is assumed.
The radial dilation and its vanishing alternative are proved by
`exists_selected_elapsed_retained_radial_dilations`; the high-shell germ in
`norm_iteratedFDeriv_normalizedResidual_le_retained_seminorm` supplies the
analytic transfer, including the low-frequency collar and order minus one.
The residual is literally `directRetardedAmplitudes Ac Bc W₀ W₁ true`, with
BOTH original coefficients multiplied by the chart plateau. Its agreement
with the original residual under the common masks is supplied by
`selected_common_smooth_direct_residual` for these same inputs.
Consumers: `Qb` in `CompleteFactor.hprimitiveMasks` and `Comparable.hbudget`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_normalizedResidual_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (c C a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p)
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (hthreshold : f.radialThreshold ≤ threshold)
    (Δ : ℝ) (θ : ℝ → ℂ) (hθ : HasCompactSupport θ)
    (hθone : ∀ r ∈ Icc 0 Δ, θ r = 1) :
    ∃ Kglobal : f.centers → Set (JointVariables E),
    ∃ Kelapsed : f.centers → Set V,
    ∃ Qb : ℕ → ℝ,
      (∀ p, IsCompact (Kglobal p)) ∧ (∀ p, IsCompact (Kelapsed p)) ∧
      (∀ p, Kelapsed p = tsupport θ ×ˢ Kglobal p) ∧
      (∀ p, Kglobal p = Comparable.comparableJointCarrier c C a₀ b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a₀ b₀)) ∧
      (∀ p, Icc 0 Δ ×ˢ Kglobal p ⊆ Kelapsed p) ∧
      (∀ j, 0 ≤ Qb j) ∧
      ∀ (Rstar : ℕ), 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j - Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cchart : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let Fs := fun p ↦ selectedBufferedAmplitude f p Q B (Φ p) (Cchart p)
      let W := fun p (j : Fin 3) ↦
        collared (f.chart p).radialSection (if j=0 then 0 else 1) (angular p) (Fs p j)
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p, ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) →
      (∀ p j, ContDiff ℝ ∞ (W p j)) →
      (∀ p,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        tsupport (Fs p 2) ⊆ closedBall (z.1, z) ((f.chart p).bufferRadius/2)) →
      (∀ p (v : T), (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
        ∀ j : Fin (d+1), (fun k ↦ W p 2 v k j) =
          WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
            (fun y k ↦ W p 1
              (physicalSlice (coordinateSplit (f.chart p).index) v.2.1 v.2.2.2 y) k j)
            ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1))) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p,
        let Aoriginal := fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal
        let Boriginal := fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal
        let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
        let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
        let b := directRetardedAmplitudes Ac Bc
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 0)
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1) true
        ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) ∧
        (∀ v ∈ Kelapsed p, ∀ j,
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) v‖ ≤ ρ ^ (-1 : ℝ) * Qb j * L ^ j) ∧
        (∀ r ∈ Icc 0 Δ, ∀ v ∈ Kglobal p, ∀ j,
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) (r, v)‖ ≤
            ρ ^ (-1 : ℝ) * Qb j * L ^ j) ∧
        ∀ (mi mo : LocalizerSymbol (d+1)) u y,
          ∀ v ∈ elapsedOutputJetCarrier (Kelapsed p) mi mo u y, ∀ j,
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) v‖ ≤
            ρ ^ (-1 : ℝ) * Qb j * L ^ j := by
  classical
  obtain ⟨tlo, thi, _, hthi, hdilate⟩ :=
    exists_selected_elapsed_retained_radial_dilations (q := d+1) f hρb hsrcρ
      c C a₀ b₀ ha₀ ra rb hra hab
  obtain ⟨Kglobal, Kelapsed, hKg, hKe, _, heq, hglobal, _⟩ :=
    exists_selected_elapsed_comparable_carriers (q := d+1) f output ho hoc hout
      threshold c C a₀ b₀ ha₀ θ hθ
  have hcover p : Icc 0 Δ ×ˢ Kglobal p ⊆ Kelapsed p := by
    rintro ⟨r, v⟩ ⟨hr, hv⟩
    rw [heq p]
    exact ⟨subset_tsupport θ (by change θ r ≠ 0; rw [hθone r hr]; exact one_ne_zero), hv⟩
  have hvglobal p v (hv : v ∈ Kelapsed p) : v.2 ∈
      Comparable.comparableJointCarrier c C a₀ b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a₀ b₀) := by
    rw [heq p] at hv
    rw [← hglobal p]
    exact hv.2
  have hzero p v (hv : v ∈ Kelapsed p) : (elapsedJointCoordinates v).2 ≠ 0 := by
    have hr := (hdilate threshold hthreshold output p v (hvglobal p v hv)).2.2.1
    intro hz
    change spatialPart v.2.2.1 = 0 at hz
    rw [hz, smul_zero, map_zero] at hr
    exact (hra p).ne' hr.symm
  let χ := fun p (v : V) ↦ chartOutputMask f p v.2.1.1
  have hχ p : ContDiff ℝ ∞ (χ p) := (chartPhysicalMasks_properties f p).1.comp
    contDiff_snd.fst.fst
  let Tcost := fun p j ↦ normalizedResidualTransferConstant (Kelapsed p) (χ p) thi j
  have hTcost p j : 0 ≤ Tcost p j := normalizedResidualTransferConstant_nonneg _ _ hthi.le j
  obtain ⟨D, hD, hprofile⟩ := exists_selected_amplitude_order_profile f ra rb cost hcost A hA
  let Qb := fun j ↦ (∑ p, Tcost p j) * D j
  have hQb j : 0 ≤ Qb j := mul_nonneg
    (Finset.sum_nonneg (fun p _ ↦ hTcost p j)) (hD j)
  refine ⟨Kglobal, Kelapsed, Qb, hKg, hKe, heq, hglobal, hcover, hQb, ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular Fs W J hang hW hFs hphysical hbudget
    p Aoriginal Boriginal Ac Bc b
  have haux := selected_common_smooth_direct_residual f p (hρb p) (hsrcρ p)
    output hout Q B (W p) (hW p) (hphysical p)
  change b = _ ∧ ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) ∧ _ at haux
  have hn : normalizedElapsedSymbol ρ b = fun v ↦ χ p v •
      normalizedElapsedSymbol ρ (curryCharacteristicMatrix (W p 2)) v := by
    rw [haux.1]
    funext v
    have hv : timeSpacePoint (v.2.1.1 0) (spatialPart v.2.1.1) = v.2.1.1 :=
      timeSpaceMeasurableEquiv.symm_apply_apply v.2.1.1
    simp only [normalizedElapsedSymbol, hv, curryCharacteristicMatrix, χ]
  have hbound : ∀ v ∈ Kelapsed p, ∀ j,
      ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) v‖ ≤
        ρ ^ (-1 : ℝ) * Qb j * L ^ j := by
    intro v hv j
    have hd := hdilate threshold hthreshold output p v (hvglobal p v hv)
    have hs := hd.2.2.2 (angular p) (hang p) (Fs p 2) (hFs p) ρ
      (zero_lt_one.trans_le hρ) j
    change _ ∨ iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ
      (fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) • W p 2 (t, (s, (y, η))))) v = 0 at hs
    rcases hs with hmap | hz
    · have hb := hprofile Rstar hRstar L hL Q B hQ hB Φ Cchart angular hbudget p 2 j
      have hWjoint : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude
          (curryCharacteristicMatrix (W p 2))) :=
        (hW p 2).comp evolutionToCharacteristicPoint.contDiff
      have hb' : BoundedTwoTimeOrderSeminorm 1 (J p) j
          (curryCharacteristicMatrix (W p 2)) ∧
          twoTimeOrderSeminorm 1 (J p) j (curryCharacteristicMatrix (W p 2)) ≤ D j * L ^ j :=
        hb
      have ht := norm_iteratedFDeriv_normalizedResidual_le_retained_seminorm
        (f.chart p).radialSection (angular p) (Fs p 2) (hKe p) (hzero p) (χ p) (hχ p)
        (isCompact_bufferedJetSet _ _ _ _ _) hWjoint hb'.1 hρ hd.1 hd.2.1.2 hv hmap
      rw [hn]
      apply ht.trans
      calc
        _ ≤ ρ⁻¹ * Tcost p j * (D j * L ^ j) :=
          mul_le_mul_of_nonneg_left hb'.2 (mul_nonneg (by positivity) (hTcost p j))
        _ ≤ ρ⁻¹ * (∑ p, Tcost p j) * (D j * L ^ j) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (fun p _ ↦ hTcost p j) (Finset.mem_univ p)) (by positivity))
            (mul_nonneg (hD j) (pow_nonneg (zero_le_one.trans hL) _))
        _ = _ := by rw [Real.rpow_neg_one]; dsimp only [Qb]; ring
    · rw [haux.1]
      rw [hz, norm_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hρ) _) (hQb j))
        (pow_nonneg (zero_le_one.trans hL) _)
  exact ⟨haux.2.1, hbound,
    fun r hr v hv j ↦ hbound (r, v) (hcover p ⟨hr, hv⟩) j,
    fun _ _ _ _ v hv j ↦ hbound v hv.1 j⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
