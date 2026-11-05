module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.ComparableProfiles
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.PhysicalProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CutoffBudgets

/-!
# Produced amplitude profiles for the global elliptic diagonal factors

The existing `AmplitudeProfiles` is instantiated from the actual elliptic
symbol producers and the parent's supplied buffered proof localizers. Both
literal orientations retain their individual orders and zero offsets.
Consumer: the diagonal restriction estimates in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.EvolutionLocalization
open FourierIntegral FiniteChain.Graph KernelEstimates
open PhysicalShells PhysicalShells.Comparable PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χo" => fun y ↦ (f.outputMask y : ℂ)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- Instantiate all diagonal amplitude-profile fields for the actual inverse,
full residual and source, in that order. The original coefficient reserve is
unchanged; all offsets are zero and symbol orders are `-1,-1,0`. Input/output
localizer derivatives are produced from their supplied smooth compact masks,
not assumed as quantitative grades (`app:ch_regular:eq:high-amplitude`,
`app:ch_regular:lem:finite-chain`). -/
theorem exists_elliptic_masked_diagonal_profiles
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (hout : ContDiff ℝ ∞ χout) (hcout : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold) {a b : ℝ} (ha : 0 < a)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k)
    (mi mo : LocalizerSymbol (d+1)) {Ki Ii Ko Oo : Set (E × E)}
    (hi : IsBufferedLocalizer mi Ki Ii) (ho : IsBufferedLocalizer mo Ko Oo) :
    let Kb := tsupport χout ×ˢ tsupport (χs)
    let Kpdo := comparableJointCarrier 1 1 a b ((Prod.fst '' Kb) ×ˢ frequencyAnnulus
      (a / (16*annulusFactor 1 1)) (4 * max 1 (4*annulusFactor 1 1*b))) Kb (frequencyAnnulus a b)
    ∃ D : AmplitudeProfiles,
      D.symbolOffset = 0 ∧ D.inputMaskOffset = 0 ∧ D.outputMaskOffset = 0 ∧ D.offset = 0 ∧
      (∀ L : ℝ, 1 ≤ L → ∀ y k v,
        ‖iteratedFDeriv ℝ k (fun w : V ↦ (mi (y, w.2.2.1) : ℂ)) v‖ ≤
          D.inputMask k * L ^ (k + D.inputMaskOffset)) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ y ξ k,
        ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ξ)) y‖ ≤ D.outputMask k * L ^ (k + D.outputMaskOffset)) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ backward (j : Fin 3),
        let c := ![ellipticInverseSymbol f hK threshold Q,
          ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold] j
        let A := orientedMaskedPDOAmplitude backward χout (χs) c
        (∀ k v, v ∈ Kpdo →
          ‖iteratedFDeriv ℝ k (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
            ρ ^ (![-1, -1, (0 : ℝ)] j) * D.symbol k * L ^ (k + D.symbolOffset)) ∧
        (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb, ∀ k,
          ‖iteratedFDeriv ℝ k (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
            (max 1 (branchRadius low l)) ^ (![-1, -1, (0 : ℝ)] j) * D.symbol k * L ^ (k + D.symbolOffset)) := by
  intro Kb Kpdo
  have ht1 := f.radialThreshold_ge_one.trans ht
  obtain ⟨Dc, hDc, hc⟩ := exists_elliptic_masked_comparable_profile f hK hΩ hball χout
    hout hcout hsout
    threshold ht1 (b := b) ha AQ AB hAQ hAB
  obtain ⟨Dp, hDp, hp⟩ := exists_elliptic_masked_noncomparable_profile f hK hΩ hball χout hout hcout hsout AQ AB hAQ hAB
  obtain ⟨Ds, hDs, hs⟩ := exists_ellipticSource_masked_diagonal_grades f hK χout hout hcout threshold ht1 (b := b) ha
  obtain ⟨Di, Do, hDi, hDo, hin, hout⟩ := exists_elapsed_localizer_grades hi ho
  let C k := Dc k + Dp k + Ds k
  have hC k : 0 ≤ C k := add_nonneg (add_nonneg (hDc k) (hDp k)) (hDs k)
  let D : AmplitudeProfiles := {
    symbol := C, graphCutoff := fun _ ↦ 0, outputCutoff := fun _ ↦ 0,
    inputMask := Di, outputMask := Do,
    symbol_nonneg := hC, graphCutoff_nonneg := fun _ ↦ le_rfl,
    outputCutoff_nonneg := fun _ ↦ le_rfl, inputMask_nonneg := hDi, outputMask_nonneg := hDo,
    symbolOffset := 0, graphCutoffOffset := 0, outputCutoffOffset := 0,
    inputMaskOffset := 0, outputMaskOffset := 0 }
  refine ⟨D, rfl, rfl, rfl, rfl, hin, hout, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hmap hQl hBl hQp hBp backward j c A
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  have hcomp := hc Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp
  have hphys := hp Rstar hR L ρ hL hρp threshold ht Q B hQ hB hmap hQl hBl hQp hBp
  have hsrc := hs L ρ hL hρ backward
  have hcmp k : Dc k ≤ C k := by dsimp [C]; linarith [hDp k, hDs k]
  have hphy k : Dp k ≤ C k := by dsimp [C]; linarith [hDc k, hDs k]
  have hsr k : Ds k ≤ C k := by dsimp [C]; linarith [hDc k, hDp k]
  have henlarge (r s : ℝ) (hr : 0 ≤ r) (D' : ℕ → ℝ) (hd : ∀ k, D' k ≤ C k) k :
      r^s * D' k * L^k ≤ r^s * C k * L^k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hd k) (Real.rpow_nonneg hr _))
      (pow_nonneg (zero_le_one.trans hL) _)
  fin_cases j
  · constructor
    · intro k v hv
      exact (hcomp false backward k v hv).trans (henlarge ρ (-1) hρp.le Dc hcmp k)
    · intro low l ξ hξ z hz k
      exact (hphys _ (Or.inl rfl) backward low l ξ hξ z hz k).trans
        (henlarge _ (-1) (zero_le_one.trans (le_max_left _ _)) Dp hphy k)
  · constructor
    · intro k v hv
      exact (hcomp true backward k v hv).trans (henlarge ρ (-1) hρp.le Dc hcmp k)
    · intro low l ξ hξ z hz k
      exact (hphys _ (Or.inr rfl) backward low l ξ hξ z hz k).trans
        (henlarge _ (-1) (zero_le_one.trans (le_max_left _ _)) Dp hphy k)
  · constructor
    · intro k v hv
      exact (hsrc.1 v hv k).trans (henlarge ρ 0 hρp.le Ds hsr k)
    · intro low l ξ hξ z hz k
      exact (hsrc.2 low l ξ hξ z hz k).trans
        (henlarge _ 0 (zero_le_one.trans (le_max_left _ _)) Ds hsr k)

/-- Instantiate all diagonal amplitude-profile fields for the actual inverse,
full residual and source, in that order. The original coefficient reserve is
unchanged; all offsets are zero and symbol orders are `-1,-1,0`. Input/output
localizer derivatives are produced from their supplied smooth compact masks,
not assumed as quantitative grades (`app:ch_regular:eq:high-amplitude`,
`app:ch_regular:lem:finite-chain`). -/
theorem exists_elliptic_diagonal_profiles
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold) {a b : ℝ} (ha : 0 < a)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k)
    (mi mo : LocalizerSymbol (d+1)) {Ki Ii Ko Oo : Set (E × E)}
    (hi : IsBufferedLocalizer mi Ki Ii) (ho : IsBufferedLocalizer mo Ko Oo) :
    let Kb := tsupport (χo) ×ˢ tsupport (χs)
    let Kpdo := comparableJointCarrier 1 1 a b ((Prod.fst '' Kb) ×ˢ frequencyAnnulus
      (a / (16*annulusFactor 1 1)) (4 * max 1 (4*annulusFactor 1 1*b))) Kb (frequencyAnnulus a b)
    ∃ D : AmplitudeProfiles,
      D.symbolOffset = 0 ∧ D.inputMaskOffset = 0 ∧ D.outputMaskOffset = 0 ∧ D.offset = 0 ∧
      (∀ L : ℝ, 1 ≤ L → ∀ y k v,
        ‖iteratedFDeriv ℝ k (fun w : V ↦ (mi (y, w.2.2.1) : ℂ)) v‖ ≤
          D.inputMask k * L ^ (k + D.inputMaskOffset)) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ y ξ k,
        ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ξ)) y‖ ≤ D.outputMask k * L ^ (k + D.outputMaskOffset)) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ backward (j : Fin 3),
        let c := ![ellipticInverseSymbol f hK threshold Q,
          ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold] j
        let A := orientedMaskedPDOAmplitude backward (χo) (χs) c
        (∀ k v, v ∈ Kpdo →
          ‖iteratedFDeriv ℝ k (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
            ρ ^ (![-1, -1, (0 : ℝ)] j) * D.symbol k * L ^ (k + D.symbolOffset)) ∧
        (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb, ∀ k,
          ‖iteratedFDeriv ℝ k (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
            (max 1 (branchRadius low l)) ^ (![-1, -1, (0 : ℝ)] j) * D.symbol k * L ^ (k + D.symbolOffset)) := by
  exact exists_elliptic_masked_diagonal_profiles f hK hΩ hball (χo)
    (Complex.ofRealCLM.contDiff.comp f.outputMask_smooth)
    (f.outputMask_compact.comp_left Complex.ofReal_zero) (elliptic_physical_carrier f).2.1
    threshold ht ha AQ AB hAQ hAB mi mo hi ho

end JanetCartan.RegularSector.EllipticLocalization
