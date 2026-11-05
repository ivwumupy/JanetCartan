module

public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.ObservedChains.SourceSupport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.NormalizedAlternatingObservation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.ChronologicalWordObservation

/-!
# Observing the actual measured residual powers from individual estimates

Apply the accepted alternating-chain observation theorem to the literal signed
measured letters, then apply the accepted chronological-word summation theorem.
There is no assumed observed-word or residual-power decay. The actual family,
operators, source, radial threshold and rates are fixed before proof depth;
only proof localizers are supplied anew at a finite depth. A single terminal
symbol and its right quantization are retained throughout.

This is the independent analytic implication required by
`ArbitraryAccuracy.rapidDecayAt_inverse_of_finite_chains.hchain` and
`SignedProductEstimates.normalized_correctedSource_angular_finite_expansion`.
The actual initialized analytic inputs remain with their named producers.
Do not import this high leaf through the low `NormalizedResidualWords` umbrella.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedResidualWords.ObservedChains
open NormalizedSolver Realization FiniteMasks.ActualFamily FiniteAssembly
open FiniteResidual.FiniteIdentity FiniteEvolution FiniteAlgebraic Characteristic.PdoRealization
open Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open FourierIntegral FourierIntegral.LowBounds LocalSobolev SmallSupport
open ArbitraryAccuracy ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.ResidualLocalization
open ResponseTransfer FiniteChain.Graph

variable {d : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
local notation "Hu" => LocalL2 (univ : Set E) V
local notation "G" => restrictionSobolevScale (univ : Set E) V MeasurableSet.univ

/-- Individual estimates on the actual half-normalized characteristic,
reflected and elliptic letters imply EVERY observed power of the same real
measured residual, including depth zero. Projection to real data occurs only
after each complete complex word. The observation is the literal normalized
source minus one identity, with the original restriction and zero extension.

Explicit producer inputs:
* `hsupp` and `hb`: the selected direct constructor's support and algebraic
  normal-amplitude certificates on the same doubled collar;
* `hu`, `hsupport`, and the first conjunct of `hproof`: the original source's
  uniform low bound, physical support and first-mask tail from
  `OriginalSourceApplication` / `both-initial-source-localization`; the literal
  cut datum uses `cut_source_ae_zero_off_support`;
* full/near low norms and `hcost`: the signed-letter cost endpoints retained
  by `PrescribedAlternatingConstruction`;
* factor leakage in `hproof`: the prescribed measured retarded/PDO/signed
  leaves in `exists_finite_selected_direct_construction_with_prescribed_alternating_leakage`;
* left low norms, cross leakage, terminal leakage, and the SAME `mt`/`Mt`:
  `exists_selected_terminal_even_masks_with_localizer_estimates`.

All constants precede the varying index, and each leakage loss precedes its
accuracy. The fixed threshold `L₀` is distinct from the varying slow scale `L`.
`both-localized-response` retains the original-initializer applications of
these inputs; `both-response-transfer` retains the same-inverse application.
This implication does not construct the unconditional response or Theorem 1.1
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem measuredResidual_hchain_of_individual_estimates
    (f : ActualMaskFamily Ω x RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (Q : ι → E → Fin (d+1) → MetricTensor (d+1)) (B : ι → E → MetricTensor (d+1))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (Ralg Calg : ι → f.centers → ℝ)
    (hb : ∀ i p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L₀) (Q i) (B i) 1)) (Ralg i p) (Calg i p))
    (χ₂ χ₃ : ContDiffBump x) (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1)
    {D : Set E} (hD : MeasurableSet D)
    (hχ₂D : tsupport (χ₂ : E → ℝ) ⊆ D) (hχ₃D : tsupport (χ₃ : E → ℝ) ⊆ D)
    (U : Set E) (hU : IsOpen U) (hχ₃U : tsupport (χ₃ : E → ℝ) ⊆ U)
    (hcore : U ⊆ ball x f.physicalRadius) (houtput : ∀ y ∈ U, output y = 1)
    (u : ι → LocalL2 D RV)
    (hsupport : ∀ i, ∀ᵐ y ∂volume.restrict D,
      y ∉ tsupport (χ₂ : E → ℝ) → u i y = 0)
    (ρ L A : ι → ℝ) (σ : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (hσ : 0 < σ) (hscale : ∀ i, L i ≤ (ρ i)^(1-σ)) (hA : ∀ i, 0 ≤ A i)
    (hu : ∃ C a : ℝ, 0 ≤ C ∧ ∀ i, ‖u i‖ ≤ C*A i*(ρ i)^a)
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mt, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mt, NormedSpace.normalize p.2 ∈ K)
    (Mt : ι → H →L[ℂ] H)
    (hMt : ∀ i v, Mt i v =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (rightLocalizer (ρ i) mt (fun z ↦ (v z).ofLp) y))
    (W : Set E) (hW : MeasurableSet W) :
    let hob := fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2
    let letters := fun i a ↦ measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
      (selectedFullPhysicalResidualTerm f hK L₀ (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) a)
    let factors := fun a i ↦
      (localRetardedOperator MeasurableSet.univ univ (letters i a)).toLinearMap
    let source := fun i ↦ restrictL2 univ (l2ComplexInclusion volume (zeroExtend hD (u i)))
    (∀ a, ∃ C c : ℝ, 0 ≤ C ∧ ∀ i v, ‖factors a i v‖ ≤ C*(ρ i)^c*‖v‖) →
    (∀ a, HasPolynomialSobolevCost G G ρ (factors a)) →
    (∀ n : ℕ, ∃ right left : ℕ → ι → Hu →ₗ[ℝ] Hu,
      (∀ s, RapidDecayAt G s ρ A (fun i ↦ source i - right 0 i (source i))) ∧
      (∀ j < n, ∀ a, ∃ C c : ℝ, 0 ≤ C ∧ ∀ i v,
        ‖factors a i (right j i v)‖ ≤ C*(ρ i)^c*‖v‖) ∧
      (∀ j < n, ∃ C c : ℝ, 0 ≤ C ∧ ∀ i v, ‖left j i v‖ ≤ C*(ρ i)^c*‖v‖) ∧
      (∀ j < n, ∀ a s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
          (1-left j i) (factors a i (right j i v)) ∈ (G).level s ∧
          (G).gradeNorm s ((1-left j i) (factors a i (right j i v))) ≤
            C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖) ∧
      (∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
          (1-right (j+1) i) (left j i v) ∈ (G).level s ∧
          (G).gradeNorm s ((1-right (j+1) i) (left j i v)) ≤
            C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖) ∧
      (∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
          (1-(localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap)
            (right n i v) ∈ (G).level s ∧
          (G).gradeNorm s ((1-(localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap)
            (right n i v)) ≤ C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖)) →
    let retarded := fun i ↦ (sourceCutMultiplier output ho.continuous hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (T i)).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let P := fun i ↦ measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
      (pairedResidual f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i))
    ∀ s j, RapidDecayAt (restrictionSobolevScale W RV hW) s ρ A
      (fun i ↦ localRealCompression hD W (pairedSource f hK L₀ output ho.continuous hob - 1)
        ((localRealCompression hD D (P i)^j) (u i))) := by
  intro hob letters factors source hfullLow hcost hproof retarded P
  have hsourceNorm : ∃ C a : ℝ, 0 ≤ C ∧ ∀ i, ‖source i‖ ≤ C*A i*(ρ i)^a := by
    obtain ⟨C, a, hC, hu⟩ := hu
    exact ⟨C, a, hC, fun i ↦ (complex_source_norm_le hD (u i)).trans (hu i)⟩
  have hsourceSupport i : sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
      (zeroExtend MeasurableSet.univ (source i)) = zeroExtend MeasurableSet.univ (source i) :=
    complex_source_plateau_of_support hD χ₂ χ₃ hnest (u i) (hsupport i)
  have hfactorSupport a i (v : Hu) :
      sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
        (zeroExtend MeasurableSet.univ (factors a i v)) =
      zeroExtend MeasurableSet.univ (factors a i v) := by
    exact local_measuredOperator_oriented_source_plateau
      χ₂ χ₃ χ₃ χ₂.continuous χ₃.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) (bump_norm_le_one χ₃)
      (selectedFullPhysicalResidualTerm f hK L₀ (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) a) false hnest v
  intro s
  apply normalizedSource_measuredResidual_hchain_of_factorChains
    f hK (fun _ ↦ L₀) Q B W₁ output ho.continuous hob hib T
    χ₂ χ₃ χ₂.continuous χ₃.continuous (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
    hD hχ₂D hχ₃D W hW s ρ A u hsupp Ralg Calg hb
  intro n w
  obtain ⟨right, left, hsource, hnear, hleft, hfactor, hcross, htleak⟩ := hproof n
  exact normalizedSource_alternatingChain_observation_rapidDecayAt
    f hK hsym L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃U hcore houtput
    mt ht htc hlo hann hterminal n (fun j ↦ factors (w j)) right left Mt source ρ L A σ
    hρ hL hLρ hσ hscale hA hMt hsourceNorm hsource hsourceSupport
    (fun j _ i v _ ↦ hfactorSupport (w j) i v)
    (fun j _ ↦ hfullLow (w j)) (fun j hj ↦ hnear j hj (w j)) hleft
    (fun j _ ↦ hcost (w j)) (fun j hj ↦ hfactor j hj (w j)) hcross htleak false s

end JanetCartan.RegularSector.NormalizedResidualWords.ObservedChains
