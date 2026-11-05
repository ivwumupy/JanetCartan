module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.TerminalDefect
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.TerminalLocalizerCost
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.RestrictionFactors.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalRecut
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.Normalized.Restriction

/-!
# The normalized terminal source on a supported complete chain

Apply the actual normalized terminal source estimate after moving the prescribed
right localizer to the full measured word. Only that full word needs the original
physical support. This retains the source's low collar and ONE identity
subtraction in `app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open ResponseTransfer FourierIntegral FourierIntegral.LowBounds FiniteChain.Graph LocalSobolev Pseudodifferential
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
local notation "Hu" => LocalL2 (univ : Set E) V
local notation "G" => restrictionSobolevScale (univ : Set E) V MeasurableSet.univ

/-- Apply the actual supported terminal source estimate and its proved
polynomial cost to the full finite chain. The analytic inputs are individual
factor and terminal-mask leakage, with their existing primitive producers;
no estimate of the observed chain is assumed. The original physical cutoff
fixes each full factor's range and the initial datum. Both literal source
orientations retain the same `pairedSource - 1`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem normalizedSource_finiteChain_observation_rapidDecayAt
    (f : ActualMaskFamily Ω x RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (χ₃ : ContDiffBump x) (U : Set E) (hU : IsOpen U)
    (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ U)
    (hcore : U ⊆ ball x f.physicalRadius) (houtput : ∀ y ∈ U, output y = 1)
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mt, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mt, NormedSpace.normalize p.2 ∈ K)
    (n : ℕ) (T M : ℕ → ι → Hu →ₗ[ℝ] Hu) (Mt : ι → H →L[ℂ] H)
    (u : ι → Hu) (ρ L A : ι → ℝ) (σ : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (hσ : 0 < σ) (hscale : ∀ i, L i ≤ (ρ i)^(1-σ)) (hA : ∀ i, 0 ≤ A i)
    (hMt : ∀ i v, Mt i v =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (rightLocalizer (ρ i) mt (fun z ↦ (v z).ofLp) y))
    (hu : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖u i‖ ≤ D*A i*(ρ i)^a)
    (hsource : ∀ s, RapidDecayAt G s ρ A (fun i ↦ u i-M 0 i (u i)))
    (hsourceSupport : ∀ i,
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ (u i)) =
      SmallSupport.zeroExtend MeasurableSet.univ (u i))
    (hfactorSupport : ∀ j < n, ∀ i v,
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ v) =
      SmallSupport.zeroExtend MeasurableSet.univ v →
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ (T j i v)) =
      SmallSupport.zeroExtend MeasurableSet.univ (T j i v))
    (hfullLow : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v, ‖T j i v‖ ≤ D*(ρ i)^c*‖v‖)
    (hlow : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖T j i (M j i v)‖ ≤ D*(ρ i)^c*‖v‖)
    (hcost : ∀ j < n, HasPolynomialSobolevCost G G ρ (T j))
    (hleak : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-M (j+1) i) (T j i (M j i v)) ∈ (G).level s ∧
        (G).gradeNorm s ((1-M (j+1) i) (T j i (M j i v))) ≤
          C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖)
    (htleak : ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-(localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap)
          (M n i v) ∈ (G).level s ∧
        (G).gradeNorm s ((1-(localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap)
          (M n i v)) ≤ C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖) :
    ∀ backward : Bool, ∀ s,
      let S := pairedSource f hK L₀ output ho.continuous
        (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
      let P := if backward then S.adjoint else S
      RapidDecayAt G s ρ A (fun i ↦ restrictL2 univ ((P-1)
        (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i)))) := by
  let R i := (localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap
  have hdef := finiteChain_terminal_defect_rapidDecayAt (fun _ ↦ G) n T M R u ρ L A σ
    hρ (fun i ↦ zero_le_one.trans (hL i)) hσ hscale hA hu hsource hlow hcost hleak
    (terminalRightLocalizer_hasPolynomialRestrictionCost mt ht htc ρ hρ Mt hMt) htleak
  obtain ⟨D, a, hD, hnorm⟩ := factorChain_polynomial_norm T u ρ A n hρ hu hfullLow n le_rfl
  have hsupported : ∀ j ≤ n, ∀ i,
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u j i)) =
      SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u j i) := by
    intro j hj
    induction j with
    | zero => exact hsourceSupport
    | succ j ih =>
      intro i
      exact hfactorSupport j (by omega) i _ (ih (by omega) i)
  intro backward s S P
  let Bobs : ι → Hu →ₗ[ℝ] Hu := fun _ ↦
    (localRetardedOperator MeasurableSet.univ univ P).toLinearMap-LinearMap.id
  have hBcost : HasPolynomialSobolevCost G G ρ Bobs := by
    have h := normalizedSource_discrepancy_hasPolynomialRestrictionCost
      f hK output ho hoc (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
      ρ (fun _ ↦ L₀) (fun _ ↦ hL₀) univ MeasurableSet.univ
      (subset_univ _) (subset_univ _) backward
    cases backward <;>
      simpa only [Bobs, P, S, Bool.false_eq_true, ite_true, ite_false,
        localRetardedOperator_adjoint MeasurableSet.univ MeasurableSet.univ] using h
  have herr := rapidDecayAt_polynomial_factor hρ hA hBcost hdef s
  obtain ⟨C, _, hC, _, hterminalBound⟩ :=
    SignedProductEstimates.exists_normalizedSource_supported_terminal_bounds
      f hK hsym L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃ hcore houtput mt ht htc hlo hann hterminal s
  have hnear : RapidDecayAt G s ρ A (fun i ↦ Bobs i (R i (factorChain T u n i))) := by
    apply rapidDecayAt_of_factor_bounds G s ρ L A _ σ ((d+1+s : ℕ)+a) 0
      hρ (fun i ↦ zero_le_one.trans (hL i)) hσ hscale hA
    intro q
    refine ⟨C q*D, mul_nonneg (hC q) hD, ?_⟩
    intro i
    have hb := (hterminalBound (ρ i) (L i) (hL i) (hLρ i) (Mt i) (hMt i) q
      univ MeasurableSet.univ (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i))
      (hsupported n le_rfl i) backward).1
    have he : Bobs i (R i (factorChain T u n i)) = restrictL2 univ ((P-1)
        (Mt i (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i)))) := by
      change restrictL2 univ (P (SmallSupport.zeroExtend MeasurableSet.univ
          (restrictL2 univ (Mt i (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i)))))) -
        restrictL2 univ (Mt i (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i))) = _
      rw [zeroExtend_restrictL2_univ, sub_apply, one_apply_eq_self, map_sub]
    rw [he]
    refine ⟨hb.1, hb.2.trans ?_⟩
    rw [LinearIsometry.norm_map]
    have hCq := hC q
    have hρi : 0 ≤ ρ i := zero_le_one.trans (hρ i)
    have hLi : 0 ≤ L i := zero_le_one.trans (hL i)
    calc
      _ ≤ C q*(ρ i)^((d+1+s : ℕ):ℝ)*L i^0*(L i/ρ i)^q*(D*A i*(ρ i)^a) :=
        mul_le_mul_of_nonneg_left (hnorm i) (by positivity)
      _ = _ := by rw [Real.rpow_add (zero_lt_one.trans_le (hρ i))]; ring
  intro accuracy
  obtain ⟨Ce, hCe, he⟩ := herr accuracy
  obtain ⟨Ct, hCt, ht⟩ := hnear accuracy
  refine ⟨Ce+Ct, add_nonneg hCe hCt, ?_⟩
  intro i
  have hid : restrictL2 univ ((P-1)
      (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i))) =
    Bobs i (factorChain T u n i-R i (factorChain T u n i)) +
      Bobs i (R i (factorChain T u n i)) := by
    simp only [map_sub, sub_add_cancel]
    change restrictL2 univ ((P-1) (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i))) =
      restrictL2 univ (P (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i))) -
        factorChain T u n i
    rw [sub_apply, one_apply_eq_self, map_sub, restrictL2_zeroExtend]
  dsimp only
  rw [hid]
  refine ⟨((G).level s).add_mem (he i).1 (ht i).1,
    (gradeNorm_add_le G (he i).1 (ht i).1).trans ?_⟩
  exact (add_le_add (he i).2 (ht i).2).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
