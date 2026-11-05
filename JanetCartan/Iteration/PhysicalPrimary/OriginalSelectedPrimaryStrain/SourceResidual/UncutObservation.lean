module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.Normalized.Real
import all JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedObservedResidual.CorrectedSourceTail
import all JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.RecutRemainderObservation
import all JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalReal

/-!
# Observe the original inverse without a second source cutoff

The actual primary solver is `χ₃ * Inv(h)`, where the input `h` already
contains `χ₂`. The recut corrected-source theorem therefore does not apply to
this literal input. This variant uses the same finite Neumann identity and
the existing order-zero normalized source bound. Support of `h` and the left
mask of the original residual make every finite power fixed by `χ₃`; no
identity `χ₂ * h = h` is required or asserted.

The consumer is the source discrepancy in the actual primary strain
(`main:eq:primary-strain`, `app:ch_regular:eq:finite-neumann-identity`,
`app:ch_regular:eq:resolved-angular-tail`). The source first-mask estimates
and inverse remainder remain explicit here and are instantiated on the
original history graph in the adjacent application modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual

open LocalSobolev SmallSupport ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization
open FourierIntegral.LowBounds
open ArbitraryAccuracy.SelectedLocalization SignedProductEstimates

variable {d : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Put the two original smooth measurements on the corresponding local
input and output. In particular the input bump is after the inverse, not on
the original primary source (`app:ch_regular:eq:exact-physical`). -/
theorem measured_discrepancy_eq_bumps {D : Set E} (hD : MeasurableSet D)
    (V : Set E) (μ ν : ContDiffBump center) (T : H →L[ℂ] H) (u : LocalL2 D E) :
    localRealCompression hD V
      (measuredOperator μ ν μ.continuous ν.continuous
        (bump_norm_le_one μ) (bump_norm_le_one ν) T) u =
      bumpL2 (p := 2) le_rfl μ
        (localRealCompression hD V T (bumpL2 (p := 2) le_rfl ν u)) := by
  have hi : sourceCutMultiplier ν ν.continuous (bump_norm_le_one ν)
      (zeroExtend hD (l2ComplexInclusion (volume.restrict D) u)) =
      zeroExtend hD (l2ComplexInclusion (volume.restrict D)
        (bumpL2 (p := 2) le_rfl ν u)) := by
    rw [terminal_inclusion_bump, sourceCutMultiplier_zeroExtend_bump]
  calc
    _ = localRealCompression hD V
        ((sourceCutMultiplier μ μ.continuous (bump_norm_le_one μ)).comp T)
        (bumpL2 (p := 2) le_rfl ν u) :=
      congrArg (fun z : H ↦ l2RealPart (volume.restrict V)
        (restrictL2 V (sourceCutMultiplier μ μ.continuous (bump_norm_le_one μ) (T z)))) hi
    _ = _ := sourceCut_realCompression_eq_bump hD V μ T _

/-- The original outer bump fixes a datum supported in the inner bump's
support. This does not say the inner bump fixes that datum. -/
theorem outer_bump_fixes_supported {D : Set E} (χ₂ χ₃ : ContDiffBump center)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) (u : LocalL2 D E)
    (hsupport : ∀ᵐ y ∂volume.restrict D, y ∉ tsupport (χ₂ : E → ℝ) → u y = 0) :
    bumpL2 (p := 2) le_rfl χ₃ u = u := by
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₃ u, hsupport] with y hb hu
  rw [hb]
  by_cases hy : y ∈ tsupport (χ₂ : E → ℝ)
  · rw [hnest y hy, one_smul]
  · rw [hu hy, smul_zero]

private theorem bump_rapid {V : Set E} (hV : MeasurableSet V) (χ : ContDiffBump center)
    (hχ : tsupport (χ : E → ℝ) ⊆ V) (ρ A : ι → ℝ) (s : ℕ) (v : ι → LocalL2 V E)
    (h : RapidDecayAt (restrictionSobolevScale V E hV) s ρ A v) :
    RapidDecayAt (restrictionSobolevScale V E hV) s ρ A
      (fun i ↦ bumpL2 (p := 2) le_rfl χ (v i)) := by
  obtain ⟨B, hB, hb⟩ := exists_bumpL2_sobolev_bound (F := E) χ s
  intro q
  obtain ⟨C, hC, hc⟩ := h q
  refine ⟨B*C, mul_nonneg (zero_le_one.trans hB) hC, ?_⟩
  intro i
  obtain ⟨hm, hn⟩ := hb V hV hχ (v i) (hc i).1
  refine ⟨hm, ?_⟩
  rw [restrictionSobolevScale_gradeNorm hV hm]
  have hi := (hc i).2
  rw [restrictionSobolevScale_gradeNorm hV (hc i).1] at hi
  exact hn.trans ((mul_le_mul_of_nonneg_left hi (zero_le_one.trans hB)).trans_eq (by ring))

private theorem inverse_rapid_from_power_remainders {D V : Set E} (hV : MeasurableSet V)
    (K : ι → LocalL2 D E →L[ℝ] LocalL2 D E)
    (observe : LocalL2 D E →L[ℝ] LocalL2 V E) (Cobs : ℝ) (hCobs : 0 ≤ Cobs)
    (ρ A : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (s : ℕ) (u : ι → LocalL2 D E) (hK : ∀ i, ‖K i‖ < 1)
    (hcost : ∀ v, MemRestrictionSobolev D s v →
      MemRestrictionSobolev V s (observe v) ∧
        restrictionSobolevNorm V s (observe v) ≤ Cobs * restrictionSobolevNorm D s v)
    (hchain : ∀ j, RapidDecayAt (restrictionSobolevScale V E hV) s ρ A
      (fun i ↦ observe ((K i^j) (u i))))
    (hremainder : ∀ q : ℕ, ∃ depth : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      MemRestrictionSobolev D s (neumannInverse (K i) ((K i^(depth+s)) (u i))) ∧
      restrictionSobolevNorm D s (neumannInverse (K i) ((K i^(depth+s)) (u i))) ≤
        C*A i*((ρ i)^q)⁻¹) :
    RapidDecayAt (restrictionSobolevScale V E hV) s ρ A
      (fun i ↦ observe (neumannInverse (K i) (u i))) := by
  let G := restrictionSobolevScale V E hV
  intro accuracy
  obtain ⟨q, hq⟩ := exists_nat_gt accuracy
  obtain ⟨depth, Crem, hCrem, hrem⟩ := hremainder q
  let power := depth+s
  let rem := fun i ↦ neumannInverse (K i) ((K i^power) (u i))
  have hobsrem (i : ι) : observe (rem i) ∈ G.level s ∧
      G.gradeNorm s (observe (rem i)) ≤ Cobs*Crem*A i*(ρ i)^(-accuracy) := by
    obtain ⟨hm, hn⟩ := hcost (rem i) (hrem i).1
    refine ⟨hm, ?_⟩
    rw [restrictionSobolevScale_gradeNorm hV hm]
    have hrate : ((ρ i)^q)⁻¹ ≤ (ρ i)^(-accuracy) := by
      have hh := Real.rpow_le_rpow_of_exponent_le (hρ i) (neg_le_neg hq.le)
      simpa only [Real.rpow_neg (zero_le_one.trans (hρ i)), Real.rpow_natCast] using hh
    calc
      _ ≤ Cobs * restrictionSobolevNorm D s (rem i) := hn
      _ ≤ Cobs * (Crem*A i*((ρ i)^q)⁻¹) := mul_le_mul_of_nonneg_left (hrem i).2 hCobs
      _ = (Cobs*Crem*A i)*((ρ i)^q)⁻¹ := by ring
      _ ≤ (Cobs*Crem*A i)*(ρ i)^(-accuracy) :=
        mul_le_mul_of_nonneg_left hrate (mul_nonneg (mul_nonneg hCobs hCrem) (hA i))
  choose C hC hc using fun j ↦ hchain j accuracy
  refine ⟨Cobs*Crem + ∑ j ∈ Finset.range power, C j,
    add_nonneg (mul_nonneg hCobs hCrem) (Finset.sum_nonneg fun j _ ↦ hC j), ?_⟩
  intro i
  have hdecomp : observe (neumannInverse (K i) (u i)) =
      ((-1 : ℝ)^power) • observe (rem i) +
        ∑ j ∈ Finset.range power, ((-1 : ℝ)^j) • observe ((K i^j) (u i)) :=
    eq_add_of_sub_eq (finite_neumann_observation_identity (K i)
      (neumannInverse (K i)) (neumannInverse_mul_add _ (hK i))
      observe.toLinearMap power (u i))
  obtain ⟨hsm, hsb⟩ := signed_sum_bound G s power
    (fun j ↦ observe ((K i^j) (u i))) C (A i*(ρ i)^(-accuracy))
    (fun j _ ↦ (hc j i).1)
    (fun j _ ↦ by simpa only [mul_assoc] using (hc j i).2)
  have hrm := (G.level s).smul_mem ((-1 : ℝ)^power) (hobsrem i).1
  change observe (neumannInverse (K i) (u i)) ∈ G.level s ∧
    G.gradeNorm s (observe (neumannInverse (K i) (u i))) ≤ _
  rw [hdecomp]
  refine ⟨(G.level s).add_mem hrm hsm, (gradeNorm_add_le G hrm hsm).trans ?_⟩
  rw [G.gradeNorm_neg_one_pow_smul s power (hobsrem i).1]
  exact (add_le_add (hobsrem i).2 hsb).trans_eq (by ring)

private theorem restrict_observation_rapid {D V W : Set E} (hD : MeasurableSet D)
    (hV : MeasurableSet V) (hW : MeasurableSet W) (hWV : W ⊆ V)
    (χ : ContDiffBump center) (hχ : ∀ y ∈ W, χ y = 1) (T : H →L[ℂ] H)
    (ρ A : ι → ℝ) (s : ℕ) (u : ι → LocalL2 D E)
    (h : RapidDecayAt (restrictionSobolevScale V E hV) s ρ A
      (fun i ↦ bumpL2 (p := 2) le_rfl χ (localRealCompression hD V T (u i)))) :
    RapidDecayAt (restrictionSobolevScale W E hW) s ρ A
      (fun i ↦ localRealCompression hD W T (u i)) := by
  intro accuracy
  obtain ⟨C, hC, hc⟩ := h accuracy
  refine ⟨C, hC, ?_⟩
  intro i
  obtain ⟨hm, hn⟩ := observed_core_sobolev_bound hD V W hV hW hWV χ hχ T (u i) s (hc i).1
  refine ⟨hm, ?_⟩
  rw [restrictionSobolevScale_gradeNorm hW hm]
  have hb := (hc i).2
  rw [restrictionSobolevScale_gradeNorm hV (hc i).1] at hb
  exact hn.trans hb

/-- The finite inverse identity on the SAME already localized source gives
arbitrary angular decay for `χ₃ * Inv(h)`. Its only analytic inputs are the
observed powers and the unobserved inverse remainder of `h` itself. No
additional multiplication by `χ₂` occurs (`main:eq:primary-strain`,
`app:ch_regular:eq:resolved-angular-tail`). -/
theorem uncut_angular_rapidDecayAt_of_original_remainder
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (Q : ι → E → Fin (d+1) → MetricTensor (d+1)) (B : ι → E → MetricTensor (d+1))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1)) (retarded : ι → H →L[ℂ] H)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    {D : Set E} (hD : MeasurableSet D)
    (χ₂ χ₃ χobs : ContDiffBump center)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1)
    (hχ₃D : tsupport (χ₃ : E → ℝ) ⊆ D)
    (Vobs Wcore : Set E) (hVobs : MeasurableSet Vobs) (hWcore : MeasurableSet Wcore)
    (hχobsV : tsupport (χobs : E → ℝ) ⊆ Vobs) (hWV : Wcore ⊆ Vobs)
    (hχobsCore : ∀ y ∈ Wcore, χobs y = 1)
    (ρ A : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (s : ℕ) (u : ι → LocalL2 D E)
    (hsupport : ∀ i, ∀ᵐ y ∂volume.restrict D,
      y ∉ tsupport (χ₂ : E → ℝ) → u i y = 0) :
    let Krecut := fun i ↦ localRealCompression hD D
      (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
        (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
        (pairedResidual f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i)))
    let observation := localRealCompression hD Vobs
      (pairedSource f hK L₀ output ho.continuous hob - 1)
    (∀ i, ‖Krecut i‖ < 1) →
    (∀ j, RapidDecayAt (restrictionSobolevScale Vobs E hVobs) s ρ A
      (fun i ↦ observation ((Krecut i^j) (u i)))) →
    (∀ q : ℕ, ∃ depth : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      MemRestrictionSobolev D s (neumannInverse (Krecut i) ((Krecut i^(depth+s)) (u i))) ∧
      restrictionSobolevNorm D s (neumannInverse (Krecut i) ((Krecut i^(depth+s)) (u i))) ≤
        C*A i*((ρ i)^q)⁻¹) →
    RapidDecayAt (restrictionSobolevScale Wcore E hWcore) s ρ A
      (fun i ↦ localRealCompression hD Wcore
        (pairedSource f hK L₀ output ho.continuous hob - 1)
        (bumpL2 (p := 2) le_rfl χ₃ (neumannInverse (Krecut i) (u i)))) := by
  intro Krecut observation hKrecut hchain hremainder
  let G := restrictionSobolevScale Vobs E hVobs
  let cutObs : LocalL2 Vobs E →L[ℝ] LocalL2 Vobs E :=
    bumpL2 (p := 2) le_rfl χobs
  let observe : LocalL2 D E →L[ℝ] LocalL2 Vobs E :=
    localRealCompression hD Vobs
      (measuredOperator χobs χ₃ χobs.continuous χ₃.continuous
        (bump_norm_le_one χobs) (bump_norm_le_one χ₃)
        (pairedSource f hK L₀ output ho.continuous hob - 1))
  have hfix (i : ι) (j : ℕ) :
      bumpL2 (p := 2) le_rfl χ₃ ((Krecut i^j) (u i)) = (Krecut i^j) (u i) := by
    cases j with
    | zero => simpa only [pow_zero, one_apply_eq_self] using
        outer_bump_fixes_supported χ₂ χ₃ hnest (u i) (hsupport i)
    | succ j =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        recut_real_measured_plateau hD χ₂ χ₃ hnest
          (pairedResidual f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i))
          ((Krecut i^j) (u i))
  have hobserve (v : LocalL2 D E) :
      observe v = cutObs (observation (bumpL2 (p := 2) le_rfl χ₃ v)) :=
    measured_discrepancy_eq_bumps hD Vobs χobs χ₃ _ v
  have hchainCut (j : ℕ) : RapidDecayAt G s ρ A
      (fun i ↦ observe ((Krecut i^j) (u i))) := by
    have he : (fun i ↦ observe ((Krecut i^j) (u i))) =
        (fun i ↦ bumpL2 (p := 2) le_rfl χobs (observation ((Krecut i^j) (u i)))) := by
      funext i
      exact (hobserve _).trans (congrArg (fun v ↦ cutObs (observation v)) (hfix i j))
    rw [he]
    exact bump_rapid hVobs χobs hχobsV ρ A s _ (hchain j)
  obtain ⟨Cobs, hCobs, hcost⟩ := exists_normalizedRealSource_measured_discrepancy_signed_constants
    f hK output ho hoc hob χobs χ₃ χobs.contDiff χ₃.contDiff
    χobs.hasCompactSupport χ₃.hasCompactSupport
    (bump_norm_le_one χobs) (bump_norm_le_one χ₃)
  have htail := inverse_rapid_from_power_remainders hVobs Krecut observe (Cobs s) (hCobs s)
    ρ A hρ hA s u hKrecut (hcost L₀ hL₀ D Vobs hD hVobs hχ₃D hχobsV s).1 hchainCut hremainder
  have he : (fun i ↦ observe (neumannInverse (Krecut i) (u i))) =
      (fun i ↦ bumpL2 (p := 2) le_rfl χobs
        (observation (bumpL2 (p := 2) le_rfl χ₃ (neumannInverse (Krecut i) (u i))))) :=
    funext (fun i ↦ hobserve _)
  rw [he] at htail
  exact restrict_observation_rapid hD hVobs hWcore hWV χobs hχobsCore
    (pairedSource f hK L₀ output ho.continuous hob - 1) ρ A s
    (fun i ↦ bumpL2 (p := 2) le_rfl χ₃ (neumannInverse (Krecut i) (u i))) htail

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual
