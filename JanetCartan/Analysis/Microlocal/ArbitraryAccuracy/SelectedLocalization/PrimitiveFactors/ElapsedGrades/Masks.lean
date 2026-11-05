module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.CommonMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhaseGrades

/-!
# Joint grades of the actual common physical masks and multiplier

The multiplier is fixed at `2 * threshold`. Its normalized seminorm controls
all source frequencies `ρ ≥ 1`; the unrelated slow scale `L` only enlarges
the bound. Constants are uniform over the original finite family and chosen
before the accuracy. Consumer: the three physical-mask components of
`CompleteFactor.hprimitiveMasks` (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FinitePdo
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FiniteEvolution.PhysicalCutoff
open RegularSector.Characteristic.ResidualCoordinates
open FourierIntegral FourierIntegral.PrimitiveProfiles FiniteChain.Graph
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E

/-- The SAME endpoint output, chart input, and selected multiplier have
uniform joint elapsed profiles with zero slow-scale offsets. The joint carrier
must be compact and exclude zero in its normalized source covector; these are
geometric inclusions for the protected-mask assembly, not analytic bounds.
This supplies `Qt`, `Qs`, and `Qg` in `CompleteFactor`, retaining the coordinate
permutation inside the fixed doubled cutoff (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_selected_elapsed_mask_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (J : f.centers → Set V) (hJ : ∀ p, IsCompact (J p))
    (hzero : ∀ p, ∀ v ∈ J p, v.2.2.1 ≠ 0) :
    ∃ Qt Qs Qg : ℕ → ℝ,
      (∀ m, 0 ≤ Qt m) ∧ (∀ m, 0 ≤ Qs m) ∧ (∀ m, 0 ≤ Qg m) ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ → ∀ p, ∀ v ∈ J p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ endpointOutputMask f p output w.2.1.1) v‖ ≤
          Qt m * L ^ m ∧
        ‖iteratedFDeriv ℝ m (fun w : V ↦ chartInputMask f p w.2.1.2) v‖ ≤
          Qs m * L ^ m ∧
        ‖iteratedFDeriv ℝ m (fun w : V ↦ selectedEndpointMultiplier f p threshold (ρ • w.2.2.1)) v‖ ≤
          Qg m * L ^ m := by
  classical
  let π : V →L[ℝ] ℝ × E :=
    (0 : V →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.fst ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
  let β := fun p ↦ selectedEndpointMultiplier f p threshold
  let Jβ := fun p ↦ π '' J p
  have hJβ p : IsCompact (Jβ p) := (hJ p).image π.continuous
  have hJzero p : ∀ v ∈ Jβ p, v.2 ≠ 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hzero p v hv
  have hβ p m : BoundedNormalizedSeminorm (Jβ p) m (fun w : ℝ × E ↦ β p w.2) :=
    boundedNormalizedSeminorm_physical_dilatedConicMask (f.angularMask_smooth p)
      (f.chart p).index hthreshold (hJβ p) (hJzero p) m
  let Dt := fun p m ↦ cNorm (J p) m (fun w : V ↦ endpointOutputMask f p output w.2.1.1)
  let Ds := fun p m ↦ cNorm (J p) m (fun w : V ↦ chartInputMask f p w.2.1.2)
  let Dg := fun p m ↦ normalizedSeminorm (Jβ p) m (fun w : ℝ × E ↦ β p w.2) * ‖π‖ ^ m
  have hDt p m : 0 ≤ Dt p m := cNorm_nonneg _ _ _
  have hDs p m : 0 ≤ Ds p m := cNorm_nonneg _ _ _
  have hDg p m : 0 ≤ Dg p m := mul_nonneg (normalizedSeminorm_nonneg _ _ _)
    (pow_nonneg (norm_nonneg _) _)
  refine ⟨fun m ↦ ∑ p, Dt p m, fun m ↦ ∑ p, Ds p m, fun m ↦ ∑ p, Dg p m,
    fun m ↦ Finset.sum_nonneg (fun p _ ↦ hDt p m),
    fun m ↦ Finset.sum_nonneg (fun p _ ↦ hDs p m),
    fun m ↦ Finset.sum_nonneg (fun p _ ↦ hDg p m), ?_⟩
  intro L ρ hL hρ p v hv m
  have henlarge (D : f.centers → ℝ) (hD : ∀ p, 0 ≤ D p) : D p ≤ (∑ p, D p) * L ^ m :=
    (Finset.single_le_sum (fun p _ ↦ hD p) (Finset.mem_univ p)).trans
      (le_mul_of_one_le_right (Finset.sum_nonneg (fun p _ ↦ hD p)) (one_le_pow₀ hL))
  have hts : ContDiff ℝ ∞ (fun w : V ↦ endpointOutputMask f p output w.2.1.1) :=
    (endpointOutputMask_properties f p ho hoc hout).1.comp contDiff_snd.fst.fst
  have hss : ContDiff ℝ ∞ (fun w : V ↦ chartInputMask f p w.2.1.2) :=
    (chartPhysicalMasks_properties f p).2.1.comp contDiff_snd.fst.snd
  refine ⟨(norm_iteratedFDeriv_le_cNorm (hJ p) (hts.of_le (by simp)) hv le_rfl).trans
      (henlarge (fun p ↦ Dt p m) (fun p ↦ hDt p m)),
    (norm_iteratedFDeriv_le_cNorm (hJ p) (hss.of_le (by simp)) hv le_rfl).trans
      (henlarge (fun p ↦ Ds p m) (fun p ↦ hDs p m)), ?_⟩
  have hn : ContDiff ℝ ∞ (normalizedField ρ (fun w : ℝ × E ↦ β p w.2)) :=
    (selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.const_smul ρ)
  have he : (fun w : V ↦ β p (ρ • w.2.2.1)) =
      normalizedField ρ (fun w : ℝ × E ↦ β p w.2) ∘ π := rfl
  change ‖iteratedFDeriv ℝ m (fun w : V ↦ β p (ρ • w.2.2.1)) v‖ ≤ _
  rw [he, π.iteratedFDeriv_comp_right hn v (by simp)]
  apply ((iteratedFDeriv ℝ m (normalizedField ρ (fun w : ℝ × E ↦ β p w.2))
    (π v)).norm_compContinuousLinearMap_le (fun _ ↦ π)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply (mul_le_mul_of_nonneg_right
    ((norm_iteratedFDeriv_le_cNorm (hJβ p) (hn.of_le (by simp))
      (mem_image_of_mem π hv) le_rfl).trans (cNorm_normalizedField_le (hβ p m) hρ))
    (pow_nonneg (norm_nonneg _) _)).trans
  exact henlarge (fun p ↦ Dg p m) (fun p ↦ hDg p m)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
