module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Inputs
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Full momentum comparison from joint phase comparison

For `app:lem:common-hamilton-phase` and Step 1 of
`app:ch_seed:prop:seed-actual-menu`, the full momentum is a fixed contraction
of the joint phase differential. Its full Fréchet derivative therefore costs
exactly two phase derivatives. The consumer is `CarrierFullPhaseInput.comparison`.
This deduction does not supply the phase continuity hypothesis; the concrete
common Hamilton family supplies that hypothesis separately.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase

variable {n : ℕ}

/-- Physical Riesz extraction from the full phase differential, retaining all
canonical variables (`app:lem:common-hamilton-phase`). -/
def momentumDifferentialExtraction :
    ((Euclidean n × (ℝ × Euclidean (n - 1))) →L[ℝ] ℝ) →L[ℝ] Euclidean n :=
  (InnerProductSpace.toDual ℝ (Euclidean n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℝ (Euclidean n)
      (Euclidean n × (ℝ × Euclidean (n - 1))) ℝ).flip
        (ContinuousLinearMap.inl ℝ (Euclidean n) (ℝ × Euclidean (n - 1))))

/-- The physical extraction is a contraction for the shared product maximum
norm (`app:lem:common-hamilton-phase`). -/
theorem norm_momentumDifferentialExtraction_le :
    ‖momentumDifferentialExtraction (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖(InnerProductSpace.toDual ℝ (Euclidean n)).symm
    (L.comp (ContinuousLinearMap.inl ℝ _ _))‖ ≤ 1 * ‖L‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  simpa using L.le_opNorm (v, 0)

variable {H H₀ : HomogeneousSymbol (Euclidean n)}
  {Φ : HamiltonFlow H (Euclidean (n - 1))}
  {Φ₀ : HamiltonFlow H₀ (Euclidean (n - 1))}

/-- The actual chart momentum is extracted from the actual full phase
differential (`app:lem:common-hamilton-phase`). -/
theorem chartMomentum_eq_extracted_phaseDifferential (C : ProjectionChart Φ)
    {q : Euclidean n × (ℝ × Euclidean (n - 1))} (hq : q ∈ C.target) :
    C.chartMomentum q = momentumDifferentialExtraction (fderiv ℝ (phase C.coordinates) q) := by
  rw [(C.hasFDerivAt_phase hq).fderiv]
  apply (InnerProductSpace.toDual ℝ (Euclidean n)).injective
  ext v
  change ⟪C.chartMomentum q, v⟫_ℝ =
    (InnerProductSpace.toDual ℝ (Euclidean n))
      ((InnerProductSpace.toDual ℝ (Euclidean n)).symm _) v
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp [phaseDifferential_apply, ProjectionChart.chartMomentum]

/-- Local smoothness of the full phase gives local smoothness of its actual
momentum without an additional flow regularity premise
(`app:lem:common-hamilton-phase`). -/
theorem contDiffAt_chartMomentum_of_phase (C : ProjectionChart Φ)
    {q : Euclidean n × (ℝ × Euclidean (n - 1))} (hq : q ∈ C.target)
    (hS : ContDiffAt ℝ ∞ (phase C.coordinates) q) :
    ContDiffAt ℝ ∞ C.chartMomentum q := by
  have he : C.chartMomentum =ᶠ[𝓝 q]
      momentumDifferentialExtraction ∘ fderiv ℝ (phase C.coordinates) :=
    eventuallyEq_of_mem (C.isOpen_target.mem_nhds hq)
      (fun z hz ↦ chartMomentum_eq_extracted_phaseDifferential C hz)
  exact (momentumDifferentialExtraction.contDiff.contDiffAt.comp q
    (hS.fderiv_right (m := ∞) (by simp))).congr_of_eventuallyEq he

/-- Every joint momentum-difference jet costs exactly one joint phase jet.
In particular this includes physical and canonical directions in the full
Fréchet derivative (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem norm_iteratedFDeriv_chartMomentum_sub_le (C : ProjectionChart Φ)
    (C₀ : ProjectionChart Φ₀)
    {q : Euclidean n × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ C.target) (hq₀ : q ∈ C₀.target)
    (hS : ContDiffAt ℝ ∞ (phase C.coordinates) q)
    (hS₀ : ContDiffAt ℝ ∞ (phase C₀.coordinates) q) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (C.chartMomentum - C₀.chartMomentum) q‖ ≤
      ‖iteratedFDeriv ℝ (k + 1)
        (phase C.coordinates - phase C₀.coordinates) q‖ := by
  let f := phase C.coordinates - phase C₀.coordinates
  have hf : ContDiffAt ℝ ∞ f q :=
    hS.sub hS₀
  have he : C.chartMomentum - C₀.chartMomentum =ᶠ[𝓝 q]
      momentumDifferentialExtraction ∘ fderiv ℝ f := by
    filter_upwards [C.isOpen_target.mem_nhds hq, C₀.isOpen_target.mem_nhds hq₀] with z hz hz₀
    simp only [Pi.sub_apply, Function.comp_apply, f,
      fderiv_sub (C.hasFDerivAt_phase hz).differentiableAt
        (C₀.hasFDerivAt_phase hz₀).differentiableAt, map_sub,
      ← chartMomentum_eq_extracted_phaseDifferential C hz,
      ← chartMomentum_eq_extracted_phaseDifferential C₀ hz₀]
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  calc
    _ ≤ ‖momentumDifferentialExtraction (n := n)‖ *
        ‖iteratedFDeriv ℝ k (fderiv ℝ f) q‖ :=
      momentumDifferentialExtraction.norm_iteratedFDeriv_comp_left
        (hf.fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) q‖ :=
      mul_le_mul_of_nonneg_right norm_momentumDifferentialExtraction_le (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- Full momentum and full derivative comparison on a compact common target
follow from joint `C²` phase comparison. This discharges the two estimates in
`CarrierFullPhaseInput.comparison` once the constructed family supplies its
phase tolerance (`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem chartMomentum_comparison_le_phase_cNorm_two (C : ProjectionChart Φ)
    (C₀ : ProjectionChart Φ₀)
    {K : Set (Euclidean n × (ℝ × Euclidean (n - 1)))} (hK : IsCompact K)
    (hKC : K ⊆ C.target) (hKC₀ : K ⊆ C₀.target)
    (hS : ∀ z ∈ K, ContDiffAt ℝ ∞ (phase C.coordinates) z)
    (hS₀ : ∀ z ∈ K, ContDiffAt ℝ ∞ (phase C₀.coordinates) z)
    {q : Euclidean n × (ℝ × Euclidean (n - 1))} (hq : q ∈ K) :
    ‖C.chartMomentum q - C₀.chartMomentum q‖ ≤
        cNorm K 2 (phase C.coordinates - phase C₀.coordinates) ∧
      ‖fderiv ℝ C.chartMomentum q - fderiv ℝ C₀.chartMomentum q‖ ≤
        cNorm K 2 (phase C.coordinates - phase C₀.coordinates) := by
  have hf : ∀ z ∈ K, ContDiffAt ℝ 2 (phase C.coordinates - phase C₀.coordinates) z := by
    intro z hz
    exact ((hS z hz).sub (hS₀ z hz)).of_le (by simp)
  constructor
  · have hh := (norm_iteratedFDeriv_chartMomentum_sub_le C C₀
      (hKC hq) (hKC₀ hq) (hS q hq) (hS₀ q hq) 0).trans
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hq (by norm_num : 0 + 1 ≤ 2))
    simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hh
  · have hh := (norm_iteratedFDeriv_chartMomentum_sub_le C C₀
      (hKC hq) (hKC₀ hq) (hS q hq) (hS₀ q hq) 1).trans
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hq (by norm_num : 1 + 1 ≤ 2))
    rw [norm_iteratedFDeriv_one,
      fderiv_sub
        ((contDiffAt_chartMomentum_of_phase C (hKC hq) (hS q hq)).differentiableAt (by simp))
        ((contDiffAt_chartMomentum_of_phase C₀ (hKC₀ hq) (hS₀ q hq)).differentiableAt (by simp))] at hh
    exact hh

end JanetCartan.ActualCarriers.CurrentFullPhase
