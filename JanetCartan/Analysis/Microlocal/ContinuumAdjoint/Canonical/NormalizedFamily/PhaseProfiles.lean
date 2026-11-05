module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedPhase

/-!
# Compact profiles for the same normalized Hamilton phase

The phase, physical covector and Hamilton footpoint are the literal fields of
`FrozenModel.normalizedCarrierData`. Their compact range, a positive covector
gap, and all mixed and fixed-scale derivative bounds are constructed through
scale zero. The original carrier labels and compact sets are unchanged.

These are primitive inputs for the normalized application of
`UniformEndpoint.exists_uniform_scalarTransportCarrierAdjoint_periodic_raw_bound`
in `app:ch_background:prop:bg-adjoint`. No operator bound, ODE-footpoint
identification, or conic inverse estimate is assumed or asserted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open ContinuumNormal.FrozenModel NormalizedBackground

private theorem norm_iteratedFDeriv_slice_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {I : Set ℝ} {V : Set E}
    (hI : IsOpen I) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f (I ×ˢ V))
    {σ : ℝ} (hσ : σ ∈ I) {x : E} (hx : x ∈ V) (s : ℕ) :
    ‖iteratedFDeriv ℝ s (fun y ↦ f (σ, y)) x‖ ≤
      ‖iteratedFDeriv ℝ s f (σ, x)‖ := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  let W := (fun y : ℝ × E ↦ y + (σ, 0)) ⁻¹' (I ×ˢ V)
  have hW : IsOpen W := (hI.prod hV).preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ ∞ (fun y ↦ f (y + (σ, 0))) W :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (fun _ hy ↦ hy)
  have hpre : IsOpen (L ⁻¹' W) := hW.preimage L.continuous
  have hxW : L x ∈ W := by simpa [L, W] using And.intro hσ hx
  have he := L.iteratedFDerivWithin_comp_right hg hW.uniqueDiffOn hpre.uniqueDiffOn
    hxW (i := s) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hxW,
    iteratedFDerivWithin_of_isOpen _ hW hxW, iteratedFDeriv_comp_add_right] at he
  have he' : iteratedFDeriv ℝ s (fun y ↦ f (σ, y)) x =
      (iteratedFDeriv ℝ s f (σ, x)).compContinuousLinearMap (fun _ ↦ L) := by
    simpa [L, Function.comp_def] using he
  rw [he']
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    (fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ℝ ℝ E)

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Compact parameter range and uniform profiles for the SAME normalized
phase, covector and Hamilton footpoint (`app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-derivative-trade`). The positive covector gap and the
entire derivative profile precede `σ`, including `σ = 0`. The fixed-scale
derivatives include every physical and carrier direction; the joint derivatives
also include scale. Consumer: the phase and coefficient inputs of the
normalized literal-adjoint endpoint. -/
theorem exists_normalized_phase_compact_profiles {c C : ℝ} (hP : P.IsValid c C)
    {D : Set (Euclidean n)} (hD : IsCompact D)
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hKW : K ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let W := parameter ⁻¹' parameterInterior (3 * P.radius / 2)
    let J := fun q : ℝ × (Euclidean n × CarrierParameter) ↦
      (normalizedPhase T Q q.1 q.2.1 (T.reference.spatialPatch (parameter q.2.2)),
        normalizedCovector T Q q.1 q.2.1 q.2.2,
        normalizedTransportPosition T Q q.1 q.2)
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧ ∃ κ > (0 : ℝ),
    ∃ A : ℕ → ℝ, (∀ s, 0 < A s) ∧
      ContDiffOn ℝ ∞ J (Ioo (-2 * σ₀) (2 * σ₀) ×ˢ B ×ˢ W) ∧
      IsCompact (J '' (Icc (0 : ℝ) σ₀ ×ˢ D ×ˢ K)) ∧
      (∀ σ ∈ Icc (0 : ℝ) σ₀, ∀ x ∈ D, ∀ z ∈ K,
        κ ≤ ‖normalizedCovector T Q σ x z‖) ∧
      (∀ s σ, σ ∈ Icc (0 : ℝ) σ₀ → ∀ x ∈ D, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ s J (σ, (x, z))‖ ≤ A s ∧
        ‖iteratedFDeriv ℝ s (fun p ↦ J (σ, p)) (x, z)‖ ≤ A s) ∧
      ∀ s σ, σ ∈ Icc (0 : ℝ) σ₀ →
        cNorm (D ×ˢ K) s (fun p ↦ J (σ, p)) ≤
          ∑ j ∈ Finset.range (s + 1), A j := by
  dsimp only
  let W := parameter ⁻¹' parameterInterior (3 * P.radius / 2)
  let J := fun q : ℝ × (Euclidean n × CarrierParameter) ↦
    (normalizedPhase T Q q.1 q.2.1 (T.reference.spatialPatch (parameter q.2.2)),
      normalizedCovector T Q q.1 q.2.1 q.2.2,
      normalizedTransportPosition T Q q.1 q.2)
  obtain ⟨B, hB, hDB, σ₀, hσ₀, hσ₁, hJ, hmaps, _, hbound⟩ :=
    exists_retained_phase_normalization_bounds T Q hP hD hK hKW
  have hW : IsOpen W := (isOpen_parameterInterior _).preimage parameter.continuous
  have hscale : Icc (0 : ℝ) σ₀ ⊆ Ioo (-2 * σ₀) (2 * σ₀) := by
    intro σ hσ
    constructor <;> linarith [hσ.1, hσ.2]
  have hsub : Icc (0 : ℝ) σ₀ ×ˢ D ×ˢ K ⊆
      Ioo (-2 * σ₀) (2 * σ₀) ×ˢ B ×ˢ W :=
    prod_mono hscale (prod_mono hDB hKW)
  have hcompact : IsCompact (Icc (0 : ℝ) σ₀ ×ˢ D ×ˢ K) :=
    isCompact_Icc.prod (hD.prod hK)
  have hne : ∀ p ∈ Icc (0 : ℝ) σ₀ ×ˢ D ×ˢ K,
      0 < ‖normalizedCovector T Q p.1 p.2.1 p.2.2‖ := by
    intro p hp
    have hx := hmaps p.1 (hscale hp.1) p.2.1 (hDB hp.2.1)
    have hz : parameter p.2.2 ∈ parameterInterior (2 * P.radius) := by
      intro i
      exact (hKW hp.2.2 i).trans (by linarith [hP.1])
    rw [normalizedCovector_eq_retainedCarrierGradient T Q hP hx hz]
    exact norm_pos_iff.mpr (retained_carrierGradient_ne_zero T Q hx hz)
  obtain ⟨κ, hκ, hgap⟩ := hcompact.exists_forall_le'
    ((hJ.snd.fst.continuousOn.norm).mono hsub) hne
  choose A hA hA_bound using hbound
  have hslice (s : ℕ) (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) σ₀)
      (x : Euclidean n) (hx : x ∈ D) (z : CarrierParameter) (hz : z ∈ K) :
      ‖iteratedFDeriv ℝ s (fun p ↦ J (σ, p)) (x, z)‖ ≤ A s :=
    (norm_iteratedFDeriv_slice_le isOpen_Ioo (hB.prod hW) hJ
      (hscale hσ) ⟨hDB hx, hKW hz⟩ s).trans (hA_bound s σ hσ x hx z hz)
  refine ⟨B, hB, hDB, σ₀, hσ₀, hσ₁, κ, hκ, A, hA, hJ,
    hcompact.image_of_continuousOn (hJ.continuousOn.mono hsub),
    fun σ hσ x hx z hz ↦ hgap (σ, (x, z)) ⟨hσ, hx, hz⟩,
    fun s σ hσ x hx z hz ↦ ⟨hA_bound s σ hσ x hx z hz, hslice s σ hσ x hx z hz⟩, ?_⟩
  intro s σ hσ
  exact cNorm_le_sum_of_bounds (fun j _ ↦ (hA j).le)
    (fun j _ p hp ↦ hslice j σ hσ p.1 hp.1 p.2 hp.2)

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
