module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.SourceFootpoint
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# All-order bounds for the matched source density footpoint

Apply the existing integral extension of the seed inverse to the SAME
positive-scale inverse supplied by the source transport matching. One fixed
scale interval works at every order, and the initial labels stay unchanged.
The consumer is the actual density coefficient assembly, followed by the
full reflected amplitude in `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedCarrierProfiles
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport CanonicalCarrier
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference WideDensity
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol

/-- Restricting the divided footpoint to a fixed scale loses no spatial or
carrier derivative (`app:ch_background:prop:bg-normalized`). -/
private theorem norm_iteratedFDeriv_source_footpoint_slice_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {I : Set ℝ} {V : Set E}
    (hI : IsOpen I) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f (I ×ˢ V))
    {σ : ℝ} (hσ : σ ∈ I) {x : E} (hx : x ∈ V) (p : ℕ) :
    ‖iteratedFDeriv ℝ p (fun y ↦ f (σ, y)) x‖ ≤
      ‖iteratedFDeriv ℝ p f (σ, x)‖ := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  let W := (fun y : ℝ × E ↦ y + (σ, 0)) ⁻¹' (I ×ˢ V)
  have hW : IsOpen W := (hI.prod hV).preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ ∞ (fun y ↦ f (y + (σ, 0))) W :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (fun _ hy ↦ hy)
  have hpre : IsOpen (L ⁻¹' W) := hW.preimage L.continuous
  have hxW : L x ∈ W := by simpa [L, W] using And.intro hσ hx
  have he := L.iteratedFDerivWithin_comp_right hg hW.uniqueDiffOn hpre.uniqueDiffOn
    hxW (i := p) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hxW,
    iteratedFDerivWithin_of_isOpen _ hW hxW, iteratedFDeriv_comp_add_right] at he
  have he' : iteratedFDeriv ℝ p (fun y ↦ f (σ, y)) x =
      (iteratedFDeriv ℝ p f (σ, x)).compContinuousLinearMap (fun _ ↦ L) := by
    simpa [L, Function.comp_def] using he
  rw [he']
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
      (fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ℝ ℝ E))

/-- All-order primitive bounds for the actual matched source ODE inverse.
The seed smoothness and Cauchy identities are outputs of
`exists_retained_seed_matched_unit_transport`; its positive-scale branch
supplies the displayed matching identity. No bound on the varying inverse
is a premise. The common interval is fixed before every derivative order,
and includes the limit only through the literal integral extension
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_source_densityFootpoint_profiles {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    (hD : D.region ⊆ ball (0 : Euclidean n) R ×ˢ V) :
    ∃ H : ℕ → ℝ, (∀ p, 0 < H p) ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 8),
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        D.region →
      ContDiffOn ℝ ∞ (densityFootpoint T Yσ) D.region ∧
        ∀ p, cNorm D.carrier p (densityFootpoint T Yσ) ≤ H p := by
  let g := sourceDensityFootpointExtension T Y
  let I := Ioo (-(1 / 4) : ℝ) (1 / 4)
  let W := ball (0 : Euclidean n) R ×ˢ V
  have hW : IsOpen W := isOpen_ball.prod hV
  have hg : ContDiffOn ℝ ∞ g (I ×ˢ W) := sourceDensityFootpointExtension_contDiffOn T hV hY
  have hK : IsCompact D.carrier := isCompact_closedBall ..
  have hscale : Icc (0 : ℝ) (1 / 8) ⊆ I := by
    intro σ hσ
    constructor <;> linarith [hσ.1, hσ.2]
  have hsub : Icc (0 : ℝ) (1 / 8) ×ˢ D.carrier ⊆ I ×ˢ W :=
    prod_mono hscale (D.ball_subset.trans hD)
  have hb (p : ℕ) : ∃ A > (0 : ℝ),
      ∀ q ∈ Icc (0 : ℝ) (1 / 8) ×ˢ D.carrier, ‖iteratedFDeriv ℝ p g q‖ ≤ A := by
    obtain ⟨A, hA⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hg (isOpen_Ioo.prod hW)
        (by simp : (p : ℕ∞ω) ≤ ∞)).mono hsub)
    exact ⟨|A| + 1, by positivity, fun q hq ↦
      (hA q hq).trans ((le_abs_self A).trans (le_add_of_nonneg_right zero_le_one))⟩
  choose A hA hbound using hb
  refine ⟨fun p ↦ (∑ j ∈ Finset.range (p + 1), A j) + 1,
    fun p ↦ add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg (fun j _ ↦ (hA j).le)) zero_lt_one, ?_⟩
  intro σ hσ Yσ hmatch
  have hσI := hscale ⟨hσ.1.le, hσ.2⟩
  have hreg : ContDiffOn ℝ ∞ (fun p ↦ g (σ, p)) D.region :=
    hg.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨hσI, hD hp⟩)
  have heq : EqOn (densityFootpoint T Yσ) (fun p ↦ g (σ, p)) D.region := by
    intro p hp
    rw [hmatch hp]
    apply (sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ.1.ne' ?_).symm
    exact ⟨(convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem
      (mem_ball_self hR) (hD hp).1 ⟨hσ.1.le, hσ.2.trans (by norm_num)⟩, (hD hp).2⟩
  refine ⟨hreg.congr (fun p hp ↦ heq hp), ?_⟩
  intro p
  have hnorm : cNorm D.carrier p (densityFootpoint T Yσ) =
      cNorm D.carrier p (fun q ↦ g (σ, q)) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ p
    intro q hq
    filter_upwards [D.isOpen_region.mem_nhds (D.ball_subset hq)] with x hx
    exact heq hx
  rw [hnorm]
  apply (cNorm_le_sum_of_bounds (fun j _ ↦ (hA j).le) ?_).trans
    (le_add_of_nonneg_right zero_le_one)
  intro j _ q hq
  exact (norm_iteratedFDeriv_source_footpoint_slice_le isOpen_Ioo hW hg hσI
    (hD (D.ball_subset hq)) j).trans (hbound j (σ, q) ⟨⟨hσ.1.le, hσ.2⟩, hq⟩)

end JanetCartan.ContinuumRow.NormalizedCarrierProfiles
