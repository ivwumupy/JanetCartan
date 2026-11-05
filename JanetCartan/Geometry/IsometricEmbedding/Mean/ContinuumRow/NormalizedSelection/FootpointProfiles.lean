module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.NormalizedCarrierBaseline.SourceFootpoint

/-!
# Uniform all-order profiles of the original source ODE labels

The divided seed inverse extends smoothly through scale zero. Compactness on
one fixed scale interval gives every finite derivative bound on the original
coefficient chart. This supplies the inverse-label input to
`NormalizedCarrierProfiles.exists_density_weighted_coefficient_controls`,
without selecting an interval separately for every derivative order.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier NullTransport
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference WideDensity
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol

/-- One compact scale interval controls every order of the literal source
ODE footpoint. The matching identity is the output of retained source-flow
uniqueness. Constants precede the scale, the matched inverse and the order;
only seed smoothness and its Cauchy identities enter the proof
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_matched_source_densityFootpoint_all_order_profiles
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    (hD : D.region ⊆ ball (0 : Euclidean n) R ×ˢ V) :
    ∃ H : ℕ → ℝ, (∀ m, 0 < H m) ∧
      ∀ σ ∈ Ioc (0 : ℝ) (1 / 8),
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        D.region →
      ContDiffOn ℝ ∞ (densityFootpoint T Yσ) D.region ∧
        ∀ m, cNorm D.carrier m (densityFootpoint T Yσ) ≤ H m := by
  let g := sourceDensityFootpointExtension T Y
  let W := Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ D.region
  let K := Icc (0 : ℝ) (1 / 8) ×ˢ D.carrier
  have hW : IsOpen W := isOpen_Ioo.prod D.isOpen_region
  have hg : ContDiffOn ℝ ∞ g W :=
    (sourceDensityFootpointExtension_contDiffOn T hV hY).mono
      (fun _ hq ↦ ⟨hq.1, hD hq.2⟩)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall ..)
  have hKW : K ⊆ W := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, D.ball_subset hq.2⟩
  have hslice (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) (1 / 8)) (m : ℕ) :
      cNorm D.carrier m (fun p ↦ g (σ, p)) ≤ (m + 1 : ℝ) * cNorm K m g := by
    have hσW : σ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) :=
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hbound (j : ℕ) (hj : j ≤ m) (x) (hx : x ∈ D.carrier) :
        ‖iteratedFDeriv ℝ j (fun p ↦ g (σ, p)) x‖ ≤ cNorm K m g := by
      let L := ContinuousLinearMap.inr ℝ ℝ (Euclidean n × CarrierParameter)
      let W' := (fun q : ℝ × (Euclidean n × CarrierParameter) ↦ q + (σ, 0)) ⁻¹' W
      have hW' : IsOpen W' := hW.preimage (continuous_id.add continuous_const)
      have hg' : ContDiffOn ℝ ∞ (fun q ↦ g (q + (σ, 0))) W' :=
        hg.comp (contDiffOn_id.add contDiffOn_const) (fun _ hq ↦ hq)
      have hxW : L x ∈ W' := by
        change (0 + σ, x + 0) ∈ W
        simpa only [zero_add, add_zero] using
          (show (σ, x) ∈ W from ⟨hσW, D.ball_subset hx⟩)
      have he := L.iteratedFDerivWithin_comp_right hg' hW'.uniqueDiffOn
        (hW'.preimage L.continuous).uniqueDiffOn hxW (i := j) (by simp)
      rw [iteratedFDerivWithin_of_isOpen _ (hW'.preimage L.continuous) hxW,
        iteratedFDerivWithin_of_isOpen _ hW' hxW, iteratedFDeriv_comp_add_right] at he
      have he' : iteratedFDeriv ℝ j (fun p ↦ g (σ, p)) x =
          (iteratedFDeriv ℝ j g (σ, x)).compContinuousLinearMap (fun _ ↦ L) := by
        simpa [L, Function.comp_def] using he
      rw [he']
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (by intro p; simp [L])
      have hprod : (∏ _ : Fin j, ‖L‖) ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL)
      exact (mul_le_of_le_one_right (norm_nonneg _) hprod).trans
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
          (fun q hq ↦ (hg.contDiffAt (hW.mem_nhds (hKW hq))).of_le (by simp))
          ⟨hσ, hx⟩ hj)
    simpa using cNorm_le_sum_of_bounds (fun _ _ ↦ cNorm_nonneg K m g) hbound
  refine ⟨fun m ↦ (m + 1 : ℝ) * cNorm K m g + 1,
    fun m ↦ by have := cNorm_nonneg K m g; positivity, ?_⟩
  intro σ hσ Yσ hmatch
  have hσW : σ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) :=
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have heq : EqOn (densityFootpoint T Yσ) (fun p ↦ g (σ, p)) D.region := by
    intro p hp
    rw [hmatch hp]
    exact (sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ.1.ne'
      ⟨(convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem
        (mem_ball_self hR) (hD hp).1 ⟨hσ.1.le, by linarith [hσ.2]⟩, (hD hp).2⟩).symm
  refine ⟨(hg.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun p hp ↦ ⟨hσW, hp⟩)).congr (fun p hp ↦ heq hp), ?_⟩
  intro m
  have he : cNorm D.carrier m (densityFootpoint T Yσ) =
      cNorm D.carrier m (fun p ↦ g (σ, p)) :=
    GeometricProfile.cNorm_eq_of_eventuallyEq (fun p hp ↦
      Filter.eventuallyEq_of_mem (D.isOpen_region.mem_nhds (D.ball_subset hp))
        (fun _ hq ↦ heq hq)) m
  rw [he]
  exact (hslice σ ⟨hσ.1.le, hσ.2⟩ m).trans (by linarith)

end JanetCartan.ContinuumRow.NormalizedSelection
