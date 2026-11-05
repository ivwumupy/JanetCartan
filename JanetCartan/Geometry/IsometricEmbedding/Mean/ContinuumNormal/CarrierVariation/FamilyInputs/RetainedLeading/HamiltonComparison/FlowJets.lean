module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.RootContinuity

/-!
# Differentiated flow comparison with varying retained initial data

The flow step of `app:lem:common-hamilton-phase` must allow the retained initial
roots to vary. The existing equal-initial-data flow estimate does not do so.
Here the differentiated ODE gives spatial jet comparison with an additional
initial-state seminorm. Its actual producer is
`exists_retained_initialState_compact_tolerance`; the consumer is comparison
of the original retained forward projection. Smoothness, ODE and range remain
explicit until instantiated for that forward projection.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open JanetCartan.ODE
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_fderiv_sub_eq_norm_jet_one
    (V V₀ : E → E) (y y₀ : E) :
    ‖fderiv ℝ V y - fderiv ℝ V₀ y₀‖ =
      ‖iteratedFDeriv ℝ 1 V y - iteratedFDeriv ℝ 1 V₀ y₀‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map,
    iteratedFDeriv_zero_eq_comp]

/-- `app:lem:common-hamilton-phase`: the higher spatial-jet difference satisfies
Grönwall on either time direction. All derivative equations are deduced from the
actual ODE. Quantitative inputs involve field derivatives through `n`, reference
flow derivatives through `n`, and perturbed flow derivatives strictly below `n`.
The spatial induction must supply these lower-order bounds; this conditional
step alone does not assert finite-order continuity. -/
private theorem norm_spatial_jet_sub_le_gronwall_initial
    {U : Set P} (hU : IsOpen U) {T M ε : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    {Φ Φ₀ : P × ℝ → E} {V V₀ : E → E} {n : ℕ} (hn : 0 < n)
    (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-T) T))
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (U ×ˢ Ioo (-T) T))
    (hode : ∀ y ∈ U, ∀ τ ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Φ (y, s)) (V (Φ (y, τ))) τ)
    (hode₀ : ∀ y ∈ U, ∀ τ ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Φ₀ (y, s)) (V₀ (Φ₀ (y, τ))) τ)
    {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-T) T)
    (hinit : ‖iteratedFDeriv ℝ n (fun y ↦ Φ (y, 0)) x -
      iteratedFDeriv ℝ n (fun y ↦ Φ₀ (y, 0)) x‖ ≤ ε)
    (hV : ∀ τ ∈ uIcc 0 t, ContDiffAt ℝ n V (Φ (x, τ)))
    (hV₀ : ∀ τ ∈ uIcc 0 t, ContDiffAt ℝ n V₀ (Φ₀ (x, τ)))
    (houter : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j V (Φ (x, τ))‖ ≤ M)
    (houterDiff : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j V (Φ (x, τ)) - iteratedFDeriv ℝ j V₀ (Φ₀ (x, τ))‖ ≤ ε)
    (hinner : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x‖ ≤ M)
    (hinner₀ : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, τ)) x‖ ≤ M)
    (hinnerDiff : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x -
        iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, τ)) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ n (fun y ↦ Φ (y, t)) x -
        iteratedFDeriv ℝ n (fun y ↦ Φ₀ (y, t)) x‖ ≤
      gronwallBound 1 M (M + flowJetDifferenceConstant n M) T * ε := by
  let J := fun τ ↦ iteratedFDeriv ℝ n (fun y ↦ Φ (y, τ)) x
  let J₀ := fun τ ↦ iteratedFDeriv ℝ n (fun y ↦ Φ₀ (y, τ)) x
  let A := fun τ ↦ fderiv ℝ V (Φ (x, τ))
  let A₀ := fun τ ↦ fderiv ℝ V₀ (Φ₀ (x, τ))
  let Q := fun τ ↦ jetPartitionRemainder n V (fun y ↦ Φ (y, τ)) x
  let Q₀ := fun τ ↦ jetPartitionRemainder n V₀ (fun y ↦ Φ₀ (y, τ)) x
  have hseg : uIcc 0 t ⊆ Ioo (-T) T :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ ht
  have hdiff τ (hτ : τ ∈ uIcc 0 t) :
      HasDerivAt (fun s ↦ J s - J₀ s)
        ((A τ).compContinuousMultilinearMap (J τ - J₀ τ) +
          (A τ - A₀ τ).compContinuousMultilinearMap (J₀ τ) + (Q τ - Q₀ τ)) τ := by
    convert (hasDerivAt_iteratedFDeriv_top_add_jetPartitionRemainder hU hΦ hode hn hx
      (hseg hτ) (hV τ hτ)).sub
      (hasDerivAt_iteratedFDeriv_top_add_jetPartitionRemainder hU hΦ₀ hode₀ hn hx
        (hseg hτ) (hV₀ τ hτ)) using 1
    ext v
    change A τ (J τ v - J₀ τ v) + (A τ (J₀ τ v) - A₀ τ (J₀ τ v)) +
      (Q τ v - Q₀ τ v) = (A τ (J τ v) + Q τ v) - (A₀ τ (J₀ τ v) + Q₀ τ v)
    rw [map_sub]
    abel
  have hb τ (hτ : τ ∈ uIcc 0 t) :
      ‖(A τ).compContinuousMultilinearMap (J τ - J₀ τ) +
          (A τ - A₀ τ).compContinuousMultilinearMap (J₀ τ) + (Q τ - Q₀ τ)‖ ≤
        M * ‖J τ - J₀ τ‖ + (M + flowJetDifferenceConstant n M) * ε := by
    have hA : ‖A τ‖ ≤ M := by
      simpa only [A, norm_iteratedFDeriv_one] using houter τ hτ 1 le_rfl hn
    have hAd : ‖A τ - A₀ τ‖ ≤ ε := by
      dsimp only [A, A₀]
      rw [norm_fderiv_sub_eq_norm_jet_one]
      exact houterDiff τ hτ 1 le_rfl hn
    have hQ : ‖Q τ - Q₀ τ‖ ≤ flowJetDifferenceConstant n M * ε :=
      norm_jetPartitionRemainder_sub_le hM hε (houter τ hτ) (houterDiff τ hτ)
        (hinner τ hτ) (fun j hj hjn ↦ hinner₀ τ hτ j hj hjn.le) (hinnerDiff τ hτ)
    calc
      _ ≤ (‖(A τ).compContinuousMultilinearMap (J τ - J₀ τ)‖ +
          ‖(A τ - A₀ τ).compContinuousMultilinearMap (J₀ τ)‖) + ‖Q τ - Q₀ τ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (M * ‖J τ - J₀ τ‖ + ε * M) + flowJetDifferenceConstant n M * ε := by
        apply add_le_add (add_le_add ?_ ?_) hQ
        · exact ((A τ).norm_compContinuousMultilinearMap_le _).trans
            (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
        · exact ((A τ - A₀ τ).norm_compContinuousMultilinearMap_le _).trans
            (mul_le_mul hAd (hinner₀ τ hτ n hn le_rfl) (norm_nonneg _) hε)
      _ = _ := by ring
  have hg := norm_le_gronwallBound_of_hasDerivAt_uIcc hdiff
    (δ := ε) hinit hb
  have hS := flowJetDifferenceConstant_nonneg n hM
  have htime : |t - 0| ≤ T := by simpa using (abs_lt.mpr ht).le
  apply (hg.trans (gronwallBound_mono hε (by positivity) hM htime)).trans_eq
  simpa using gronwallBound_mul 1 M (M + flowJetDifferenceConstant n M) ε T

private theorem spatial_slice_smooth {U : Set P} (hU : IsOpen U)
    {T : ℝ} {Φ : P × ℝ → E}
    (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-T) T))
    {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    ContDiffAt ℝ ∞ (fun y ↦ Φ (y, t)) x :=
  (hΦ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)

private theorem spatial_reference_bound {K U : Set P}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {T T' : ℝ} (hT' : T' < T) {Φ₀ : P × ℝ → E}
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (U ×ˢ Ioo (-T) T)) (m : ℕ) :
    ∃ B ≥ 0, ∀ j ≤ m, ∀ x ∈ K, ∀ t ∈ Icc (-T') T',
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, t)) x‖ ≤ B := by
  have hboundOne (j : ℕ) : ∃ B ≥ 0, ∀ x ∈ K, ∀ t ∈ Icc (-T') T',
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, t)) x‖ ≤ B := by
    have hc : ContinuousOn
        (fun q : ℝ × P ↦ iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, q.1)) q.2)
        (Icc (-T') T' ×ˢ K) := by
      intro q hq
      have ht : q.1 ∈ Ioo (-T) T := ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
      have hs := (hΦ₀.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds
        ⟨hKU hq.2, ht⟩)).comp q (contDiffAt_snd.prodMk contDiffAt_fst)
      exact (NormalComparison.contDiffAt_spatial_iteratedFDeriv hs j).continuousAt.continuousWithinAt
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
    exact ⟨max B 0, le_max_right _ _, fun x hx t ht ↦
      (hB (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)⟩
  induction m with
  | zero =>
    obtain ⟨B, hB, hb⟩ := hboundOne 0
    refine ⟨B, hB, ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    exact hb
  | succ m ih =>
    obtain ⟨B, hB, hb⟩ := ih
    obtain ⟨C, hC, hc⟩ := hboundOne (m + 1)
    refine ⟨max B C, hB.trans (le_max_left _ _), ?_⟩
    intro j hj x hx t ht
    by_cases hjm : j ≤ m
    · exact (hb j hjm x hx t ht).trans (le_max_left _ _)
    · have : j = m + 1 := by omega
      subst j
      exact (hc x hx t ht).trans (le_max_right _ _)


/-- Spatial jets of actual solutions are controlled by field and initial-state
jets through the SAME order. This is the differentiated ODE estimate consumed
by the retained forward-projection comparison. The initial error is produced
by `exists_retained_initialState_compact_tolerance`, rather than assumed to
vanish (`app:lem:common-hamilton-phase`). -/
theorem exists_retained_spatial_flow_jet_comparison
    {K U : Set P} {S W : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hS : IsCompact S) (hconv : Convex ℝ S) (hW : IsOpen W) (hSW : S ⊆ W)
    {T T' : ℝ} (hT'pos : 0 < T') (hT' : T' < T)
    {V₀ : E → E} {Φ₀ : P × ℝ → E}
    (hV₀ : ContDiffOn ℝ ∞ V₀ W)
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (U ×ˢ Ioo (-T) T))
    (hode₀ : ∀ x ∈ U, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Φ₀ (x, s)) (V₀ (Φ₀ (x, t))) t)
    (hrange₀ : ∀ x ∈ K, ∀ t ∈ Ioo (-T) T, Φ₀ (x, t) ∈ S) (m : ℕ) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ (V : E → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-T) T) →
      (∀ x ∈ U, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Φ (x, s)) (V (Φ (x, t))) t) →
      (∀ x ∈ K, ∀ t ∈ Ioo (-T) T, Φ (x, t) ∈ S) →
      ∀ e ≥ (0 : ℝ), e ≤ δ → cNorm S m (V - V₀) ≤ e →
      (∀ j ≤ m, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, 0)) x -
          iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, 0)) x‖ ≤ e) →
      ∀ j ≤ m, ∀ x ∈ K, ∀ t ∈ Icc (-T') T',
        ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, t)) x -
          iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, t)) x‖ ≤ C * e := by
  have hT : 0 < T := hT'pos.trans hT'
  have htime : Icc (-T') T' ⊆ Ioo (-T) T :=
    fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  induction m with
  | zero =>
    let L : ℝ≥0 := ⟨cNorm S 1 V₀, cNorm_nonneg _ _ _⟩
    have hlip : LipschitzOnWith L V₀ S := by
      apply lipschitzOnWith_iff_norm_sub_le.mpr
      intro y hy z hz
      change _ ≤ cNorm S 1 V₀ * _
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map] using
        norm_field_jet_displacement_le hS hconv hW hSW hV₀ 0 hy hz
    refine ⟨1, zero_lt_one, gronwallBound 1 L 1 T,
      gronwallBound_nonneg zero_le_one L.coe_nonneg zero_le_one hT.le, ?_⟩
    intro V Φ hV _hΦ hode hrange e he _hsmall hfield hinit j hj x hx t ht
    have : j = 0 := by omega
    subst j
    have hsub : uIcc 0 t ⊆ Ioo (-T) T :=
      ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ (htime ht)
    have hvalue : ∀ y ∈ S, ‖V y - V₀ y‖ ≤ e := by
      intro y hy
      have hh := (norm_field_jet_sub_le_cNorm hS hW hSW hV hV₀ (le_refl 0) hy).trans hfield
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map] using hh
    have hi : ‖Φ (x, 0) - Φ₀ (x, 0)‖ ≤ e := by
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map] using hinit 0 le_rfl x hx
    have hg := norm_le_gronwallBound_of_hasDerivAt_uIcc
      (fun τ hτ ↦ (hode x (hKU hx) τ (hsub hτ)).sub
        (hode₀ x (hKU hx) τ (hsub hτ))) hi
      (L := L) (ε := e) (fun τ hτ ↦ by
        calc
          _ ≤ ‖V (Φ (x, τ)) - V₀ (Φ (x, τ))‖ +
              ‖V₀ (Φ (x, τ)) - V₀ (Φ₀ (x, τ))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ e + (L : ℝ) * ‖Φ (x, τ) - Φ₀ (x, τ)‖ :=
            add_le_add (hvalue _ (hrange x hx τ (hsub hτ)))
              (hlip.norm_sub_le (hrange x hx τ (hsub hτ)) (hrange₀ x hx τ (hsub hτ)))
          _ = _ := add_comm _ _)
    have htt : |t - 0| ≤ T := by simpa using (abs_lt.mpr (htime ht)).le
    have hb := hg.trans (gronwallBound_mono he he L.coe_nonneg htt)
    have hb' : ‖Φ (x, t) - Φ₀ (x, t)‖ ≤ gronwallBound 1 L 1 T * e := by
      convert! hb using 1
      simpa using (gronwallBound_mul 1 L 1 e T).symm
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map] using hb'
  | succ m ih =>
    obtain ⟨δ, hδ, C, hC, ih⟩ := ih
    obtain ⟨B, hB, hbound⟩ := spatial_reference_bound hK hU hKU hT' hΦ₀ (m + 1)
    let R := cNorm S (m + 2) V₀
    have hR : 0 ≤ R := cNorm_nonneg _ _ _
    let M := 1 + B + R
    have hM : 0 ≤ M := by dsimp [M]; positivity
    let A := (R + 1) * C + 1
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hA1 : 1 ≤ A := by dsimp [A]; nlinarith
    have hCA : C ≤ A := by dsimp [A]; nlinarith
    let G := gronwallBound 1 M (M + flowJetDifferenceConstant (m + 1) M) T
    have hG : 0 ≤ G := gronwallBound_nonneg zero_le_one hM
      (add_nonneg hM (flowJetDifferenceConstant_nonneg _ hM)) hT.le
    refine ⟨min δ (min 1 (1 / (C + 1))),
      lt_min hδ (lt_min zero_lt_one (by positivity)),
      C + G * A, by positivity, ?_⟩
    intro V Φ hV hΦ hode hrange e he hsmall hfield hinit
    have heδ : e ≤ δ := hsmall.trans (min_le_left _ _)
    have he1 : e ≤ 1 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have heC : e ≤ 1 / (C + 1) :=
      hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hCe : C * e ≤ 1 := by
      have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp heC
      nlinarith
    have hlower : ∀ j ≤ m, ∀ x ∈ K, ∀ t ∈ Icc (-T') T',
        ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, t)) x -
          iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, t)) x‖ ≤ C * e :=
      ih V Φ hV hΦ hode hrange e he heδ
        ((cNorm_mono_order (Nat.le_succ m)).trans hfield)
        (fun j hj ↦ hinit j (hj.trans (Nat.le_succ m)))
    have hvalue x (hx : x ∈ K) t (ht : t ∈ Icc (-T') T') :
        ‖Φ (x, t) - Φ₀ (x, t)‖ ≤ C * e := by
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map] using
        hlower 0 (Nat.zero_le _) x hx t ht
    intro j hj x hx t ht
    by_cases hjm : j ≤ m
    · exact (hlower j hjm x hx t ht).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hG hA)) he)
    have hjtop : j = m + 1 := by omega
    subst j
    have hseg : uIcc 0 t ⊆ Icc (-T') T' :=
      ordConnected_Icc.uIcc_subset ⟨by linarith, hT'pos.le⟩ ht
    have htop := norm_spatial_jet_sub_le_gronwall_initial hU hT hM (mul_nonneg hA he)
      (Nat.succ_pos m) hΦ hΦ₀ hode hode₀ (hKU hx) (htime ht)
      ((hinit (m + 1) le_rfl x hx).trans
        (by simpa using mul_le_mul_of_nonneg_right hA1 he))
      (fun τ hτ ↦ (hV.contDiffAt (hW.mem_nhds
        (hSW (hrange x hx τ (htime (hseg hτ)))))).of_le (by simp))
      (fun τ hτ ↦ (hV₀.contDiffAt (hW.mem_nhds
        (hSW (hrange₀ x hx τ (htime (hseg hτ)))))).of_le (by simp))
      (M := M) (ε := A * e)
      (by
        intro τ hτ k _hk hkm
        have hy := hrange x hx τ (htime (hseg hτ))
        have hd := (norm_field_jet_sub_le_cNorm hS hW hSW hV hV₀ hkm hy).trans hfield
        have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
          (fun y hy ↦ (hV₀.contDiffAt (hW.mem_nhds (hSW hy))).of_le (by simp))
          hy (show k ≤ m + 2 by omega)
        have hh := norm_le_norm_sub_add (iteratedFDeriv ℝ k V (Φ (x, τ)))
          (iteratedFDeriv ℝ k V₀ (Φ (x, τ)))
        change _ ≤ R at hb
        dsimp [M]
        linarith)
      (by
        intro τ hτ k _hk hkm
        have hh := norm_field_jet_sub_le_cNorm_add hS hconv hW hSW hV hV₀ hkm
          (hrange x hx τ (htime (hseg hτ))) (hrange₀ x hx τ (htime (hseg hτ)))
        change _ ≤ _ + R * _ at hh
        apply hh.trans
        have hv := mul_le_mul_of_nonneg_left (hvalue x hx τ (hseg hτ)) hR
        dsimp [A]
        nlinarith)
      (by
        intro τ hτ k _hk hkm
        have hd := (hlower k (by omega) x hx τ (hseg hτ)).trans hCe
        have hb := hbound k (by omega) x hx τ (hseg hτ)
        have hh := norm_le_norm_sub_add
          (iteratedFDeriv ℝ k (fun y ↦ Φ (y, τ)) x)
          (iteratedFDeriv ℝ k (fun y ↦ Φ₀ (y, τ)) x)
        dsimp [M]
        linarith)
      (by
        intro τ hτ k _hk hkm
        exact (hbound k hkm x hx τ (hseg hτ)).trans (by dsimp [M]; linarith))
      (by
        intro τ hτ k _hk hkm
        exact (hlower k (by omega) x hx τ (hseg hτ)).trans
          (mul_le_mul_of_nonneg_right hCA he))
    change _ ≤ G * (A * e) at htop
    change _ ≤ (C + G * A) * e
    nlinarith

/-- Finite-order spatial-flow continuity allows the actual initial section to
vary. Both smallness inputs have order `m`; no bound on perturbed flow jets is
assumed. This supplies the spatial input for time augmentation of the retained
Hamilton flows (`app:lem:common-hamilton-phase`). -/
theorem exists_retained_spatial_flow_tolerance
    {K U : Set P} {S W : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hS : IsCompact S) (hconv : Convex ℝ S) (hW : IsOpen W) (hSW : S ⊆ W)
    {T T' : ℝ} (hT'pos : 0 < T') (hT' : T' < T)
    {V₀ : E → E} {Φ₀ : P × ℝ → E}
    (hV₀ : ContDiffOn ℝ ∞ V₀ W)
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (U ×ˢ Ioo (-T) T))
    (hode₀ : ∀ x ∈ U, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Φ₀ (x, s)) (V₀ (Φ₀ (x, t))) t)
    (hrange₀ : ∀ x ∈ K, ∀ t ∈ Ioo (-T) T, Φ₀ (x, t) ∈ S)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (V : E → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-T) T) →
      (∀ x ∈ U, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Φ (x, s)) (V (Φ (x, t))) t) →
      (∀ x ∈ K, ∀ t ∈ Ioo (-T) T, Φ (x, t) ∈ S) →
      cNorm S m (V - V₀) + cNorm K m (fun x ↦ Φ (x, 0) - Φ₀ (x, 0)) < δ →
      ∀ t ∈ Icc (-T') T', cNorm K m (fun x ↦ Φ (x, t) - Φ₀ (x, t)) < ε := by
  obtain ⟨δ, hδ, C, hC, hb⟩ := exists_retained_spatial_flow_jet_comparison
    hK hU hKU hS hconv hW hSW hT'pos hT' hV₀ hΦ₀ hode₀ hrange₀ m
  let D : ℝ := (m + 1) * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨min δ (ε / (D + 1)), lt_min hδ (div_pos hε (by positivity)), ?_⟩
  intro V Φ hV hΦ hode hrange hsmall t ht
  let e := cNorm S m (V - V₀) + cNorm K m (fun x ↦ Φ (x, 0) - Φ₀ (x, 0))
  have he : 0 ≤ e := add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)
  have hzero : 0 ∈ Ioo (-T) T := by constructor <;> linarith
  have hinit : ∀ j ≤ m, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, 0)) x -
        iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, 0)) x‖ ≤ e := by
    intro j hj x hx
    apply (HamiltonPhase.CompositionContinuity.norm_iteratedFDeriv_sub_le_cNorm hK
      (fun y hy ↦ (spatial_slice_smooth hU hΦ (hKU hy) hzero).of_le (by simp))
      (fun y hy ↦ (spatial_slice_smooth hU hΦ₀ (hKU hy) hzero).of_le (by simp)) hj hx).trans
    exact le_add_of_nonneg_left (cNorm_nonneg _ _ _)
  have hjet := hb V Φ hV hΦ hode hrange e he
    (hsmall.le.trans (min_le_left _ _))
    (le_add_of_nonneg_right (cNorm_nonneg _ _ _)) hinit
  have htime : t ∈ Ioo (-T) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnorm : cNorm K m (fun x ↦ Φ (x, t) - Φ₀ (x, t)) ≤ D * e := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ C * e)
      (fun _ _ ↦ mul_nonneg hC he) ?_).trans_eq (by simp [D, mul_assoc])
    intro j hj x hx
    change ‖iteratedFDeriv ℝ j ((fun y ↦ Φ (y, t)) - (fun y ↦ Φ₀ (y, t))) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (i := j)
      ((spatial_slice_smooth hU hΦ (hKU hx) htime).of_le (by simp))
      ((spatial_slice_smooth hU hΦ₀ (hKU hx) htime).of_le (by simp))]
    exact hjet j hj x hx t ht
  apply hnorm.trans_lt
  have hh := (lt_div_iff₀ (by positivity : 0 < D + 1)).mp
    (hsmall.trans_le (min_le_right _ _))
  change e * (D + 1) < ε at hh
  nlinarith

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
