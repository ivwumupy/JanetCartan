module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.FieldJets
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.Variational

/-!
# Finite-order stability of spatial flow jets

The spatial induction in `app:lem:common-hamilton-phase`. Constants depend on
one fixed reference solution on a compact inner cylinder. The perturbed flow's
lower jets are bounded by induction, and its top jet by the differentiated ODE.
The consumer is the autonomous time-augmentation assembly of joint continuity.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology NNReal

namespace JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

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

/-- `app:lem:common-hamilton-phase`: a local linear estimate for all spatial
jets through `m`, uniform on the inner time interval. The constants are selected
before the perturbed field and solution. Lower perturbed jets are bounded by
induction; there is no quantitative assumption on any perturbed flow derivative.
This estimate supplies `exists_cNorm_spatial_flow_sub_lt`. -/
theorem exists_spatial_flow_jet_sub_le
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
    ∃ δ > 0, ∃ C ≥ 0, ∀ (V : E → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-T) T) →
      (∀ x ∈ U, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Φ (x, s)) (V (Φ (x, t))) t) →
      (∀ x ∈ K, ∀ t ∈ Ioo (-T) T, Φ (x, t) ∈ S) →
      (∀ x ∈ U, Φ (x, 0) = Φ₀ (x, 0)) →
      cNorm S m (V - V₀) ≤ δ →
      ∀ j ≤ m, ∀ x ∈ K, ∀ t ∈ Icc (-T') T',
        ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, t)) x -
          iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, t)) x‖ ≤ C * cNorm S m (V - V₀) := by
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
    refine ⟨1, zero_lt_one, gronwallBound 0 L 1 T,
      gronwallBound_nonneg le_rfl L.coe_nonneg zero_le_one hT.le, ?_⟩
    intro V Φ hV _hΦ hode hrange hinit _hsmall j hj x hx t ht
    have : j = 0 := by omega
    subst j
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map] using
      norm_trajectory_sub_le_gronwall hT (cNorm_nonneg S 0 (V - V₀)) (htime ht) hlip
        (fun y hy ↦ by
          simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
            ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map] using
            norm_field_jet_sub_le_cNorm hS hW hSW hV hV₀ (le_refl 0) hy)
        (hrange x hx) (hrange₀ x hx) (hode x (hKU hx)) (hode₀ x (hKU hx))
        (hinit x (hKU hx))
  | succ m ih =>
    obtain ⟨δ, hδ, C, hC, ih⟩ := ih
    obtain ⟨B, hB, hbound⟩ := spatial_reference_bound hK hU hKU hT' hΦ₀ (m + 1)
    let R := cNorm S (m + 2) V₀
    have hR : 0 ≤ R := cNorm_nonneg _ _ _
    let M := 1 + B + R
    have hM : 0 ≤ M := by dsimp [M]; positivity
    let A := (R + 1) * C + 1
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hCA : C ≤ A := by dsimp [A]; nlinarith
    let G := gronwallBound 0 M (M + flowJetDifferenceConstant (m + 1) M) T
    have hG : 0 ≤ G := gronwallBound_nonneg le_rfl hM
      (add_nonneg hM (flowJetDifferenceConstant_nonneg _ hM)) hT.le
    refine ⟨min δ (min 1 (1 / (C + 1))),
      lt_min hδ (lt_min zero_lt_one (by positivity)),
      C + G * A, by positivity, ?_⟩
    intro V Φ hV hΦ hode hrange hinit hsmall
    let e := cNorm S (m + 1) (V - V₀)
    have he : 0 ≤ e := cNorm_nonneg _ _ _
    have heδ : cNorm S m (V - V₀) ≤ δ :=
      (cNorm_mono_order (Nat.le_succ m)).trans (hsmall.trans (min_le_left _ _))
    have he1 : e ≤ 1 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have heC : e ≤ 1 / (C + 1) :=
      hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hCe : C * e ≤ 1 := by
      have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp heC
      nlinarith
    have hlower : ∀ j ≤ m, ∀ x ∈ K, ∀ t ∈ Icc (-T') T',
        ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, t)) x -
          iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, t)) x‖ ≤ C * e := by
      intro j hj x hx t ht
      exact (ih V Φ hV hΦ hode hrange hinit heδ j hj x hx t ht).trans
        (mul_le_mul_of_nonneg_left (cNorm_mono_order (Nat.le_succ m)) hC)
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
    have htop := norm_spatial_jet_sub_le_gronwall hU hT hM (mul_nonneg hA he)
      (Nat.succ_pos m) hΦ hΦ₀ hode hode₀ hinit (hKU hx) (htime ht)
      (fun τ hτ ↦ (hV.contDiffAt (hW.mem_nhds
        (hSW (hrange x hx τ (htime (hseg hτ)))))).of_le (by simp))
      (fun τ hτ ↦ (hV₀.contDiffAt (hW.mem_nhds
        (hSW (hrange₀ x hx τ (htime (hseg hτ)))))).of_le (by simp))
      (M := M) (ε := A * e)
      (by
        intro τ hτ k _hk hkm
        have hy := hrange x hx τ (htime (hseg hτ))
        have hd := norm_field_jet_sub_le_cNorm hS hW hSW hV hV₀ hkm hy
        have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
          (fun y hy ↦ (hV₀.contDiffAt (hW.mem_nhds (hSW hy))).of_le (by simp))
          hy (show k ≤ m + 2 by omega)
        have hh := norm_le_norm_sub_add (iteratedFDeriv ℝ k V (Φ (x, τ)))
          (iteratedFDeriv ℝ k V₀ (Φ (x, τ)))
        change _ ≤ R at hb
        change _ ≤ e at hd
        dsimp [M]
        linarith)
      (by
        intro τ hτ k _hk hkm
        have hh := norm_field_jet_sub_le_cNorm_add hS hconv hW hSW hV hV₀ hkm
          (hrange x hx τ (htime (hseg hτ))) (hrange₀ x hx τ (htime (hseg hτ)))
        change _ ≤ e + R * _ at hh
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

/-- `app:lem:common-hamilton-phase`: finite-order spatial-flow continuity on a
compact inner cylinder, for arbitrary actual solutions with a common initial
section on `U`. The threshold is chosen before `V` and `Φ` and uses only the
order-`m` seminorm of their field perturbation. Reference derivatives of higher
order enter constants only. This is the spatial input to autonomous time
augmentation in the joint finite-order flow-continuity construction. -/
theorem exists_cNorm_spatial_flow_sub_lt
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
    ∃ δ > 0, ∀ (V : E → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-T) T) →
      (∀ x ∈ U, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Φ (x, s)) (V (Φ (x, t))) t) →
      (∀ x ∈ K, ∀ t ∈ Ioo (-T) T, Φ (x, t) ∈ S) →
      (∀ x ∈ U, Φ (x, 0) = Φ₀ (x, 0)) →
      cNorm S m (V - V₀) < δ →
      ∀ t ∈ Icc (-T') T', cNorm K m (fun x ↦ Φ (x, t) - Φ₀ (x, t)) < ε := by
  obtain ⟨δ, hδ, C, hC, hb⟩ := exists_spatial_flow_jet_sub_le
    hK hU hKU hS hconv hW hSW hT'pos hT' hV₀ hΦ₀ hode₀ hrange₀ m
  let D : ℝ := (m + 1) * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨min δ (ε / (D + 1)), lt_min hδ (div_pos hε (by positivity)), ?_⟩
  intro V Φ hV hΦ hode hrange hinit hsmall t ht
  have he : 0 ≤ cNorm S m (V - V₀) := cNorm_nonneg _ _ _
  have hjet := hb V Φ hV hΦ hode hrange hinit
    (hsmall.le.trans (min_le_left _ _))
  have htime : t ∈ Ioo (-T) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnorm : cNorm K m (fun x ↦ Φ (x, t) - Φ₀ (x, t)) ≤
      D * cNorm S m (V - V₀) := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ C * cNorm S m (V - V₀))
      (fun _ _ ↦ mul_nonneg hC he) ?_).trans_eq
      (by simp [D, mul_assoc])
    intro j hj x hx
    change ‖iteratedFDeriv ℝ j ((fun y ↦ Φ (y, t)) - (fun y ↦ Φ₀ (y, t))) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (i := j)
      ((spatial_slice_smooth hU hΦ (hKU hx) htime).of_le (by simp))
      ((spatial_slice_smooth hU hΦ₀ (hKU hx) htime).of_le (by simp))]
    exact hjet j hj x hx t ht
  apply hnorm.trans_lt
  have hh := (lt_div_iff₀ (by positivity : 0 < D + 1)).mp
    (hsmall.trans_le (min_le_right _ _))
  nlinarith

end JanetCartan.ODE
