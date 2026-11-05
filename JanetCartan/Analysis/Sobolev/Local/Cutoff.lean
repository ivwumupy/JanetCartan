module

public import JanetCartan.Analysis.Sobolev.Local.Cutoff.FirstOrder
public import JanetCartan.Analysis.Sobolev.Local.Cutoff.AllOrders
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakLimits
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakUniqueness

/-!
# Cutoff and zero extension in the weak restriction Sobolev scale

This module proves the cutoff estimates at every natural order required by
`app:ch_regular:eq:one-gain-tame` and
`app:ch_regular:thm:exact-correction`. The output is identified with the
existing `SmallSupport.zeroExtend` and `SmallSupport.bumpL2` operations.
The constant is fixed before the data, with no derivative loss. The complete
residual's analytic estimates remain inputs of its consuming construction.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal NNReal

set_option maxHeartbeats 600000

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "E" => EuclideanSpace ℝ (Fin n)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

variable {U V : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}

/-- The existing zero extension of the existing bump multiplier has exactly
the prescribed pointwise meaning (`app:ch_regular:thm:exact-correction`). -/
theorem zeroExtend_bumpL2_coeFn (hU : MeasurableSet U) (χ : ContDiffBump x)
    (u : LocalL2 U F) :
    SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u) =ᵐ[volume]
      fun y ↦ χ y • U.indicator u y := by
  have hb := (ae_eq_restrict_iff_indicator_ae_eq hU).mp
    (SmallSupport.bumpL2_coeFn (p := 2) le_rfl χ u)
  filter_upwards [SmallSupport.zeroExtend_coeFn hU
    (SmallSupport.bumpL2 (p := 2) le_rfl χ u), hb] with y hy hb
  rw [hy, hb]
  by_cases hyU : y ∈ U <;> simp [hyU]

set_option backward.isDefEq.respectTransparency false in
/-- The L² cutoff constant stays exactly one; positive-order constants must
not be used in the contraction argument of
`app:ch_regular:thm:exact-correction`. -/
theorem norm_zeroExtend_bumpL2_le (hU : MeasurableSet U) (χ : ContDiffBump x)
    (u : LocalL2 U F) :
    ‖SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)‖ ≤ ‖u‖ := by
  rw [(SmallSupport.zeroExtend hU).norm_map]
  simpa only [one_mul] using
    (SmallSupport.bumpL2 (F := F) (μ := volume.restrict U) (p := 2) le_rfl χ).le_of_opNorm_le
      (SmallSupport.norm_bumpL2_two_le_one (F := F) (μ := volume.restrict U) χ) u

/-- Cutting off any genuine extension agrees globally a.e. with the zero
extension of the original local class, provided the cutoff is supported in
the source domain (`app:ch_regular:thm:exact-correction`). -/
theorem SobolevExtension.bump_ae_zeroExtend {s : ℕ} {u : LocalL2 U F}
    (e : SobolevExtension U s u) (hU : MeasurableSet U) (χ : ContDiffBump x)
    (hs : tsupport (χ : E → ℝ) ⊆ U) :
    (fun y ↦ χ y • e.toFun y) =ᵐ[volume]
      SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u) := by
  have he := (ae_restrict_iff' hU).mp e.restrict_eq
  filter_upwards [he, zeroExtend_bumpL2_coeFn hU χ u] with y hy hz
  rw [hz]
  by_cases hyU : y ∈ U
  · rw [indicator_of_mem hyU, hy hyU]
  · have hχ : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hyU (hs h))
    simp [hχ]

/-- A fixed bump has a first-order restriction Sobolev bound on every output
domain, including the whole space. The a.e. hypothesis identifies the
actual output class with the existing zero extension; no positive-order
regularity or multiplier bound is assumed
(`app:ch_regular:eq:one-gain-tame`). -/
theorem exists_bump_firstOrder_constant (χ : ContDiffBump x) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U V : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U →
      ∀ (u : LocalL2 U F) (v : LocalL2 V F),
        (SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
          =ᵐ[volume.restrict V] v) →
        MemRestrictionSobolev U 1 u →
        MemRestrictionSobolev V 1 v ∧
          restrictionSobolevNorm V 1 v ≤ C * restrictionSobolevNorm U 1 u := by
  obtain ⟨B, hB⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((χ.contDiff : ContDiff ℝ ∞ (χ : E → ℝ)).continuous_fderiv (by simp))
  have hBpos : 0 ≤ B := (norm_nonneg _).trans (hB x)
  refine ⟨1 + B, by linarith, ?_⟩
  intro U V hU hs u v hv hu
  have heq (e : SobolevExtension U 1 u) :
      (fun y ↦ χ y • e.toFun y) =ᵐ[volume.restrict V] v := by
    have hlocal : (fun y ↦ χ y • e.toFun y) =ᵐ[volume.restrict V]
        SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u) :=
      ae_restrict_of_ae (e.bump_ae_zeroExtend hU χ hs)
    exact hlocal.trans hv
  have hb₀ := SmallSupport.bump_norm_le_one χ
  refine ⟨⟨hu.some.cutoffFirst χ.contDiff hb₀ hB (heq hu.some)⟩, ?_⟩
  have hCpos : 0 < 1 + B := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨e, he⟩ := exists_extension_jetNorm_lt hu
    (lt_add_of_pos_right _ (div_pos hε hCpos))
  have hout := (restrictionSobolevNorm_le (e.cutoffFirst χ.contDiff hb₀ hB (heq e))).trans
    (e.jetNorm_cutoffFirst_le χ.contDiff (by norm_num) hBpos hb₀ hB (heq e))
  have he' := mul_lt_mul_of_pos_left he hCpos
  rw [mul_add, mul_div_cancel₀ _ hCpos.ne'] at he'
  linarith

/-- The literal zero-extended L² representative has a genuine whole-space
weak jet through order one (`app:ch_regular:thm:exact-correction`). Its
zeroth jet is normalized to that representative, not merely a.e. -/
theorem exists_weakJet_zeroExtend_bumpL2_firstOrder
    (hU : MeasurableSet U) (χ : ContDiffBump x) (hs : tsupport (χ : E → ℝ) ⊆ U)
    (u : LocalL2 U F) (hu : MemRestrictionSobolev U 1 u) :
    let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
    ∃ J : (j : ℕ) → E → E [×j]→L[ℝ] F,
      Mollification.HasWeakJetOn volume z J univ 1 ∧
      ∀ j ≤ 1, MemLp (J j) 2 volume := by
  obtain ⟨B, hB⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((χ.contDiff : ContDiff ℝ ∞ (χ : E → ℝ)).continuous_fderiv (by simp))
  let e := hu.some
  let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
  let J := cutoffFirstJet χ e.jet
  have hw := hasWeakJetOn_cutoffFirstJet e.weakJet e.memLp_jet χ.contDiff
    (SmallSupport.bump_norm_le_one χ) hB
  have hz : J 0 =ᵐ[volume.restrict univ] iteratedFDeriv ℝ 0 (fun y ↦ z y) := by
    rw [Measure.restrict_univ]
    filter_upwards [e.bump_ae_zeroExtend hU χ hs] with y hy
    dsimp only [J]
    rw [hw.1]
    ext v
    simpa only [iteratedFDeriv_zero_apply] using hy
  refine ⟨Mollification.normalizeWeakJet z J, ?_, ?_⟩
  · exact hw.congr_ae rfl (fun j _ ↦ Mollification.normalizeWeakJet_ae hz j)
  · intro j hj
    simpa only [Measure.restrict_univ] using Mollification.memLp_normalizeWeakJet hz
      (show MemLp (J j) 2 (volume.restrict univ) by
        simpa only [Measure.restrict_univ] using memLp_cutoffFirstJet e.memLp_jet χ.contDiff
          (SmallSupport.bump_norm_le_one χ) hB j)

/-- The existing zero extension, restricted to any measurement domain,
obeys the first-order bound with one constant chosen before the input.
Taking `V = univ` is whole-space restriction Sobolev membership
(`app:ch_regular:eq:one-gain-tame`). -/
theorem exists_bump_zeroExtension_firstOrder_bound (χ : ContDiffBump x) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U V : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U → ∀ u : LocalL2 U F,
      MemRestrictionSobolev U 1 u →
      let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
      let v := ((Lp.memLp z).restrict V).toLp z
      MemRestrictionSobolev V 1 v ∧
        restrictionSobolevNorm V 1 v ≤ C * restrictionSobolevNorm U 1 u := by
  obtain ⟨C, hC, hbound⟩ := exists_bump_firstOrder_constant (F := F) χ
  refine ⟨C, hC, fun U V hU hs u hu ↦ ?_⟩
  exact hbound U V hU hs u _ (MemLp.coeFn_toLp _).symm hu

variable [CompleteSpace F]

/-- Multiply an actual extension by a fixed smooth bump, using the constructed
all-order weak Leibniz jet. The a.e. premise only identifies the output class
(`app:ch_regular:eq:one-gain-tame`). -/
def SobolevExtension.cutoffAll {s : ℕ} {u : LocalL2 U F} {v : LocalL2 V F}
    (e : SobolevExtension U s u) (χ : ContDiffBump x)
    (hv : (fun y ↦ χ y • e.toFun y) =ᵐ[volume.restrict V] v) :
    SobolevExtension V s v where
  toFun := fun y ↦ χ y • e.toFun y
  jet := cutoffAllJet χ χ.contDiff χ.hasCompactSupport e.jet
  weakJet := hasWeakJetOn_cutoffAllJet e.weakJet e.memLp_jet χ.contDiff χ.hasCompactSupport
  memLp_fun := memLp_bounded_smul e.memLp_fun χ.continuous (SmallSupport.bump_norm_le_one χ)
  memLp_jet := fun _ hj ↦ memLp_cutoffAllJet e.memLp_jet χ.contDiff χ.hasCompactSupport hj
  restrict_eq := hv

/-- A fixed bump preserves the restriction Sobolev norm at every natural
order, on any measurement domain. The bound is transported through the
infimum over actual extensions; no positive-order multiplier estimate is an
input (`app:ch_regular:eq:one-gain-tame`). -/
theorem exists_bump_sobolev_constant (χ : ContDiffBump x) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U V : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U →
      ∀ (u : LocalL2 U F) (v : LocalL2 V F),
        (SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
          =ᵐ[volume.restrict V] v) →
        MemRestrictionSobolev U s u →
        MemRestrictionSobolev V s v ∧
          restrictionSobolevNorm V s v ≤ C * restrictionSobolevNorm U s u := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoffAllJet_bound (F := F)
    χ χ.contDiff χ.hasCompactSupport s
  refine ⟨C, hC, ?_⟩
  intro U V hU hs u v hv hu
  have heq (e : SobolevExtension U s u) :
      (fun y ↦ χ y • e.toFun y) =ᵐ[volume.restrict V] v := by
    have hlocal : (fun y ↦ χ y • e.toFun y) =ᵐ[volume.restrict V]
        SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u) :=
      ae_restrict_of_ae (e.bump_ae_zeroExtend hU χ hs)
    exact hlocal.trans hv
  refine ⟨⟨hu.some.cutoffAll χ (heq hu.some)⟩, ?_⟩
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨e, he⟩ := exists_extension_jetNorm_lt hu
    (lt_add_of_pos_right _ (div_pos hε hCpos))
  have hout := (restrictionSobolevNorm_le (e.cutoffAll χ (heq e))).trans
    (hbound e.jet e.memLp_jet)
  change restrictionSobolevNorm V s v ≤ C * e.jetNorm at hout
  have he' := mul_lt_mul_of_pos_left he hCpos
  rw [mul_add, mul_div_cancel₀ _ hCpos.ne'] at he'
  linarith

/-- The existing local L² bump multiplier preserves each restriction
Sobolev level, with its constant fixed before the domain and data. This is
the source-cutoff bound needed by `app:ch_regular:eq:one-gain-tame`. -/
theorem exists_bumpL2_sobolev_bound (χ : ContDiffBump x) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set E) (_hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U → ∀ u : LocalL2 U F,
      MemRestrictionSobolev U s u →
      MemRestrictionSobolev U s (SmallSupport.bumpL2 (p := 2) le_rfl χ u) ∧
        restrictionSobolevNorm U s (SmallSupport.bumpL2 (p := 2) le_rfl χ u) ≤
          C * restrictionSobolevNorm U s u := by
  obtain ⟨C, hC, hbound⟩ := exists_bump_sobolev_constant (F := F) χ s
  refine ⟨C, hC, fun U hU hs u hu ↦ hbound U U hU hs u _ ?_ hu⟩
  filter_upwards [ae_restrict_of_ae (SmallSupport.zeroExtend_coeFn hU
    (SmallSupport.bumpL2 (p := 2) le_rfl χ u)), ae_restrict_mem hU] with y hy hyU
  simpa only [indicator_of_mem hyU] using hy

/-- The literal zero-extended representative has a genuine whole-space weak
jet through any prescribed natural order. Normalization changes only a.e.
representatives (`app:ch_regular:thm:exact-correction`). -/
theorem exists_weakJet_zeroExtend_bumpL2
    (hU : MeasurableSet U) (χ : ContDiffBump x) (hs : tsupport (χ : E → ℝ) ⊆ U)
    (s : ℕ) (u : LocalL2 U F) (hu : MemRestrictionSobolev U s u) :
    let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
    ∃ J : (j : ℕ) → E → E [×j]→L[ℝ] F,
      Mollification.HasWeakJetOn volume z J univ s ∧
      ∀ j ≤ s, MemLp (J j) 2 volume := by
  let e := hu.some
  let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
  let J := cutoffAllJet χ χ.contDiff χ.hasCompactSupport e.jet
  have hw := hasWeakJetOn_cutoffAllJet e.weakJet e.memLp_jet χ.contDiff χ.hasCompactSupport
  have hz : J 0 =ᵐ[volume.restrict univ] iteratedFDeriv ℝ 0 (fun y ↦ z y) := by
    rw [Measure.restrict_univ]
    filter_upwards [e.bump_ae_zeroExtend hU χ hs] with y hy
    dsimp only [J]
    rw [hw.1]
    ext v
    simpa only [iteratedFDeriv_zero_apply] using hy
  refine ⟨Mollification.normalizeWeakJet z J, ?_, ?_⟩
  · exact hw.congr_ae rfl (fun j _ ↦ Mollification.normalizeWeakJet_ae hz j)
  · intro j hj
    simpa only [Measure.restrict_univ] using Mollification.memLp_normalizeWeakJet hz
      (show MemLp (J j) 2 (volume.restrict univ) by
        simpa only [Measure.restrict_univ] using
          memLp_cutoffAllJet e.memLp_jet χ.contDiff χ.hasCompactSupport hj)

/-- Zero extension after the existing bump multiplier has restriction H^s
membership and a uniform bound on every measurement domain, in particular
`V = univ`. The fixed constant depends only on the cutoff and order, not
the data or domains (`app:ch_regular:eq:one-gain-tame`). -/
theorem exists_bump_zeroExtension_bound (χ : ContDiffBump x) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U V : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U → ∀ u : LocalL2 U F,
      MemRestrictionSobolev U s u →
      let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
      let v := ((Lp.memLp z).restrict V).toLp z
      MemRestrictionSobolev V s v ∧
        restrictionSobolevNorm V s v ≤ C * restrictionSobolevNorm U s u := by
  obtain ⟨C, hC, hbound⟩ := exists_bump_sobolev_constant (F := F) χ s
  refine ⟨C, hC, fun U V hU hs u hu ↦ ?_⟩
  exact hbound U V hU hs u _ (MemLp.coeFn_toLp _).symm hu

/-- The genuine weak jet of the literal zero extension obeys the same bound
as its whole-space restriction norm. Uniqueness of weak derivatives identifies
its norm with the infimum over extensions; no minimizing extension is assumed
(`app:ch_regular:eq:one-gain-tame`, `app:ch_regular:thm:exact-correction`). -/
theorem exists_bump_zeroExtension_weakJet_bound (χ : ContDiffBump x) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U → ∀ u : LocalL2 U F,
      MemRestrictionSobolev U s u →
      let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
      ∃ J : (j : ℕ) → E → E [×j]→L[ℝ] F,
        Mollification.HasWeakJetOn volume z J univ s ∧
        (∀ j ≤ s, MemLp (J j) 2 volume) ∧
        ∑ j ∈ Finset.range (s + 1), (eLpNorm (J j) 2 volume).toReal ≤
          C * restrictionSobolevNorm U s u := by
  obtain ⟨C, hC, hbound⟩ := exists_bump_zeroExtension_bound (F := F) χ s
  refine ⟨C, hC, fun U hU hs u hu ↦ ?_⟩
  let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
  let v : LocalL2 univ F := ((Lp.memLp z).restrict univ).toLp z
  obtain ⟨J, hw, hJ⟩ := exists_weakJet_zeroExtend_bumpL2 hU χ hs s u hu
  obtain ⟨hv, hn⟩ := hbound U univ hU hs u hu
  refine ⟨J, hw, hJ, le_trans ?_ hn⟩
  change _ ≤ restrictionSobolevNorm univ s v
  unfold restrictionSobolevNorm
  apply le_csInf
  · exact ⟨hv.some.jetNorm, hv.some, rfl⟩
  · rintro _ ⟨e, rfl⟩
    have heq : z =ᵐ[volume.restrict univ] e.toFun :=
      (MemLp.coeFn_toLp ((Lp.memLp z).restrict univ)).symm.trans e.restrict_eq.symm
    have hjets := hw.ae_eq e.weakJet isOpen_univ heq
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro j hj
    have heqj : J j =ᵐ[volume] e.jet j := by
      simpa only [Measure.restrict_univ] using
        hjets j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    rw [eLpNorm_congr_ae heqj]

end JanetCartan.LocalSobolev
