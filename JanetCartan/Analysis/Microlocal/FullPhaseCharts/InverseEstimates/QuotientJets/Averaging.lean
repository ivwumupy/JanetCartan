module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Integral
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Joint jets under physical averaging

The physical averaging step of `app:ch_seed:prop:seed-phase-charts` costs exactly
one phase derivative. The parameter space is arbitrary, so epsilon, time and
the transverse spectator variables remain among the differentiated variables.
These estimates will be applied to the literal integral quotient; they do not
assert its primitive one-high estimate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

local instance : NormedSpace ℝ X := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ (P × X) := Prod.normedSpace
local instance : NormedSpace ℝ ((P × X) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((P × X) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Restriction of a joint phase differential to the physical directions,
used in `app:ch_seed:prop:seed-phase-charts`. -/
def physicalDifferentialRestriction :
    ((P × X) →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ X (P × X) ℝ).flip
    (ContinuousLinearMap.inr ℝ P X)

omit [CompleteSpace X] in
/-- Physical restriction is a contraction, independently of every parameter
and phase (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_physicalDifferentialRestriction_le :
    ‖physicalDifferentialRestriction (P := P) (X := X)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simpa [physicalDifferentialRestriction] using L.le_opNorm (0, v)

omit [CompleteSpace X] in
/-- Identification with the actual partial differential in the phase-chart
integral (`app:ch_seed:prop:seed-phase-charts`). -/
theorem physicalDifferentialRestriction_fderiv {S : P → X → ℝ} {q : P × X}
    (hS : DifferentiableAt ℝ (Function.uncurry S) q) :
    physicalDifferentialRestriction (fderiv ℝ (Function.uncurry S) q) =
      fderiv ℝ (S q.1) q.2 := by
  exact ((hS.hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv).symm

/-- The joint physical-gradient jet loses just one primitive phase derivative.
No parameter derivative is omitted (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_iteratedFDeriv_jointPhaseGradient_le
    {S : P → X → ℝ} {V : Set P} {U : Set X}
    (hV : IsOpen V) (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    {q : P × X} (hq : q ∈ V ×ˢ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : P × X ↦ gradient (S w.1) w.2) q‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) (Function.uncurry S) q‖ := by
  let R := physicalDifferentialRestriction (P := P) (X := X)
  have he : EqOn (fun w : P × X ↦ gradient (S w.1) w.2)
      ((InnerProductSpace.toDual ℝ X).symm ∘ R ∘ fderiv ℝ (Function.uncurry S))
      (V ×ˢ U) := by
    intro w hw
    rw [Function.comp_apply, Function.comp_apply,
      physicalDifferentialRestriction_fderiv
        ((hS.contDiffAt ((hV.prod hU).mem_nhds hw)).differentiableAt (by simp))]
    rfl
  have hj := iteratedFDerivWithin_congr (𝕜 := ℝ) he hq k
  rw [iteratedFDerivWithin_of_isOpen _ (hV.prod hU) hq,
    iteratedFDerivWithin_of_isOpen _ (hV.prod hU) hq] at hj
  rw [hj, (InnerProductSpace.toDual ℝ X).symm.norm_iteratedFDeriv_comp_left]
  have hd := (hS.contDiffAt ((hV.prod hU).mem_nhds hq)).fderiv_right
    (m := ∞) (by simp)
  calc
    _ ≤ ‖R‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ (Function.uncurry S)) q‖ :=
      R.norm_iteratedFDeriv_comp_left hd (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ (Function.uncurry S)) q‖ :=
      mul_le_mul_of_nonneg_right norm_physicalDifferentialRestriction_le (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- The partial physical gradient has its joint `C^k` seminorm bounded by
the primitive phase `C^(k+1)` seminorm, with constant one. Applied in covector
space, this supplies both low and high inputs to the shifted-gradient tame
composition (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem cNorm_jointPhaseGradient_le
    {S : P → X → ℝ} {V : Set P} {U : Set X} {K : Set (P × X)}
    (hV : IsOpen V) (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hK : IsCompact K) (hKU : K ⊆ V ×ˢ U) (k : ℕ) :
    cNorm K k (fun w : P × X ↦ gradient (S w.1) w.2) ≤
      cNorm K (k + 1) (Function.uncurry S) := by
  let D : ℕ → ℝ := fun j ↦ sSup
    ((fun q ↦ ‖iteratedFDeriv ℝ j (Function.uncurry S) q‖) '' K)
  have hD (j : ℕ) : 0 ≤ D j := sSup_norm_iteratedFDeriv_nonneg K j _
  have hb (j : ℕ) : BddAbove
      ((fun q ↦ ‖iteratedFDeriv ℝ j (Function.uncurry S) q‖) '' K) :=
    bddAbove_norm_iteratedFDeriv_of_contDiffAt hK
      (fun q hq ↦ (hS.contDiffAt ((hV.prod hU).mem_nhds (hKU hq))).of_le (by simp))
      le_rfl
  apply (cNorm_le_sum_of_bounds (C := fun j ↦ D (j + 1))
    (fun j _ ↦ hD (j + 1)) ?_).trans
  · change (∑ j ∈ Finset.range (k + 1), D (j + 1)) ≤ ∑ j ∈ Finset.range (k + 1 + 1), D j
    rw [Finset.sum_range_succ' D (k + 1)]
    exact le_add_of_nonneg_right (hD 0)
  · intro j _ q hq
    exact (norm_iteratedFDeriv_jointPhaseGradient_le hV hU hS (hKU hq) j).trans
      (le_csSup (hb (j + 1)) (mem_image_of_mem _ hq))

/-- Segment substitution retaining all parameters and both physical positions
in `app:ch_seed:prop:seed-phase-charts`. -/
def jointPhysicalSegment (t : ℝ) : (P × X × X) →L[ℝ] P × X :=
  let p := ContinuousLinearMap.fst ℝ P (X × X)
  let xy := ContinuousLinearMap.snd ℝ P (X × X)
  let x := (ContinuousLinearMap.fst ℝ X X).comp xy
  let y := (ContinuousLinearMap.snd ℝ X X).comp xy
  p.prod (y + t • (x - y))

omit [CompleteSpace X] in
/-- Evaluation of the physical segment map. -/
@[simp] theorem jointPhysicalSegment_apply (t : ℝ) (q : P × X × X) :
    jointPhysicalSegment t q = (q.1, q.2.2 + t • (q.2.1 - q.2.2)) := rfl

omit [CompleteSpace X] in
/-- Uniform geometric bound for the physical segment substitution
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_jointPhysicalSegment_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖jointPhysicalSegment (P := P) (X := X) t‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change max ‖q.1‖ ‖q.2.2 + t • (q.2.1 - q.2.2)‖ ≤ 3 * ‖q‖
  have hp := norm_fst_le q
  have hx := (norm_fst_le q.2).trans (norm_snd_le q)
  have hy := (norm_snd_le q.2).trans (norm_snd_le q)
  apply max_le
  · nlinarith [norm_nonneg q]
  · calc
      _ ≤ ‖q.2.2‖ + ‖t • (q.2.1 - q.2.2)‖ := norm_add_le _ _
      _ = ‖q.2.2‖ + t * ‖q.2.1 - q.2.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖q.2.2‖ + 1 * (‖q.2.1‖ + ‖q.2.2‖) :=
        add_le_add le_rfl (mul_le_mul ht.2 (norm_sub_le _ _)
          (norm_nonneg _) zero_le_one)
      _ ≤ 3 * ‖q‖ := by linarith

/-- Joint jets of the physical integrand use one additional joint phase jet
and the fixed factor `3 ^ k` (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_iteratedFDeriv_physicalSegmentGradient_le
    {S : P → X → ℝ} {V : Set P} {U : Set X}
    (hV : IsOpen V) (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : P × X × X} (hq : jointPhysicalSegment t q ∈ V ×ˢ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : P × X × X ↦
      gradient (S w.1) (w.2.2 + t • (w.2.1 - w.2.2))) q‖ ≤
      3 ^ k * ‖iteratedFDeriv ℝ (k + 1) (Function.uncurry S)
        (jointPhysicalSegment t q)‖ := by
  have h := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (jointPhysicalSegment t) (hV.prod hU) (contDiffOn_phaseGradient hV hU hS) hq k
  apply h.trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ (k + 1) (Function.uncurry S)
        (jointPhysicalSegment t q)‖ * 3 ^ k := by
      gcongr
      · exact norm_iteratedFDeriv_jointPhaseGradient_le hV hU hS hq k
      · exact norm_jointPhysicalSegment_le ht
    _ = _ := mul_comm _ _

/-- All joint jets of the literal physical average are bounded by primitive
phase jets. The domains are open, and physical-segment containment is explicit.
This is the averaging step, not the one-high bound for the quotient phase
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_iteratedFDeriv_averagedPhaseGradient_joint_le
    {S : P → X → ℝ} {V : Set P} {U B : Set X}
    (hV : IsOpen V) (hU : IsOpen U) (hB : IsOpen B)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hsegment : ∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
      y + t • (x - y) ∈ U)
    {C : ℕ → ℝ} {k : ℕ}
    (hjets : ∀ j ≤ k + 1, ∀ w ∈ V ×ˢ U,
      ‖iteratedFDeriv ℝ j (Function.uncurry S) w‖ ≤ C j)
    {q : P × X × X} (hq : q ∈ V ×ˢ B ×ˢ B) :
    ‖iteratedFDeriv ℝ k (fun w : P × X × X ↦
      averagedPhaseGradient S w.1 w.2.1 w.2.2) q‖ ≤ 3 ^ k * C (k + 1) := by
  let H : ℝ × (P × X × X) → X := fun w ↦
    gradient (S w.2.1) (w.2.2.2 + w.1 • (w.2.2.1 - w.2.2.2))
  have hH : ∀ w ∈ Icc (0 : ℝ) 1 ×ˢ (V ×ˢ B ×ˢ B), ContDiffAt ℝ ∞ H w := by
    intro w hw
    have hm : (w.2.1, w.2.2.2 + w.1 • (w.2.2.1 - w.2.2.2)) ∈ V ×ˢ U :=
      ⟨hw.2.1, hsegment _ hw.2.2.1 _ hw.2.2.2 _ hw.1⟩
    have hg : ContDiffAt ℝ ∞ (fun a : ℝ × (P × X × X) ↦
        (a.2.1, a.2.2.2 + a.1 • (a.2.2.1 - a.2.2.2))) w :=
      contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.snd.add
        (contDiffAt_fst.smul (contDiffAt_snd.snd.fst.sub contDiffAt_snd.snd.snd)))
    have hh := ((contDiffOn_phaseGradient hV hU hS).contDiffAt
      ((hV.prod hU).mem_nhds hm)).comp w hg
    exact hh
  apply NormalComparison.norm_iteratedFDeriv_unitIntervalIntegral_le
    (H := H) (B := fun j ↦ 3 ^ j * C (j + 1)) (hV.prod (hB.prod hB)) hH _ hq
  intro j hj t ht w hw
  have hm : jointPhysicalSegment t w ∈ V ×ˢ U :=
    ⟨hw.1, hsegment _ hw.2.1 _ hw.2.2 _ ht⟩
  exact (norm_iteratedFDeriv_physicalSegmentGradient_le hV hU hS ht hm j).trans
    (mul_le_mul_of_nonneg_left (hjets (j + 1) (by omega) _ hm) (by positivity))

end JanetCartan.FullPhaseCharts.InverseEstimates
