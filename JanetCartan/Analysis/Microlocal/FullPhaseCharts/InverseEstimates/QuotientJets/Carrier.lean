module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Primitive carrier substitution bounds

The consumer is the shifted-gradient composition in `QuotientJets`.
For `app:ch_seed:eq:seed-quotient-integral`, the substitution is affine in epsilon
and linear in each carrier. Its high norm therefore has additive primitive
carrier contributions, uniformly over the covector integration parameter.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Projection retaining all carrier parameters in
`app:ch_seed:eq:seed-quotient-integral`. -/
def carrierParameterProjection : ((P × ℝ) × X) →L[ℝ] P :=
  (ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ (P × ℝ) X)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] in
/-- The parameter projection is a contraction, for the joint carrier jets. -/
theorem norm_carrierParameterProjection_le :
    ‖carrierParameterProjection (P := P) (X := X)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖q.1.1‖ ≤ 1 * ‖q‖
  simpa only [one_mul] using (norm_fst_le q.1).trans (norm_fst_le q)


omit [FiniteDimensional ℝ X] in
/-- Primitive carrier jets bound the lifted carrier on the joint working ball,
including epsilon and physical variables (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem cNorm_carrierLift_le (a : (P × ℝ) × X) (ρ : ℝ)
    {V : Set P} (hV : IsOpen V) (hball : Metric.closedBall a.1.1 ρ ⊆ V)
    {z : P → E} (hz : ContDiffOn ℝ ∞ z V) (k : ℕ) :
    cNorm (Metric.closedBall a ρ) k (fun q : (P × ℝ) × X ↦ z q.1.1) ≤
      (k + 1 : ℝ) * cNorm (Metric.closedBall a.1.1 ρ) k z := by
  have hm : MapsTo (carrierParameterProjection (P := P) (X := X))
      (Metric.closedBall a ρ) (Metric.closedBall a.1.1 ρ) := by
    intro q hq
    change dist q.1.1 a.1.1 ≤ ρ
    have h := (norm_fst_le (q.1 - a.1)).trans (norm_fst_le (q - a))
    have hd : dist q.1.1 a.1.1 ≤ dist q a := by
      simpa only [dist_eq_norm, Prod.fst_sub] using h
    exact hd.trans hq
  exact cNorm_comp_contraction_le_on (carrierParameterProjection (P := P) (X := X))
    norm_carrierParameterProjection_le (isCompact_closedBall _ _) hV hball hz hm k

/-- The literal shifted covector substitution. All spectators remain in `P`. -/
def carrierSubstitution (z v : P → E) (t : ℝ) (q : (P × ℝ) × X) : (P × X) × E :=
  ((q.1.1, q.2), z q.1.1 + (t * q.1.2) • v q.1.1)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] in
/-- Uniform joint smoothness of the actual substitution, including epsilon zero. -/
theorem contDiffOn_carrierSubstitution {V : Set P} {I : Set ℝ} {U : Set X}
    {z v : P → E} (hz : ContDiffOn ℝ ∞ z V) (hv : ContDiffOn ℝ ∞ v V) (t : ℝ) :
    ContDiffOn ℝ ∞ (carrierSubstitution (X := X) z v t) ((V ×ˢ I) ×ˢ U) :=
  (contDiffOn_fst.fst.prodMk contDiffOn_snd).prodMk
    ((hz.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1)).add
      ((contDiffOn_const.mul contDiffOn_fst.snd).smul
        (hv.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1))))

/-- The shifted covector substitution has a linear high carrier bound, with a
constant fixed before the carriers and before the integration parameter.
This supplies the inner-map input of the tame composition for
`app:ch_seed:eq:seed-quotient-integral`. -/
theorem exists_cNorm_carrierSubstitution_le
    (a : (P × ℝ) × X) (ρ : ℝ)
    {V : Set P} {I : Set ℝ} {U : Set X}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U)
    (hball : Metric.closedBall a ρ ⊆ (V ×ˢ I) ×ˢ U)
    (hparam : Metric.closedBall a.1.1 ρ ⊆ V) (k : ℕ) :
    ∃ D > (0 : ℝ), ∀ (z v : P → E),
      ContDiffOn ℝ ∞ z V → ContDiffOn ℝ ∞ v V →
      ∀ t ∈ Icc (0 : ℝ) 1,
      cNorm (Metric.closedBall a ρ) k (carrierSubstitution z v t) ≤
        D * (1 + cNorm (Metric.closedBall a.1.1 ρ) k z +
          cNorm (Metric.closedBall a.1.1 ρ) k v) := by
  let K := Metric.closedBall a ρ
  let J := Metric.closedBall a.1.1 ρ
  let Q := (V ×ˢ I) ×ˢ U
  let e : ((P × ℝ) × X) → ℝ := fun q ↦ q.1.2
  let p : ((P × ℝ) × X) → P × X := fun q ↦ (q.1.1, q.2)
  let b := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  let L : ℝ := ∑ j ∈ Finset.range (k + 1), ‖b‖ *
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ ↦
    mul_nonneg (norm_nonneg b) (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)))
  have he : 0 ≤ cNorm K k e := cNorm_nonneg _ _ _
  have hp : 0 ≤ cNorm K k p := cNorm_nonneg _ _ _
  let D := 1 + cNorm K k p + (k + 1) + L * cNorm K k e * (k + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro z v hz hv t ht
  have hzQ : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × X ↦ z q.1.1) Q :=
    hz.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1)
  have hvQ : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × X ↦ v q.1.1) Q :=
    hv.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1)
  have heQ : ContDiffOn ℝ ∞ e Q := contDiffOn_fst.snd
  have hteQ : ContDiffOn ℝ ∞ (fun q ↦ t * e q) Q := contDiffOn_const.mul heQ
  have hprodQ := hteQ.smul hvQ
  have hQ : IsOpen Q := (hV.prod hI).prod hU
  have hb := cNorm_bilinear_le_on b (isCompact_closedBall a ρ) hQ hball hteQ hvQ k
  have hte : cNorm K k (fun q ↦ t * e q) ≤ cNorm K k e := by
    change cNorm K k (t • e) ≤ cNorm K k e
    rw [cNorm_smul t (contDiff_fst.snd : ContDiff ℝ k e)]
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left he ht.2
  have hvb := cNorm_carrierLift_le a ρ hV hparam hv k
  have hzb := cNorm_carrierLift_le a ρ hV hparam hz k
  have hprod : cNorm K k (fun q : (P × ℝ) × X ↦ (t * e q) • v q.1.1) ≤
      L * cNorm K k e * ((k + 1 : ℝ) * cNorm J k v) := by
    exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hte hL) hvb
      (cNorm_nonneg _ _ _) (mul_nonneg hL he))
  have hadd := cNorm_add_le_of_contDiffAt (r := k) (isCompact_closedBall a ρ)
    (fun q hq ↦ (hzQ.contDiffAt (hQ.mem_nhds (hball hq))).of_le (by simp))
    (fun q hq ↦ (hprodQ.contDiffAt (hQ.mem_nhds (hball hq))).of_le (by simp))
  have hpair := cNorm_prodMk_le_on K (isCompact_closedBall a ρ) k
    (fun _ _ ↦ (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt)
    (fun q hq ↦ ((hzQ.add hprodQ).contDiffAt (hQ.mem_nhds (hball hq))).of_le (by simp))
  apply hpair.trans
  apply (add_le_add le_rfl (hadd.trans (add_le_add hzb hprod))).trans
  change cNorm K k p + ((k + 1) * cNorm J k z +
    L * cNorm K k e * ((k + 1) * cNorm J k v)) ≤ _
  have hz0 := cNorm_nonneg J k z
  have hv0 := cNorm_nonneg J k v
  have hcoef : 0 ≤ L * cNorm K k e * (k + 1 : ℝ) := by positivity
  dsimp only [D]
  nlinarith [mul_nonneg hp hz0, mul_nonneg hp hv0,
    mul_nonneg hcoef hz0, mul_nonneg hcoef hv0]

end JanetCartan.FullPhaseCharts.InverseEstimates
