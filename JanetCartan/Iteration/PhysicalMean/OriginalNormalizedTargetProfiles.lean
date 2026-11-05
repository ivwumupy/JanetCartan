module
public import JanetCartan.Iteration.PhysicalSmoothing.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.FiniteMoment.RevisedSource
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# True physical profiles of the SAME normalized finite-moment target

The tensor itself, not its possibly noninjective measurement, has an all-order
physical profile fixed before the smoothing order and history. Only its numeric
CURRENT-stage threshold depends on that approximation order. The exact original
finite-moment field, chart and defect are unchanged. Consumers are the actual
single completed mean's physical profiles and its symmetry gate in
`main:prop:mean` / `new:eq:mean-error-formula`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set Metric Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles
open DefectSmoothing LocalSobolev PhysicalSmoothing

/-- Retain the physical part of the actual finite-moment producer, including
its honest symmetry frequency. No tensor profile is assumed. -/
theorem exists_original_tensor_bounds (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : ℝ, 1 ≤ S ∧ (2 : ℝ)*m ≤ S ∧ ∃ C : ℕ → ℝ,
      (∀ q, 0 ≤ C q) ∧ ∀ R : ℝ, S ≤ R →
      ∀ e : MetricField n, ContDiffOn ℝ ∞ e (D.chart n) →
      ∀ δ : ℝ, 0 < δ → cNorm (D.core n) 0 e ≤ δ^2 →
      ∀ (K : Set (Euclidean n)) (q : ℕ),
        cNorm K q (revisedFiniteMomentSource D R m δ e) ≤
          C q * R^((q : ℝ)-2*RevisedScales.forcingExponent n) := by
  obtain ⟨K0,S,C,_,_,hS,hmS,hC,_,hb⟩ := exists_revisedFiniteMomentSource_bounds (n := n) D m hm
  refine ⟨S,hS,hmS,C,hC,?_⟩
  intro R hR e he δ hδ hsmall K q
  obtain ⟨hsm,_,hcompact,_,_,hjets,_,_⟩ := hb R hR e he δ hδ hsmall
  have hbounded (j : ℕ) :
      BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j (revisedFiniteMomentSource D R m δ e) x‖) '' univ) := by
    have hcont : Continuous (iteratedFDeriv ℝ j (revisedFiniteMomentSource D R m δ e)) :=
      hsm.continuous_iteratedFDeriv (by simp)
    simpa only [Set.image_univ] using
      hcont.norm.bddAbove_range_of_hasCompactSupport (hcompact.iteratedFDeriv j).norm
  apply (cNorm_mono_set_of_bddAbove (Set.subset_univ K) (fun j _ ↦ hbounded j)).trans
  exact (le_add_of_nonneg_right (show 0 ≤ cartesianJetNorm univ q
    (fun j ↦ iteratedFDeriv ℝ j (revisedFiniteMomentSource D R m δ e)) from Real.sqrt_nonneg _)).trans (hjets q)

/-- Genuine original finite-moment threshold, before every history and tensor. -/
def rawFrequency (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) : ℝ :=
  (exists_original_tensor_bounds n D m hm).choose
/-- Genuine physical tensor cost; independent of the measured target. -/
def rawCost (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) : ℕ → ℝ :=
  (exists_original_tensor_bounds n D m hm).choose_spec.2.2.choose

theorem rawCost_nonneg (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) :
    ∀ q, 0 ≤ rawCost n D m hm q :=
  (exists_original_tensor_bounds n D m hm).choose_spec.2.2.choose_spec.1

/-- Zero extension at the unused approximation order zero. -/
def orderCost (n : ℕ) (D : LocalDomain) (m q : ℕ) : ℝ :=
  if hm : 1 ≤ m then rawCost n D m hm q else 0

theorem orderCost_nonneg (n : ℕ) (D : LocalDomain) (m q : ℕ) :
    0 ≤ orderCost n D m q := by
  unfold orderCost
  split
  · exact rawCost_nonneg _ _ _ _ _
  · rfl

/-- The actual tensor's common order-only budget precedes approximation order,
metric, defect size, frequency, history and Picard count. -/
def Ctarget (n : ℕ) (D : LocalDomain) (q : ℕ) : ℝ :=
  1 + ∑ m ∈ range (q+1), orderCost n D m q

theorem one_le_Ctarget (n : ℕ) (D : LocalDomain) (q : ℕ) : 1 ≤ Ctarget n D q := by
  unfold Ctarget
  exact le_add_of_nonneg_right (sum_nonneg fun m _ ↦ orderCost_nonneg _ _ _ _)

theorem Ctarget_nonneg (n : ℕ) (D : LocalDomain) (q : ℕ) : 0 ≤ Ctarget n D q :=
  zero_le_one.trans (one_le_Ctarget n D q)

/-- A numerical CURRENT-stage gate only. It is not an initial geometric
threshold and must not enter a supposedly order-independent Tref. -/
def Starget (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) : ℝ :=
  max (rawFrequency n D m hm) (max 1 (∑ q ∈ range (m+1), orderCost n D m q))

theorem one_le_Starget (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ Starget n D m hm :=
  (exists_original_tensor_bounds n D m hm).choose_spec.1.trans (le_max_left _ _)

theorem moment_le_Starget (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ)*m ≤ Starget n D m hm :=
  (exists_original_tensor_bounds n D m hm).choose_spec.2.1.trans (le_max_left _ _)

private theorem rawCost_le (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m)
    {R : ℝ} (hR : Starget n D m hm ≤ R) (q : ℕ) :
    rawCost n D m hm q ≤ Ctarget n D q * R := by
  have h1 : 1 ≤ R := (one_le_Starget n D m hm).trans hR
  have hC := Ctarget_nonneg n D q
  have hC1 := one_le_Ctarget n D q
  have he : rawCost n D m hm q = orderCost n D m q := by simp [orderCost, hm]
  rw [he]
  by_cases hq : q ≤ m
  · have hsum : orderCost n D m q ≤ ∑ k ∈ range (m+1), orderCost n D m k :=
      single_le_sum (f := fun k ↦ orderCost n D m k) (fun k _ ↦ orderCost_nonneg _ _ _ _)
        (show q ∈ range (m+1) from mem_range.mpr (by omega))
    have hsumR : (∑ k ∈ range (m+1), orderCost n D m k) ≤ R :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hR)
    exact (hsum.trans hsumR).trans (le_mul_of_one_le_left (zero_le_one.trans h1) hC1)
  · have hsum : orderCost n D m q ≤ ∑ k ∈ range (q+1), orderCost n D k q :=
      single_le_sum (f := fun k ↦ orderCost n D k q) (fun k _ ↦ orderCost_nonneg _ _ _ _)
        (show m ∈ range (q+1) from mem_range.mpr (by omega))
    have hsmall : orderCost n D m q ≤ Ctarget n D q :=
      hsum.trans (le_add_of_nonneg_left zero_le_one)
    exact hsmall.trans (le_mul_of_one_le_right hC h1)

/-- Every physical tensor derivative order has its TRUE R profile, for the
same finite-moment source, on any requested physical set. All analytic inputs
are the original smooth defect and its original zeroth smallness bound. -/
theorem tensor_profile (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : Starget n D m hm ≤ R)
    (e : MetricField n) (he : ContDiffOn ℝ ∞ e (D.chart n))
    (δ : ℝ) (hδ : 0 < δ) (hsmall : cNorm (D.core n) 0 e ≤ δ^2)
    (K : Set (Euclidean n)) (q : ℕ) :
    cNorm K q (revisedFiniteMomentSource D R m δ e) ≤ Ctarget n D q * R^q := by
  have h1 : 1 ≤ R := (one_le_Starget n D m hm).trans hR
  have hp : 0 < R := zero_lt_one.trans_le h1
  have hbase := (exists_original_tensor_bounds n D m hm).choose_spec.2.2.choose_spec.2
    R ((le_max_left _ _).trans hR) e he δ hδ hsmall K q
  have hcoef := rawCost_le n D m hm hR q
  have ha : 1 ≤ 2*RevisedScales.forcingExponent n := by
    unfold RevisedScales.forcingExponent
    have hc : (0 : ℝ) ≤ RevisedScales.baselineOrder n := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ rawCost n D m hm q * R^((q : ℝ)-2*RevisedScales.forcingExponent n) := hbase
    _ ≤ (Ctarget n D q * R) * R^((q : ℝ)-2*RevisedScales.forcingExponent n) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hp.le _)
    _ = Ctarget n D q * R^(1+((q : ℝ)-2*RevisedScales.forcingExponent n)) := by
      rw [Real.rpow_add hp, Real.rpow_one]
      ring
    _ ≤ Ctarget n D q * R^(q : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (Ctarget_nonneg _ _ _)
    _ = _ := by rw [Real.rpow_natCast]

/-- The SAME normalized source of an original physical history, without a
measured-source inversion or an assumed tensor estimate. -/
theorem normalized_target_profile (n j : ℕ) (D : LocalDomain) (G : FlatReference n)
    (R : ℝ) (m : ℕ) (hm : 1 ≤ m) (gs : MetricField n)
    (hgs : ContDiffOn ℝ ∞ gs (D.chart n)) (δ : ℝ) (hδ : 0 < δ)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
    (hsmall : cNorm (D.core n) 0 (inducedMetric (RevisedGlobal.finiteMap G.map u) - gs) ≤ δ^2)
    (hR : Starget n D m hm ≤ R) (K : Set (Euclidean n)) (q : ℕ) :
    cNorm K q (normalizedSource D R m δ gs G.map u) ≤ Ctarget n D q * R^q := by
  have he := contDiffOn_historyDefect hgs G.contDiff u
  have hb : cNorm (D.core n) 0 (historyDefect gs G.map u) ≤ δ^2 := by
    change cNorm _ 0 (gs - inducedMetric (RevisedGlobal.finiteMap G.map u)) ≤ _
    rw [← neg_sub (inducedMetric (RevisedGlobal.finiteMap G.map u)) gs, cNorm_neg]
    exact hsmall
  exact tensor_profile n D m hm R hR _ he δ hδ hb K q

end JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles
end
