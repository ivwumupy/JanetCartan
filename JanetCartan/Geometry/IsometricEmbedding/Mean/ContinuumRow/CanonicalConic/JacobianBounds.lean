module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.InverseDomain

/-!
# Uniform Jacobian bounds for the actual supported cone

The fixed reference half-gap gives a uniform determinant upper bound before
the immersion is chosen. The actual buffered chart gives its lower bound.
The already proved conic determinant law then extends both bounds to the
whole cone, retaining degree one in the covector (`bg-jacobian`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction.ConicChart

variable {n : ℕ}

/-- A fixed bound for differentials and their determinants on the reference
half-gap. It is chosen before the immersion, as required for the conic
Jacobian comparison in `app:ch_background:eq:bg-jacobian`. -/
theorem exists_reference_differential_upper
    (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))) :
    ∃ C > (0 : ℝ), ∀ D : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1)),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp D -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2 →
      ‖D‖ ≤ C ∧ |D.det| ≤ C := by
  let f := fun D : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1)) ↦
    (G : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp D
  have hf : Continuous f := continuous_const.clm_comp continuous_id
  have hK := (isCompact_closedBall (ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1)))
    (1 / 2 : ℝ)).image hf
  have hb := hK.image (continuous_id.norm.add ContinuousLinearMap.continuous_det.norm)
  obtain ⟨C, hC, hbound⟩ := hb.isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun D hD ↦ ?_⟩
  have hmem : D ∈ f '' closedBall (ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1)))
      (1 / 2 : ℝ) := by
    refine ⟨(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp D,
      ?_, ?_⟩
    · simpa only [mem_closedBall, dist_eq_norm] using hD
    · apply ContinuousLinearMap.ext
      intro x
      exact G.apply_symm_apply (D x)
  have h : ‖‖D‖ + ‖D.det‖‖ ≤ C := hbound _ ⟨D, hmem, rfl⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  exact ⟨(le_add_of_nonneg_right (norm_nonneg D.det)).trans h,
    (le_add_of_nonneg_left (norm_nonneg D)).trans h⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Absolute determinant in the retained adapted coordinates. The physical
measure-normalized determinant is identified by coordinate conjugacy in the
kernel adapter (`app:ch_background:eq:bg-jacobian`). -/
def adaptedJacobian (p : Euclidean 2 × Euclidean n × Euclidean n)
    (u : ℝ × Euclidean (n - 1)) : ℝ :=
  |(fderiv ℝ (adaptedTransportChart T Q p) u).det|

/-- Differentiating the actual covector homogeneity recovers the value from
its covector differential. This supplies the output-frequency upper bound
without assuming a symbol estimate (`app:ch_background:eq:bg-Psi`). -/
theorem adaptedTransportChart_eq_fderiv_radial
    (p : Euclidean 2 × Euclidean n × Euclidean n) (u : ℝ × Euclidean (n - 1))
    (hd : DifferentiableAt ℝ (adaptedTransportChart T Q p) u) :
    (fderiv ℝ (adaptedTransportChart T Q p) u) (0, u.2) = adaptedTransportChart T Q p u := by
  have hc : HasDerivAt (fun t : ℝ ↦ radialScale t u) (0, u.2) 1 := by
    simpa only [radialScale, id_eq, one_smul] using
      (hasDerivAt_const (1 : ℝ) u.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const u.2)
  have hd' : HasFDerivAt (adaptedTransportChart T Q p)
      (fderiv ℝ (adaptedTransportChart T Q p) u) (radialScale 1 u) := by
    simpa only [radialScale_one] using hd.hasFDerivAt
  have hh := hd'.comp_hasDerivAt 1 hc
  have hr : HasDerivAt (fun t : ℝ ↦ t • adaptedTransportChart T Q p u)
      (adaptedTransportChart T Q p u) 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const
      (adaptedTransportChart T Q p u)
  have he : (adaptedTransportChart T Q p ∘ fun t ↦ radialScale t u) =
      fun t ↦ t • adaptedTransportChart T Q p u := by
    funext t
    exact adaptedTransportChart_radialScale T Q p u t
  rw [he] at hh
  exact hh.unique hr

variable {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr hf in
/-- Differentiability of every actual conic slice, proved by the local-chart
normalization (`app:ch_background:eq:bg-jacobian`). -/
theorem adaptedTransportChart_differentiableAt_on_cone
    {p : Euclidean 2 × Euclidean n × Euclidean n} (hp : p ∈ physicalParameterSet z₀ a)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) :
    DifferentiableAt ℝ (adaptedTransportChart T Q p) u := by
  have hopen : IsOpen (physicalParameterSet (n := n) z₀ a ×ˢ
      supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) :=
    (physicalParameterSet_open (n := n) z₀ a).prod
      (supportedCone_open z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r))
  have hmem : (p, u) ∈ physicalParameterSet z₀ a ×ˢ
      supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r) := ⟨hp, hu⟩
  have hh := (adaptedTransportChart_smooth_on_cone T Q hηb hr hf).contDiffAt
    (hopen.mem_nhds hmem)
  have hc : ContDiffAt ℝ ∞ (fun v : ℝ × Euclidean (n - 1) ↦ (p, v)) u :=
    contDiffAt_const.prodMk contDiffAt_id
  have hs := hh.comp u hc
  change ContDiffAt ℝ ∞ (adaptedTransportChart T Q p) u at hs
  exact hs.differentiableAt (by simp)

include hηb hr hf hInv htrans in
/-- The literal absolute determinant scales by one covector power. This
instantiates the generic conic differentiation proof for the actual Hamilton
chart (`app:ch_background:eq:bg-jacobian`). -/
theorem adaptedJacobian_radialScale
    {p : Euclidean 2 × Euclidean n × Euclidean n} (hp : p ∈ physicalParameterSet z₀ a)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r))
    {t : ℝ} (ht : 0 < t) :
    adaptedJacobian T Q p (radialScale t u) = t * adaptedJacobian T Q p u := by
  let A := supportedAnnularData T Q z₀ hηb hr p (hInv.injective p hp) (htrans p hp)
  exact A.jacobian_radialScale (fun w t _ ↦ adaptedTransportChart_radialScale T Q p w t)
    (fun _ hw ↦ adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf hp hw) hu ht

include hηb hr hf hInv htrans in
/-- Explicit uniform constants for the actual conic Jacobian. The upper
constant `C` is produced by `exists_reference_differential_upper` from the
fixed reference before `F`; the positive lower constant is the output of
`exists_actual_local_charts`. Neither conic bound is assumed
(`app:ch_background:eq:bg-jacobian`). -/
theorem adaptedJacobian_bounds {C : ℝ}
    (hgap : ∀ p ∈ physicalParameterSet z₀ a, ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
    (hC : ∀ D : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1)),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp D -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2 → |D.det| ≤ C)
    {p : Euclidean 2 × Euclidean n × Euclidean n} (hp : p ∈ physicalParameterSet z₀ a)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) :
    (cJ / ‖ηb‖) * ‖u.2‖ ≤ adaptedJacobian T Q p u ∧
      adaptedJacobian T Q p u ≤ (C / ‖ηb‖) * ‖u.2‖ := by
  have hμ := norm_pos_iff.mpr hηb
  have hη := norm_pos_iff.mpr hu.2.1
  have hw : radialScale (‖ηb‖ / ‖u.2‖) u ∈ dataBox z₀ ηb (2 * r) :=
    prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
        (normalizedInput_mem_dataSet hηb hr hu)
  have hl := (hInv.differential_bounds p hp _ hw).2.2
  have hh := hC _ (hgap p hp _ hw)
  change cJ ≤ adaptedJacobian T Q p (radialScale (‖ηb‖ / ‖u.2‖) u) at hl
  change adaptedJacobian T Q p (radialScale (‖ηb‖ / ‖u.2‖) u) ≤ C at hh
  rw [adaptedJacobian_radialScale T Q hηb hr hf hInv htrans hp hu (div_pos hμ hη)] at hl hh
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hμ).mpr
    have h := (le_div_iff₀ hη).mp (show cJ ≤ ‖ηb‖ * adaptedJacobian T Q p u / ‖u.2‖ by
      simpa only [div_mul_eq_mul_div] using hl)
    simpa only [mul_comm] using h
  · have h := (div_le_iff₀ hη).mp (show ‖ηb‖ * adaptedJacobian T Q p u / ‖u.2‖ ≤ C by
      simpa only [div_mul_eq_mul_div] using hh)
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hμ).mpr (by simpa only [mul_comm] using h)

include hηb hr hf hInv htrans in
/-- The actual output covector and input covector have uniform comparable
magnitudes. The constant comes from the fixed reference differential half-gap
and thus precedes the immersion (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem adaptedTransportChart_norm_bounds {C : ℝ}
    (hgap : ∀ p ∈ physicalParameterSet z₀ a, ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
    (hC : ∀ D : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1)),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp D -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2 → ‖D‖ ≤ C)
    {p : Euclidean 2 × Euclidean n × Euclidean n} (hp : p ∈ physicalParameterSet z₀ a)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) :
    (1 - angularWidth ηb r / 4) * ‖u.2‖ ≤ ‖adaptedTransportChart T Q p u‖ ∧
      ‖adaptedTransportChart T Q p u‖ ≤ C * ‖u.2‖ := by
  let A := supportedAnnularData T Q z₀ hηb hr p (hInv.injective p hp) (htrans p hp)
  refine ⟨A.norm_lower hu, ?_⟩
  let t := ‖ηb‖ / ‖u.2‖
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hηb) (norm_pos_iff.mpr hu.2.1)
  have hw : radialScale t u ∈ dataBox z₀ ηb (2 * r) :=
    prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
        (normalizedInput_mem_dataSet hηb hr hu)
  have hD := hC _ (hgap p hp _ hw)
  have hd := adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf hp
    (radialScale_mem_supportedCone hu ht)
  have he := adaptedTransportChart_eq_fderiv_radial T Q p (radialScale t u) hd
  have hb : ‖adaptedTransportChart T Q p (radialScale t u)‖ ≤ C * ‖t • u.2‖ := by
    rw [← he]
    apply ((fderiv ℝ (adaptedTransportChart T Q p) (radialScale t u)).le_opNorm _).trans
    have hn : ‖((0 : ℝ), (radialScale t u).2)‖ = ‖t • u.2‖ := by
      simp [radialScale, Prod.norm_def]
    rw [hn]
    exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)
  rw [adaptedTransportChart_radialScale, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht] at hb
  apply (mul_le_mul_iff_right₀ ht).mp
  calc
    t * ‖adaptedTransportChart T Q p u‖ ≤ C * (t * ‖u.2‖) := hb
    _ = t * (C * ‖u.2‖) := by ring

end JanetCartan.ContinuumRow.CanonicalConic
