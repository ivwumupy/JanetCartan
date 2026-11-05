module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierRank
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.MinorBounds.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.AdaptedReduction

/-!
# Actual fixed-minor and adapted root gaps

The finite refinement here is chosen from the frozen patch before the current
frame. Primitive `C⁶` frame closeness preserves its selected entries and the
determinant derivative in the retained section normal for the *same* constructed
carrier. These are concrete inputs to the scalar transport construction in
`app:ch_waves:thm:leading`; no current minor or root bound is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Matrix Matrix.Norms.Frobenius Topology

namespace JanetCartan.NullTransport
open ActualCarriers FrozenMenu CurrentFullPhase

/-- Value comparison on the whole doubled open patch, using the same full
chart and its retained target. This leaves a parameter buffer around the
closed working cube for transport (`app:ch_waves:thm:leading`). -/
theorem exists_buffered_carrier_value_threshold {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius,
      ∀ z ∈ parameterInterior (2 * P.radius),
        ‖T.carrierGradient Q x z - P.toFun z‖ < ε := by
  obtain ⟨δ, hδ, hc⟩ := T.family.exists_momentum_comparison_threshold hε
  refine ⟨δ, hδ, fun Q hclose x hx z hz ↦ ?_⟩
  have ht := T.reference.target_contains x hx z hz
  have hg : T.carrierGradient Q x z =
      (T.currentChart Q).chartMomentum (x, (0, T.reference.spatialPatch z)) :=
    (hasGradientAt_carrierPhase (T.currentChart Q) T.reference.spatialPatch ht).gradient
  have hf : T.reference.chart.chartMomentum (x, (0, T.reference.spatialPatch z)) =
      P.toFun z :=
    (chartMomentum_eq_of_phase_linear T.reference.chart
      T.reference.covector T.reference.phase_linear ht).trans (T.reference.patch_covector z hz)
  rw [hg, ← hf]
  exact (hc Q hclose _ (ball_subset_closedBall ht)).1

/-- On the compact frozen parameter cube, small frame and covector errors
control the literal adjugate and the determinant differential in the retained
normal. This supplies the two perturbation errors used by
`exists_actual_null_gaps` (`app:ch_waves:thm:leading`). -/
theorem exists_patch_null_data_radius {n : ℕ} {P : Patch n} {c C : ℝ}
    (hP : P.IsValid c C) (ν : Euclidean n) {η : ℝ} (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ (Q : Fin n → MetricTensor n) (ξ : Euclidean n)
      (z : Euclidean 3), z ∈ parameterCube (3 * P.radius / 2) →
      ‖Q - cubeStress n‖ < δ → ‖ξ - P.toFun z‖ < δ →
      ‖(pencil Q ξ).adjugate - (cubePencil (P.toFun z)).adjugate‖ < η ∧
      |fderiv ℝ (determinant Q) ξ ν - fderiv ℝ cubeDeterminant (P.toFun z) ν| < η := by
  let J : (Fin n → MetricTensor n) × Euclidean n → MetricTensor n × ℝ :=
    fun p ↦ ((pencil p.1 p.2).adjugate, fderiv ℝ (determinant p.1) p.2 ν)
  have hJ : Continuous J := (contDiff_adjugate_pencil.continuous).prodMk
    ((contDiff_fderiv_determinant.continuous).clm_apply continuous_const)
  let f : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 → ℝ :=
    fun p ↦ ‖J (cubeStress n + p.1.1, P.toFun p.2 + p.1.2) -
      J (cubeStress n, P.toFun p.2)‖
  have hev : ∀ᶠ e in 𝓝 (0 : (Fin n → MetricTensor n) × Euclidean n),
      ∀ z ∈ parameterCube (3 * P.radius / 2), f (e, z) < η := by
    apply (isCompact_parameterCube (3 * P.radius / 2)).eventually_forall_of_forall_eventually
    intro z hz
    have hp : ContinuousAt P.toFun z := (hP.2.2.2.1.contDiffAt
      ((isOpen_parameterInterior _).mem_nhds
        (fun i ↦ (hz i).trans_lt (by linarith [hP.1])))).continuousAt
    have hq : ContinuousAt
        (fun p : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 ↦
          (cubeStress n + p.1.1, P.toFun p.2 + p.1.2)) (0, z) :=
      (continuousAt_const.add continuousAt_fst.fst).prodMk
        ((hp.comp continuousAt_snd).add continuousAt_fst.snd)
    have hq₀ : ContinuousAt
        (fun p : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 ↦
          (cubeStress n, P.toFun p.2)) (0, z) :=
      continuousAt_const.prodMk (hp.comp continuousAt_snd)
    have hf : ContinuousAt f (0, z) :=
      ((hJ.continuousAt.comp hq).sub (hJ.continuousAt.comp hq₀)).norm
    apply hf.eventually (gt_mem_nhds _)
    simpa [f] using hη
  obtain ⟨δ, hδ, hclose⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun Q ξ z hz hQ hξ ↦ ?_⟩
  have he : dist (Q - cubeStress n, ξ - P.toFun z) 0 < δ := by
    simpa only [dist_eq_norm, sub_zero, Prod.norm_def] using max_lt hQ hξ
  have hdet : determinant (cubeStress n) = cubeDeterminant :=
    funext (determinant_cubeStress (n := n))
  simpa only [f, J, add_sub_cancel, add_sub_cancel_left, Prod.fst_sub, Prod.snd_sub,
    Prod.norm_def, max_lt_iff, Real.norm_eq_abs, pencil_cubeStress,
    hdet] using hclose he z hz

/-- A finite open refinement of the frozen patch, with one fixed adjugate
entry on each member, chosen *before* the current frame. The positive minor
and adapted root bounds hold for the literal `T.carrierGradient` and follow
from primitive `C⁶` frame closeness. This closes both gap inputs of the scalar
transport construction (`app:ch_waves:thm:leading`). -/
theorem exists_actual_null_gaps {n : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ μ κ : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        ∀ Q, cNorm K 6 (Q.1 - fun _ ↦ cubeStress n) < δ →
          ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, x ∈ K →
          ∀ z ∈ parameterCube (3 * P.radius / 2),
            κ ≤ fderiv ℝ (determinant (Q.1 x)) (T.carrierGradient Q x z)
              T.data.adapted.normal ∧
            ∀ r c, z ∈ V r c →
              μ ≤ |(pencil (Q.1 x) (T.carrierGradient Q x z)).adjugate r c| := by
  classical
  obtain ⟨d₀, a, hd₀, ha, hgap⟩ := exists_patch_adjugate_perturbation_radius hn hP
  have hng : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let μ := a / (4 * n)
  let κ := T.data.localReference.determinantGap / 2
  have hμ : 0 < μ := div_pos ha (by positivity)
  have hκ : 0 < κ := half_pos T.data.localReference.determinantGap_pos
  let V : Fin n → Fin n → Set (Euclidean 3) := fun r c ↦
    {z ∈ parameterInterior (2 * P.radius) |
      2 * μ < |(cubePencil (P.toFun z)).adjugate r c|}
  have hV (r c : Fin n) : IsOpen (V r c) := by
    have hs : ContinuousOn (fun z ↦ |(cubePencil (P.toFun z)).adjugate r c|)
        (parameterInterior (2 * P.radius)) := by
      have hm := contDiff_adjugate_pencil.continuous.comp_continuousOn
        ((continuousOn_const (c := cubeStress n)).prodMk hP.2.2.2.1.continuousOn)
      have he := ((Matrix.entryLinearMap ℝ ℝ r c).toContinuousLinearMap.continuous.comp_continuousOn hm).abs
      simpa only [Function.comp_def, pencil_cubeStress, LinearMap.coe_toContinuousLinearMap',
        Matrix.entryLinearMap_apply] using he
    exact hs.isOpen_inter_preimage (isOpen_parameterInterior _) isOpen_Ioi
  have hcover : parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c := by
    intro z hz
    have hag : a ≤ ‖(cubePencil (P.toFun z)).adjugate‖ := by
      simpa only [pencil_cubeStress] using hgap (cubeStress n) (P.toFun z) z hz
        (by simpa using hd₀) (by simpa using hd₀)
    have hex : ∃ r c : Fin n, a / n ≤ |(cubePencil (P.toFun z)).adjugate r c| := by
      cases n with
      | zero => omega
      | succ m => simpa only [Nat.cast_add, Nat.cast_one] using
          exists_large_cofactor (cubePencil (P.toFun z)) hag
    obtain ⟨r, c, hrc⟩ := hex
    refine mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨c,
      parameterCube_subset_doubledInterior hP.1 hz, ?_⟩⟩
    have hhalf : 2 * μ = (a / n) / 2 := by dsimp [μ]; ring
    rw [hhalf]
    exact (half_lt_self (div_pos ha hng)).trans_le hrc
  obtain ⟨d, hd, hdata⟩ := exists_patch_null_data_radius hP T.data.adapted.normal
    (lt_min hμ hκ)
  obtain ⟨e, he, hcomp⟩ := exists_buffered_carrier_value_threshold T hd
  refine ⟨min d e, μ, κ, lt_min hd he, hμ, hκ, V, hV, hcover, ?_⟩
  intro Q hclose x hx hxK z hz
  have hs : ∀ y ∈ K, ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress n) y := by
    intro y hy
    exact ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hy))).sub contDiffAt_const).of_le (by simp)
  have hQx : ‖Q.1 x - cubeStress n‖ < d := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hxK (Nat.zero_le 6)
    have hv : ‖Q.1 x - cubeStress n‖ ≤ cNorm K 6 (Q.1 - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hh
    exact hv.trans_lt (hclose.trans_le (min_le_left _ _))
  have hlocal := (cNorm_mono_set_of_contDiffAt hball hK hs).trans_lt
    (hclose.trans_le (min_le_right _ _))
  have hz' : z ∈ parameterInterior (2 * P.radius) :=
    fun i ↦ (hz i).trans_lt (by linarith [hP.1])
  have hξ := hcomp Q hlocal x hx z hz'
  obtain ⟨hadj, hroot⟩ := hdata (Q.1 x) (T.carrierGradient Q x z) z hz hQx hξ
  refine ⟨?_, fun r c hzV ↦ ?_⟩
  · have hz₂ : z ∈ parameterCube (2 * P.radius) :=
      fun i ↦ (hz' i).le
    have hf := T.data.localReference.determinant_gap _ (T.data.buffered_mem z hz₂)
    have hh := (abs_lt.mp (hroot.trans_le (min_le_right _ _))).1
    dsimp [κ] at *
    linarith
  · have he := (abs_entry_le_frobenius
      ((pencil (Q.1 x) (T.carrierGradient Q x z)).adjugate -
        (cubePencil (P.toFun z)).adjugate) r c).trans_lt
          (hadj.trans_le (min_le_left _ _))
    change |(pencil (Q.1 x) (T.carrierGradient Q x z)).adjugate r c -
      (cubePencil (P.toFun z)).adjugate r c| < μ at he
    have hl := abs_sub_abs_le_abs_sub
      ((cubePencil (P.toFun z)).adjugate r c)
      ((pencil (Q.1 x) (T.carrierGradient Q x z)).adjugate r c)
    rw [abs_sub_comm] at hl
    have hh := hzV.2
    linarith

/-- Instantiate the adjugate identities and the adapted denominator bounds
on the actual carrier, using the gaps just constructed from primitive frame
closeness. All indices and constants precede the current frame
(`app:ch_waves:thm:leading`). -/
theorem exists_actual_nullvectors {n : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ μ κ : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        ∀ Q, cNorm K 6 (Q.1 - fun _ ↦ cubeStress n) < δ →
          (∀ x ∈ U, ∀ i, (Q.1 x i).IsSymm) →
          ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, x ∈ K →
          ∀ z ∈ parameterCube (3 * P.radius / 2), ∀ r c, z ∈ V r c →
            let M := reducedSymbol (Q.1 x) (T.carrierGradient Q x z)
            let d := adaptedTimeCoefficient (Q.1 x) (T.carrierGradient Q x z)
              r c T.data.adapted.normal
            M.det = 0 ∧ μ ≤ |M.adjugate r c| ∧
              rightNullvector M c ≠ 0 ∧ leftNullvector M r ≠ 0 ∧
              M *ᵥ rightNullvector M c = 0 ∧ leftNullvector M r ᵥ* M = 0 ∧
              μ * κ ≤ |d| ∧ d ≠ 0 ∧ |d⁻¹| ≤ (μ * κ)⁻¹ := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hgap⟩ :=
    exists_actual_null_gaps hn hP T hK hKU hball
  refine ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, ?_⟩
  intro Q hclose hsymm x hx hxK z hz r c hzV
  obtain ⟨hroot, hminor⟩ := hgap Q hclose x hx hxK z hz
  have hm := hminor r c hzV
  have hne := abs_pos.mp (hμ.trans_le hm)
  have hchar := T.carrier_characteristic Q hx
    (fun i ↦ (hz i).trans_lt (by linarith [hP.1]))
  refine ⟨hchar, hm, rightNullvector_ne_zero hne, leftNullvector_ne_zero hne,
    mulVec_rightNullvector hchar c, leftNullvector_vecMul hchar r, ?_⟩
  exact adaptedTimeCoefficient_bounds _ (hsymm x (hKU hxK)) _ hchar _ hμ hκ hm hroot

end JanetCartan.NullTransport
