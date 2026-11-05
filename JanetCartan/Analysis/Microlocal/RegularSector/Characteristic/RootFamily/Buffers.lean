module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.PrimitiveBounds.Compact

/-!
# Fixed coefficient and frequency buffers for one pencil root

The frozen simple root and the original selected adjugate entry produce common
positive minor and transport gaps on nested compact parameter buffers. These
choices precede every variable coefficient field. This supplies the geometric
root inputs to `app:ch_regular_base:lem:characteristic-kernel`; coefficient
seminorm estimates are separate from this finite-dimensional construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.RootFamily

open ActualCarriers

variable {n d : ℕ}

/-- The actual matrix on the jointly constructed coefficient/root graph
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def coefficientRootPencil (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (H : (Fin n → MetricTensor n) × Euclidean d → ℝ)
    (p : (Fin n → MetricTensor n) × Euclidean d) : MetricTensor n :=
  pencil p.1 (e.symm (H p, p.2))

/-- Fixed normalized buffers and positive original minor/transport gaps are
constructed from the frozen pencil. The same branch is smooth and homogeneous
on its whole conic chart, and its graph over the outer compact buffer has a
positive distance from the edge of the scalar band. The constants and every
domain precede `Q` (`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_buffered_coefficientRoot
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (A₀ : Fin n → MetricTensor n) (η₀ : Euclidean d) (τ₀ : ℝ)
    (r c : Fin n) (hξ : e.symm (τ₀, η₀) ≠ 0)
    (hp : determinant A₀ (e.symm (τ₀, η₀)) = 0)
    (ht : fderiv ℝ (determinant A₀) (e.symm (τ₀, η₀)) (e.symm (1, 0)) ≠ 0)
    (hm : (pencil A₀ (e.symm (τ₀, η₀))).adjugate r c ≠ 0) :
    ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
      (U : Set ((Fin n → MetricTensor n) × Euclidean d)) (V : Set ℝ)
      (H : (Fin n → MetricTensor n) × Euclidean d → ℝ),
      ∃ ε > (0 : ℝ), ∃ κ > 0, ∃ μ > 0, ∃ ν > 0, ∃ G > 0, ∃ δ > 0,
      ℓ η₀ = 1 ∧ IsOpen U ∧ IsOpen V ∧ H (A₀, η₀) = τ₀ ∧
      ContDiffOn ℝ ∞ H (CharacteristicRoot.conicDomain ℓ U) ∧
      closedBall (A₀, η₀) (3 * ε) ⊆ CharacteristicRoot.conicDomain ℓ U ∧
      (∀ p ∈ CharacteristicRoot.conicDomain ℓ U,
        p.2 ≠ 0 ∧ determinant p.1 (e.symm (H p, p.2)) = 0 ∧
        (p, H p) ∈ CharacteristicRoot.conicBand ℓ U V ∧
        κ ≤ |determinantNormalization (e.symm (H p, p.2)) *
          fderiv ℝ (determinant p.1) (e.symm (H p, p.2)) (e.symm (1, 0))|) ∧
      (∀ p ∈ CharacteristicRoot.conicDomain ℓ U, ∀ a : ℝ, 0 < a →
        (p.1, a • p.2) ∈ CharacteristicRoot.conicDomain ℓ U ∧
        H (p.1, a • p.2) = a * H p) ∧
      (∀ z ∈ CharacteristicRoot.conicBand ℓ U V,
        determinant z.1.1 (e.symm (z.2, z.1.2)) = 0 ↔ H z.1 = z.2) ∧
      (∀ p ∈ closedBall (A₀, η₀) (3 * ε),
        |H p| ≤ G ∧ μ ≤ |(coefficientRootPencil e H p).adjugate r c| ∧
        ν ≤ |minorTransportCoefficient (coefficientRootPencil e H p)
          (pencil p.1 (e.symm (1, 0))) r c|) ∧
      cthickening δ ((fun p ↦ (p, H p)) '' closedBall (A₀, η₀) (3 * ε)) ⊆
        CharacteristicRoot.conicBand ℓ U V := by
  obtain ⟨ℓ, U, V, κ, H, hℓ, hU, hV, hκ, hbaseD, hbase, hH,
    hroot, hscale, huniq, hbuffer⟩ :=
    exists_coefficientRoot_conic_patch e A₀ η₀ τ₀ hξ hp ht
  let p₀ := (A₀, η₀)
  let D := CharacteristicRoot.conicDomain ℓ U
  have hD : IsOpen D := CharacteristicRoot.isOpen_conicDomain ℓ hU
  have hHa : ContDiffAt ℝ ∞ H p₀ := hH.contDiffAt (hD.mem_nhds hbaseD)
  have hP : ContDiffAt ℝ ∞ (coefficientRootPencil e H) p₀ :=
    contDiff_pencil.contDiffAt.comp p₀ (contDiffAt_fst.prodMk
      (e.symm.contDiff.contDiffAt.comp p₀ (hHa.prodMk contDiffAt_snd)))
  have hA : ContDiff ℝ ∞
      (fun p : (Fin n → MetricTensor n) × Euclidean d ↦ pencil p.1 (e.symm (1, 0))) :=
    contDiff_pencil.comp (contDiff_fst.prodMk contDiff_const)
  let m : (Fin n → MetricTensor n) × Euclidean d → ℝ :=
    fun p ↦ (coefficientRootPencil e H p).adjugate r c
  let t : (Fin n → MetricTensor n) × Euclidean d → ℝ :=
    fun p ↦ minorTransportCoefficient (coefficientRootPencil e H p)
      (pencil p.1 (e.symm (1, 0))) r c
  have hmc : ContinuousAt m p₀ :=
    ((continuous_apply c).comp
      ((continuous_apply r).comp continuous_id.matrix_adjugate)).continuousAt.comp
        hP.continuousAt
  have htc : ContinuousAt t p₀ :=
    ((contDiff_minorTransportCoefficient_pair r c (m := ∞)).contDiffAt.comp p₀
      (hP.prodMk hA.contDiffAt)).continuousAt
  have hm₀ : m p₀ ≠ 0 := by simpa only [m, p₀, coefficientRootPencil, hbase] using hm
  have ht₀ : t p₀ ≠ 0 := by
    have ht' : fderiv ℝ Matrix.det (pencil A₀ (e.symm (τ₀, η₀)))
        (pencil A₀ (e.symm (1, 0))) ≠ 0 := by
      rwa [(hasFDerivAt_determinant _ _).fderiv] at ht
    simpa only [t, p₀, coefficientRootPencil, hbase] using
      minorTransportCoefficient_ne_zero_of_root hp hm ht'
  let μ := |m p₀| / 2
  let ν := |t p₀| / 2
  let G := |τ₀| + 1
  have hμ : 0 < μ := half_pos (abs_pos.mpr hm₀)
  have hν : 0 < ν := half_pos (abs_pos.mpr ht₀)
  have hG : 0 < G := by dsimp [G]; positivity
  have hμevent : ∀ᶠ p in 𝓝 p₀, μ < |m p| :=
    hmc.abs.tendsto.eventually (eventually_gt_nhds (half_lt_self (abs_pos.mpr hm₀)))
  have hνevent : ∀ᶠ p in 𝓝 p₀, ν < |t p| :=
    htc.abs.tendsto.eventually (eventually_gt_nhds (half_lt_self (abs_pos.mpr ht₀)))
  have hGevent : ∀ᶠ p in 𝓝 p₀, |H p| < G :=
    hHa.continuousAt.abs.tendsto.eventually (eventually_lt_nhds (by
      change |H (A₀, η₀)| < |τ₀| + 1
      rw [hbase]
      linarith))
  have hevent : ∀ᶠ p in 𝓝 p₀,
      p ∈ D ∧ |H p| < G ∧ μ < |m p| ∧ ν < |t p| := by
    filter_upwards [hD.mem_nhds hbaseD, hGevent, hμevent, hνevent]
      with p hp hG' hμ' hν'
    exact ⟨hp, hG', hμ', hν'⟩
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε := a / 4
  have hε : 0 < ε := by positivity
  have hclosed : ∀ p ∈ closedBall p₀ (3 * ε),
      p ∈ D ∧ |H p| < G ∧ μ < |m p| ∧ ν < |t p| := by
    intro p hp
    apply hball
    apply mem_ball.mpr
    have hd := mem_closedBall.mp hp
    dsimp [ε] at hd
    linarith
  have hsub : closedBall p₀ (3 * ε) ⊆ D := fun p hp ↦ (hclosed p hp).1
  obtain ⟨δ, hδ, hδbuffer⟩ := hbuffer _ (isCompact_closedBall p₀ (3 * ε)) hsub
  refine ⟨ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    hℓ, hU, hV, hbase, hH, hsub, hroot, hscale, huniq, ?_, hδbuffer⟩
  intro p hp
  have h := hclosed p hp
  exact ⟨h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

end JanetCartan.RegularSector.Characteristic.RootFamily
