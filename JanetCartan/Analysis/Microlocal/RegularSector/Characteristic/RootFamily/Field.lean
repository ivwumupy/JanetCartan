module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Buffers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilNullvectors

/-!
# The same root branch for varying physical coefficients

The physical domain and pointed frequency cone are fixed before the smooth
field `Q`. The field root is the composition of the single finite-dimensional
branch with `Q`, including at every positive radius. The original selected
adjugate entry and transport denominator are bounded on the normalized graph;
their distinct radial degrees are retained explicitly.

Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`. The consumers are the root input of
the two-time flow and the minor input of the amplitude construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.RootFamily

open ActualCarriers

variable {n d : ℕ}

/-- The fixed physical/conic domain of the family
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def fieldDomain (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Ω : Set (Euclidean n)) (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε : ℝ) :
    Set (RootState (Euclidean d)) :=
  {w | 0 < ℓ w.2.2 ∧ e.symm (w.1, w.2.1) ∈ Ω ∧
    (ℓ w.2.2)⁻¹ • w.2.2 ∈ ball η₀ ε}

/-- Substitution of the original field into the single coefficient branch
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def fieldRoot (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n)
    (H : (Fin n → MetricTensor n) × Euclidean d → ℝ) (w : RootState (Euclidean d)) : ℝ :=
  H (Q (e.symm (w.1, w.2.1)), w.2.2)

/-- The normalized frequency graph is evaluated using that same branch
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def normalizedFieldParameter (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (ℓ : Euclidean d →L[ℝ] ℝ)
    (w : RootState (Euclidean d)) : (Fin n → MetricTensor n) × Euclidean d :=
  (Q (e.symm (w.1, w.2.1)), (ℓ w.2.2)⁻¹ • w.2.2)

/-- Openness of the domain fixed before the coefficient field
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem isOpen_fieldDomain (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε : ℝ) :
    IsOpen (fieldDomain e Ω ℓ η₀ ε) := by
  let R : RootState (Euclidean d) → (ℝ × Euclidean d) × Euclidean d :=
    fun w ↦ ((w.1, w.2.1), w.2.2)
  exact (CharacteristicRoot.isOpen_conicDomain ℓ
    ((hΩ.preimage e.symm.continuous).prod isOpen_ball)).preimage
      ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd)

/-- The fixed domain contains every positive radius on each of its rays
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem fieldDomain_smul (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Ω : Set (Euclidean n)) (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε : ℝ)
    {w : RootState (Euclidean d)} (hw : w ∈ fieldDomain e Ω ℓ η₀ ε)
    {a : ℝ} (ha : 0 < a) :
    (w.1, (w.2.1, a • w.2.2)) ∈ fieldDomain e Ω ℓ η₀ ε := by
  have he := CharacteristicRoot.normalize_smul ℓ
    (((w.1, w.2.1), w.2.2) : (ℝ × Euclidean d) × Euclidean d) ha.ne'
  refine ⟨by simpa only [map_smul, smul_eq_mul] using mul_pos ha hw.1, hw.2.1, ?_⟩
  change (ℓ (a • w.2.2))⁻¹ • (a • w.2.2) ∈ ball η₀ ε
  rw [show (ℓ (a • w.2.2))⁻¹ • (a • w.2.2) = (ℓ w.2.2)⁻¹ • w.2.2 from
    congrArg Prod.snd he]
  exact hw.2.2

private theorem normalizedFieldParameter_mem
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {ℓ : Euclidean d →L[ℝ] ℝ}
    {A₀ : Fin n → MetricTensor n} {η₀ : Euclidean d} {ε : ℝ} (hε : 0 < ε)
    {Q : Euclidean n → Fin n → MetricTensor n}
    (hQrange : MapsTo Q Ω (closedBall A₀ ε))
    {w : RootState (Euclidean d)} (hw : w ∈ fieldDomain e Ω ℓ η₀ ε) :
    normalizedFieldParameter e Q ℓ w ∈ closedBall (A₀, η₀) (3 * ε) := by
  rw [← closedBall_prod_same]
  exact ⟨closedBall_subset_closedBall (by linarith) (hQrange hw.2.1),
    closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hw.2.2)⟩

private theorem fieldParameter_mem
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {ℓ : Euclidean d →L[ℝ] ℝ}
    {U : Set ((Fin n → MetricTensor n) × Euclidean d)}
    {A₀ : Fin n → MetricTensor n} {η₀ : Euclidean d} {ε : ℝ} (hε : 0 < ε)
    (hsub : closedBall (A₀, η₀) (3 * ε) ⊆ CharacteristicRoot.conicDomain ℓ U)
    {Q : Euclidean n → Fin n → MetricTensor n}
    (hQrange : MapsTo Q Ω (closedBall A₀ ε))
    {w : RootState (Euclidean d)} (hw : w ∈ fieldDomain e Ω ℓ η₀ ε) :
    (Q (e.symm (w.1, w.2.1)), w.2.2) ∈ CharacteristicRoot.conicDomain ℓ U := by
  have hn := hsub (normalizedFieldParameter_mem e hε hQrange hw)
  simpa only [normalizedFieldParameter, smul_inv_smul₀ hw.1.ne'] using
    CharacteristicRoot.mem_conicDomain_smul ℓ U hn hw.1

/-- The transport denominator has twice the adjugate degree, while its time
coefficient stays fixed (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem minorTransportCoefficient_radial (P A : MetricTensor n) (r c : Fin n) (a : ℝ) :
    minorTransportCoefficient (a • P) A r c =
      a ^ (2 * (n - 1)) * minorTransportCoefficient P A r c := by
  have hr : NullTransport.rightNullvector (a • P) c =
      a ^ (n - 1) • NullTransport.rightNullvector P c := by
    ext i
    simp [NullTransport.rightNullvector, adjugate_smul]
  have hl : NullTransport.leftNullvector (a • P) r =
      a ^ (n - 1) • NullTransport.leftNullvector P r := by
    ext i
    simp [NullTransport.leftNullvector, adjugate_smul]
  simp only [minorTransportCoefficient, hr, hl, mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [two_mul, pow_add]
  ring

/-- Construct the actual roots of every nearby smooth field on a common
physical/conic domain. The original minor is retained, normalized gaps are
positive constants, and actual radial gaps have their exact degrees. The
same `H` supplies the root, range, band and homogeneous extension. No root,
root derivative, reciprocal or transport solution is supplied as an input
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_uniform_fieldRoot
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
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
      cthickening δ ((fun p ↦ (p, H p)) '' closedBall (A₀, η₀) (3 * ε)) ⊆
        CharacteristicRoot.conicBand ℓ U V ∧
      IsOpen (fieldDomain e Ω ℓ η₀ ε) ∧
      (∀ x ∈ Ω, ((e x).1, ((e x).2, η₀)) ∈ fieldDomain e Ω ℓ η₀ ε) ∧
      ∀ Q : Euclidean n → Fin n → MetricTensor n,
        ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
        let h := fieldRoot e Q H
        let D := fieldDomain e Ω ℓ η₀ ε
        ContDiffOn ℝ ∞ h D ∧
        (∀ w ∈ D, ∀ a : ℝ, 0 < a → h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
        ∀ w ∈ D,
          let p := (Q (e.symm (w.1, w.2.1)), w.2.2)
          let pNorm := normalizedFieldParameter e Q ℓ w
          let PNorm := coefficientRootPencil e H pNorm
          w.2.2 ≠ 0 ∧ (rootPencil e Q h w).det = 0 ∧
          (p, h w) ∈ CharacteristicRoot.conicBand ℓ U V ∧
          (∀ τ, (p, τ) ∈ CharacteristicRoot.conicBand ℓ U V →
            (determinant p.1 (e.symm (τ, p.2)) = 0 ↔ h w = τ)) ∧
          κ ≤ |determinantNormalization (e.symm (h w, w.2.2)) *
            fderiv ℝ (determinant p.1) (e.symm (h w, w.2.2)) (e.symm (1, 0))| ∧
          h w = ℓ w.2.2 * H pNorm ∧ |h w| ≤ ℓ w.2.2 * G ∧
          rootPencil e Q h w = ℓ w.2.2 • PNorm ∧
          μ ≤ |PNorm.adjugate r c| ∧
          ν ≤ |minorTransportCoefficient PNorm (rootTimeCoefficient e Q w) r c| ∧
          (ℓ w.2.2) ^ (n - 1) * μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
          (ℓ w.2.2) ^ (2 * (n - 1)) * ν ≤
            |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c| := by
  obtain ⟨ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    hℓ, hU, hV, hbase, hH, hsub, hroot, hscale, huniq, hbound, hbuffer⟩ :=
    exists_buffered_coefficientRoot e A₀ η₀ τ₀ r c hξ hp ht hm
  refine ⟨ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    hℓ, hU, hV, hbase, hH, hsub, hbuffer, isOpen_fieldDomain e hΩ ℓ η₀ ε, ?_, ?_⟩
  · intro x hx
    exact ⟨by simpa only [hℓ] using zero_lt_one,
      by simpa only [Prod.eta, e.symm_apply_apply] using hx,
      by simpa only [hℓ, inv_one, one_smul] using mem_ball_self hε⟩
  intro Q hQ hQrange
  have hmap := fun w hw ↦ fieldParameter_mem e hε hsub hQrange (w := w) hw
  refine ⟨?_, ?_, ?_⟩
  · exact hH.comp
      ((hQ.comp (e.symm.contDiff.comp_contDiffOn
        (contDiffOn_fst.prodMk contDiffOn_snd.fst)) (fun _ hw ↦ hw.2.1)).prodMk
          contDiffOn_snd.snd) hmap
  · intro w hw a ha
    exact (hscale _ (hmap w hw) a ha).2
  · intro w hw
    let pNorm := normalizedFieldParameter e Q ℓ w
    have hnormmem := normalizedFieldParameter_mem e hε hQrange hw
    have hnD := hsub hnormmem
    have hhscale : fieldRoot e Q H w = ℓ w.2.2 * H pNorm := by
      simpa only [pNorm, normalizedFieldParameter, smul_inv_smul₀ hw.1.ne', fieldRoot]
        using (hscale pNorm hnD (ℓ w.2.2) hw.1).2
    have hPscale : rootPencil e Q (fieldRoot e Q H) w =
        ℓ w.2.2 • coefficientRootPencil e H pNorm := by
      have he : (fieldRoot e Q H w, w.2.2) =
          ℓ w.2.2 • (H pNorm, pNorm.2) := by
        exact Prod.ext hhscale (smul_inv_smul₀ hw.1.ne' w.2.2).symm
      simp only [rootPencil, he, map_smul, coefficientRootPencil]
      exact (pencilContinuousLinearMap _).map_smul _ _
    have hb := hbound pNorm hnormmem
    obtain ⟨hη, hdet, hband, hgap⟩ := hroot _ (hmap w hw)
    refine ⟨hη, hdet, hband,
      fun τ hτ ↦ huniq ((Q (e.symm (w.1, w.2.1)), w.2.2), τ) hτ, hgap, hhscale, ?_,
      hPscale, hb.2.1, hb.2.2, ?_, ?_⟩
    · rw [hhscale, abs_mul, abs_of_pos hw.1]
      exact mul_le_mul_of_nonneg_left hb.1 hw.1.le
    · rw [hPscale, adjugate_smul]
      simp only [Fintype.card_fin, Matrix.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (pow_nonneg hw.1.le _)]
      exact mul_le_mul_of_nonneg_left hb.2.1 (pow_nonneg hw.1.le _)
    · rw [hPscale, minorTransportCoefficient_radial, abs_mul,
        abs_of_nonneg (pow_nonneg hw.1.le _)]
      exact mul_le_mul_of_nonneg_left hb.2.2 (pow_nonneg hw.1.le _)

end JanetCartan.RegularSector.Characteristic.RootFamily
