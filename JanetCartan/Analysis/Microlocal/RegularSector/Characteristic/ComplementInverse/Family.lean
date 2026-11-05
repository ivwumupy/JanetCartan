module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition

/-!
# Quantitative construction on actual minor families

This assembles the complement inverse of
`paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, from the
original primitive matrices and minor/transport gaps. The same interval gives
both determinant gaps, smooth dependence, the original oblique inverse,
uniqueness, degree-minus-one homogeneity, and single-high finite-jet estimates.
The constants precede the family, its open neighborhood, and its jet order.

The arrays need only be smooth near the working closed ball. A smooth extension
is used solely to apply the primitive estimate; equality of germs transfers
every ambient derivative back to the original array. Pairing the primitive
arrays costs only their sum of seminorms. The graded bound has reserve loss zero.

Consumers: `W₁` and `Op(b₋₁ α)` in
`app:ch_regular_base:eq:complement-inverse` and
`app:ch_regular_base:eq:complement-symbol`. Selecting the physical sector,
composing with its two-time phase, and realizing the operators belong to the
regular-sector construction.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff Topology
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The original simple-root determinant gap produces the transport gap in the
primitive coefficient class (`app:ch_regular_base:lem:characteristic-kernel`).
This uses the same selected minor and the exact determinant derivative. -/
theorem minorCoefficientClass_mem_of_root_gap {H A : Matrix ι ι ℝ} {r c : ι}
    {M μ κ : ℝ} (hH : ‖H‖ ≤ M) (hA : ‖A‖ ≤ M) (hroot : H.det = 0)
    (hμ : 0 < μ) (hκ : 0 ≤ κ) (hm : μ ≤ |H.adjugate r c|)
    (ht : κ ≤ |fderiv ℝ Matrix.det H A|) :
    (H, A) ∈ minorCoefficientClass r c M μ (μ * κ) :=
  ⟨hH, hA, hroot, hm, NullTransport.transportCoefficient_gap hroot hμ hκ hm ht⟩

section Families
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- The complete quantitative complement construction for local smooth minor
families (`app:ch_regular_base:lem:characteristic-kernel`). All range, kernel,
normalization and completion-gap inputs of the primitive estimate are discharged
from the displayed original data. The identities, homogeneity and both kinds
of jet bounds concern the literal `minorComplementInverse` of the same pencil.

The constants are fixed before every family and all reserves and finite orders.
The graded estimate loses no reserve; `P` bounds only the primitive arrays.
There is no assumed inverse, inverse budget, or auxiliary determinant gap. -/
theorem exists_quantitative_minorComplementInverse_family
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) (r c : ι) (M : ℝ)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (Ω : Set E), IsOpen Ω → Metric.closedBall x ρ ⊆ Ω →
      ∀ (H A : E → Matrix ι ι ℝ) (e : E → ℝ),
        ContDiffOn ℝ ∞ H Ω → ContDiffOn ℝ ∞ A Ω → ContDiffOn ℝ ∞ e Ω →
        (∀ y ∈ Metric.closedBall x ρ, ‖H y‖ ≤ M ∧ ‖A y‖ ≤ M ∧
          (H y).det = 0 ∧ μ ≤ |(H y).adjugate r c| ∧
          ν ≤ |minorTransportCoefficient (H y) (A y) r c| ∧ |e y| ≤ ε) →
        let b := fun y ↦ minorComplementInverse (H y) (A y) r c (e y)
        (∀ y ∈ Metric.closedBall x ρ, ContDiffAt ℝ ∞ b y) ∧
        (∀ y ∈ Metric.closedBall x ρ,
          let k := minorRightNullvector (H y) r c
          let l := minorLeftNullvector (H y) (A y) r c
          δ ≤ |(pencilCompletion (H y) (A y) k l (e y)).det| ∧
          δ ≤ |(borderedPencil (H y) (A y) k l (e y)).det| ∧
          l ᵥ* (H y + e y • A y) = e y • (l ᵥ* A y) ∧
          (H y + e y • A y) * b y = complementProjection (A y) k l ∧
          (l ᵥ* A y) ᵥ* b y = 0 ∧
          (∀ B : Matrix ι ι ℝ,
            (H y + e y • A y) * B = complementProjection (A y) k l →
            (l ᵥ* A y) ᵥ* B = 0 → B = b y) ∧
          ∀ a : ℝ, a ≠ 0 →
            minorComplementInverse (a • H y) (A y) r c (a * e y) = a⁻¹ • b y) ∧
        (∀ j : ℕ, cNorm (Metric.closedBall x ρ) j b ≤
          C j * (1 + cNorm (Metric.closedBall x ρ) j H +
            cNorm (Metric.closedBall x ρ) j A + cNorm (Metric.closedBall x ρ) j e)) ∧
        (∀ (P : ℕ → ℝ) (R N : ℕ) (T : ℝ), 1 ≤ T →
          (∀ j ≤ N, cNorm (Metric.closedBall x ρ) j H +
            cNorm (Metric.closedBall x ρ) j A + cNorm (Metric.closedBall x ρ) j e ≤
              P j * T ^ (j - R)) →
          ∀ j ≤ N, cNorm (Metric.closedBall x ρ) j b ≤
            (C j * (1 + P j)) * T ^ (j - R)) := by
  obtain ⟨ε, hε, δ, hδ, C, hC, hgap, hdomain, hbound⟩ :=
    exists_minorComplementInverse_primitive_tame x hρ r c M hμ hν
  refine ⟨ε, hε, δ, hδ, C, hC, ?_⟩
  intro Ω hΩ hball H A e hH hA he hprimitive
  let U : E → (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ := fun y ↦ ((H y, A y), e y)
  have hU : ContDiffOn ℝ ∞ U Ω := (hH.prodMk hA).prodMk he
  have hmem (y) (hy : y ∈ Metric.closedBall x ρ) :
      (H y, A y) ∈ minorCoefficientClass r c M μ ν := by
    obtain ⟨hHy, hAy, hr, hm, ht, _⟩ := hprimitive y hy
    exact ⟨hHy, hAy, hr, hm, ht⟩
  have hUt : MapsTo U (Metric.closedBall x ρ)
      (minorCoefficientClass r c M μ ν ×ˢ Metric.closedBall (0 : ℝ) ε) := by
    intro y hy
    exact ⟨hmem y hy, by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      using (hprimitive y hy).2.2.2.2.2⟩
  have hsmooth (y) (hy : y ∈ Metric.closedBall x ρ) :
      ContDiffAt ℝ ∞ (fun y ↦ minorComplementInverse (H y) (A y) r c (e y)) y :=
    ((minorComplementDomain_regular r c).2.contDiffAt
      ((minorComplementDomain_regular r c (m := ∞)).1.mem_nhds (hdomain (hUt hy)))).comp y
        (hU.contDiffAt (hΩ.mem_nhds (hball hy)))
  have htame (j : ℕ) :
      cNorm (Metric.closedBall x ρ) j
        (fun y ↦ minorComplementInverse (H y) (A y) r c (e y)) ≤
          C j * (1 + cNorm (Metric.closedBall x ρ) j H +
            cNorm (Metric.closedBall x ρ) j A + cNorm (Metric.closedBall x ρ) j e) := by
    obtain ⟨V, hV, _, _, hVU⟩ :=
      ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall x hρ hΩ hball hU
    have hVt : MapsTo V (Metric.closedBall x ρ)
        (minorCoefficientClass r c M μ ν ×ˢ Metric.closedBall (0 : ℝ) ε) := by
      intro y hy
      rw [(hVU y hy).eq_of_nhds]
      exact hUt hy
    have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq hVU j
    have hcomp : cNorm (Metric.closedBall x ρ) j
        (fun y ↦ minorComplementInverse (V y).1.1 (V y).1.2 r c (V y).2) =
        cNorm (Metric.closedBall x ρ) j
          (fun y ↦ minorComplementInverse (H y) (A y) r c (e y)) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq _ j
      intro y hy
      exact (hVU y hy).fun_comp
        (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
          minorComplementInverse p.1.1 p.1.2 r c p.2)
    have hpaired : cNorm (Metric.closedBall x ρ) j U ≤
        cNorm (Metric.closedBall x ρ) j H + cNorm (Metric.closedBall x ρ) j A +
          cNorm (Metric.closedBall x ρ) j e := by
      apply (FullPhaseCharts.InverseEstimates.cNorm_prodMk_le_on _
        (isCompact_closedBall x ρ) j
        (fun y hy ↦ ((hH.prodMk hA).contDiffAt (hΩ.mem_nhds (hball hy))).of_le (by simp))
        (fun y hy ↦ (he.contDiffAt (hΩ.mem_nhds (hball hy))).of_le (by simp))).trans
      apply add_le_add _ le_rfl
      exact FullPhaseCharts.InverseEstimates.cNorm_prodMk_le_on _
        (isCompact_closedBall x ρ) j
        (fun y hy ↦ (hH.contDiffAt (hΩ.mem_nhds (hball hy))).of_le (by simp))
        (fun y hy ↦ (hA.contDiffAt (hΩ.mem_nhds (hball hy))).of_le (by simp))
    calc
      _ ≤ C j * (1 + cNorm (Metric.closedBall x ρ) j U) := by
        simpa only [hnorm, hcomp] using hbound j V hV hVt
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (hC j).le
  refine ⟨hsmooth, ?_, htame, ?_⟩
  · intro y hy
    obtain ⟨_, _, hr, hm, ht, he'⟩ := hprimitive y hy
    have hm' := abs_pos.mp (hμ.trans_le hm)
    have ht' := abs_pos.mp (hν.trans_le ht)
    obtain ⟨hk, hl, hn, _⟩ := minor_normalization hr hm' ht'
    obtain ⟨hc, hb⟩ := hgap (H y, A y) (hmem y hy) (e y) he'
    have hd := abs_pos.mp (hδ.trans_le hc)
    exact ⟨hc, hb, left_pencil hl _, complementInverse_identity hl hn hd,
      complementInverse_constraint hl hn hd, fun _ hB hq ↦ complementInverse_unique hd hB hq,
      fun _ ha ↦ minorComplementInverse_smul hr hm' ht' hd ha⟩
  · intro P R N T hT hprofile j hj
    have hpow : 1 ≤ T ^ (j - R) := one_le_pow₀ hT
    calc
      _ ≤ C j * (1 + cNorm (Metric.closedBall x ρ) j H +
          cNorm (Metric.closedBall x ρ) j A + cNorm (Metric.closedBall x ρ) j e) := htame j
      _ ≤ C j * ((1 + P j) * T ^ (j - R)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hprofile j hj]) (hC j).le
      _ = _ := by ring

end Families
end JanetCartan.RegularSector.Characteristic
