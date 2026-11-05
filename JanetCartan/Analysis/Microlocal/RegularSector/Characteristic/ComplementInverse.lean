module
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.NormalizedMinor
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Bordered
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Family
/-!
# Direct construction of the characteristic complement inverse

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, construct
an actual smooth inverse from `ker(lᵀ A)` to `ker lᵀ` for the original pencil
`H + e A`. Multiplication gives the paper's oblique projection
`I - (A k) lᵀ`, and the range constraint proves uniqueness.

The rank-one completion, the literal bordered matrix, their common interval
and determinant gaps, and degree-minus-one homogeneity are proved in the
leaf modules. The fixed-minor constructor discharges all nullvector inputs
using the characteristic equation, selected adjugate entry, and original
transport denominator. The pointwise specialization uses the original
simple-root determinant derivative to produce that denominator.

Consumers: `W₁` and `Op(b₋₁ α)` in
`app:ch_regular_base:eq:complement-inverse` and
`app:ch_regular_base:eq:complement-symbol`.
`exists_quantitative_minorComplementInverse_family` combines these identities
with local smoothness, single-high Frobenius jet bounds and graded bounds with
reserve loss zero. Only the original matrix budgets and minor/transport gaps
are inputs, and all constants precede the family and finite orders. The parent
regular-sector construction retains its physical symbols, phase substitution,
cutoffs, operator realization and complete residual.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Construct a positive interval and a smooth, unique complement inverse from
exactly the original kernel and normalization data
(`app:ch_regular_base:eq:complement-inverse`). The completion determinant gap
is a conclusion, and both identities concern the same original pencil. -/
theorem exists_smooth_complementInverse (H A : Matrix ι ι ℝ) (k l : ι → ℝ)
    (hk : H *ᵥ k = 0) (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1)
    (hker : ∀ v, H *ᵥ v = 0 → ∃ a : ℝ, v = a • k) :
    ∃ ε > 0, ∃ δ > 0,
      ContDiffOn ℝ ∞ (complementInverse H A k l) (Metric.ball 0 ε) ∧
      ∀ e : ℝ, |e| < ε →
        δ ≤ |(pencilCompletion H A k l e).det| ∧
        pencilCompletion H A k l e *ᵥ k = A *ᵥ k ∧
        (H + e • A) * complementInverse H A k l e = complementProjection A k l ∧
        (l ᵥ* A) ᵥ* complementInverse H A k l e = 0 ∧
        ∀ b : Matrix ι ι ℝ,
          (H + e • A) * b = complementProjection A k l →
          (l ᵥ* A) ᵥ* b = 0 → b = complementInverse H A k l e := by
  obtain ⟨ε, hε, δ, hδ, hgap⟩ := exists_uniform_completion_gap
    (fun _ : Unit ↦ H) (fun _ : Unit ↦ A) (fun _ : Unit ↦ k) (fun _ : Unit ↦ l)
    continuous_const continuous_const continuous_const continuous_const
    (K := {()}) isCompact_singleton (fun _ _ ↦ hl) (fun _ _ ↦ hn) (fun _ _ ↦ hker)
  have hd (e : ℝ) (he : |e| ≤ ε) : (pencilCompletion H A k l e).det ≠ 0 :=
    abs_pos.mp (hδ.trans_le (hgap () rfl e he))
  refine ⟨ε, hε, δ, hδ, ?_, ?_⟩
  · apply contDiffOn_complementInverse
      (H := fun _ : ℝ ↦ H) (A := fun _ : ℝ ↦ A)
      (k := fun _ : ℝ ↦ k) (l := fun _ : ℝ ↦ l) (e := id)
      (fun _ _ ↦ contDiffOn_const) (fun _ _ ↦ contDiffOn_const)
      contDiffOn_const contDiffOn_const contDiffOn_id
    intro e he
    exact hd e (by simpa [Metric.mem_ball, Real.dist_eq] using (Metric.mem_ball.mp he).le)
  · intro e he
    exact ⟨hgap () rfl e he.le, pencilCompletion_mulVec hk hn e,
      complementInverse_identity hl hn (hd e he.le), complementInverse_constraint hl hn (hd e he.le),
      fun _ hb hq ↦ complementInverse_unique (hd e he.le) hb hq⟩

/-- The original characteristic matrix, fixed minor and simple-root condition
construct the smooth, unique complement inverse. All kernel and normalization
inputs are discharged (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_smooth_minorComplementInverse (H A : Matrix ι ι ℝ) (r c : ι)
    (hH : H.det = 0) (hm : H.adjugate r c ≠ 0)
    (ht : fderiv ℝ Matrix.det H A ≠ 0) :
    ∃ ε > 0, ContDiffOn ℝ ∞ (minorComplementInverse H A r c) (Metric.ball 0 ε) ∧
      ∀ e : ℝ, |e| < ε →
        (H + e • A) * minorComplementInverse H A r c e =
          complementProjection A (minorRightNullvector H r c) (minorLeftNullvector H A r c) ∧
        (minorLeftNullvector H A r c ᵥ* A) ᵥ* minorComplementInverse H A r c e = 0 ∧
        ∀ b : Matrix ι ι ℝ,
          (H + e • A) * b =
            complementProjection A (minorRightNullvector H r c) (minorLeftNullvector H A r c) →
          (minorLeftNullvector H A r c ᵥ* A) ᵥ* b = 0 → b = minorComplementInverse H A r c e := by
  obtain ⟨hk, hl, hn, hker⟩ := minor_normalization hH hm
    (minorTransportCoefficient_ne_zero_of_root hH hm ht)
  obtain ⟨ε, hε, _, _, hsmooth, hspec⟩ := exists_smooth_complementInverse H A
    (minorRightNullvector H r c) (minorLeftNullvector H A r c) hk hl hn hker
  exact ⟨ε, hε, hsmooth, fun e he ↦ (hspec e he).2.2⟩

section Families
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A compact smooth family on the original minor patch has one positive
spectral interval, a positive completion determinant gap, and the actual jointly
smooth complement inverse with its exact identities and uniqueness
(`app:ch_regular_base:eq:complement-inverse`,
`app:ch_regular_base:eq:complement-symbol`). The input gaps are solely the
original minor and transport denominator gaps. -/
theorem exists_smooth_minorComplementInverse_family (H A : E → Matrix ι ι ℝ)
    (hH : Continuous H) (hA : Continuous A) {K : Set E} (hK : IsCompact K)
    (hHs : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ H x i j) K)
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ A x i j) K)
    (r c : ι) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hroot : ∀ x ∈ K, (H x).det = 0)
    (hminor : ∀ x ∈ K, μ ≤ |(H x).adjugate r c|)
    (htransport : ∀ x ∈ K, ν ≤ |minorTransportCoefficient (H x) (A x) r c|) :
    ∃ ε > 0, ∃ δ > 0,
      ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ minorComplementInverse (H p.1) (A p.1) r c p.2)
        (K ×ˢ Metric.ball 0 ε) ∧
      ∀ x ∈ K, ∀ e : ℝ, |e| < ε →
        δ ≤ |(pencilCompletion (H x) (A x) (minorRightNullvector (H x) r c)
          (minorLeftNullvector (H x) (A x) r c) e).det| ∧
        (H x + e • A x) * minorComplementInverse (H x) (A x) r c e =
          complementProjection (A x) (minorRightNullvector (H x) r c)
            (minorLeftNullvector (H x) (A x) r c) ∧
        (minorLeftNullvector (H x) (A x) r c ᵥ* A x) ᵥ*
          minorComplementInverse (H x) (A x) r c e = 0 ∧
        ∀ b : Matrix ι ι ℝ,
          (H x + e • A x) * b = complementProjection (A x)
            (minorRightNullvector (H x) r c) (minorLeftNullvector (H x) (A x) r c) →
          (minorLeftNullvector (H x) (A x) r c ᵥ* A x) ᵥ* b = 0 →
          b = minorComplementInverse (H x) (A x) r c e := by
  obtain ⟨ε, hε, δ, hδ, hgap⟩ := exists_uniform_minor_completion_gap H A hH hA hK
    r c hμ hν hroot hminor htransport
  have hm (x) (hx : x ∈ K) : (H x).adjugate r c ≠ 0 :=
    abs_pos.mp (hμ.trans_le (hminor x hx))
  have ht (x) (hx : x ∈ K) : minorTransportCoefficient (H x) (A x) r c ≠ 0 :=
    abs_pos.mp (hν.trans_le (htransport x hx))
  have hd (x) (hx : x ∈ K) (e) (he : |e| ≤ ε) :
      (pencilCompletion (H x) (A x) (minorRightNullvector (H x) r c)
        (minorLeftNullvector (H x) (A x) r c) e).det ≠ 0 :=
    abs_pos.mp (hδ.trans_le (hgap x hx e he))
  refine ⟨ε, hε, δ, hδ, ?_, ?_⟩
  · apply contDiffOn_minorComplementInverse (H := fun p : E × ℝ ↦ H p.1)
      (A := fun p : E × ℝ ↦ A p.1) (e := Prod.snd) r c
      (fun i j ↦ (hHs i j).comp contDiffOn_fst (fun _ hp ↦ hp.1))
      (fun i j ↦ (hAs i j).comp contDiffOn_fst (fun _ hp ↦ hp.1)) contDiffOn_snd
      (fun p hp ↦ hm p.1 hp.1) (fun p hp ↦ ht p.1 hp.1)
    intro p hp
    exact hd p.1 hp.1 p.2 (by simpa [Real.dist_eq] using (Metric.mem_ball.mp hp.2).le)
  · intro x hx e he
    obtain ⟨_, hl, hn, _⟩ := minor_normalization (hroot x hx) (hm x hx) (ht x hx)
    exact ⟨hgap x hx e he.le, complementInverse_identity hl hn (hd x hx e he.le),
      complementInverse_constraint hl hn (hd x hx e he.le),
      fun _ hb hq ↦ complementInverse_unique (hd x hx e he.le) hb hq⟩
end Families
end JanetCartan.RegularSector.Characteristic
