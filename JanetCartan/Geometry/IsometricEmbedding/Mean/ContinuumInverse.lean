module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.Adjoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.RetainedRow
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.IncidenceSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.IncidenceRaw

/-!
# The continuum inverse on retained rows

For `app:ch_background:prop:bg-inverse` and `app:ch_background:prop:bg-adjoint`,
the imported modules prove the quantitative induction for a single coercive
Hilbert-space inverse. `exists_retained_history_inverse_estimates` applies the
actual common-measurement bootstrap, full augmented adjoint and fixed density
multipliers on the SAME operators. It retains the image and carrier norm
domains, raw shift `2*(n+1)+14`, density shift `2*(n+1)+15`, and the exterior
component's vanishing on the original core. Constants precede the varying
histories and scalars. The local kernel, raw and high-amplitude inputs are the
initialized row's existing outputs.

`exists_realized_retained_incidence_inverse_estimates` now applies the actual
source coercivity and sharp carrier constructors on supplied retained incidence
geometry. It constructs the canonical L² right inverse, its core equation,
`hreg`, `hstep` and all normal-inverse Sobolev bounds on the SAME returned row.
Its constants and supplied inner exterior cutoff precede every source scale,
original density and target. The gap and amplitude estimates are proved by
those constructors, not assumed inputs. Its normalized density carrier keeps
the current inverse ODE label, and literal adjoint uniqueness preserves the
measured row, normal inverse and right inverse under realization.

`exists_retained_incidence_uncorrected_inverse_with_raw_bounds` constructs
the full augmented raw and cut/uncut density estimates on that same source
row. The retained-history variants with a supplied exterior preserve the
coercivity constructor's inner cutoff and its actual plateau.

The retained-history theorem fixes its reference and source scale before
choosing constants. It therefore does not yet supply the normalized-background
consumer's common radius, gap and estimates before all `σ ∈ (0, σ₀]`.
The new incidence theorem supplies that quantifier order for the normal inverse.
Corrected-density/history instantiation and the original initializer's application
to these same geometric witnesses remain necessary. This module does not yet
prove either unconditional source proposition. The general
`canonical_inverse_estimate` below retains its original interface for consumers.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumInverse

variable {H X : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- Conditional assembly of `app:ch_background:eq:bg-r-inverse` for any bounded
row with a positive adjoint gap. The hypotheses concern the normal and the raw
adjoint, not a high-order inverse. The constant depends on the gap and low
analytic constants only. Instantiating these hypotheses for the actual
continuum row remains necessary to prove the source proposition. -/
theorem canonical_inverse_estimate (G : GradedScale H) (R : GradedScale X)
    (A : X →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    {C K a : ℕ → ℝ} {b : ℕ} (hC : ∀ s, 0 ≤ C s) (hK : ∀ s, 0 ≤ K s)
    (ha : ∀ s, 0 ≤ a s) (ha_mono : Monotone a)
    (hreg : ∀ s v, v ∈ G.level s →
      CoerciveInverse.normalOperator A v ∈ G.level (s + 1) → v ∈ G.level (s + 1))
    (hstep : ∀ s v, v ∈ G.level (s + 1) →
      CoerciveInverse.normalOperator A v ∈ G.level (s + 1) →
      G.gradeNorm (s + 1) v ≤ C (s + 1) *
        (G.gradeNorm (s + 1) (CoerciveInverse.normalOperator A v) + G.gradeNorm s v +
          (1 + a (s + 1 + b)) * ‖v‖))
    (hraw_reg : ∀ s v, v ∈ G.level s → A.adjoint v ∈ R.level s)
    (hraw : ∀ s v, v ∈ G.level s → R.gradeNorm s (A.adjoint v) ≤
      K s * (G.gradeNorm s v + (1 + a (s + b)) * ‖v‖))
    (s : ℕ) {e : H} (he : e ∈ G.level s) :
    (CoerciveInverse.normalOperator A).inverse e ∈ G.level s ∧
      CoerciveInverse.rightInverse A e ∈ R.level s ∧
      A (CoerciveInverse.rightInverse A e) = e ∧
      G.gradeNorm s ((CoerciveInverse.normalOperator A).inverse e) +
        R.gradeNorm s (CoerciveInverse.rightInverse A e) ≤
          (bootstrapConstant c C s + K s * (bootstrapConstant c C s + c⁻¹)) *
            (G.gradeNorm s e + (1 + a (s + b)) * ‖e‖) := by
  have hnormal := CoerciveInverse.normalOperator_gap A hgap
  have hmem := inverse_mem G (CoerciveInverse.normalOperator A) hc hnormal hreg s he
  have hbound := inverse_gradeNorm_le G (CoerciveInverse.normalOperator A)
    hc hnormal hC ha ha_mono hreg hstep s he
  refine ⟨hmem, rightInverse_mem G R A hmem (hraw_reg s),
    CoerciveInverse.apply_rightInverse A hc hgap e, ?_⟩
  exact inverse_add_rightInverse_gradeNorm_le G R A hc hgap (hK s)
    (add_nonneg zero_le_one (ha (s + b))) hmem hbound (hraw s)

end JanetCartan.ContinuumInverse
