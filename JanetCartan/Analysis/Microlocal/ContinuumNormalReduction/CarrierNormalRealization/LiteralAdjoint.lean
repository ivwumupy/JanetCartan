module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.LiteralAdjoint.Convergence

/-!
# The literal uncut adjoint of the constructed carrier

For `app:ch_background:prop:bg-frame`, Step 1, the uniform finite complex-normal
bound proves literal adjoint membership by Fatou on the original carrier
measure. Dominated convergence gives a strong adjoint limit; eventual equality
on compact initial tests and their density identify it with the Hilbert adjoint
of the SAME extension realizing `carrierTestIntegral`.

All conditional inputs below are supplied by
`exists_carrierL2Extension_and_uniformNormals_of_primitiveNorms`: the actual
parameter-truncated masks, their uniform complex-normal bound, and the extension
with its compact-test realization. The parent global normal construction must
instantiate these inputs. No uncut membership or normal identity is assumed.
The final pairings retain both complex quadratures and the factor four of
`app:ch_background:eq:bg-realification`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open TransportKernel
variable {n N : ℕ} {d : CarrierData n N}
    {Z : Set CarrierParameter} (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    {κ : ℝ → ℝ} (hκone : ∀ t ∈ Icc (0 : ℝ) 1, κ t = 1)
    {R : ℕ → ℝ} {M Cmask : ℝ}
    (hmask : ∀ k : ℕ, CarrierRegularization.MaskHypotheses d
      (parameterTruncatedMask Z (radialCarrierMask κ (k + 1))) Z (R k) M Cmask)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
include hZ hκone hU

/-- The actual finite operators agree with this uncut extension on every
compact smooth initial test eventually. Parameter truncation is removed by the
angular support before applying radial exhaustion. Consumer: adjoint
identification by density (`app:ch_background:eq:bg-T`). -/
theorem parameterRegularizedOperator_eventually_eq_realization (u : carrierInitialTestSpace n) :
    ∀ᶠ k in atTop, (hmask k).operator (carrierInitialTestToLp u) =
      U (carrierInitialTestToLp u) := by
  filter_upwards [regularizedCarrierIntegral_eventually_eq d
    (fun k ↦ radialCarrierMask κ (k + 1))
    (radialCarrierMask_eventually_eq_one κ hκone) u.val u.property.2] with k hk
  apply Lp.ext
  have he := (hmask k).operator_ae_of_representative (carrierInitialTestToLp u) u.val
    (carrierInitialTest_memLp u).coeFn_toLp
  rw [regularizedCarrierIntegral_parameterTruncatedMask d hZ, hk] at he
  exact he.trans (hU u).symm

variable {B : ℝ} (hB : 0 ≤ B)
    (hnormal : ∀ k, ‖(hmask k).operator.comp (hmask k).operator.adjoint‖ ≤ B)
include hB hnormal

/-- The Hilbert adjoint of the SAME extension constructed from the finite
normal bounds is the literal uncut adjoint on every complex output. Fatou,
strong convergence and compact-test density discharge the analytic identification
(`app:ch_background:eq:bg-realification`, `app:ch_background:prop:bg-frame`, Step 1). -/
theorem carrierRealization_adjoint_eq_literal (w : ComplexOutputL2 n) :
    U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w := by
  have hw := (carrierAdjointIntegral_memLp_bound_of_uniformNormals hZ hκone hmask
    hB hnormal w).1
  have ht := parameterRegularizedOperator_adjoint_tendsto_literal hZ hκone hmask w hw
  have he : hw.toLp (carrierAdjointIntegral d w) = U.adjoint w := by
    apply denseRange_carrierInitialTestToLp.eq_of_inner_right ℂ
    intro u
    have hl : Tendsto (fun k ↦ inner ℂ (carrierInitialTestToLp u)
        ((hmask k).operator.adjoint w)) atTop
        (𝓝 (inner ℂ (carrierInitialTestToLp u) (U.adjoint w))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [parameterRegularizedOperator_eventually_eq_realization
        hZ hκone hmask U hU u] with k hk
      rw [(hmask k).operator.adjoint_inner_right, U.adjoint_inner_right, hk]
    exact tendsto_nhds_unique (tendsto_const_nhds.inner ht) hl
  exact he ▸ hw.coeFn_toLp

/-- Literal membership and adjoint realization for an actual L² output
function, including every smooth torus test. No uncut adjoint integrability is
assumed; `hw` concerns only the output test. This supplies the smooth-test
interface for the parent carrier construction (`app:ch_background:eq:bg-T` and
`app:ch_background:eq:bg-realification`). -/
theorem carrierRealization_literalAdjoint_of_memLp
    (w : Torus n → EuclideanSpace ℂ (Fin n)) (hw : MemLp w 2 volume) :
    MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n) ∧
      U.adjoint (hw.toLp w) =ᵐ[carrierMeasure n] carrierAdjointIntegral d w := by
  have he : carrierAdjointIntegral d (hw.toLp w) = carrierAdjointIntegral d w := by
    funext u
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    rw [hx]
  rw [← he]
  exact ⟨(carrierAdjointIntegral_memLp_bound_of_uniformNormals hZ hκone hmask
    hB hnormal (hw.toLp w)).1,
    carrierRealization_adjoint_eq_literal hZ hκone hmask U hU hB hnormal (hw.toLp w)⟩

/-- Strong L² convergence of the finite adjoints to this extension's actual
Hilbert adjoint, with literal membership proved from finite normal bounds.
Consumer: passage of the finite global normals to the uncut normal
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem parameterRegularizedOperator_adjoint_tendsto (w : ComplexOutputL2 n) :
    Tendsto (fun k ↦ (hmask k).operator.adjoint w) atTop (𝓝 (U.adjoint w)) := by
  have hw := (carrierAdjointIntegral_memLp_bound_of_uniformNormals hZ hκone hmask
    hB hnormal w).1
  have he : hw.toLp (carrierAdjointIntegral d w) = U.adjoint w :=
    Lp.ext (hw.coeFn_toLp.trans
      (carrierRealization_adjoint_eq_literal hZ hκone hmask U hU hB hnormal w).symm)
  simpa only [he] using
    parameterRegularizedOperator_adjoint_tendsto_literal hZ hκone hmask w hw

/-- The original finite radial matrix-kernel pairings converge to the
complex normal of this extension. The finite kernel pairing is the checked
Fubini identity, with the original output and carrier measures
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem parameterRegularizedOperator_normalTestPairing_tendsto (v w : ComplexOutputL2 n) :
    Tendsto (fun k : ℕ ↦ normalTestPairing d (radialCarrierMask κ (k + 1)) v w)
      atTop (𝓝 (inner ℂ v (U (U.adjoint w)))) := by
  have ht := (parameterRegularizedOperator_adjoint_tendsto hZ hκone hmask U hU hB hnormal v).inner
    (𝕜 := ℂ) (parameterRegularizedOperator_adjoint_tendsto hZ hκone hmask U hU hB hnormal w)
  simpa only [parameterRegularizedOperator_normalTestPairing hZ (hmask _) v w,
    U.adjoint_inner_left] using ht

/-- The actual finite real normal pairings converge to the real normal of
this extension on every pair of real outputs. Both complex input quadratures
are retained through the actual real adjoints. Consumer: the parent's global
uncut normal identification (`app:ch_background:eq:bg-realification`). -/
theorem parameterRegularizedOperator_realNormal_tendsto (v w : OutputL2 n) :
    Tendsto (fun k ↦ inner ℝ v (realQuadratureChannel (hmask k).operator
      ((realQuadratureChannel (hmask k).operator).adjoint w))) atTop
      (𝓝 (inner ℝ v (realQuadratureChannel U ((realQuadratureChannel U).adjoint w)))) := by
  have ht := ((parameterRegularizedOperator_adjoint_tendsto hZ hκone hmask U hU hB hnormal
    (l2ComplexInclusion volume v)).const_smul (2 : ℝ)).inner (𝕜 := ℝ)
      ((parameterRegularizedOperator_adjoint_tendsto hZ hκone hmask U hU hB hnormal
        (l2ComplexInclusion volume w)).const_smul (2 : ℝ))
  have he (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
      inner ℝ v (realQuadratureChannel T ((realQuadratureChannel T).adjoint w)) =
        inner ℝ ((realQuadratureChannel T).adjoint v) ((realQuadratureChannel T).adjoint w) :=
    ((realQuadratureChannel T).adjoint_inner_left _ _).symm
  simp_rw [he, realQuadratureChannel_adjoint_apply]
  exact ht

/-- The uncut real normal is exactly four times the real part of the
literal complex-adjoint pairing on the original carrier measure. This fixes
the normalization when the parent identifies the uncut reflected symbol
(`app:ch_background:eq:bg-realification` and
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem carrierRealization_realNormal_pairing (v w : OutputL2 n) :
    inner ℝ v (realQuadratureChannel U ((realQuadratureChannel U).adjoint w)) =
      4 * (∫ u, inner ℂ
        (carrierAdjointIntegral d (l2ComplexInclusion volume v) u)
        (carrierAdjointIntegral d (l2ComplexInclusion volume w) u)
          ∂carrierMeasure n).re := by
  have he : inner ℂ (U.adjoint (l2ComplexInclusion volume v))
      (U.adjoint (l2ComplexInclusion volume w)) =
        ∫ u, inner ℂ (carrierAdjointIntegral d (l2ComplexInclusion volume v) u)
          (carrierAdjointIntegral d (l2ComplexInclusion volume w) u) ∂carrierMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [carrierRealization_adjoint_eq_literal hZ hκone hmask U hU hB hnormal
      (l2ComplexInclusion volume v),
      carrierRealization_adjoint_eq_literal hZ hκone hmask U hU hB hnormal
        (l2ComplexInclusion volume w)] with u hv hw
    rw [hv, hw]
  rw [← (realQuadratureChannel U).adjoint_inner_left,
    realQuadratureChannel_adjoint_apply, realQuadratureChannel_adjoint_apply,
    real_inner_smul_left, real_inner_smul_right, real_inner_eq_complex_re, he]
  ring

end JanetCartan.ContinuumRow.CarrierNormalRealization
