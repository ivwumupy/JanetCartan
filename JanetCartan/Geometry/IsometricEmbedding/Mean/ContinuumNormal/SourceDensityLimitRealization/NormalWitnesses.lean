module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.Weights

/-!
# Normal identities with the consumer's amplitude witnesses

The carrier constructor and the sharp spatial-freezing estimate may return
different numerical bounds for the same amplitude. Dense smooth tests identify
the resulting PDOs. Consumers: the literal `hnormal` arguments of
`exists_initialized_density_limit_coercivity_of_retained_geometry` and
`NormalizedNormalLimit.exists_source_family_controlled_half_gap`
(`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-frame`).
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ContinuumRow ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- The physical full-amplitude operator is independent of its support-box
and norm-budget witnesses. Its action on dense tests fixes the operator
(`bg-full-complex-amplitude`, `app:ch_regular_base:thm:actual-calculus`). -/
theorem fullAmplitudeOperator_eq_of_witnesses
    {n : ℕ} (hn : 0 < n) (R R' : ℝ)
    (b b' : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hb' : ContDiff ℝ ∞ (Function.uncurry b'))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (hs' : ∀ ξ i j, SupportedInCenteredBox R' (fun z ↦ b' ξ z i j))
    (B B' : ℝ)
    (hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (hB' : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b' ξ z i j) (2 * (n + 1)) B')
    (heq : b = b') :
    vectorTwoPositionL2Operator hn R b hb hs B hB =
      vectorTwoPositionL2Operator hn R' b' hb' hs' B' hB' := by
  subst b'
  apply DFunLike.coe_injective
  apply (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Euclidean n)))
    (F := EuclideanSpace ℂ (Fin n)) (p := 2) (by norm_num)).denseRange_val.equalizer
    (map_continuous _) (map_continuous _)
  funext ⟨v, f, hv, hfs, hfc⟩
  simp only [Function.comp_apply]
  have hf : MemLp f 2 volume := hfc.continuous.memLp_of_hasCompactSupport hfs
  have he : v = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  rw [he]
  apply Lp.ext
  exact (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R b hb hs B hB f hf
    (fun j ↦ ((contDiff_piLp 2).mp hfc j).of_le (by simp))
    (fun j ↦ hfs.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) ↦ v j) rfl)).trans
    (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R' b hb' hs' B' hB' f hf
      (fun j ↦ ((contDiff_piLp 2).mp hfc j).of_le (by simp))
      (fun j ↦ hfs.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) ↦ v j) rfl)).symm

/-- Transfer a constructed literal normal to the consumer's regularity and
bound witnesses for the same amplitude. The carrier is unchanged, including
after the supplied common measurement restriction (`bg-real-symbol`). -/
theorem realized_normal_eq_of_amplitude_witnesses
    {n : ℕ} (hn : 0 < n) (R R' : ℝ)
    (b b' : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hb' : ContDiff ℝ ∞ (Function.uncurry b'))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (hs' : ∀ ξ i j, SupportedInCenteredBox R' (fun z ↦ b' ξ z i j))
    (B B' : ℝ)
    (hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (hB' : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b' ξ z i j) (2 * (n + 1)) B')
    (heq : b = b') (Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hV : carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
      realOutputCompression (transferOperator (vectorTwoPositionL2Operator hn R b hb hs B hB))) :
    carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
      realOutputCompression (transferOperator (vectorTwoPositionL2Operator hn R' b' hb' hs' B' hB')) := by
  rwa [fullAmplitudeOperator_eq_of_witnesses hn R R' b b' hb hb' hs hs' B B' hB hB' heq] at hV

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
