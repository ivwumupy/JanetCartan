module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Periodic
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Postcomposition
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly

/-!
# Identification with the literal real carrier adjoint

The complex operator constructed by the derivative endpoint is identified with
the adjoint of the original carrier using their literal integral representatives.
Real inclusion is bounded on the existing periodic Sobolev spaces, and the raw
scale keeps both complex quadratures. Thus realification costs exactly the
factor two in the source. There is no change of input measure or Fourier scale.

The raw complex estimate is supplied by the local canonical construction;
the original carrier and its representative are supplied by the supported-shell
carrier construction. Their common finite-family instantiation remains with the
parent (`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-realification`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow CarrierSobolev DerivativeKernels
open ContinuumCommutator.HigherRegularity.RealCommutator

variable {n N s : ℕ}

/-- Real scalar multiplication in the full raw scale retains every carrier
and initial derivative (`app:ch_background:eq:bg-realification`). -/
theorem rawSobolev_real_smul {f : CarrierL2 n} (hf : MemRawSobolev s f) (c : ℝ) :
    MemRawSobolev s (c • f) ∧ rawSobolevNorm s (c • f) = ‖c‖ * rawSobolevNorm s f := by
  let u := RawSobolevSpace.ofRawL2 s f hf
  have he₀ : RawSobolevSpace.toRawL2 s u = f := RawSobolevSpace.toRawL2_ofRawL2 s f hf
  have he : RawSobolevSpace.toRawL2 s (c • u) = c • f := by
    rw [(RawSobolevSpace.toRawL2 s).map_smul_of_tower, he₀]
  refine ⟨he ▸ RawSobolevSpace.toRawL2_mem s (c • u), ?_⟩
  calc
    _ = ‖c • u‖ := by rw [RawSobolevSpace.norm_eq s (c • u), he]
    _ = ‖c‖ * ‖u‖ := norm_smul c u
    _ = _ := by rw [RawSobolevSpace.norm_eq s u, he₀]

/-- The endpoint operator gives the original real adjoint, not a new choice
of inverse or carrier. The two representative premises are the exact outputs
of the scalar-transport and supported-shell carrier producers
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierChannel_adjoint_eq_literal_operator (d : CarrierData n N)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (A : ComplexOutputL2 n →L[ℂ] CarrierL2 n)
    (hA : ∀ v, A v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v)
    (hU : ∀ v, U.adjoint v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v)
    (v : OutputL2 n) :
    (carrierChannel U).adjoint v = (2 : ℝ) • A (l2ComplexInclusion volume v) := by
  rw [carrierChannel_adjoint_apply,
    literalCarrierAdjointOperator_unique d U.adjoint A hU hA]

/-- Transfer the checked complex raw estimate to the literal real carrier
adjoint, retaining both quadratures and the single high coefficient. The
only analytic estimate premise is exactly the complex endpoint already proved
from primitive profiles; this lemma proves the real Sobolev transfer
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-realification`). -/
theorem carrierChannel_adjoint_raw_bound (d : CarrierData n N)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (A : ComplexOutputL2 n →L[ℂ] CarrierL2 n)
    (hA : ∀ v, A v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v)
    (hU : ∀ v, U.adjoint v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v)
    {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hraw : ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
      MemRawSobolev s (A (PeriodicSobolevSpace.toL2 s v)) ∧
      rawSobolevNorm s (A (PeriodicSobolevSpace.toL2 s v)) ≤
        C * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 s v‖))
    (v : PeriodicSobolevSpace n (Euclidean n) s) :
    MemRawSobolev s ((carrierChannel U).adjoint (PeriodicSobolevSpace.toL2 s v)) ∧
      rawSobolevNorm s ((carrierChannel U).adjoint (PeriodicSobolevSpace.toL2 s v)) ≤
        (2*C) * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 s v‖) := by
  let vc := sobolevMap (euclideanComplexInclusion (ι := Fin n)) s v
  have heq : PeriodicSobolevSpace.toL2 s vc =
      l2ComplexInclusion volume (PeriodicSobolevSpace.toL2 s v) := rfl
  have hvc : ‖vc‖ ≤ ‖v‖ :=
    (norm_sobolevMap_le (euclideanComplexInclusion (ι := Fin n)) s v).trans
      ((mul_le_mul_of_nonneg_right (euclideanComplexInclusion_norm_le (ι := Fin n))
        (norm_nonneg v)).trans_eq (one_mul _))
  have hvc₀ : ‖PeriodicSobolevSpace.toL2 s vc‖ ≤ ‖PeriodicSobolevSpace.toL2 s v‖ := by
    rw [heq]
    exact ((l2ComplexInclusion volume).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (l2ComplexInclusion_norm_le (ι := Fin n) volume)
        (norm_nonneg (PeriodicSobolevSpace.toL2 s v))).trans_eq (one_mul _))
  obtain ⟨hmem, hb⟩ := hraw vc
  rw [carrierChannel_adjoint_eq_literal_operator d U A hA hU, ← heq]
  obtain ⟨hmem₂, hnorm₂⟩ := rawSobolev_real_smul hmem (2 : ℝ)
  refine ⟨hmem₂, ?_⟩
  rw [hnorm₂, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (C * (‖vc‖ + H * ‖PeriodicSobolevSpace.toL2 s vc‖)) := by gcongr
    _ ≤ 2 * (C * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 s v‖)) := by gcongr
    _ = _ := by ring

end JanetCartan.ContinuumAdjoint.Canonical
