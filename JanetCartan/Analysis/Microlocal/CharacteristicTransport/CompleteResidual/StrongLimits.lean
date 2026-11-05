module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.WeakEquation

/-!
# Using the literal Hilbert-space regularization outputs

The retarded producer
`EvolutionIntegral.KernelIdentification.exists_retardedOperator_of_regularizations`
returns Euclidean-valued L² classes, a.e. kernel representatives, and strong
limits. This module consumes precisely that form of convergence, converting
to coordinate functions and restricting to the measurement domain. The same
conversion applies to the matrix PDO regularizations.

Source: `app:ch_regular_base:eq:energy-complete-residual`. The complete
finite-cutoff equation and the actual instantiation of these strong limits
remain obligations of the solver construction.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicTransport.CompleteResidual

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "FV" => Fin q → ℂ
local notation "H" => EuclideanSpace ℂ (Fin q)
local notation "C2" => Lp H 2 (volume : Measure E)

private theorem coordinate_limits_of_strongL2 {ι : Type*} {l : Filter ι}
    (ureg : ι → C2) (u : C2) (f : ι → E → FV)
    (hrep : ∀ k, ureg k =ᵐ[volume] fun x ↦ WithLp.toLp 2 (f k x))
    (hlim : Tendsto ureg l (𝓝 u)) (U : Set E) :
    (∀ k, MemLp (f k) 2 (volume.restrict U)) ∧
      MemLp (fun x ↦ (u x).ofLp) 2 (volume.restrict U) ∧
      Tendsto (fun k ↦ eLpNorm (f k - (fun x ↦ (u x).ofLp)) 2 (volume.restrict U)) l (𝓝 0) := by
  let L : H →L[ℝ] FV :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)).toContinuousLinearMap.restrictScalars ℝ
  have he (k : ι) : (fun x ↦ L (ureg k x)) =ᵐ[volume] f k := by
    filter_upwards [hrep k] with x hx
    exact congrArg L hx
  have hf (k : ι) : MemLp (f k) 2 volume :=
    (memLp_congr_ae (he k)).mp (L.comp_memLp' (Lp.memLp (ureg k)))
  have hu : MemLp (fun x ↦ (u x).ofLp) 2 volume := L.comp_memLp' (Lp.memLp u)
  have ht : Tendsto (fun k ↦ eLpNorm ((ureg k : E → H) - (u : E → H)) 2 volume) l (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k ↦ (ureg k : E → H)) (fun k ↦ Lp.memLp (ureg k)) u (Lp.memLp u)).mp
    simpa only [Lp.toLp_coeFn] using hlim
  have htL := Mollification.tendsto_eLpNorm_compCLM_sub L (fun k ↦ Lp.memLp (ureg k))
    (Lp.memLp u) ht
  have htf : Tendsto (fun k ↦ eLpNorm (f k - (fun x ↦ (u x).ofLp)) 2 volume) l (𝓝 0) := by
    apply htL.congr
    intro k
    exact eLpNorm_congr_ae ((he k).sub EventuallyEq.rfl)
  refine ⟨fun k ↦ (hf k).restrict U, hu.restrict U, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htf
    (fun _ ↦ zero_le) (fun k ↦ eLpNorm_restrict_le _ _ _ _)

/-- The concrete shape of the graph/PDO strong-limit outputs suffices for
the uncut test equation. Representatives are identified only a.e.; the output
is never differentiated pointwise. The finite identity is still a separate
input to be proved by kernel and PDO calculus
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_test_of_strongL2 {ι : Type*} {l : Filter ι} [NeBot l]
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    {U : Set E} (hU : MeasurableSet U)
    (ureg rreg : ι → C2) (u g : C2) (f r : ι → E → FV)
    (hf : ∀ k, ContDiff ℝ 1 (f k))
    (hurep : ∀ k, ureg k =ᵐ[volume] fun x ↦ WithLp.toLp 2 (f k x))
    (hrrep : ∀ k, rreg k =ᵐ[volume] fun x ↦ WithLp.toLp 2 (r k x))
    (hulim : Tendsto ureg l (𝓝 u)) (hrlim : Tendsto rreg l (𝓝 g))
    (hfinite : ∀ k, WKB.firstOrderApply
      (fun x a ↦ ((A x a).map Complex.ofReal).mulVecLin)
      (fun x ↦ ((B x).map Complex.ofReal).mulVecLin) (f k) =ᵐ[volume.restrict U] r k)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (i : Fin q) :
    physicalTestAction A B (fun x ↦ (u x).ofLp) φ i = ∫ x, φ x • g x i := by
  obtain ⟨hfm, hum, hfl⟩ := coordinate_limits_of_strongL2 ureg u f hurep hulim U
  obtain ⟨hrm, hgm, hrl⟩ := coordinate_limits_of_strongL2 rreg g r hrrep hrlim U
  exact firstOrderApply_test_of_tendsto A B hA hB hU hf hfm hrm hum hgm hfl hrl
    hfinite hφ hc hs i

/-- Once the same uncut output has its Sobolev weak derivative, the literal
L² regularization limits imply the local a.e. equation. The derivative premise
is produced by the graph/PDO regularity estimates; no uncut residual equation
is assumed (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalWeakApply_ae_of_strongL2 {ι : Type*} {l : Filter ι} [NeBot l]
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    {U : Set E} (hU : IsOpen U)
    (ureg rreg : ι → C2) (u g : C2) (f r : ι → E → FV)
    (hf : ∀ k, ContDiff ℝ 1 (f k))
    (hurep : ∀ k, ureg k =ᵐ[volume] fun x ↦ WithLp.toLp 2 (f k x))
    (hrrep : ∀ k, rreg k =ᵐ[volume] fun x ↦ WithLp.toLp 2 (r k x))
    (hulim : Tendsto ureg l (𝓝 u)) (hrlim : Tendsto rreg l (𝓝 g))
    (hfinite : ∀ k, WKB.firstOrderApply
      (fun x a ↦ ((A x a).map Complex.ofReal).mulVecLin)
      (fun x ↦ ((B x).map Complex.ofReal).mulVecLin) (f k) =ᵐ[volume.restrict U] r k)
    (du : E → E →L[ℝ] FV)
    (hw : Mollification.HasWeakFDerivOn volume (fun x ↦ (u x).ofLp) du U) :
    physicalWeakApply A B (fun x ↦ (u x).ofLp) du =ᵐ[volume.restrict U]
      fun x ↦ (g x).ofLp := by
  have hgm := (coordinate_limits_of_strongL2 rreg g r hrrep hrlim U).2.1
  apply physicalWeakApply_ae_eq_of_test A B hA hB hU hw
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hgm.locallyIntegrable (by norm_num)))
  intro φ hφ hc hs i
  exact firstOrderApply_test_of_strongL2 A B hA hB hU.measurableSet ureg rreg u g f r hf
    hurep hrrep hulim hrlim hfinite hφ hc hs i

end JanetCartan.CharacteristicTransport.CompleteResidual
