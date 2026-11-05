module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Datum-wise integration of the elapsed-time graph family

The fixed-time representation in `app:ch_regular_base:eq:fixed-time-representation`
requires strong measurability on each datum, not continuity in operator norm.
This file constructs its bounded integral from that measurability and a common
low bound, and proves that literal adjunction commutes with this construction.
Producing these hypotheses for `elapsedGraph` from the original phase and symbol
is a separate, still necessary obligation of the retarded-kernel construction.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open scoped ComplexConjugate

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Δ C : ℝ} {T : ℝ → H →L[ℂ] H}

/-- Measurability on the dense graph test space extends to every datum using
only continuity of each fixed operator. There is no continuity assumption in
elapsed time. Consumer: the measurability step of
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem aestronglyMeasurable_apply_of_dense {ι : Type*} (v : ι → H)
    (hdense : DenseRange v) (μ : Measure ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (fun r ↦ T r (v i)) μ) (u : H) :
    AEStronglyMeasurable (fun r ↦ T r u) μ := by
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense u)
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n r ↦ T r (w n))
  · intro n
    obtain ⟨i, hi⟩ := hw n
    simpa only [← hi] using hmeas i
  · exact Eventually.of_forall (fun r ↦ (T r).continuous.continuousAt.tendsto.comp hlim)

/-- Integrability on each datum follows from strong measurability and the
uniform graph bound. Consumer: `strongIntegral` for
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrableOn_apply_of_uniform_bound
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C) (u : H) :
    IntegrableOn (fun r ↦ T r u) (Icc 0 Δ) := by
  refine (integrable_const (C * ‖u‖)).mono' (hmeas u) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact (T r).le_opNorm u |>.trans (mul_le_mul_of_nonneg_right (hbound r hr) (norm_nonneg u))

/-- The fixed-interval operator is constructed by integrating each datum.
Only strong measurability of the orbits is required. The constant `C` is
the uniform LOW graph bound, not a Sobolev estimate or a continuity assumption.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def strongIntegral (T : ℝ → H →L[ℂ] H) (Δ C : ℝ)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C) : H →L[ℂ] H := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u ↦ ∫ r in Icc 0 Δ, T r u
      map_add' := fun u v ↦ by
        simp only [map_add]
        exact integral_add (integrableOn_apply_of_uniform_bound hmeas hbound u)
          (integrableOn_apply_of_uniform_bound hmeas hbound v)
      map_smul' := fun c u ↦ by simp only [map_smul, integral_smul, RingHom.id_apply] }
  refine L.mkContinuous (C * volume.real (Icc 0 Δ)) (fun u ↦ ?_)
  change ‖∫ r in Icc 0 Δ, T r u‖ ≤ (C * volume.real (Icc 0 Δ)) * ‖u‖
  have hb : ∀ᵐ r ∂volume.restrict (Icc 0 Δ), ‖T r u‖ ≤ C * ‖u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (T r).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hbound r hr) (norm_nonneg u))
  simpa only [Measure.real, Measure.restrict_apply_univ, mul_right_comm] using
    norm_integral_le_of_norm_le_const hb

/-- The constructed operator has the actual datum-wise integral action.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem strongIntegral_apply
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C) (u : H) :
    strongIntegral T Δ C hmeas hbound u = ∫ r in Icc 0 Δ, T r u := rfl

/-- The integral costs only the length of the fixed slab.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_strongIntegral_le (hΔ : 0 ≤ Δ) (hC : 0 ≤ C)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C) :
    ‖strongIntegral T Δ C hmeas hbound‖ ≤ Δ * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hΔ hC)
  intro u
  rw [strongIntegral_apply]
  have hb : ∀ᵐ r ∂volume.restrict (Icc 0 Δ), ‖T r u‖ ≤ C * ‖u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (T r).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hbound r hr) (norm_nonneg u))
  simpa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hΔ,
    mul_comm, mul_left_comm, mul_assoc] using norm_integral_le_of_norm_le_const hb

/-- A uniformly low-bounded sequence of frequency regularizations commutes
with elapsed-time integration on every datum. The primitive full graph
constructor supplies the uniform bound and strong limits; its finite kernels
must supply measurability. Consumer: the uncut identification in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem tendsto_integral_apply_of_uniform_bound
    (Treg : ℕ → ℝ → H →L[ℂ] H)
    (hmeas : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u)
      (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop (𝓝 (T r u)))
    (u : H) :
    Tendsto (fun j ↦ ∫ r in Icc 0 Δ, Treg j r u) atTop
      (𝓝 (∫ r in Icc 0 Δ, T r u)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ C * ‖u‖)
    (fun j ↦ hmeas j u) (integrable_const _)
  · intro j
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (Treg j r).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hbound j r hr) (norm_nonneg u))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hlim r hr u

variable [CompleteSpace H]

/-- Literal Hilbert adjunction commutes with the strong integral. No
operator-valued Bochner integral or operator-norm continuity is used.
The reversed kernel and its `Bβ*` factor must subsequently be identified from
the actual elapsed graphs. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem strongIntegral_adjoint_apply
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C)
    (hmeasAdj : ∀ u, AEStronglyMeasurable (fun r ↦ (T r).adjoint u)
      (volume.restrict (Icc 0 Δ))) (v : H) :
    (strongIntegral T Δ C hmeas hbound).adjoint v =
      ∫ r in Icc 0 Δ, (T r).adjoint v := by
  have hi := integrableOn_apply_of_uniform_bound hmeas hbound
  have hba : ∀ r ∈ Icc 0 Δ, ‖(T r).adjoint‖ ≤ C := by
    intro r hr
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound r hr
  have hia := integrableOn_apply_of_uniform_bound hmeasAdj hba
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, strongIntegral_apply,
    ← integral_inner (hia v)]
  calc
    inner ℂ (∫ r in Icc 0 Δ, T r u) v =
        conj (inner ℂ v (∫ r in Icc 0 Δ, T r u)) := (inner_conj_symm _ _).symm
    _ = ∫ r in Icc 0 Δ, inner ℂ (T r u) v := by
      rw [← integral_inner (hi u), ← integral_conj]
      simp only [inner_conj_symm]
    _ = ∫ r in Icc 0 Δ, inner ℂ u ((T r).adjoint v) := by
      congr 1
      funext r
      exact (T r).adjoint_inner_right u v |>.symm

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
