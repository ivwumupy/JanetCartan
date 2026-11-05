module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.StrongIntegral
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SobolevIntegration.ClosedBalls

/-!
# Integrating uniform integer Sobolev graph estimates

The last step of `app:ch_regular_base:lem:retarded-kernel` transfers the per-time
bounds to the actual datum-wise strong integral and its literal Hilbert adjoint.
The order loss `e` is `0` or `1` in the manuscript; the integration implication
itself works for every natural `e`, with the same truncated subtraction as
`exists_graph_integer_sobolev_constant` and `exists_adjoint_integer_sobolev_constant`.
The fixed coefficient shift `μ` and the profile `H` do not change on integration.

These are conditional integration deductions. The parent retarded construction
must obtain the per-time estimates from `PrimitiveRealization.Family`,
`SobolevBounds.IntegerBounds`, and the actual uniform phase/amplitude budgets.
It also owes datum-wise L² measurability and the uniform low operator bound.
No per-time estimate, kernel identification, or primitive budget is supplied here.
The closed Fourier Sobolev ball argument needs only L² orbit measurability,
so it introduces no Sobolev-valued measurability premise.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open JanetCartan.Pseudodifferential

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ} {Δ C₀ : ℝ}
variable {T : ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q}

/-- Uniform per-time integer Sobolev membership and the one-high bound pass
to the actual strong integral, costing exactly `Δ`. The premises are the
conclusions of `exists_graph_integer_sobolev_constant`, after the parent bounds
the actual high seminorms by `H (s + μ)` uniformly in elapsed time.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem strongIntegral_integer_sobolev_bound (hΔ : 0 ≤ Δ)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀)
    (e μ s : ℕ) (C : ℝ) (H : ℕ → ℝ)
    (hsob : ∀ r ∈ Icc 0 Δ, ∀ u, MemVectorFourierSobolev ((s - e : ℕ) : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (T r u) ∧
        vectorFourierSobolevNorm (s : ℝ) (T r u) ≤ C *
          (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖))
    (u : SpacetimeL2 d q) (hu : MemVectorFourierSobolev ((s - e : ℕ) : ℝ) u) :
    MemVectorFourierSobolev (s : ℝ) (strongIntegral T Δ C₀ hmeas hbound u) ∧
      vectorFourierSobolevNorm (s : ℝ) (strongIntegral T Δ C₀ hmeas hbound u) ≤
        (Δ * C) * (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖) := by
  rw [strongIntegral_apply]
  have hinst : (NormedSpace.complexToReal (E := SpacetimeL2 d q)) =
      (inferInstance : NormedSpace ℝ (SpacetimeL2 d q)) := NormedSpace.restrictScalars_eq ℝ ℂ
  rw [hinst]
  simpa only [mul_assoc] using
    SobolevIntegration.integral_vectorSobolev_bound hΔ (s : ℝ)
      (C * (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖))
      (fun r ↦ T r u) (integrableOn_apply_of_uniform_bound hmeas hbound u)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact hsob r hr u hu)

/-- The corresponding per-time adjoint conclusion transfers to the literal
Hilbert adjoint of the constructed strong integral, with the same interval
length and fixed coefficient shift. The parent must instantiate
`exists_adjoint_integer_sobolev_constant` for the actual reversed graphs.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem strongIntegral_adjoint_integer_sobolev_bound (hΔ : 0 ≤ Δ)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀)
    (hmeasAdj : ∀ u, AEStronglyMeasurable (fun r ↦ (T r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    (e μ s : ℕ) (C : ℝ) (H : ℕ → ℝ)
    (hsobAdj : ∀ r ∈ Icc 0 Δ, ∀ u, MemVectorFourierSobolev ((s - e : ℕ) : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) ((T r).adjoint u) ∧
        vectorFourierSobolevNorm (s : ℝ) ((T r).adjoint u) ≤ C *
          (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖))
    (u : SpacetimeL2 d q) (hu : MemVectorFourierSobolev ((s - e : ℕ) : ℝ) u) :
    MemVectorFourierSobolev (s : ℝ) ((strongIntegral T Δ C₀ hmeas hbound).adjoint u) ∧
      vectorFourierSobolevNorm (s : ℝ) ((strongIntegral T Δ C₀ hmeas hbound).adjoint u) ≤
        (Δ * C) * (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖) := by
  have hboundAdj : ∀ r ∈ Icc 0 Δ, ‖(T r).adjoint‖ ≤ C₀ := by
    intro r hr
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound r hr
  rw [strongIntegral_adjoint_apply hmeas hbound hmeasAdj]
  simpa only [strongIntegral_apply] using
    strongIntegral_integer_sobolev_bound hΔ hmeasAdj hboundAdj e μ s C H hsobAdj u hu

/-- All integer orders for the forward integral and its literal adjoint,
with one fixed shift `μ`, one time-independent high profile `H`, and the
explicit output constants `Δ * C s`. For `e = 0` and `e = 1`, these are the
order-zero and gain-one integration conclusions of
`app:ch_regular_base:lem:retarded-kernel`. All per-time analytic premises
remain the parent construction's obligations. -/
theorem strongIntegral_and_adjoint_integer_sobolev_bounds (hΔ : 0 ≤ Δ)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀)
    (hmeasAdj : ∀ u, AEStronglyMeasurable (fun r ↦ (T r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    (e μ : ℕ) (C H : ℕ → ℝ)
    (hsob : ∀ s r, r ∈ Icc 0 Δ → ∀ u,
      MemVectorFourierSobolev ((s - e : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T r u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T r u) ≤ C s *
            (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖))
    (hsobAdj : ∀ s r, r ∈ Icc 0 Δ → ∀ u,
      MemVectorFourierSobolev ((s - e : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) ((T r).adjoint u) ∧
          vectorFourierSobolevNorm (s : ℝ) ((T r).adjoint u) ≤ C s *
            (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖)) :
    ∀ s u, MemVectorFourierSobolev ((s - e : ℕ) : ℝ) u →
      (MemVectorFourierSobolev (s : ℝ) (strongIntegral T Δ C₀ hmeas hbound u) ∧
        vectorFourierSobolevNorm (s : ℝ) (strongIntegral T Δ C₀ hmeas hbound u) ≤
          (Δ * C s) *
            (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖)) ∧
      (MemVectorFourierSobolev (s : ℝ) ((strongIntegral T Δ C₀ hmeas hbound).adjoint u) ∧
        vectorFourierSobolevNorm (s : ℝ) ((strongIntegral T Δ C₀ hmeas hbound).adjoint u) ≤
          (Δ * C s) *
            (vectorFourierSobolevNorm ((s - e : ℕ) : ℝ) u + H (s + μ) * ‖u‖)) := by
  intro s u hu
  exact ⟨strongIntegral_integer_sobolev_bound hΔ hmeas hbound e μ s (C s) H
      (hsob s) u hu,
    strongIntegral_adjoint_integer_sobolev_bound hΔ hmeas hbound hmeasAdj e μ s (C s) H
      (hsobAdj s) u hu⟩

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
