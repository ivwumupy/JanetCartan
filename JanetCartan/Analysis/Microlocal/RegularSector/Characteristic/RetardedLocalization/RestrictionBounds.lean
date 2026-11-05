module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer

/-!
# The fixed inverse's genuine restriction-H¹ endpoint

Apply the proved Fourier-to-weak-jet conversion to the same retarded map and
its literal adjoint. The dimension constant precedes every operator, domain
and input. There is no derivative loss, and zero extension preserves the
source L² norm exactly. The positive Fourier premise is the existing signed
primitive constructor's output, whose geometric instantiation remains with
the actual sector. Source: `app:ch_regular:thm:exact-correction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace JanetCartan.RegularSector.Characteristic.RetardedLocalization
open LocalSobolev Pseudodifferential EvolutionIntegral

/-- The gain-one primitive retarded estimate supplies the exact `LocalL2`
to restriction-`H¹` premise of the fixed-domain inverse, in both orientations.
Only a fixed dimension constant is added; the high coefficient order stays
`1+μ` (`app:ch_regular:thm:exact-correction`). -/
theorem exists_localRetarded_restrictionH1_constant (d q : ℕ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (μ : ℕ)
        (Δ : ℝ) (C Hhi : ℕ → ℝ),
        (∀ s : ℕ, ∀ T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
          (T = Q ∨ T = Q.adjoint) → ∀ u,
          MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
            MemVectorFourierSobolev (s : ℝ) (T u) ∧
              vectorFourierSobolevNorm (s : ℝ) (T u) ≤ (Δ * C s) *
                (vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u + Hhi (s+μ) * ‖u‖)) →
        ∀ (U W : Set (Euclidean (d+1))) (hU : MeasurableSet U) (_hW : MeasurableSet W),
          (∀ f : LocalL2 U (EuclideanSpace ℂ (Fin q)),
            MemRestrictionSobolev W 1 (localRetardedOperator hU W Q f) ∧
              restrictionSobolevNorm W 1 (localRetardedOperator hU W Q f) ≤
                (D * (Δ * C 1) * (1 + Hhi (1+μ))) * ‖f‖) ∧
          (∀ g : LocalL2 W (EuclideanSpace ℂ (Fin q)),
            MemRestrictionSobolev U 1 ((localRetardedOperator hU W Q).adjoint g) ∧
              restrictionSobolevNorm U 1 ((localRetardedOperator hU W Q).adjoint g) ≤
                (D * (Δ * C 1) * (1 + Hhi (1+μ))) * ‖g‖) := by
  obtain ⟨D, hD, hconvert⟩ := vector_restrictionSobolev_nat_bounds (d+1) q 1
  refine ⟨D, hD, ?_⟩
  intro Q μ Δ C Hhi hpos U W hU hW
  have hlocal (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (hT : T = Q ∨ T = Q.adjoint)
      {A : Set (Euclidean (d+1))} (hA : MeasurableSet A)
      (B : Set (Euclidean (d+1))) (u : LocalL2 A (EuclideanSpace ℂ (Fin q))) :
      MemRestrictionSobolev B 1 (localRetardedOperator hA B T u) ∧
        restrictionSobolevNorm B 1 (localRetardedOperator hA B T u) ≤
          (D * (Δ * C 1) * (1 + Hhi (1+μ))) * ‖u‖ := by
    have hu : MemVectorFourierSobolev ((1-1 : ℕ) : ℝ) (SmallSupport.zeroExtend hA u) := by
      simpa only [Nat.sub_self, Nat.cast_zero] using
        (show MemVectorFourierSobolev 0 (SmallSupport.zeroExtend hA u) from
          fun _ ↦ memFourierSobolev_zero _)
    obtain ⟨hreg, hbound⟩ := hpos 1 T hT (SmallSupport.zeroExtend hA u) hu
    obtain ⟨hmem, hn⟩ := hconvert _ hreg B (localRetardedOperator hA B T u)
      (restrictL2_coeFn B (T (SmallSupport.zeroExtend hA u))).symm
    refine ⟨hmem, hn.trans ?_⟩
    have he := mul_le_mul_of_nonneg_left hbound hD.le
    simpa only [Nat.sub_self, Nat.cast_zero, vectorFourierSobolevNorm_zero,
      LinearIsometry.norm_map, mul_add, mul_one, add_mul, mul_assoc] using he
  exact ⟨hlocal Q (Or.inl rfl) hU W, fun g ↦ by
    rw [localRetardedOperator_adjoint hU hW]
    exact hlocal Q.adjoint (Or.inr rfl) hW U g⟩

end JanetCartan.RegularSector.Characteristic.RetardedLocalization
