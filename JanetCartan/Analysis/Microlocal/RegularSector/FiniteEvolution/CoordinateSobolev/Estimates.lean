module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Fourier
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.RetardedOperators

/-!
# Signed estimates for the same operators in physical coordinates

The premises below are the exact estimates produced by `PhysicalCutoff` and
`FiniteEvolution.PhysicalOperators`. Coordinate conjugation preserves their
constants, coefficient profile and fixed shift. Finite summation adds constants
only. Negative orders concern L² inputs, without a distribution-completion claim.
Consumers: the finite physical solver and complete residual in
`app:ch_regular_base:eq:sector-theorem-solution`, `sector-theorem-residual`, and
`energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace JanetCartan.RegularSector.FiniteEvolution
open Characteristic.EvolutionIntegral Characteristic.UniformEvolution Pseudodifferential
variable {d q : ℕ}
local notation "H" => SpacetimeL2 d q

/-- Transfer a chart estimate, retaining both tame terms and their exact
constants (`sector-theorem-solution`, `sector-theorem-residual`). -/
theorem physicalOperator_sobolev_bound
    (i : Fin (d+1)) (T : H →L[ℂ] H) (s t C K : ℝ)
    (hT : ∀ u, MemVectorFourierSobolev s u →
      MemVectorFourierSobolev t (T u) ∧
      vectorFourierSobolevNorm t (T u) ≤ C * (vectorFourierSobolevNorm s u + K * ‖u‖))
    (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev t (physicalOperator i T u) ∧
    vectorFourierSobolevNorm t (physicalOperator i T u) ≤
      C * (vectorFourierSobolevNorm s u + K * ‖u‖) := by
  simpa only [physicalOperator_apply, memVectorFourierSobolev_physicalPullbackL2_symm,
    vectorFourierSobolevNorm_physicalPullbackL2_symm,
    vectorFourierSobolevNorm_physicalPullbackL2, LinearIsometryEquiv.norm_map] using
    hT (physicalPullbackL2 i u) ((memVectorFourierSobolev_physicalPullbackL2 i s u).mpr hu)

/-- Transfer an estimate with a single signed Sobolev input norm. This applies
in particular to negative integers and H⁻¹ → L² on L² data (`negative-duality`). -/
theorem physicalOperator_signed_bound
    (i : Fin (d+1)) (T : H →L[ℂ] H) (s t C : ℝ)
    (hT : ∀ u, MemVectorFourierSobolev t (T u) ∧
      vectorFourierSobolevNorm t (T u) ≤ C * vectorFourierSobolevNorm s u) (u : H) :
    MemVectorFourierSobolev t (physicalOperator i T u) ∧
      vectorFourierSobolevNorm t (physicalOperator i T u) ≤ C * vectorFourierSobolevNorm s u := by
  simpa only [physicalOperator_apply, memVectorFourierSobolev_physicalPullbackL2_symm,
    vectorFourierSobolevNorm_physicalPullbackL2_symm,
    vectorFourierSobolevNorm_physicalPullbackL2] using hT (physicalPullbackL2 i u)

/-- Both orientations of the positive integer estimate, with the same profile
and fixed shift. `o=0` is order zero and `o=1` is gain one. The premise is the
positive clause produced by `PhysicalOperators` (`measured-adjoint`). -/
theorem physicalOperator_positive_integer_bounds
    (i : Fin (d+1)) (T : H →L[ℂ] H) (o μ : ℕ) (C K : ℕ → ℝ)
    (hT : ∀ s : ℕ, ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ C s *
        (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u + K (s+μ) * ‖u‖))
    (s : ℕ) (V : H →L[ℂ] H)
    (hV : V = physicalOperator i T ∨ V = (physicalOperator i T).adjoint)
    (u : H) (hu : MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u) :
    MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ C s *
        (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u + K (s+μ) * ‖u‖) := by
  rcases hV with rfl | rfl
  · exact physicalOperator_sobolev_bound i T _ _ _ _ (hT s T (Or.inl rfl)) u hu
  · rw [physicalOperator_adjoint]
    exact physicalOperator_sobolev_bound i T.adjoint _ _ _ _
      (hT s T.adjoint (Or.inr rfl)) u hu

/-- Both negative integer estimates for the actual physical map and its
literal adjoint, with no distribution-completion extension (`negative-duality`). -/
theorem physicalOperator_negative_integer_bounds
    (i : Fin (d+1)) (T : H →L[ℂ] H) (o μ : ℕ) (C K : ℕ → ℝ)
    (hT : ∀ k : ℕ, ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
      vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤ C (k+o) * K (k+o+μ) *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u)
    (k : ℕ) (V : H →L[ℂ] H)
    (hV : V = physicalOperator i T ∨ V = (physicalOperator i T).adjoint) (u : H) :
    MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
      vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤ C (k+o) * K (k+o+μ) *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u := by
  rcases hV with rfl | rfl
  · exact physicalOperator_signed_bound i T _ _ _ (hT k T (Or.inl rfl)) u
  · rw [physicalOperator_adjoint]
    exact physicalOperator_signed_bound i T.adjoint _ _ _ (hT k T.adjoint (Or.inr rfl)) u

/-- The endpoint of the same negative estimate is the literal L² norm,
with exactly the same coefficient order (`finite-gap-theorem`). -/
theorem physicalOperator_HminusOne_to_L2
    (i : Fin (d+1)) (T : H →L[ℂ] H) (C : ℝ)
    (hT : ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      ‖V u‖ ≤ C * vectorFourierSobolevNorm (-1) u)
    (V : H →L[ℂ] H)
    (hV : V = physicalOperator i T ∨ V = (physicalOperator i T).adjoint) (u : H) :
    ‖V u‖ ≤ C * vectorFourierSobolevNorm (-1) u := by
  rcases hV with rfl | rfl
  · simpa only [physicalOperator_apply, LinearIsometryEquiv.norm_map,
      vectorFourierSobolevNorm_physicalPullbackL2] using hT T (Or.inl rfl) (physicalPullbackL2 i u)
  · rw [physicalOperator_adjoint]
    simpa only [physicalOperator_apply, LinearIsometryEquiv.norm_map,
      vectorFourierSobolevNorm_physicalPullbackL2] using
      hT T.adjoint (Or.inr rfl) (physicalPullbackL2 i u)

private theorem finite_vector_sobolev_sum {ι : Type*} [Fintype ι]
    (s : ℝ) (f : ι → H) (hf : ∀ p, MemVectorFourierSobolev s (f p)) :
    MemVectorFourierSobolev s (∑ p, f p) ∧
      vectorFourierSobolevNorm s (∑ p, f p) ≤ ∑ p, vectorFourierSobolevNorm s (f p) := by
  classical
  have h (a : Fin q) := fourierSobolev_finsetSum Finset.univ
    (fun p ↦ finiteL2CoordinateIsometry volume (f p) a) (fun p _ ↦ hf p a)
  constructor
  · intro a
    simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] using (h a).1
  · let b : ι → EuclideanSpace ℝ (Fin q) := fun p ↦ WithLp.toLp 2
      (fun a ↦ fourierSobolevNorm s (finiteL2CoordinateIsometry volume (f p) a))
    change ‖_‖ ≤ ∑ p, ‖b p‖
    apply le_trans (b := ‖∑ p, b p‖) ?_ (norm_sum_le _ _)
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro a _
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simp only [Real.norm_eq_abs, WithLp.ofLp_sum, Finset.sum_apply, map_sum, b]
    rw [abs_of_nonneg (fourierSobolevNorm_nonneg _ _), abs_of_nonneg
      (Finset.sum_nonneg (fun p _ ↦ fourierSobolevNorm_nonneg s
        (finiteL2CoordinateIsometry volume (f p) a)))]
    exact (h a).2

/-- Finite physical sums retain Sobolev membership and the exact sum of tame
bounds. Each chart may have its own coefficient profile; no uniformization
or extra profile is assumed (`energy-complete-residual`). -/
theorem finitePhysicalOperator_sobolev_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) (s t : ℝ) (C K : ι → ℝ)
    (hT : ∀ p u, MemVectorFourierSobolev s u →
      MemVectorFourierSobolev t (T p u) ∧
      vectorFourierSobolevNorm t (T p u) ≤ C p *
        (vectorFourierSobolevNorm s u + K p * ‖u‖))
    (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev t (finitePhysicalOperator index T u) ∧
      vectorFourierSobolevNorm t (finitePhysicalOperator index T u) ≤
        ∑ p, C p * (vectorFourierSobolevNorm s u + K p * ‖u‖) := by
  have hp p := physicalOperator_sobolev_bound (index p) (T p) s t (C p) (K p) (hT p) u hu
  obtain ⟨hm, hb⟩ := finite_vector_sobolev_sum t
    (fun p ↦ physicalOperator (index p) (T p) u) (fun p ↦ (hp p).1)
  simpa only [finitePhysicalOperator, sum_apply] using
    And.intro hm (hb.trans (Finset.sum_le_sum (fun p _ ↦ (hp p).2)))

/-- Finite summation of the negative estimates is on the same L² inputs,
with the same signed orders (`sector-theorem-residual`). -/
theorem finitePhysicalOperator_signed_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) (s t : ℝ) (C : ι → ℝ)
    (hT : ∀ p u, MemVectorFourierSobolev t (T p u) ∧
      vectorFourierSobolevNorm t (T p u) ≤ C p * vectorFourierSobolevNorm s u) (u : H) :
    MemVectorFourierSobolev t (finitePhysicalOperator index T u) ∧
      vectorFourierSobolevNorm t (finitePhysicalOperator index T u) ≤
        (∑ p, C p) * vectorFourierSobolevNorm s u := by
  have hp p := physicalOperator_signed_bound (index p) (T p) s t (C p) (hT p) u
  obtain ⟨hm, hb⟩ := finite_vector_sobolev_sum t
    (fun p ↦ physicalOperator (index p) (T p) u) (fun p ↦ (hp p).1)
  simpa only [finitePhysicalOperator, sum_apply, Finset.sum_mul] using
    And.intro hm (hb.trans (Finset.sum_le_sum (fun p _ ↦ (hp p).2)))

/-- Both orientations of a finite physical sum retain the same common
coefficient profile and fixed shift, adding only the chart constants
(`sector-theorem-solution`, `sector-theorem-residual`, `measured-adjoint`). -/
theorem finitePhysicalOperator_positive_integer_bounds {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) (o μ : ℕ)
    (C : ι → ℕ → ℝ) (K : ℕ → ℝ)
    (hT : ∀ p, ∀ s : ℕ, ∀ V : H →L[ℂ] H, (V = T p ∨ V = (T p).adjoint) → ∀ u,
      MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ C p s *
        (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u + K (s+μ) * ‖u‖))
    (s : ℕ) (V : H →L[ℂ] H)
    (hV : V = finitePhysicalOperator index T ∨ V = (finitePhysicalOperator index T).adjoint)
    (u : H) (hu : MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u) :
    MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ (∑ p, C p s) *
        (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u + K (s+μ) * ‖u‖) := by
  rcases hV with rfl | rfl
  · simpa only [Finset.sum_mul] using finitePhysicalOperator_sobolev_bound index T
      _ _ (fun p ↦ C p s) (fun _ ↦ K (s+μ)) (fun p ↦ hT p s (T p) (Or.inl rfl)) u hu
  · rw [finitePhysicalOperator_adjoint]
    simpa only [Finset.sum_mul] using finitePhysicalOperator_sobolev_bound index
      (fun p ↦ (T p).adjoint) _ _ (fun p ↦ C p s) (fun _ ↦ K (s+μ))
      (fun p ↦ hT p s (T p).adjoint (Or.inr rfl)) u hu

/-- The finite negative integer bounds and literal-adjoint bounds have the
same coefficient profile and shift as their chart producers (`negative-duality`). -/
theorem finitePhysicalOperator_negative_integer_bounds {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) (o μ : ℕ)
    (C : ι → ℕ → ℝ) (K : ℕ → ℝ)
    (hT : ∀ p, ∀ k : ℕ, ∀ V : H →L[ℂ] H, (V = T p ∨ V = (T p).adjoint) → ∀ u,
      MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
      vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤ C p (k+o) * K (k+o+μ) *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u)
    (k : ℕ) (V : H →L[ℂ] H)
    (hV : V = finitePhysicalOperator index T ∨ V = (finitePhysicalOperator index T).adjoint)
    (u : H) :
    MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
      vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤ (∑ p, C p (k+o)) * K (k+o+μ) *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u := by
  rcases hV with rfl | rfl
  · simpa only [Finset.sum_mul] using finitePhysicalOperator_signed_bound index T _ _
      (fun p ↦ C p (k+o) * K (k+o+μ)) (fun p ↦ hT p k (T p) (Or.inl rfl)) u
  · rw [finitePhysicalOperator_adjoint]
    simpa only [Finset.sum_mul] using finitePhysicalOperator_signed_bound index
      (fun p ↦ (T p).adjoint) _ _ (fun p ↦ C p (k+o) * K (k+o+μ))
      (fun p ↦ hT p k (T p).adjoint (Or.inr rfl)) u

/-- The finite residual's H⁻¹ → L² endpoint, including its literal adjoint.
This is the `o=1, k=0` negative integer estimate, on L² data
(`app:ch_regular_base:eq:finite-gap-theorem`). -/
theorem finitePhysicalOperator_HminusOne_to_L2 {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) (C : ι → ℝ)
    (hT : ∀ p, ∀ V : H →L[ℂ] H, (V = T p ∨ V = (T p).adjoint) → ∀ u,
      ‖V u‖ ≤ C p * vectorFourierSobolevNorm (-1) u)
    (V : H →L[ℂ] H)
    (hV : V = finitePhysicalOperator index T ∨ V = (finitePhysicalOperator index T).adjoint)
    (u : H) : ‖V u‖ ≤ (∑ p, C p) * vectorFourierSobolevNorm (-1) u := by
  have h (p : ι) (V : H →L[ℂ] H) (hV : V = T p ∨ V = (T p).adjoint) (v : H) :
      MemVectorFourierSobolev 0 (V v) ∧
        vectorFourierSobolevNorm 0 (V v) ≤ C p * vectorFourierSobolevNorm (-1) v :=
    ⟨fun _ ↦ memFourierSobolev_zero _, by simpa using hT p V hV v⟩
  rcases hV with rfl | rfl
  · simpa only [vectorFourierSobolevNorm_zero] using
      (finitePhysicalOperator_signed_bound index T (-1) 0 C
        (fun p ↦ h p (T p) (Or.inl rfl)) u).2
  · rw [finitePhysicalOperator_adjoint]
    simpa only [vectorFourierSobolevNorm_zero] using
      (finitePhysicalOperator_signed_bound index (fun p ↦ (T p).adjoint) (-1) 0 C
        (fun p ↦ h p (T p).adjoint (Or.inr rfl)) u).2

end JanetCartan.RegularSector.FiniteEvolution
