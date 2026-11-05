module

public import JanetCartan.Analysis.ODE.SmoothDependence.LocalExistence

/-!
# The linear variational initial value problem

The first-variation equation in `app:ch_regular_base:lem:buffered-interpolation`
is an affine ODE on continuous linear maps. This file proves its existence and
uniqueness with explicit coefficient and time bounds. It does not assume or prove
that a nonlinear flow is differentiable in its initial values.
-/

@[expose] public section

open Metric Set
open scoped NNReal Topology

namespace JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the affine first-variation
field has Lipschitz constant bounded by the norm of its linear coefficient. -/
lemma lipschitzWith_affine_variational (A : E →L[ℝ] E) (B : P →L[ℝ] E) :
    LipschitzWith ‖A‖₊ (fun J : P →L[ℝ] E ↦ A.comp J + B) := by
  apply LipschitzWith.of_dist_le_mul
  intro J H
  simp only [dist_eq_norm, add_sub_add_right_eq_sub, ← ContinuousLinearMap.comp_sub,
    coe_nnnorm]
  exact A.opNorm_comp_le (J - H)

/-- `app:ch_regular_base:lem:buffered-interpolation`: uniqueness for the
inhomogeneous operator-valued variational equation on an open time interval. -/
theorem variational_solution_unique {A : ℝ → E →L[ℝ] E} {B : ℝ → P →L[ℝ] E}
    {J H : ℝ → P →L[ℝ] E} {a b t₀ : ℝ} {K : ℝ≥0}
    (hA : ∀ t ∈ Ioo a b, ‖A t‖ ≤ K) (ht₀ : t₀ ∈ Ioo a b)
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J ((A t).comp (J t) + B t) t)
    (hH : ∀ t ∈ Ioo a b, HasDerivAt H ((A t).comp (H t) + B t) t)
    (hinit : J t₀ = H t₀) : EqOn J H (Ioo a b) := by
  exact ODE_solution_unique_of_mem_Ioo
    (s := fun _ ↦ univ) (K := K)
    (fun t ht ↦ ((lipschitzWith_affine_variational (A t) (B t)).weaken
      (by exact_mod_cast hA t ht)).lipschitzOnWith) ht₀
    (fun t ht ↦ ⟨hJ t ht, mem_univ _⟩) (fun t ht ↦ ⟨hH t ht, mem_univ _⟩) hinit

/-- `app:ch_regular_base:lem:buffered-interpolation`: existence of the
inhomogeneous operator-valued variational solution under an explicit time bound.
This constructs a candidate variation; identification with a derivative of the
nonlinear flow requires a separate differentiable-dependence theorem. -/
theorem exists_variational_solution [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {B : ℝ → P →L[ℝ] E}
    {a b : ℝ} (t₀ : Icc a b) (J₀ : P →L[ℝ] E) {R K M : ℝ≥0}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hAnorm : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) (hBnorm : ∀ t ∈ Icc a b, ‖B t‖ ≤ M)
    (htime : (K * (‖J₀‖ + R) + M) * max (b - t₀) (t₀ - a) ≤ R) :
    ∃ J : ℝ → P →L[ℝ] E, J t₀ = J₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt J ((A t).comp (J t) + B t) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, J t ∈ closedBall J₀ R) := by
  let L : ℝ≥0 := K * (‖J₀‖₊ + R) + M
  have hpl : IsPicardLindelof (fun t J ↦ (A t).comp J + B t) t₀ J₀ R 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact ((lipschitzWith_affine_variational (A t) (B t)).weaken
        (by exact_mod_cast hAnorm t ht)).lipschitzOnWith
    · intro J _
      exact (hA.clm_comp continuousOn_const).add hB
    · intro t ht J hJ
      calc
        ‖(A t).comp J + B t‖ ≤ ‖(A t).comp J‖ + ‖B t‖ := norm_add_le _ _
        _ ≤ ‖A t‖ * ‖J‖ + ‖B t‖ := add_le_add ((A t).opNorm_comp_le J) le_rfl
        _ ≤ K * (‖J₀‖ + R) + M := by
          gcongr
          · exact hAnorm t ht
          · have := mem_closedBall_iff_norm.mp hJ
            have hn := norm_le_norm_sub_add J J₀
            linarith
          · exact hBnorm t ht
        _ = L := by simp [L]
    · simpa [L] using htime
  obtain ⟨Φ, hinit, hd, hrange, _, _⟩ := exists_localFlow_with_range hpl
  have hJ₀ : J₀ ∈ closedBall J₀ (0 : ℝ≥0) := mem_closedBall_self le_rfl
  exact ⟨fun t ↦ Φ (J₀, t), hinit J₀ hJ₀, hd J₀ hJ₀, hrange J₀ hJ₀⟩

end JanetCartan.ODE
