module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Assembly

/-!
# Diagonal specialization

The identity canonical chart supplies every geometric premise for the diagonal
phase, in both orientations (`app:ch_regular:lem:finite-chain`). Thus the uniform
mask and actual derivative-gap theorem applies without an additional phase
construction for diagonal factors.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph
open Set
open FourierIntegral
variable {n : ℕ}

private theorem diagonal_u_fderiv (u ξ : Euclidean n) :
    fderiv ℝ (fun v => inner ℝ v ξ) u = innerSL ℝ ξ := by
  have he : (fun v => inner ℝ v ξ) = innerSL ℝ ξ := by
    funext v
    exact real_inner_comm ξ v
  rw [he]
  exact (innerSL ℝ ξ).fderiv

private theorem diagonal_xi_fderiv (u ξ : Euclidean n) :
    fderiv ℝ (fun v => inner ℝ u v) ξ = innerSL ℝ u :=
  (innerSL ℝ u).fderiv

/-- The diagonal phase has forward chart control with unit low constants
on any input buffer and any actual domain (`app:ch_regular:lem:finite-chain`). -/
theorem diagonal_forwardChartControl (I D : Set (Euclidean n × Euclidean n)) :
    ForwardChartControl (fun u ξ => inner ℝ u ξ) id I D 1 1 := by
  constructor
  · intro u ξ _
    exact differentiable_inner (u,ξ)
  · intro y η _
    exact (diagonal_forwardRelation_iff y y η η).mpr ⟨rfl,rfl⟩
  · intro y η _ u ξ _
    simp only [id_eq, diagonal_xi_fderiv, one_mul, ← map_sub, innerSL_apply_norm]
    exact le_rfl
  · intro y η _ u ξ _
    simp only [diagonal_xi_fderiv, sub_self, norm_zero, one_mul]
    exact norm_nonneg _
  · intro y η _ u ξ _
    simp only [id_eq, diagonal_u_fderiv, one_mul, ← map_sub, innerSL_apply_norm]
    exact le_add_of_nonneg_left (norm_nonneg _)

/-- The literal reverse diagonal phase has the same identity chart and low
constants (`app:ch_regular:lem:finite-chain`). -/
theorem diagonal_reverseChartControl (I D : Set (Euclidean n × Euclidean n)) :
    ReverseChartControl (fun u ξ => inner ℝ u ξ) id I D 1 1 := by
  constructor
  · intro u ξ _
    exact differentiable_inner (u,ξ)
  · intro y η _
    exact (diagonal_forwardRelation_iff y y η η).mpr ⟨rfl,rfl⟩
  · intro y η _ u ξ _
    simp only [id_eq, diagonal_u_fderiv, one_mul, ← map_sub, innerSL_apply_norm]
    exact le_rfl
  · intro y η _ u ξ _
    simp only [diagonal_u_fderiv, sub_self, norm_zero, one_mul]
    exact norm_nonneg _
  · intro y η _ u ξ _
    simp only [id_eq, diagonal_xi_fderiv, one_mul, ← map_sub, innerSL_apply_norm]
    rw [norm_sub_rev y u]
    exact le_add_of_nonneg_right (norm_nonneg _)

/-- Complete diagonal specialization: the masks and actual complementary
amplitude-support gap in either orientation require only nested physical/chart
buffers (`app:ch_regular:lem:finite-chain`). All phase and inverse-chart premises
are discharged by the identity chart. -/
theorem exists_diagonal_bufferedLocalizers_joint_gap (backward : Bool)
    {K I J O : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hI : IsOpen I) (hKI : K ⊆ I)
    (hJ : IsCompact J) (hO : IsOpen O) (hJO : J ⊆ O) (hIJ : I ⊆ J) :
    ∃ (mi mo : LocalizerSymbol n) (δ : ℝ), 0 < δ ∧
      IsBufferedLocalizer mi K I ∧ IsBufferedLocalizer mo J O ∧
      tsupport mi ⊆ interior {q | mo q = 1} ∧
      ∀ (r : ℕ) (ρ : ℝ) (a : FullAmplitude n r) (χA χo : Euclidean n → ℝ)
        (x y : Euclidean n) (p : JointVariables (Euclidean n)),
        p ∈ tsupport (jointAmplitude ρ a mi mo χA χo x y) →
        δ ≤ ‖fderiv ℝ (jointPhase backward (fun u ξ => inner ℝ u ξ) x y) p‖ := by
  have H : ∀ _ : Unit, if backward then
      ReverseChartControl (fun u ξ => inner ℝ u ξ) id I univ 1 1
      else ForwardChartControl (fun u ξ => inner ℝ u ξ) id I univ 1 1 := by
    intro t
    cases backward
    · exact diagonal_forwardChartControl I univ
    · exact diagonal_reverseChartControl I univ
  obtain ⟨mi,mo,δ,hδ,hi,ho,hbuffer,hgap⟩ :=
    exists_uniform_bufferedLocalizers_joint_gap backward hK hI hKI hJ hO hJO
      (fun _ : Unit => fun u ξ => inner ℝ u ξ) (fun _ : Unit => id)
      (fun _ : Unit => univ) (fun _ _ hp => hIJ hp)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) H
  exact ⟨mi,mo,δ,hδ,hi,ho,hbuffer (),
    fun r ρ a χA χo x y p hp => hgap () r ρ a χA χo x y p hp (mem_univ _)⟩

end JanetCartan.FiniteChain.Graph
