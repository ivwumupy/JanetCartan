module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.PackedPhase
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.ComplementaryGaps

/-!
# Buffered squared-gradient gaps in a fixed boundary collar

For `app:ch_regular:lem:finite-chain`, this module discharges the gradient-gap
hypotheses of half-space integration by parts on compact complementary mask
supports. Both the normal collar width and the positive squared-gradient
constants are chosen uniformly before the external base parameters.
-/

@[expose] public noncomputable section

open Set
namespace JanetCartan.FiniteChain.Retarded
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Buffered proof masks yield a uniform tangential squared-gradient gap in
a fixed normal collar and a uniform full-gradient gap on the interior compact
set (`app:ch_regular:lem:finite-chain`). The input-base equations are retained.
The boundary collar uses tangential derivatives only. -/
theorem exists_buffered_packedPhase_gradient_gaps {X ι κ : Type*}
    [TopologicalSpace X] [Fintype ι] [Fintype κ] {K : Set X} (hK : IsCompact K)
    (eT : Module.Basis ι ℝ (TangentialVariables E))
    (eI : Module.Basis κ ℝ (ℝ × TangentialVariables E))
    {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage false R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (x : X → ℝ × TangentialVariables E)
    (hi : Continuous xi) (ho : Continuous xo) (hx : Continuous x)
    (hd : ∀ p ∈ K, 0 ≤ (x p).1)
    (hin : ∀ p ∈ K, (xi p, (x p).2.2.2) ∈ tsupport mi)
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (hout : ∀ p ∈ K, (xo p, (x p).2.2.1) ∈ tsupport (fun q => 1 - mo q)) :
    ∃ ε > 0, ∃ δT > 0, ∃ δI > 0, ∀ p ∈ K,
      (∀ d : ℝ, |d| ≤ ε → δT ≤ Localization.phaseGradientSquare eT
        (fun w => packedPhase (xi p) (xo p) (d, w)) (x p).2) ∧
      δI ≤ Localization.phaseGradientSquare eI (packedPhase (xi p) (xo p)) (x p) := by
  obtain ⟨δb, hb, hbgap⟩ := exists_complementary_boundary_gap hK hmo hbuffer xi xo
    (fun p => (x p).2.1.1) (fun p => (x p).2.2.1.1) (fun p => (x p).2.2.2.1)
    (fun p => (x p).2.1.2) (fun p => (x p).2.2.1.2) (fun p => (x p).2.2.2.2)
    hi ho (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) hin hoR hout
  obtain ⟨δi, hiδ, higap⟩ := exists_complementary_interior_gap hK hmo hbuffer xi xo
    (fun p => (x p).1) (fun p => (x p).2.1.1) (fun p => (x p).2.2.1.1)
    (fun p => (x p).2.2.2.1) (fun p => (x p).2.1.2)
    (fun p => (x p).2.2.1.2) (fun p => (x p).2.2.2.2)
    hi ho (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) hd hin hoR hout
  obtain ⟨δI, hδI, hI⟩ := exists_packedPhase_interior_gradient_gap hK eI xi xo x hi ho hx
    (fun p hp => hiδ.trans_le (higap p hp))
  have hcompact : IsCompact (K ×ˢ Icc (-δb / 2) (δb / 2)) := hK.prod isCompact_Icc
  obtain ⟨δT, hδT, hT⟩ := exists_packedPhase_tangential_gradient_gap hcompact eT
    (fun p : X × ℝ => xi p.1) (fun p : X × ℝ => xo p.1)
    (fun p : X × ℝ => (p.2, (x p.1).2)) (by fun_prop) (by fun_prop) (by fun_prop)
    (by
      intro p hp
      apply (half_pos hb).trans_le
      apply (hbgap p.1 hp.1).2 p.2
      exact abs_le.mpr ⟨by linarith [hp.2.1], hp.2.2⟩)
  refine ⟨δb / 2, half_pos hb, δT, hδT, δI, hδI, fun p hp => ⟨?_, hI p hp⟩⟩
  intro d hd'
  exact hT (p, d) ⟨hp, by have hh := abs_le.mp hd'; constructor <;> linarith [hh.1, hh.2]⟩
end JanetCartan.FiniteChain.Retarded
