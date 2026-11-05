module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Basic

/-!
# Uniform literal-phase profiles

Compact parameter sets give all-order phase profiles for
`KernelDecay.norm_fourierKernel_le_of_halfSpace_data`, as required in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped ContDiff
open Set
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
variable {A V W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
private theorem contDiff_joint_iteratedFDeriv (f : A → V → W) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : A × V => iteratedFDeriv ℝ j (f p.1) p.2) := by
  induction j with
  | zero =>
    convert
      (continuousMultilinearCurryFin0 ℝ V W).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hf using 1
    funext p
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  | succ j ih =>
    have hd : ContDiff ℝ ∞ (fun p : A × V =>
        fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) := by
      apply ContDiff.fderiv (f := fun p : A × V => iteratedFDeriv ℝ j (f p.1))
        (g := fun p => p.2) (m := ∞) ?_ contDiff_snd (by simp)
      exact ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    convert
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) W).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hd using 1
    funext p
    rw [iteratedFDeriv_succ_eq_comp_left]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local fun_prop] ContDiff.inner

/-- Joint smoothness of the phase gradient, including both external bases
(`app:ch_regular:lem:finite-chain`). The upper branch is the literal adjoint. -/
theorem contDiff_joint_literalPhase_fderiv (upper : Bool) :
    ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E) =>
      fderiv ℝ (literalPhase upper p.1.1 p.1.2) p.2) := by
  apply ContDiff.fderiv (f := fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E) =>
      literalPhase upper p.1.1 p.1.2)
    (g := fun p => p.2) (m := ∞) ?_ contDiff_snd (by simp)
  unfold Function.uncurry literalPhase packedPhase LocalizedKernel.packedUpperPhase phase adjointPhase
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- Uniform all-order phase-gradient bounds on an arbitrary compact joint
support (`app:ch_regular:lem:finite-chain`). No gap is imposed on this carrier.
The profile precedes the derivative scale, frequency and integration order. -/
theorem exists_uniform_literalPhase_profile {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (upper : Bool)
    (xi xo : X → ℝ × E) (x : X → ℝ × TangentialVariables E)
    (hi : Continuous xi) (ho : Continuous xo) (hx : Continuous x) :
    ∃ P : ℕ → ℝ, (∀ j, 0 ≤ P j) ∧ ∀ p ∈ K, ∀ j, ∀ L : ℝ, 1 ≤ L →
      ‖iteratedFDeriv ℝ j (fderiv ℝ (literalPhase upper (xi p) (xo p))) (x p)‖ ≤
        P j * L ^ j := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (literalPhase upper (xi p) (xo p))) (x p)‖ ≤ C := by
    intro j
    have hc := (contDiff_joint_iteratedFDeriv
      (fun b : (ℝ × E) × (ℝ × E) => fderiv ℝ (literalPhase upper b.1 b.2))
      (contDiff_joint_literalPhase_fderiv upper) j).continuous
    exact hK.exists_bound_of_continuousOn (hc.comp ((hi.prodMk ho).prodMk hx)).continuousOn
  choose C hC using hb
  refine ⟨fun j => max 0 (C j), fun j => le_max_left _ _, ?_⟩
  intro p hp j L hL
  exact ((hC j p hp).trans (le_max_right _ _)).trans
    (le_mul_of_one_le_right (le_max_left _ _) (one_le_pow₀ hL))

end JanetCartan.FiniteChain.Retarded.KernelDecay
