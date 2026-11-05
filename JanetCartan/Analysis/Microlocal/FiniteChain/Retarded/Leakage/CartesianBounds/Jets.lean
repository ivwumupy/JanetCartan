module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Leakage.CompactKernel
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Grades.MixedJets

/-!
# Cartesian jets of the concrete retarded kernels

The existing Cartesian jets are bounded by the full output differential, with
their exact total order. This supplies the derivative step in the common kernel
estimate of `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
open scoped ContDiff
open JanetCartan.RetardedSobolev JanetCartan.RetardedSobolev.Spaces

namespace JanetCartan.FiniteChain.Retarded.Leakage

variable {Y F : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Unit transverse words consume exactly their length in the full derivative
order (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_transverseJet_le {f : ℝ × Y → F}
    (hf : ContDiff ℝ ∞ f) (vs : List Y) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1)
    (j : ℕ) (x : ℝ × Y) :
    ‖iteratedFDeriv ℝ j (transverseJet vs f) x‖ ≤
      ‖iteratedFDeriv ℝ (vs.length + j) f x‖ := by
  induction vs generalizing j with
  | nil =>
    change ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ (0 + j) f x‖
    rw [Nat.zero_add]
  | cons v vs ih =>
    have hs := contDiff_transverseJet hf vs
    rw [transverseJet, transverseDeriv_eq_fderiv v (hs.differentiable (by simp))]
    calc
      _ ≤ ‖(0, v)‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (transverseJet vs f)) x‖ :=
        norm_iteratedFDeriv_clm_apply_const
          (hs.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)
      _ ≤ ‖iteratedFDeriv ℝ j (fderiv ℝ (transverseJet vs f)) x‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (by simpa using hv v (by simp))
      _ = ‖iteratedFDeriv ℝ (j + 1) (transverseJet vs f) x‖ :=
        norm_iteratedFDeriv_fderiv
      _ ≤ ‖iteratedFDeriv ℝ (vs.length + (j + 1)) f x‖ :=
        ih (fun w hw => hv w (by simp [hw])) (j + 1)
      _ = _ := congrArg (fun l : ℕ => ‖iteratedFDeriv ℝ l f x‖) (by simp only [List.length_cons]; omega)

/-- A time jet is the full differential evaluated on unit time vectors
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_timeJet_le_iteratedFDeriv {f : ℝ × Y → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ℝ × Y) :
    ‖timeJet j f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  rw [timeJet, iteratedDeriv_eq_iteratedFDeriv,
    KernelDecay.outputJet_apply_eq_jointJet hf]
  apply ((iteratedFDeriv ℝ j f x).le_opNorm _).trans
  simp

/-- Every existing Cartesian jet is controlled at its actual total order;
there is no loss depending on the number of integrations by parts
(`app:ch_regular:lem:finite-chain`). -/
theorem norm_cartesianJet_le_iteratedFDeriv {n m : ℕ}
    {f : ℝ × (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (i : JetIndex n m) (p : (Fin n → ℝ) × ℝ) :
    ‖jet i f p‖ ≤ ‖iteratedFDeriv ℝ (i.1.val + i.2.2.val) f (p.2, p.1)‖ := by
  apply (norm_timeJet_le_iteratedFDeriv (contDiff_transverseJet hf _) _ _).trans
  have h := norm_iteratedFDeriv_transverseJet_le hf
    (List.ofFn (fun j => Pi.single (i.2.1 j) 1)) (by
      intro v hv
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      rw [Pi.norm_single, norm_one]) i.2.2.val (p.2, p.1)
  rw [List.length_ofFn] at h
  exact h

end JanetCartan.FiniteChain.Retarded.Leakage
