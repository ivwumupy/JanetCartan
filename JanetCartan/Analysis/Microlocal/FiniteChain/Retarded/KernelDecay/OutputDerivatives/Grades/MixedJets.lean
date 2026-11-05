module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Factorization
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Jets

/-!
# Joint derivatives control output jets

The mixed output/frequency derivatives in `app:ch_regular:eq:high-amplitude`
are used by the output amplitude estimate for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
variable {V Z F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A partial output jet is the joint jet in pure output directions. This
retains all mixed derivatives when the frequency is subsequently differentiated
(`app:ch_regular:eq:high-amplitude`). -/
theorem outputJet_apply_eq_jointJet {f : V × Z → F} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (v : Fin m → V) (x : V) (z : Z) :
    iteratedFDeriv ℝ m (fun y => f (y, z)) x v =
      iteratedFDeriv ℝ m f (x, z) (fun i => (v i, 0)) := by
  let p : V →L[ℝ] V × Z := (ContinuousLinearMap.id ℝ V).prod 0
  let g : V × Z → F := fun q => f ((0, z) + q)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have he : (fun y => f (y, z)) = g ∘ p := by funext y; simp [g, p]
  rw [he, p.iteratedFDeriv_comp_right hg x (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  dsimp [g]
  rw [iteratedFDeriv_comp_add_left]
  simp [p]

/-- Unit output directions cost no operator norm. Integration order `j`
uses precisely the joint primitive derivative order `m+j`, supplying the
fixed offset `m` in `app:ch_regular:eq:chain-tail`. -/
theorem norm_iteratedFDeriv_outputJet_apply_le {f : V × Z → F}
    (hf : ContDiff ℝ ∞ f) (m j : ℕ) (v : Fin m → V)
    (hv : ∀ i, ‖v i‖ ≤ 1) (x : V) (z : Z) :
    ‖iteratedFDeriv ℝ j (fun ξ => iteratedFDeriv ℝ m (fun y => f (y, ξ)) x v) z‖ ≤
      ‖iteratedFDeriv ℝ (m + j) f (x, z)‖ := by
  let w : Fin m → V × Z := fun i => (v i, 0)
  let e := ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => V × Z) F w
  have he : ‖e‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change ‖a w‖ ≤ 1 * ‖a‖
    rw [one_mul]
    apply (a.le_opNorm w).trans
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => by simpa [w] using hv i)
  have hd : ContDiff ℝ ∞ (iteratedFDeriv ℝ m f) := hf.iteratedFDeriv_right (by simp)
  have hs := e.contDiff.comp hd
  simp_rw [outputJet_apply_eq_jointJet hf]
  change ‖iteratedFDeriv ℝ j (fun ξ => (e ∘ iteratedFDeriv ℝ m f) (x, ξ)) z‖ ≤ _
  apply (norm_iteratedFDeriv_symbol_slice_le hs j x z).trans
  apply (e.norm_iteratedFDeriv_comp_left hd.contDiffAt (by simp)).trans
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ m f) (x, z)‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ = _ := by rw [one_mul, LocalSobolev.FiniteOrder.norm_iteratedFDeriv_iteratedFDeriv]

end JanetCartan.FiniteChain.Retarded.KernelDecay
