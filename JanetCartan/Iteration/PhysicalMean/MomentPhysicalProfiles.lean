module

public import JanetCartan.Iteration.PhysicalMean.MomentTemplates
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Physical-only primitive profiles for the sampled moment templates

The phase producer supplies physical jets of the SAME frequency-dependent
inverse directions, not carrier or frequency derivatives. The two contractive
coordinate embeddings below specialize the expression calculus without losing
an order or changing its reserve. This is the primitive input consumed by the
scalar amplitude tester in `app:ch_mean_pairs:eq:raw-adjoint-moments`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels ContinuumRow

private theorem norm_iteratedFDeriv_comp_contraction
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] F) (hA : ‖A‖ ≤ 1) {f : F → G} (hf : ContDiff ℝ ∞ f) (q : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ q (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ q f (A x)‖ := by
  rw [A.iteratedFDeriv_comp_right hf x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : ‖A‖ ^ q ≤ 1 := pow_le_one₀ (norm_nonneg _) hA
  simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ q f (A x)))

private theorem physical_branchField_smooth {n : ℕ}
    (L : Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hL : ∀ h, ContDiff ℝ ∞ (L h)) (d : InitialCarrierDerivative n) (j : Fin n) :
    ContDiff ℝ ∞ (branchField (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0) d j) := by
  cases d with
  | initial h =>
      exact Complex.ofRealCLM.contDiff.comp
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hL h)).comp contDiff_snd)
  | carrier h => exact contDiff_const

/-- The actual sampled template has physical jets with the total unspent
reserve. Only the original amplitude's PHYSICAL jets and those of the inverse
directions occur, even when the latter depend on the frozen input frequency.
All constants are chosen from the word and primitive profile before histories
and samples (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledAdjointMomentTemplate_physical_jet_le
    {n : ℕ} (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    (ds : List (Euclidean (n - 1))) (t : AdjointMomentTemplate n)
    (ht : t ∈ adjointMomentTemplates (ds.map InitialCarrierDerivative.initial))
    (a : Euclidean n → ℂ) (ha : ContDiff ℝ ∞ a)
    (L : Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hL : ∀ h, ContDiff ℝ ∞ (L h)) (r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (x : Euclidean n)
    (hamp : ∀ i, ‖iteratedFDeriv ℝ i a x‖ ≤ B i * T ^ (i - r₀))
    (hcoeff : ∀ h ∈ ds, ∀ i, ‖iteratedFDeriv ℝ i (L h) x‖ ≤ B i * T ^ (i - r₀)) (q : ℕ) :
    ‖iteratedFDeriv ℝ q (fun y ↦
      t.1.evaluate (fun _ y h ↦ L h y) (fun _ _ _ ↦ 0) (fun _ y _ ↦ a y) 0 (0, y)) x‖ ≤
        adjointMomentJetConstant B (ds.map InitialCarrierDerivative.initial) q *
          T ^ (ds.length - t.2.length + q - r₀) := by
  let L' := fun (_ : CarrierParameter) (y : Euclidean n) h ↦ L h y
  let V' := fun (_ : CarrierParameter) (_ : Euclidean n) (_ : CarrierParameter) ↦ (0 : Euclidean n)
  let a' : AdjointAmplitude n := fun _ y _ ↦ a y
  have ha' (η : Euclidean (n - 1)) : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a' p.1 p.2 η) :=
    ha.comp contDiff_snd
  have hf := physical_branchField_smooth L hL
  have hmap := map_adjointMomentTemplates_eq_expansion L' V' a' ha' hf
    (ds.map InitialCarrierDerivative.initial)
  have ht' : t.toTerm L' V' a' ∈ adjointDerivativeExpansion L' V'
      (ds.map InitialCarrierDerivative.initial) a' := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have haB (i : ℕ) : ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ a' p.1 p.2 0) (0, x)‖ ≤
      B i * T ^ (i - r₀) :=
    (norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.snd ℝ CarrierParameter (Euclidean n))
      (ContinuousLinearMap.norm_snd_le ..) ha i (0, x)).trans (hamp i)
  have hLB : ∀ d ∈ ds.map InitialCarrierDerivative.initial, ∀ j i,
      ‖iteratedFDeriv ℝ i (branchField L' V' d j) (0, x)‖ ≤ B i * T ^ (i - r₀) := by
    intro d hd j i
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hd
    let P : Euclidean n →L[ℝ] ℂ := Complex.ofRealCLM.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j)
    have hP : ‖P‖ ≤ 1 := by
      apply P.opNorm_le_bound zero_le_one
      intro v
      simpa only [P, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
        PiLp.proj_apply, Complex.norm_real, one_mul] using PiLp.norm_apply_le v j
    have hp (i : ℕ) : ‖iteratedFDeriv ℝ i (fun y ↦ (L h y j : ℂ)) x‖ ≤
        ‖iteratedFDeriv ℝ i (L h) x‖ := by
      exact (P.norm_iteratedFDeriv_comp_left (hL h).contDiffAt (by simp)).trans
        ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _))
    exact (norm_iteratedFDeriv_comp_contraction
      (ContinuousLinearMap.snd ℝ CarrierParameter (Euclidean n))
      (ContinuousLinearMap.norm_snd_le ..) (P.contDiff.comp (hL h)) i (0, x)).trans
        ((hp i).trans (hcoeff h hh i))
  have hjet := norm_iteratedFDeriv_adjointExpansionTerm_le_reserve B hB
    (ds.map InitialCarrierDerivative.initial) L' V' a' ha' hf 0 (0, x) r₀ hT haB hLB
    (t.toTerm L' V' a') ht' q
  have hsm := t.1.contDiff_evaluate L' V' a' 0 (ha' 0) hf
  apply (norm_iteratedFDeriv_comp_contraction
    (ContinuousLinearMap.inr ℝ CarrierParameter (Euclidean n))
    (ContinuousLinearMap.norm_inr_le_one ℝ CarrierParameter (Euclidean n)) hsm q x).trans
  simpa only [AdjointMomentTemplate.toTerm, List.length_map, ContinuousLinearMap.inr_apply,
    Prod.mk.eta] using hjet

end JanetCartan.PhysicalMean
