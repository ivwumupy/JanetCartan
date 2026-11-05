module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Amplitude
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.ReflectedBounds

/-!
# Physical entry budgets for the full reflected carrier amplitude

For `app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:eq:bg-real-symbol`, transfer the published mixed transport
jets to the exact paired-position amplitude. The primitive norm theorems in
`CarrierNormalRealization.PrimitiveBudget` discharge the mixed input. The
extra physical derivative is consumed by `ContinuumCommutator.Translation.Assembly`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol ContinuumNormal TransportKernel
open Pseudodifferential AmplitudeBound
variable {n N : ℕ}

private def fullPhysicalInclusion : Euclidean (2 * n) →L[ℝ] Variables n :=
  freezingOutputProjection.prod (freezingSourceProjection.prod 0)

/-- The full paired amplitude inherits uniform physical entry jets from the
mixed transport jets, without any extra physical cutoff. The fixed constant
precedes the amplitude and its single budget (`app:ch_background:prop:bg-frame`,
Step 1). The final primitive producers below discharge both analytic inputs. -/
theorem exists_fullReflectedMatrixAmplitude_bounds_of_mixed (s : ℕ) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → SliceVariable n)
      (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)),
      ContDiff ℝ ∞ (amplitude a J u Ω S) → ∀ A : ℝ, 0 ≤ A →
      (∀ p : Variables n, ∀ k ≤ s, ∀ I : Finset (Fin k),
        ∀ v : Fin k → Variables n,
        (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
        (∀ j ∉ I, (v j).2.2 = 0) →
        (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k (amplitude a J u Ω S) p v‖ ≤
          A * ∏ j, ‖v j‖) →
      ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)) ∧
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) s (C * A) := by
  classical
  choose C hC hb using fun i j : Fin n ↦
    SourceConvergence.exists_reflectedEntry_joint_bound_of_mixed (N := N) s i j
  let E := (∑ i, ∑ j, C i j) + 1
  have hE : 0 < E := by
    have : 0 ≤ ∑ i, ∑ j, C i j :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hC i j).le
    dsimp [E]
    linarith
  have hCE (i j : Fin n) : C i j ≤ E := by
    calc
      C i j ≤ ∑ j, C i j := Finset.single_le_sum (fun j _ ↦ (hC i j).le) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, C i j := Finset.single_le_sum
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hC i j).le) (Finset.mem_univ i)
      _ ≤ E := le_add_of_nonneg_right zero_le_one
  let D := max 1 ‖fullPhysicalInclusion (n := n)‖
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨E * D ^ s, mul_pos hE (pow_pos (zero_lt_one.trans_le hD) _), ?_⟩
  intro a J u Ω S ha A hA hm
  have hentry (i j : Fin n) := hb i j a J u Ω S ha A hA hm
  have hsmooth (i j : Fin n) : ContDiff ℝ ∞
      (fun p : Euclidean n × Euclidean (2 * n) ↦
        fullReflectedMatrixAmplitude a J u Ω S p.1 p.2 i j) :=
    (hentry i j).1.comp
      ((freezingOutputProjection.contDiff.comp contDiff_snd).prodMk
        ((freezingSourceProjection.contDiff.comp contDiff_snd).prodMk contDiff_fst))
  refine ⟨?_, ?_⟩
  · have he : Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S) =
        fun p : Euclidean n × Euclidean (2 * n) ↦
          ∑ i : Fin n, ∑ j : Fin n,
            fullReflectedMatrixAmplitude a J u Ω S p.1 p.2 i j •
              (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℂ) := by
      funext p
      ext i j
      simp [Matrix.single, Matrix.sum_apply, ite_and, Function.uncurry_def]
    rw [he]
    exact ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦
      (hsmooth i j).smul contDiff_const
  · intro i j ξ is his z
    let f := fun q : Variables n ↦
      (reflectedSymbolAmplitude a J u Ω S (q.1, q.2.1, (2 * Real.pi) • q.2.2) i j : ℂ)
    have hf : ContDiff ℝ ∞ f := (hentry i j).1
    apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv
      ((hsmooth i j).comp (contDiff_const.prodMk contDiff_id)) is z).trans
    have ht := norm_iteratedFDeriv_comp_linear_le fullPhysicalInclusion
      (fun p ↦ f ((0, 0, ξ) + p)) (hf.comp (contDiff_const.add contDiff_id)) is.length z
    simp only [iteratedFDeriv_comp_add_left'] at ht
    have hnorm : ‖fullPhysicalInclusion (n := n)‖ ^ is.length ≤ D ^ s :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ hD his)
    calc
      _ ≤ ‖iteratedFDeriv ℝ is.length f
          (freezingOutputProjection z, freezingSourceProjection z, ξ)‖ *
            ‖fullPhysicalInclusion (n := n)‖ ^ is.length := by
        simpa [f, Function.comp_def, fullPhysicalInclusion, fullReflectedMatrixAmplitude] using ht
      _ ≤ (C i j * A) * D ^ s :=
        mul_le_mul ((hentry i j).2 _ _ his) hnorm (by positivity)
          (mul_nonneg (hC i j).le hA)
      _ ≤ (E * A) * D ^ s := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCE i j) hA) (by positivity)
      _ = (E * D ^ s) * A := by ring

end JanetCartan.ContinuumRow.CarrierNormalRealization
