module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Diagonal
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.ShellBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalSmooth

/-!
# Mixed jets to rescaled joint jets

The conversion used by the actual diagonal remainder following
`app:ch_background:eq:bg-real-symbol`. Each frequency direction cancels one
power of the shell radius; summing physical/frequency choices costs `2^k`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol
variable {n : ℕ}

private def frequencyScale (t : ℝ) : Variables n →L[ℝ] Variables n :=
  (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n × Euclidean n)).prod
    ((ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp
      (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n)) |>.prod
        (t • (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
          (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n))))

/-- The weighted mixed jets supplied by `GlobalNormBounds` control the joint
jet after any signed frequency dilation on the unit annulus. This is the
conversion consumed by the reflected shell estimate in
`app:ch_background:eq:bg-real-symbol`. -/
theorem norm_iteratedFDeriv_frequencyScale_le_of_mixed
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Variables n → F) (hf : ContDiff ℝ ∞ f) (s : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ p : Variables n, ∀ k ≤ s, ∀ I : Finset (Fin k),
      ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k f p v‖ ≤
        A * ∏ j, ‖v j‖)
    (t : ℝ) (p : Variables n) (hp : 1 ≤ ‖p.2.2‖) (k : ℕ) (hk : k ≤ s) :
    ‖iteratedFDeriv ℝ k (fun q : Variables n ↦ f (q.1, q.2.1, t • q.2.2)) p‖ ≤
      2 ^ s * A := by
  classical
  change ‖iteratedFDeriv ℝ k (f ∘ frequencyScale t) p‖ ≤ _
  rw [(frequencyScale t).iteratedFDeriv_comp_right hf p (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let v₀ : Fin k → Variables n := fun j ↦ ((v j).1, (v j).2.1, 0)
  let v₁ : Fin k → Variables n := fun j ↦ (0, 0, (v j).2.2)
  let M := iteratedFDeriv ℝ k f (frequencyScale t p)
  have hexp : (fun j ↦ frequencyScale t (v j)) = (fun j ↦ t • v₁ j) + v₀ := by
    funext j
    simp [frequencyScale, v₀, v₁]
  change ‖M (fun j ↦ frequencyScale t (v j))‖ ≤ _
  rw [hexp, M.map_add_univ]
  have hterm (I : Finset (Fin k)) :
      ‖M (I.piecewise (fun j ↦ t • v₁ j) v₀)‖ ≤ A * ∏ j, ‖v j‖ := by
    have he : I.piecewise (fun j ↦ t • v₁ j) v₀ =
        I.piecewise (fun j ↦ t • I.piecewise v₁ v₀ j) (I.piecewise v₁ v₀) := by
      funext j
      by_cases hj : j ∈ I <;> simp [Finset.piecewise, hj]
    rw [he, M.map_piecewise_smul]
    simp only [Finset.prod_const, norm_smul, norm_pow, Real.norm_eq_abs]
    have hb' := hb (frequencyScale t p) k hk I (I.piecewise v₁ v₀)
      (by intro j hj; simp [Finset.piecewise, hj, v₁])
      (by intro j hj; simp [Finset.piecewise, hj, v₀])
    have hw : |t| ≤ 1 + ‖(frequencyScale t p).2.2‖ := by
      change |t| ≤ 1 + ‖t • p.2.2‖
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg t]
    calc
      _ ≤ (1 + ‖(frequencyScale t p).2.2‖) ^ I.card *
          ‖M (I.piecewise v₁ v₀)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) hw _) (norm_nonneg _)
      _ ≤ A * ∏ j, ‖I.piecewise v₁ v₀ j‖ := hb'
      _ ≤ A * ∏ j, ‖v j‖ := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        intro j _
        by_cases hj : j ∈ I
        · simp only [Finset.piecewise, ite_eq_left hj, v₁, Prod.norm_def, norm_zero,
            max_eq_right (norm_nonneg _)]
          exact (norm_snd_le (v j).2).trans (norm_snd_le (v j))
        · simp only [Finset.piecewise, ite_eq_right hj, v₀, Prod.norm_def, norm_zero,
            max_eq_left (norm_nonneg _)]
          exact max_le (norm_fst_le _) ((norm_fst_le (v j).2).trans (norm_snd_le _))
  calc
    _ ≤ ∑ I : Finset (Fin k), ‖M (I.piecewise (fun j ↦ t • v₁ j) v₀)‖ := norm_sum_le _ _
    _ ≤ ∑ _I : Finset (Fin k), A * ∏ j, ‖v j‖ := Finset.sum_le_sum (fun I _ ↦ hterm I)
    _ = 2 ^ k * A * ∏ j, ‖v j‖ := by simp [Fintype.card_finset, mul_assoc]
    _ ≤ _ := by gcongr; norm_num

end JanetCartan.ContinuumRow.TransportKernel
