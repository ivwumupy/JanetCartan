module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderBounds

/-!
# Low frequencies of the original reflected Taylor remainder

The mixed jets in `TransportSymbol.GlobalNormBounds` also give unweighted
joint bounds, including at zero. These supply the missing low-frequency
part of the error estimate following `app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- Forget the frequency weights by expanding every tangent into physical
and frequency parts. Used at low frequencies of the original remainder in
`app:ch_background:eq:bg-real-symbol`; the mixed premise is precisely the
output of `exists_transportAmplitude_global_mixed_bound_of_primitiveNorms`. -/
theorem norm_iteratedFDeriv_global_le_of_mixed
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Variables n → F) (s : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ p : Variables n, ∀ k ≤ s, ∀ I : Finset (Fin k),
      ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k f p v‖ ≤
        A * ∏ j, ‖v j‖)
    (p : Variables n) (k : ℕ) (hk : k ≤ s) :
    ‖iteratedFDeriv ℝ k f p‖ ≤ 2 ^ s * A := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let v₀ : Fin k → Variables n := fun j ↦ ((v j).1, (v j).2.1, 0)
  let v₁ : Fin k → Variables n := fun j ↦ (0, 0, (v j).2.2)
  let M := iteratedFDeriv ℝ k f p
  have hv : v = v₁ + v₀ := by funext j; simp [v₁, v₀]
  change ‖M v‖ ≤ _
  conv_lhs => rw [hv, M.map_add_univ]
  have hterm (I : Finset (Fin k)) :
      ‖M (I.piecewise v₁ v₀)‖ ≤ A * ∏ j, ‖v j‖ := by
    have hb' := hb p k hk I (I.piecewise v₁ v₀)
      (by intro j hj; simp [Finset.piecewise, hj, v₁])
      (by intro j hj; simp [Finset.piecewise, hj, v₀])
    calc
      _ ≤ (1 + ‖p.2.2‖) ^ I.card * ‖M (I.piecewise v₁ v₀)‖ := by
        exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg p.2.2]))
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
    _ ≤ ∑ I : Finset (Fin k), ‖M (I.piecewise v₁ v₀)‖ := norm_sum_le _ _
    _ ≤ ∑ _I : Finset (Fin k), A * ∏ j, ‖v j‖ := Finset.sum_le_sum (fun I _ ↦ hterm I)
    _ = 2 ^ k * A * ∏ j, ‖v j‖ := by simp [Fintype.card_finset, mul_assoc]
    _ ≤ _ := by gcongr; norm_num

private def remainderFrequencyDilation (t : ℝ) : Variables n →L[ℝ] Variables n :=
  (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n × Euclidean n)).prod
    ((ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp
      (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n)) |>.prod
        (t • (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
          (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n))))

/-- The original normalized reflected remainder has a uniform unweighted
joint bound, including zero frequency. The constant precedes the amplitude
and its single high budget. Primitive jets cost `r+2`, source cutoff jets
cost `r+1`. The mixed premise is produced by `GlobalNormBounds`.
Source: the error paragraph following `app:ch_background:eq:bg-real-symbol`. -/
theorem exists_reflectedEntry_diagonalRemainder_global_bound_of_mixed
    (r : ℕ) (basis : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β)
    {Bβ : ℝ} (hBβ : 0 ≤ Bβ)
    (hβBound : ∀ k ≤ r + 1, ∀ y, ‖iteratedFDeriv ℝ k β y‖ ≤ Bβ)
    (i j : Fin n) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → SliceVariable n)
      (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2)),
      ContDiff ℝ ∞ (amplitude a J u Ω K) → ∀ A : ℝ, 0 ≤ A →
      (∀ p : Variables n, ∀ k ≤ r + 2, ∀ I : Finset (Fin k),
        ∀ v : Fin k → Variables n,
        (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
        (∀ j ∉ I, (v j).2.2 = 0) →
        (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) p v‖ ≤
          A * ∏ j, ‖v j‖) →
      ∀ p : Variables n, ∀ k ≤ r,
        ‖iteratedFDeriv ℝ k (fun q : Variables n ↦
          diagonalRemainderAmplitude basis
            (fun x y ξ ↦ (reflectedSymbolAmplitude a J u Ω K
              (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β q.1 q.2.1 q.2.2) p‖ ≤ C * A := by
  let t := 2 * Real.pi
  let D := max 1 (max ‖remainderFrequencyDilation (n := n) t‖
    ‖remainderFrequencyDilation (n := n) (-t)‖)
  have hD : 1 ≤ D := le_max_left _ _
  let L := Complex.ofRealCLM.comp (realMatrixEntry i j)
  let C₀ := ‖L‖ * (4 * (2 * Real.pi) ^ n) * 2 ^ (r + 2) * D ^ (r + 2)
  let C₁ := ‖(2 * Real.pi * Complex.I)⁻¹‖ * n * 2 ^ (r + 1) * Bβ * C₀
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  refine ⟨C₁ + 1, by positivity, ?_⟩
  intro a J u Ω K ha A hA hb
  let f := amplitude a J u Ω K
  have hf : ContDiff ℝ ∞ f := ha
  have hglobal := norm_iteratedFDeriv_global_le_of_mixed f (r + 2) hA hb
  have hscale (t' : ℝ) (ht' : ‖remainderFrequencyDilation (n := n) t'‖ ≤ D)
      (p : Variables n) (k : ℕ) (hk : k ≤ r + 2) :
      ‖iteratedFDeriv ℝ k (f ∘ remainderFrequencyDilation t') p‖ ≤
        2 ^ (r + 2) * A * D ^ (r + 2) := by
    apply (norm_iteratedFDeriv_comp_linear_le (remainderFrequencyDilation t') f hf k p).trans
    exact mul_le_mul (hglobal _ k hk)
      ((pow_le_pow_left₀ (norm_nonneg _) ht' _).trans (pow_le_pow_right₀ hD hk))
      (by positivity) (by positivity)
  let g := fun q : Variables n ↦ (2 * (2 * Real.pi) ^ n) •
    (f (remainderFrequencyDilation t q) + f (remainderFrequencyDilation (-t) q))
  have hg : ContDiff ℝ ∞ g := ((hf.comp (remainderFrequencyDilation t).contDiff).add
    (hf.comp (remainderFrequencyDilation (-t)).contDiff)).const_smul _
  let c := fun x y ξ ↦ (reflectedSymbolAmplitude a J u Ω K (x, y, t • ξ) i j : ℂ)
  have he : (fun q : Variables n ↦ c q.1 q.2.1 q.2.2) = L ∘ g := by
    funext q
    change _ = ((g q) i j : ℂ)
    simp [c, g, f, remainderFrequencyDilation, reflectedSymbolAmplitude, t, mul_add]
  have hc : ContDiff ℝ ∞ (fun q : Variables n ↦ c q.1 q.2.1 q.2.2) :=
    he ▸ L.contDiff.comp hg
  have hcg (p : Variables n) (k : ℕ) (hk : k ≤ r + 2) :
      ‖iteratedFDeriv ℝ k (fun q : Variables n ↦ c q.1 q.2.1 q.2.2) p‖ ≤ C₀ * A := by
    rw [he]
    apply (L.norm_iteratedFDeriv_comp_left hg.contDiffAt (by simp)).trans
    have hg' : ‖iteratedFDeriv ℝ k g p‖ ≤
        (4 * (2 * Real.pi) ^ n) * (2 ^ (r + 2) * A * D ^ (r + 2)) := by
      rw [show g = (2 * (2 * Real.pi) ^ n) •
          (f ∘ remainderFrequencyDilation t + f ∘ remainderFrequencyDilation (-t)) from rfl,
        iteratedFDeriv_const_smul_apply (i := k)
          (f := f ∘ remainderFrequencyDilation t + f ∘ remainderFrequencyDilation (-t))
          (((hf.comp (remainderFrequencyDilation t).contDiff).add
            (hf.comp (remainderFrequencyDilation (-t)).contDiff)).contDiffAt.of_le (by simp)),
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * (2 * Real.pi) ^ n),
        iteratedFDeriv_add_apply (i := k) (f := f ∘ remainderFrequencyDilation t)
          (g := f ∘ remainderFrequencyDilation (-t))
          ((hf.comp (remainderFrequencyDilation t).contDiff).contDiffAt.of_le (by simp))
          ((hf.comp (remainderFrequencyDilation (-t)).contDiff).contDiffAt.of_le (by simp))]
      have h₁ := hscale t ((le_max_left _ _).trans (le_max_right _ _)) p k hk
      have h₂ := hscale (-t) ((le_max_right _ _).trans (le_max_right _ _)) p k hk
      calc
        _ ≤ (2 * (2 * Real.pi) ^ n) *
            ((2 ^ (r + 2) * A * D ^ (r + 2)) + (2 ^ (r + 2) * A * D ^ (r + 2))) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h₁ h₂)) (by positivity)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left hg' (norm_nonneg _)).trans_eq (by dsimp [C₀]; ring)
  intro p k hk
  have hrem := norm_iteratedFDeriv_diagonalRemainderAmplitude_joint_le basis c β hc hβ p k
    (fun _ ↦ C₀ * A) (fun l hl _ _ ↦ hcg _ (l + 1) (by omega))
  have hsum : (∑ l ∈ Finset.range (k + 2), ((k + 1).choose l : ℝ) *
      ‖iteratedFDeriv ℝ l β p.2.1‖ * (C₀ * A)) ≤ 2 ^ (k + 1) * Bβ * (C₀ * A) := by
    calc
      _ ≤ ∑ l ∈ Finset.range (k + 2), ((k + 1).choose l : ℝ) * Bβ * (C₀ * A) := by
        apply Finset.sum_le_sum
        intro l hl
        gcongr
        exact hβBound l (by have := Finset.mem_range.mp hl; omega) _
      _ = _ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose (k + 1)
  apply hrem.trans
  simp only [Fintype.card_fin]
  calc
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * n * (2 ^ (k + 1) * Bβ * (C₀ * A)) := by gcongr
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * n * (2 ^ (r + 1) * Bβ * (C₀ * A)) := by
      gcongr
      norm_num
    _ = C₁ * A := by dsimp [C₁]; ring
    _ ≤ (C₁ + 1) * A := mul_le_mul_of_nonneg_right (by linarith) hA

end JanetCartan.ContinuumRow.TransportKernel
