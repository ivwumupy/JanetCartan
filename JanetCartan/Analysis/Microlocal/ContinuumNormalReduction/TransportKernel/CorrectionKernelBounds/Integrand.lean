module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.CompletionBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplierBounds.FarDerivatives.Partition

/-! # Physical jets of the correction integrand
The compact frequency error following `app:ch_background:eq:bg-symbol`.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n : ℕ}

private def physicalInsertion : (Euclidean n × Euclidean n) →L[ℝ] TransportSymbol.Variables n :=
  (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).prod
    ((ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).prod 0)

private theorem norm_physicalInsertion_le : ‖physicalInsertion (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp [physicalInsertion, Prod.norm_def]

/-- Fixing frequency and taking a matrix entry does not enlarge physical jets.
Used by the kernel estimate after `app:ch_background:eq:bg-symbol`. -/
theorem norm_iteratedFDeriv_physicalEntry_le
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) (i j : Fin n) (r : ℕ)
    (p : Euclidean n × Euclidean n) (k : Euclidean n) :
    ‖iteratedFDeriv ℝ r (fun q : Euclidean n × Euclidean n ↦
      (f (q.1, q.2, k) i j : ℂ)) p‖ ≤ ‖iteratedFDeriv ℝ r f (p.1, p.2, k)‖ := by
  let L := Complex.ofRealCLM.comp (realMatrixEntry i j)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro M
    change ‖(M i j : ℂ)‖ ≤ 1 * ‖M‖
    rw [Complex.norm_real, one_mul]
    exact (PiLp.norm_apply_le (WithLp.toLp 2 (M i)) j).trans
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (M i))) i)
  let g := fun q : TransportSymbol.Variables n ↦ f (q + (0, 0, k))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun q : Euclidean n × Euclidean n ↦ (f (q.1, q.2, k) i j : ℂ)) =
      L ∘ (g ∘ physicalInsertion) := by funext q; simp [L, g, physicalInsertion, realMatrixEntry]; rfl
  rw [he]
  apply (L.norm_iteratedFDeriv_comp_left
    (hg.comp physicalInsertion.contDiff).contDiffAt (by simp)).trans
  apply (mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
  rw [one_mul, physicalInsertion.iteratedFDeriv_comp_right hg p (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ r g (physicalInsertion p)‖ * ∏ _ : Fin r, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun _ _ ↦ norm_physicalInsertion_le)) (norm_nonneg _)
    _ = _ := by simp [g, physicalInsertion, iteratedFDeriv_comp_add_right]

private def physicalPhase (k : Euclidean n) : (Euclidean n × Euclidean n) →L[ℝ] ℝ :=
  (innerSL ℝ k).comp
    (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n) -
      ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n))

private theorem physicalPhase_apply (k : Euclidean n) (p : Euclidean n × Euclidean n) :
    physicalPhase k p = inner ℝ (p.1 - p.2) k := by
  simp [physicalPhase, real_inner_comm, inner_sub_right]

/-- Each physical phase derivative costs at most twice the frequency radius,
independently of the positions (`app:ch_background:eq:bg-symbol`). -/
theorem norm_iteratedFDeriv_correctionPhase_le {R : ℝ} {k : Euclidean n}
    (hk : ‖k‖ ≤ R) (r : ℕ) (p : Euclidean n × Euclidean n) :
    ‖iteratedFDeriv ℝ r (fun q : Euclidean n × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (q.1 - q.2) k)) p‖ ≤ (2 * R) ^ r := by
  have hR : 0 ≤ R := (norm_nonneg k).trans hk
  let L := physicalPhase k
  have hL : ‖L‖ ≤ 2 * R := by
    apply L.opNorm_le_bound (by positivity)
    intro q
    calc
      ‖L q‖ ≤ ‖q.1 - q.2‖ * ‖k‖ := by
        rw [physicalPhase_apply]; exact norm_inner_le_norm _ _
      _ ≤ (‖q.1‖ + ‖q.2‖) * R :=
        mul_le_mul (norm_sub_le _ _) hk (norm_nonneg _) (by positivity)
      _ ≤ (‖q‖ + ‖q‖) * R := mul_le_mul_of_nonneg_right
        (add_le_add (norm_fst_le q) (norm_snd_le q)) ((norm_nonneg _).trans hk)
      _ = (2 * R) * ‖q‖ := by ring
  have he : (fun q : Euclidean n × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (q.1 - q.2) k)) =
      (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ))) ∘ L := by
    funext q; simp [NormalComparison.oscillatoryFactor, L, physicalPhase_apply]
  have hf : ContDiff ℝ ∞ (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ))) := by
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  rw [he, L.iteratedFDeriv_comp_right hf p (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [FourierIntegral.SourceBounds.norm_iteratedFDeriv_physical_exp, one_mul]
  simpa using Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin r))) (fun _ _ ↦ norm_nonneg L)
    (fun _ _ ↦ hL)

/-- Leibniz constant for the physical jets of the bounded-frequency error.
It involves only the order and frequency radius (`app:ch_background:eq:bg-symbol`). -/
def correctionIntegrandJetConstant (r : ℕ) (R : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * (2 * R) ^ l

/-- The matrix amplitude enters linearly in every finite physical jet of the
literal correction integrand (`app:ch_background:eq:bg-symbol`). -/
theorem norm_iteratedFDeriv_correctionIntegrand_le
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) {R A : ℝ} {k : Euclidean n} (hk : ‖k‖ ≤ R)
    (r : ℕ) (p : Euclidean n × Euclidean n)
    (hb : ∀ l ≤ r, ‖iteratedFDeriv ℝ l f (p.1, p.2, k)‖ ≤ A) (i j : Fin n) :
    ‖iteratedFDeriv ℝ r (fun q : Euclidean n × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (q.1 - q.2) k) *
        (f (q.1, q.2, k) i j : ℂ)) p‖ ≤ correctionIntegrandJetConstant r R * A := by
  have hR : 0 ≤ R := (norm_nonneg k).trans hk
  have hp : ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (q.1 - q.2) k)) := by
    unfold NormalComparison.oscillatoryFactor
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((contDiff_fst.sub contDiff_snd).inner ℝ contDiff_const)))).cexp
  have ha : ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean n ↦
      (f (q.1, q.2, k) i j : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (((realMatrixEntry i j).contDiff.comp hf).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)))
  apply (norm_iteratedFDeriv_mul_le hp ha p (by simp : (r : ℕ∞ω) ≤ ∞)).trans
  rw [correctionIntegrandJetConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_correctionPhase_le hk l p)
      (Nat.cast_nonneg _))
    ((norm_iteratedFDeriv_physicalEntry_le hf i j (r - l) p k).trans
      (hb _ (Nat.sub_le _ _))) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))

end JanetCartan.ContinuumRow.TransportKernel
