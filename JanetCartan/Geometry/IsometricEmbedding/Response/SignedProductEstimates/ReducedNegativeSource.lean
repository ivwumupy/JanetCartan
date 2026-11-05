module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative

/-!
# Negative Sobolev size of the complete reduced signed sources

The finite inverse remainder in `app:ch_pairs:prop:pairs-lag-sum` consumes
negative Sobolev bounds for the actual reduced vector source. Apply the
existing scalar negative-source estimate to its literal channels and use
the proved L² coordinate isometry. The full half stress contraction, source
cutoff and reduced cutoff all remain present.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open ResponseTransfer.SourceNegative Pseudodifferential Sampling.BackgroundModulation
variable {n N : ℕ}

/-- Both complete reduced signed sources have negative Sobolev size
`D_k * rho^(-k)` in the EXISTING vector Fourier space
(`app:ch_regular:eq:inverse-remainder`; `app:ch_pairs:prop:pairs-lag-sum`, Step 1).
The envelope cutoff is proved to leave the original modulated source unchanged.
All constants precede the varying phases, row, cutoffs, amplitudes and true
frequencies. The same stress contraction and source are retained; no estimate
on the inverse or its residual chains is assumed or asserted here. -/
theorem exists_reduced_signed_negative_source_constants
    {Senv : Set (Euclidean n)} (hSenv : IsCompact Senv)
    (Ssrc : Set (Euclidean n)) {c G ν : ℝ} (hc : 0 < c)
    (hν : 0 < ν) (hνone : ν < 1)
    (P X Y Z CQ C : ℕ → ℝ) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hZ : ∀ r, 0 ≤ Z r) (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U →
      ∀ (χ ψ η φp φm : Euclidean n → ℝ) (L ρp ρm : ℝ),
      SourceGeometry χ φp Ssrc c G L P X → SourceGeometry χ φm Ssrc c G L P X →
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Senv → tsupport ψ ⊆ U →
      EqOn ψ (fun _ ↦ 1) (tsupport χ) →
      1 ≤ ρp → 1 ≤ ρm → L ≤ ρp ^ (1 - ν) → L ≤ ρm ^ (1 - ν) →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
      ContDiffOn ℝ ∞ η U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r ψ x‖ ≤ Y r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r η x‖ ≤ Z r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q x‖ ≤ CQ r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      let p := modulatedSource χ φp (fun x ↦ η x • ((1 / 2 : ℝ) •
        complexStressContraction (Q x) (symmetricBilinearTensor (A x) (B x)))) ρp
      let m := modulatedSource χ φm (fun x ↦ η x • ((1 / 2 : ℝ) •
        complexStressContraction (Q x) (symmetricBilinearTensor (A x) ((B x).map conj)))) ρm
      ∃ hp : MemLp p 2 volume, ∃ hm : MemLp m 2 volume, ∀ k : ℕ,
        (MemVectorFourierSobolev (-(k : ℝ)) (hp.toLp p) ∧
          vectorFourierSobolevNorm (-(k : ℝ)) (hp.toLp p) ≤ D k * (ρp ^ k)⁻¹) ∧
        (MemVectorFourierSobolev (-(k : ℝ)) (hm.toLp m) ∧
          vectorFourierSobolevNorm (-(k : ℝ)) (hm.toLp m) ≤ D k * (ρm ^ k)⁻¹) := by
  obtain ⟨J, hJ, henv⟩ := exists_cutoff_reduced_signed_sobolev_constants (N := N)
    hSenv Y Z CQ C hY hZ hCQ hC
  let D := fun k ↦ (n : ℝ) * modulatedSourceNegativeConstant n k Ssrc c G ν P X J
  refine ⟨D, fun k ↦ mul_nonneg (Nat.cast_nonneg _) (modulatedSourceNegativeConstant_nonneg
    n k Ssrc c G ν P X J hc.le hX hJ), ?_⟩
  intro U hU χ ψ η φp φm L ρp ρm gp gm hψ hψS hψU hone hρp hρm hgapP hgapM
    Q A B hη hQ hA hB hψb hηb hQb hAb hBb
  dsimp only
  obtain ⟨hpm, hmm, henvs⟩ := henv U hU L gp.scale_one_le ψ η Q A B hψ hψS hψU
    hη hQ hA hB hψb hηb hQb hAb hBb
  have hfull (φ : Euclidean n → ℝ) (a : Euclidean n → EuclideanSpace ℂ (Fin n))
      (ρ : ℝ) (g : SourceGeometry χ φ Ssrc c G L P X)
      (hρ : 1 ≤ ρ) (hgap : L ≤ ρ ^ (1 - ν))
      (ha : MemLp (fun x ↦ ψ x • a x) 2 volume)
      (haB : ∀ i, SobolevEnvelopeBounds (fun x ↦ (ψ x • a x) i) (ha.eval_piLp i) 1 L J) :
      ∃ hs : MemLp (modulatedSource χ φ a ρ) 2 volume, ∀ k : ℕ,
        MemVectorFourierSobolev (-(k : ℝ)) (hs.toLp (modulatedSource χ φ a ρ)) ∧
        vectorFourierSobolevNorm (-(k : ℝ)) (hs.toLp (modulatedSource χ φ a ρ)) ≤
          D k * (ρ ^ k)⁻¹ := by
    have he : modulatedSource χ φ a ρ = modulatedSource χ φ (fun x ↦ ψ x • a x) ρ := by
      funext x
      by_cases hx : χ x = 0
      · simp only [modulatedSource, hx, zero_smul]
      · simp only [modulatedSource, hone (subset_tsupport χ hx), one_smul]
    rw [he]
    let b := fun x ↦ ψ x • a x
    have hb : MemLp (modulatedSource χ φ b ρ) 2 volume := source_memLp g ha ρ
    refine ⟨hb, fun k ↦ ?_⟩
    have hscalar (i : Fin n) :
        MemFourierSobolev (-(k : ℝ))
          ((hb.eval_piLp i).toLp (fun x ↦ modulatedSource χ φ b ρ x i)) ∧
        fourierSobolevNorm (-(k : ℝ))
          ((hb.eval_piLp i).toLp (fun x ↦ modulatedSource χ φ b ρ x i)) ≤
          modulatedSourceNegativeConstant n k Ssrc c G ν P X J * ρ ^ (-(k : ℝ)) := by
      have hec : (fun x ↦ modulatedSource χ φ b ρ x i) =
          modulatedSource χ φ (fun x ↦ (ψ x • a x) i) ρ := by
        funext x
        simp only [modulatedSource, b, PiLp.smul_apply]
      have heL := MemLp.toLp_congr (hb.eval_piLp i)
        (source_memLp g (ha.eval_piLp i) ρ) (Filter.Eventually.of_forall (congrFun hec))
      rw [heL]
      simpa only [mul_one] using
        modulatedSource_memFourierSobolev_and_norm_le g (haB i) le_rfl hρ hν hνone hgap k
    constructor
    · simpa only [MemVectorFourierSobolev, MemMatrixFourierSobolev,
        finiteL2CoordinateIsometry_toLp, PiLp.toLp_apply] using fun i ↦ (hscalar i).1
    · unfold vectorFourierSobolevNorm
      rw [finiteL2CoordinateIsometry_toLp]
      calc
        _ ≤ ∑ i : Fin n, fourierSobolevNorm (-(k : ℝ))
            ((hb.eval_piLp i).toLp (fun x ↦ modulatedSource χ φ b ρ x i)) :=
          matrixFourierSobolevNorm_le_sum (-(k : ℝ)) (WithLp.toLp 2 (fun i ↦
            (hb.eval_piLp i).toLp (fun x ↦ modulatedSource χ φ b ρ x i)))
        _ ≤ ∑ _i : Fin n, modulatedSourceNegativeConstant n k Ssrc c G ν P X J *
            ρ ^ (-(k : ℝ)) := Finset.sum_le_sum (fun i _ ↦ (hscalar i).2)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.rpow_neg (zero_le_one.trans hρ), Real.rpow_natCast, D, mul_assoc]
  obtain ⟨hps, hp⟩ := hfull φp _ ρp gp hρp hgapP hpm (fun i ↦ (henvs i).1)
  obtain ⟨hms, hm⟩ := hfull φm _ ρm gm hρm hgapM hmm (fun i ↦ (henvs i).2)
  exact ⟨hps, hms, fun k ↦ ⟨hp k, hm k⟩⟩

end JanetCartan.SignedProductEstimates
