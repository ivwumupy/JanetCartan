module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.RoughBounds.Integration

/-!
# Deterministic physical rough estimate with the original sample weights

Bounded sampled and continuum masses give
`app:ch_waves:eq:background-quadrature-rough` from classical physical jets.
The retained physical jets are produced in `RoughBounds.Retained`; carrier
matching uses the SAME retained family. This deduction is independent of the
L2 quadrature construction and holds for every shift realization.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.Sampling.RetainedBackground
open SeparatedSampling BackgroundQuadrature ColoredNormalComparison
open SamplingKernelBounds.Expectation

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The physical sample-minus-colored-integral bound, with the unchanged
nonnegative weights and the exact finite colored masks. Its only analytic
input is the physical jet bound, produced for the actual retained polynomial
by `exists_retained_background_physical_and_transport_budgets`
(`app:ch_waves:eq:background-quadrature-rough`). -/
theorem cNorm_background_sample_sub_colored_le
    {p : ℕ} {ψ : Point → ℝ} {B P : ℝ}
    {window : ℝ → ℝ} {M : ℝ}
    (hwindow : WindowBounds p window M) (hws : ContDiff ℝ ∞ window)
    (hψ : PatchBounds ψ B P) (hψs : ContDiff ℝ ∞ ψ)
    (H : (Fin 3 → Fin (p + 1)) → Point → Euclidean n → V)
    (hH : ∀ c, ContDiff ℝ ∞ (fun q : Euclidean n × Point ↦ H c q.2 q.1))
    {A : ℕ → ℝ} {r : ℕ} (hA : ∀ j ≤ r, 0 ≤ A j)
    (hj : ∀ j ≤ r, ∀ c z x, ‖iteratedFDeriv ℝ j (H c z) x‖ ≤ A j)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : Lattice → Point) :
    cNorm K r (fun x ↦
      (∑ a ∈ samples p B ψ window h U,
        weight ψ window h U a • H (color p a.1) (node h U a) x) -
      ∑ c, ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h))
        window h c z • (ψ z • H c z x)) ≤
      2 * (countConstant p B * (P * M ^ 3)) *
        (∑ j ∈ Finset.range (r + 1), A j) := by
  classical
  let C := ∑ j ∈ Finset.range (r + 1), A j
  have hC : 0 ≤ C := Finset.sum_nonneg fun j hj ↦
    hA j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hs (c) (z : Point) : ContDiff ℝ r (H c z) :=
    ((hH c).comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hb (c) (z : Point) : cNorm K r (H c z) ≤ C :=
    cNorm_le_sum_of_bounds hA (fun j hjr x _ ↦ hj j hjr c z x)
  let S : Euclidean n → V := fun x ↦ ∑ a ∈ samples p B ψ window h U,
    weight ψ window h U a • H (color p a.1) (node h U a) x
  let G : Lattice → Euclidean n → V := fun q x ↦
    ∫ z, (ψ z * blockWeight window h q z) • H (color p q) z x
  have hG (q) : ContDiff ℝ ∞ (G q) :=
    contDiff_weightedCarrierIntegral
      (hψs.mul (contDiff_blockWeight hws h q)) (compactSupport_patchWeight hψ q)
      (hH (color p q))
  have hGn (q : Lattice) (z : Point) : 0 ≤ ψ z * blockWeight window h q z :=
    mul_nonneg (hψ.nonneg z) (Finset.prod_nonneg fun _ _ ↦ hwindow.nonneg _)
  have hGb (q) : cNorm K r (G q) ≤
      (∫ z, ψ z * blockWeight window h q z) * C :=
    cNorm_weightedCarrierIntegral_le
      (integrable_patchWeight hψ hψs.continuous hws.continuous q) (hGn q)
      (hH (color p q)) hA (fun j hjr z x ↦ hj j hjr (color p q) z x) K
  have hsample : cNorm K r S ≤ countConstant p B * (P * M ^ 3) * C := by
    apply (cNorm_sum_smul_le _ _ hK (fun a _ ↦ hs _ _)).trans
    calc
      _ ≤ ∑ a ∈ samples p B ψ window h U, weight ψ window h U a * C := by
        apply Finset.sum_le_sum
        intro a _
        rw [Real.norm_of_nonneg (weight_nonneg hwindow hψ hh.le a)]
        exact mul_le_mul_of_nonneg_left (hb _ _) (weight_nonneg hwindow hψ hh.le a)
      _ = totalMass p B ψ window h U * C := by rw [← Finset.sum_mul]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (totalMass_le hwindow hψ hh hh₁) hC
  have hintegral : cNorm K r (fun x ↦
      ∑ q ∈ integerCube (blockCutoff p B h), G q x) ≤
        countConstant p B * (P * M ^ 3) * C := by
    apply (cNorm_sum_le _ hK (fun q _ ↦ (hG q).of_le (by simp))).trans
    apply (Finset.sum_le_sum fun q _ ↦ hGb q).trans
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (continuum_mass_le hwindow hψ hψs.continuous hws.continuous hh hh₁) hC
  have he (x : Euclidean n) :
      (∑ c, ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h))
        window h c z • (ψ z • H c z x)) =
      ∑ q ∈ integerCube (blockCutoff p B h), G q x := by
    rw [← sum_blockIntegrals_eq_sum_coloredMask_integrals _ hwindow hws.continuous
      hh.ne' (fun c z ↦ ψ z • H c z x)
      (fun c ↦ hψs.continuous.smul ((hH c).continuous.comp
        (continuous_const.prodMk continuous_id)))]
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    funext z
    simp only [smul_smul, mul_comm]
  simp_rw [he]
  have htri := cNorm_sub_le hK
    (show ContDiff ℝ r S from ContDiff.sum fun a _ ↦ (hs _ _).const_smul _)
    (show ContDiff ℝ r (fun x ↦ ∑ q ∈ integerCube (blockCutoff p B h), G q x) from
      ContDiff.sum fun q _ ↦ (hG q).of_le (by simp))
  exact htri.trans ((add_le_add hsample hintegral).trans_eq (by ring))

/-- The prescribed `C_r L^r` form of the deterministic rough bound, with
the constant before frequency, radial labels, amplitude scale and shifts.
This consumes the retained physical restrictions without spending any carrier
derivatives (`app:ch_waves:eq:background-quadrature-rough`). -/
theorem cNorm_background_sample_sub_colored_profile_le
    {p : ℕ} {ψ : Point → ℝ} {B P : ℝ} {window : ℝ → ℝ} {M : ℝ}
    (hwindow : WindowBounds p window M) (hws : ContDiff ℝ ∞ window)
    (hψ : PatchBounds ψ B P) (hψs : ContDiff ℝ ∞ ψ)
    (H : (Fin 3 → Fin (p + 1)) → Point → Euclidean n → V)
    (hH : ∀ c, ContDiff ℝ ∞ (fun q : Euclidean n × Point ↦ H c q.2 q.1))
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {r rpar : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hj : ∀ j ≤ r, ∀ c z x,
      ‖iteratedFDeriv ℝ j (H c z) x‖ ≤ A j * L ^ (j - rpar))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : Lattice → Point) :
    cNorm K r (fun x ↦
      (∑ a ∈ samples p B ψ window h U,
        weight ψ window h U a • H (color p a.1) (node h U a) x) -
      ∑ c, ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h))
        window h c z • (ψ z • H c z x)) ≤
      (2 * (countConstant p B * (P * M ^ 3)) *
        (∑ j ∈ Finset.range (r + 1), A j)) * L ^ r := by
  have hb (j : ℕ) (hjr : j ≤ r) (c) (z : Point) (x : Euclidean n) :
      ‖iteratedFDeriv ℝ j (H c z) x‖ ≤ A j * L ^ r :=
    (hj j hjr c z x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL ((Nat.sub_le j rpar).trans hjr)) (hA j))
  simpa only [← Finset.sum_mul, mul_assoc] using
    cNorm_background_sample_sub_colored_le hwindow hws hψ hψs H hH
      (fun j _ ↦ mul_nonneg (hA j) (pow_nonneg (zero_le_one.trans hL) r))
      hb hK hh hh₁ U

end JanetCartan.Sampling.RetainedBackground
