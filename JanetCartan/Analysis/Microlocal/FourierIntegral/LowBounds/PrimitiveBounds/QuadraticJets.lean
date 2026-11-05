module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.SymbolBounds

/-!
# Bilinear budgets from the original normal-amplitude jets

For `app:ch_regular_base:eq:actual-normal-amplitude`, keep the sizes of the two
original amplitudes separate from the geometry. The consumer is the uniform
compact graph estimate in `LowBounds`. The original amplitudes include all
physical, angular, low-frequency and regularization cutoffs; their jets below
include the shoulders of those cutoffs. No transformed jet is an input.

The Hamilton/compatible-geometry construction supplies the original Jacobian
jets and determinant gap. The inverse-coefficient construction supplies the
actual inverse-coordinate jets. The parent supplies the original amplitude
jets and the support buffer, uniformly over regularization parameters.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The finite reserve used by the low normal PDO estimate in actual-calculus
Step 1. Pairing positions and changing to cycle frequency cost constants but
no extra derivative orders. -/
def primitiveNormalReserve (n : ℕ) : ℕ := 2 * (n + 1)

/-- Finite jets of the literal full normal have a bilinear budget in the
original amplitude sizes, including size zero. Constants are chosen before
both amplitudes and the actual geometry. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`, actual-calculus Step 1. -/
theorem exists_crossNormalAmplitude_bilinear_jet_bound (N : ℕ) (M L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (A B : E → E → Mat) (η : E → E → E → E)
      (J : E → E → E → E →L[ℝ] E) (Ω W : Set (NormalVariables n))
      (a b : ℝ), 0 ≤ a → 0 ≤ b → IsOpen Ω → IsOpen W →
      ContDiffOn ℝ ∞ (normalInverseCoordinates η) Ω →
      MapsTo (normalInverseCoordinates η) Ω W →
      ContDiffOn ℝ ∞ (normalInputCoefficients A B J) W →
      (∀ z ∈ W, δ ≤ |(J z.1 z.2.1 z.2.2).det|) →
      (∀ z ∈ W, ∀ i ≤ N,
        ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) z‖ ≤ M) →
      (∀ z ∈ W, ∀ i ≤ N,
        ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦ A q.1 q.2.2) z‖ ≤ a) →
      (∀ z ∈ W, ∀ i ≤ N,
        ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦ B q.2.1 q.2.2) z‖ ≤ b) →
      (∀ z ∈ Ω, ∀ i, 1 ≤ i → i ≤ N →
        ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) z‖ ≤ L) →
      ∀ z ∈ Ω, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
          crossNormalAmplitude A B η J q.1 q.2.1 q.2.2) z‖ ≤ C * a * b := by
  obtain ⟨R, hR, hrec⟩ := exists_reciprocalAbsNormalJacobian_jet_bound (n := n) N M hδ
  let P := (N.factorial : ℝ) * R * (max 1 M)^N
  let Q := (2 : ℝ)^N * P * (2 : ℝ)^N
  let C := (N.factorial : ℝ) * Q * (max 1 L)^N
  have hP : 0 < P := by dsimp [P]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A B η J Ω W a b ha hb hΩ hW hη hmap hinput hgap hJjet hAjet hBjet hinv z hz k hk
  let V : Set (E →L[ℝ] E) := {T | T.det ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage ContinuousLinearMap.continuous_det
  have hJ : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) W := hinput.fst
  have hA : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ A q.1 q.2.2) W := hinput.snd.fst
  have hB : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ B q.2.1 q.2.2) W := hinput.snd.snd
  have hdet : MapsTo (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) W V :=
    fun q hq ↦ abs_pos.mp (hδ.trans_le (hgap q hq))
  have hrecSmooth : ContDiffOn ℝ ∞ (fun T : E →L[ℝ] E ↦ |T.det|⁻¹) V :=
    fun T hT ↦ (contDiffAt_reciprocalAbsNormalJacobian hT).contDiffWithinAt
  have hs := hrecSmooth.comp hJ hdet
  have hsjet (q) (hq : q ∈ W) (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦ |(J q.1 q.2.1 q.2.2).det|⁻¹) q‖ ≤ P := by
    have hh := InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le hW hV hJ hrecSmooth
      hdet hq i (fun j hj ↦ hrec _ (by simpa using hJjet q hq 0 (Nat.zero_le N))
        (hgap q hq) j (hj.trans hi)) (fun j _ hj ↦ hJjet q hq j (hj.trans hi))
    apply hh.trans
    dsimp [P]
    have hf : (i.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hi
    gcongr
    exact le_max_left _ _
  let starL : Mat ≃ₗᵢ[ℝ] Mat :=
    { Matrix.conjTransposeLinearEquiv (Fin r) (Fin r) ℝ ℂ with
      norm_map' := Matrix.frobenius_norm_conjTranspose }
  have hstar := starL.toContinuousLinearEquiv.contDiff.comp_contDiffOn hB
  have hnum := hA.mul hstar
  have hnumjet (q) (hq : q ∈ W) (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦
        A q.1 q.2.2 * (B q.2.1 q.2.2).conjTranspose) q‖ ≤ (2 : ℝ)^N * a * b := by
    have hh := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
      (ContinuousLinearMap.mul ℝ Mat) (ContinuousLinearMap.opNorm_mul_le _ _)
      hW hA hstar ha hq i (fun j hj ↦ hAjet q hq j (hj.trans hi))
      (fun j hj ↦ (starL.norm_iteratedFDeriv_comp_left _ q j).trans_le
        (hBjet q hq j (hj.trans hi)))
    apply hh.trans
    gcongr
    norm_num
  let H := fun q : NormalVariables n ↦
    |(J q.1 q.2.1 q.2.2).det|⁻¹ • (A q.1 q.2.2 * (B q.2.1 q.2.2).conjTranspose)
  have hH : ContDiffOn ℝ ∞ H W := hs.smul hnum
  have hHjet (q) (hq : q ∈ W) (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i H q‖ ≤ Q * a * b := by
    have hh := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
      (ContinuousLinearMap.lsmul ℝ ℝ) ContinuousLinearMap.opNorm_lsmul_le
      hW hs hnum hP.le hq i (fun j hj ↦ hsjet q hq j (hj.trans hi))
      (fun j hj ↦ hnumjet q hq j (hj.trans hi))
    apply hh.trans
    calc
      _ ≤ (2 : ℝ)^N * P * ((2 : ℝ)^N * a * b) := by gcongr; norm_num
      _ = Q * a * b := by dsimp [Q]; ring
  change ‖iteratedFDeriv ℝ k (H ∘ normalInverseCoordinates η) z‖ ≤ _
  apply (InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le hΩ hW hη hH hmap hz k
    (fun i hi ↦ hHjet _ (hmap hz) i (hi.trans hk))
    (fun i hi hik ↦ hinv z hz i hi (hik.trans hk))).trans
  calc
    _ ≤ (N.factorial : ℝ) * (Q * a * b) * (max 1 L)^N := by
      have hf : (k.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hk
      gcongr
      exact le_max_left _ _
    _ = C * a * b := by dsimp [C]; ring

/-- The same bilinear budget holds for every jet of the buffered zero
extension. The support and inverse equations concern the original amplitudes;
no nondegeneracy is required outside the chart. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_extendedCrossNormalAmplitude_bilinear_jet_bound (N : ℕ) (M L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (S : E → E → ℝ) (A B : E → E → Mat) (η : E → E → E → E)
      (J : E → E → E → E →L[ℝ] E) (Ω W K : Set (NormalVariables n))
      (a b : ℝ), 0 ≤ a → 0 ≤ b → IsOpen Ω → IsOpen W →
      ContDiffOn ℝ ∞ (normalInverseCoordinates η) Ω →
      MapsTo (normalInverseCoordinates η) Ω W →
      ContDiffOn ℝ ∞ (normalInputCoefficients A B J) W →
      (∀ z ∈ W, δ ≤ |(J z.1 z.2.1 z.2.2).det|) →
      (∀ z ∈ W, ∀ i ≤ N,
        ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) z‖ ≤ M) →
      (∀ z ∈ W, ∀ i ≤ N,
        ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦ A q.1 q.2.2) z‖ ≤ a) →
      (∀ z ∈ W, ∀ i ≤ N,
        ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦ B q.2.1 q.2.2) z‖ ≤ b) →
      (∀ z ∈ Ω, ∀ i, 1 ≤ i → i ≤ N →
        ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) z‖ ≤ L) →
      (∀ z ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η z) = z) →
      (∀ z ∈ W, A z.1 z.2.2 ≠ 0 → B z.2.1 z.2.2 ≠ 0 → z ∈ K) →
      IsClosed (normalForwardCoordinates S '' K) → normalForwardCoordinates S '' K ⊆ Ω →
      ∀ z, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) z‖ ≤ C * a * b := by
  obtain ⟨C, hC, hbound⟩ := exists_crossNormalAmplitude_bilinear_jet_bound (n := n) (r := r) N M L hδ
  refine ⟨C, hC, ?_⟩
  intro S A B η J Ω W K a b ha hb hΩ hW hη hmap hinput hgap hJ hA hB hinv
    hright hsupp hclosed hbuffer z k hk
  by_cases hz : z ∈ Ω
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq A B η J hΩ hz k]
    exact hbound A B η J Ω W a b ha hb hΩ hW hη hmap hinput hgap hJ hA hB hinv z hz k hk
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq_zero S A B η J
      hmap hright hsupp hclosed hbuffer hz k, norm_zero]
    exact mul_nonneg (mul_nonneg hC.le ha) hb

end JanetCartan.FourierIntegral.LowBounds
