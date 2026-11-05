module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.CoefficientProducts
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.EnvelopeDerivatives

/-!
# Actual scalar terms of the ambient reconstruction

Local coefficient multiplication on the supplied classical jets, with every
jet estimate derived from its root. Consumed by the finite expansions in
`app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.IsometricEmbedding.Reconstruction
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Constant for a single ordered-jet term in
`app:ch_response:eq:response-reconstruction-grading`. -/
def reconstructionScalarTermConstant (d k ℓ : ℕ) (C B : ℕ → ℝ) : ℝ :=
  C 0 * ((2 * Real.pi) ^ ℓ * B ℓ) + localizedMultiplierConstant d k *
    ∑ r ∈ Finset.range (k + 1), C (k - r) * ((2 * Real.pi) ^ ℓ * B (r + ℓ))

/-- Positivity of the explicit term constant for
`app:ch_response:eq:response-reconstruction-grading`. -/
theorem reconstructionScalarTermConstant_nonneg (k ℓ : ℕ) {C B : ℕ → ℝ}
    (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r) :
    0 ≤ reconstructionScalarTermConstant d k ℓ C B := by
  unfold reconstructionScalarTermConstant
  exact add_nonneg (mul_nonneg (hC _) (mul_nonneg (by positivity) (hB _)))
    (mul_nonneg (localizedMultiplierConstant_pos d k).le
      (Finset.sum_nonneg fun r _ ↦ mul_nonneg (hC _)
        (mul_nonneg (by positivity) (hB _))))

/-- An actual L² representative of a local coefficient times a classical jet.
The only analytic envelope input is the root profile from
`app:ch_response:eq:response-graded-reduced` or `response-graded-source`.
The jet producer supplies identification and weak derivative recursion. -/
theorem exists_localizedScalarJet_bound (k m : ℕ) (hk : 0 < k)
    {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    {Ω : Set E} (hΩ : IsOpen Ω) (ψ c f : E → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Ω)
    (hc : ContDiffOn ℝ ∞ c Ω)
    (P C B : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hC : ∀ r, 0 ≤ C r)
    (hB : ∀ r, 0 ≤ B r) {A L K : ℝ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hψB : ∀ r, r ≤ k → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r ψ x‖ ≤ P r * L ^ r)
    (hcB : ∀ r, r ≤ k → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r c x‖ ≤ C r * L ^ r)
    (v : List (Fin d) → L2)
    (hv : ∀ is, is.length < m → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v is) (v (i :: is)))
    (hu : MemFourierSobolev (m : ℝ) (v []))
    (hub : ∀ p, p ≤ m → fourierSobolevNorm (p : ℝ) (v []) ≤ B p * A * K ^ p)
    (w : List (Fin d)) (hkm : k + w.length ≤ m)
    (hrep : v w =ᵐ[volume] euclideanCoordinateDerivList w f) :
    ∃ u : L2, (u =ᵐ[volume] fun x ↦ ψ x * c x * euclideanCoordinateDerivList w f x) ∧
      MemFourierSobolev s u ∧ fourierSobolevNorm s u ≤
        reconstructionScalarTermConstant d k w.length (reconstructionProductBudget P C) B *
          (A * K ^ w.length) * K ^ s := by
  let b := fun x ↦ ψ x * c x
  have hb : ContDiff ℝ ∞ b := reconstructionLocalizedCoefficient_contDiff hΩ hψ hc hsupp
  have hbs : HasCompactSupport b := hψs.mul_right
  have hbud := reconstructionLocalizedCoefficient_budget hΩ hψ hc hsupp P C hP hC
    (by linarith : 0 ≤ L) k hψB hcB
  have hj (p : ℕ) (hp : p ≤ k) := reconstructionJet_graded_bound m v hv B hu hub w p
    (by omega)
  have ht := localizedScalarProduct_real_graded_bound k hk hs hsk b hb hbs
    (reconstructionProductBudget P C) (fun p ↦ (2 * Real.pi) ^ w.length * B (p + w.length))
    (reconstructionProductBudget_nonneg hP hC)
    (fun p ↦ mul_nonneg (by positivity) (hB _))
    (mul_nonneg hA (pow_nonneg (by linarith) _)) hL hLK hbud (v w)
    (hj k le_rfl).1 (fun p hp ↦ (hj p hp).2)
  refine ⟨localizedScalarProduct b hb hbs (v w), ?_, ht.1, ?_⟩
  · filter_upwards [localizedScalarProduct_ae b hb hbs (v w), hrep] with x hx hvx
    exact hx.trans (congrArg (b x * ·) hvx)
  · simpa only [reconstructionScalarTermConstant, zero_add] using ht.2

private theorem reconstructionWeightedFourier_smul (s : ℝ) (q : ℂ) (u : L2) :
    weightedL2Fourier s (q • u) =ᵐ[volume] q • weightedL2Fourier s u := by
  have h : 𝓕 (q • u) = q • 𝓕 u := (fourierCLM ℂ L2).map_smul q u
  filter_upwards [Lp.coeFn_smul q (𝓕 u)] with x hx
  simp only [weightedL2Fourier, h, hx, Pi.smul_apply]
  exact smul_comm _ _ _

/-- Both complex quadratures, including the carrier factor, are retained in
`app:ch_response:eq:response-graded-derivative`. -/
theorem reconstructionScalar_smul {s : ℝ} {u : L2} (hu : MemFourierSobolev s u)
    (q : ℂ) : MemFourierSobolev s (q • u) ∧
      fourierSobolevNorm s (q • u) = ‖q‖ * fourierSobolevNorm s u := by
  refine ⟨(hu.const_smul q).ae_eq (reconstructionWeightedFourier_smul s q u).symm, ?_⟩
  unfold fourierSobolevNorm
  rw [eLpNorm_congr_ae (reconstructionWeightedFourier_smul s q u),
    eLpNorm_const_smul, ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]

/-- Assembly of the finite coordinate terms in
`app:ch_response:eq:response-reconstruction-grading`. Each term has an actual
classical jet and a local primitive coefficient budget. The elementary grade
inequality accounts for carrier powers; no reconstructed-field bound is assumed. -/
theorem exists_reconstructionJetSum_bound {I J : Type*} [Fintype I] [Fintype J]
    (k m b : ℕ) (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    {Ω : Set E} (hΩ : IsOpen Ω) (ψ : E → ℂ) (c : I → J → E → ℂ)
    (f : J → E → ℂ) (q : J → ℂ) (w : J → List (Fin d))
    (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Ω)
    (hc : ∀ i j, ContDiffOn ℝ ∞ (c i j) Ω)
    (P : ℕ → ℝ) (C B : J → ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hC : ∀ j r, 0 ≤ C j r) (hB : ∀ j r, 0 ≤ B j r)
    {A L K ρ : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hgrade : ∀ j, ‖q j‖ * K ^ (w j).length ≤ ρ ^ b)
    (hψB : ∀ r, r ≤ k → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r ψ x‖ ≤ P r * L ^ r)
    (hcB : ∀ i j r, r ≤ k → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (c i j) x‖ ≤ C j r * L ^ r)
    (v : J → List (Fin d) → L2)
    (hv : ∀ j is, is.length < m → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v j is) (v j (i :: is)))
    (hu : ∀ j, MemFourierSobolev (m : ℝ) (v j []))
    (hub : ∀ j p, p ≤ m → fourierSobolevNorm (p : ℝ) (v j []) ≤ B j p * A * K ^ p)
    (hkm : ∀ j, k + (w j).length ≤ m)
    (hrep : ∀ j, v j (w j) =ᵐ[volume] euclideanCoordinateDerivList (w j) (f j)) :
    ∃ R : PiLp 2 (fun _ : I ↦ L2),
      (∀ i, R i =ᵐ[volume] fun x ↦ ∑ j, q j *
        (ψ x * c i j x * euclideanCoordinateDerivList (w j) (f j) x)) ∧
      MemMatrixFourierSobolev s R ∧ matrixFourierSobolevNorm s R ≤
        ((Fintype.card I : ℝ) * ∑ j,
          reconstructionScalarTermConstant d k (w j).length
            (reconstructionProductBudget P (C j)) (B j)) * A * ρ ^ b * K ^ s := by
  classical
  have ht (i : I) (j : J) := exists_localizedScalarJet_bound k m hk hs hsk hΩ ψ
    (c i j) (f j) hψ hψs hsupp (hc i j) P (C j) (B j) hP (hC j) (hB j)
    hA hL hLK hψB (hcB i j) (v j) (hv j) (hu j) (hub j) (w j) (hkm j) (hrep j)
  choose u hue hum hubound using ht
  let T (j : J) := reconstructionScalarTermConstant d k (w j).length
    (reconstructionProductBudget P (C j)) (B j)
  have hT (j : J) : 0 ≤ T j := reconstructionScalarTermConstant_nonneg k _
    (reconstructionProductBudget_nonneg hP (hC j)) (hB j)
  have hscaled (i : I) (j : J) := reconstructionScalar_smul (hum i j) (q j)
  have hbound (i : I) (j : J) : fourierSobolevNorm s (q j • u i j) ≤
      T j * A * ρ ^ b * K ^ s := by
    rw [(hscaled i j).2]
    calc
      _ ≤ ‖q j‖ * (T j * (A * K ^ (w j).length) * K ^ s) :=
        mul_le_mul_of_nonneg_left (hubound i j) (norm_nonneg _)
      _ = (T j * A * K ^ s) * (‖q j‖ * K ^ (w j).length) := by ring
      _ ≤ (T j * A * K ^ s) * ρ ^ b := mul_le_mul_of_nonneg_left (hgrade j)
        (mul_nonneg (mul_nonneg (hT j) hA) (Real.rpow_nonneg (by linarith) _))
      _ = _ := by ring
  let R : PiLp 2 (fun _ : I ↦ L2) := WithLp.toLp 2 (fun i ↦ ∑ j, q j • u i j)
  have hsum (i : I) := fourierSobolev_finsetSum Finset.univ (fun j ↦ q j • u i j)
    (fun j _ ↦ (hscaled i j).1)
  refine ⟨R, ?_, fun i ↦ (hsum i).1, (matrixFourierSobolevNorm_le_sum s R).trans ?_⟩
  · intro i
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ q j • u i j),
      ae_all_iff.mpr (fun j ↦ Lp.coeFn_smul (q j) (u i j)),
      ae_all_iff.mpr (hue i)] with x hx hqx hux
    exact hx.trans (Finset.sum_congr rfl fun j _ ↦ by simp only [hqx j, Pi.smul_apply, smul_eq_mul, hux j])
  · calc
      _ ≤ ∑ _i : I, ∑ j, T j * A * ρ ^ b * K ^ s := by
        apply Finset.sum_le_sum
        intro i _
        exact (hsum i).2.trans (Finset.sum_le_sum fun j _ ↦ hbound i j)
      _ = _ := by simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]; ring

end JanetCartan.IsometricEmbedding.Reconstruction
