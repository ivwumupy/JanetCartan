module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.ScalarTerms
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.Expansion

/-!
# Sobolev displacement bound for the actual completed variation

The four terms of `app:ch_response:eq:response-graded-displacement` are assembled
from primitive local coefficient and phase-gradient budgets and root envelope
profiles. All source tensor coordinates are included (the Frobenius convention).
The separate smooth-jet producer supplies only representatives and recursion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.IsometricEmbedding.Reconstruction
namespace JanetCartan.ResponseTransfer
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The value, derivative, phase, and source slots of
`app:ch_response:eq:response-reconstruction-grading`. -/
abbrev ReconstructionDisplacementSlot (n : ℕ) :=
  Fin n ⊕ ((Fin n × Fin n) ⊕ ((Fin n × Fin n) ⊕ (Fin n × Fin n)))

/-- Classical envelope derivative selected by each displacement term in
`app:ch_response:eq:response-graded-displacement`. -/
def reconstructionDisplacementWord : ReconstructionDisplacementSlot n → List (Fin n)
  | .inl _ => []
  | .inr (.inl ij) => [ij.1]
  | .inr (.inr _) => []

/-- Primitive product budget for each displacement slot. The phase and source
slots each contain two slow factors (`app:ch_response:eq:response-reconstruction-grading`). -/
def reconstructionDisplacementBudget (C : ℕ → ℝ) :
    ReconstructionDisplacementSlot n → ℕ → ℝ
  | .inl _ => C
  | .inr (.inl _) => C
  | .inr (.inr _) => reconstructionProductBudget C C

/-- Constant independent of all four scales in
`app:ch_response:eq:response-graded-displacement`. -/
def reconstructionDisplacementConstant (n N k : ℕ) (P C B : ℕ → ℝ) : ℝ :=
  (N : ℝ) * ∑ j : ReconstructionDisplacementSlot n,
    reconstructionScalarTermConstant n k (reconstructionDisplacementWord j).length
      (reconstructionProductBudget P (reconstructionDisplacementBudget C j)) B

set_option maxHeartbeats 800000 in
/-- The SAME completed variation has the displacement representative and bound
of `app:ch_response:eq:response-graded-displacement`. Only primitive coefficient,
cutoff and phase-gradient budgets are assumed; products and derivative envelope
bounds are derived. The parent must instantiate the supplied scalar root jets.
No global normal-rank hypothesis is required. -/
theorem completedVariationComplex_displacement_graded
    (k : ℕ) (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    (F : E → Euclidean N) {Ω : Set E} (hΩ : IsOpen Ω)
    (φ χ ψ : E → ℝ) (g : E → EuclideanSpace ℂ (Fin n))
    (a : E → Matrix (Fin n) (Fin n) ℂ)
    (hφ : Differentiable ℝ φ) (hg : Differentiable ℝ g)
    (hψ : ContDiff ℝ ∞ (fun x ↦ (ψ x : ℂ)))
    (hψs : HasCompactSupport (fun x ↦ (ψ x : ℂ)))
    (hsupp : tsupport (fun x ↦ (ψ x : ℂ)) ⊆ Ω)
    (hχ : ContDiffOn ℝ ∞ (fun x ↦ (χ x : ℂ)) Ω)
    (hphase : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ ((partialDeriv φ x i : ℝ) : ℂ)) Ω)
    (hV : ∀ l j, ContDiffOn ℝ ∞ (reconstructionValueEntry F l j) Ω)
    (hD : ∀ l ij, ContDiffOn ℝ ∞ (reconstructionDerivativeEntry F l ij) Ω)
    (hS : ∀ l ij, ContDiffOn ℝ ∞ (reconstructionSourceEntry F l ij) Ω)
    (P C B : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hC : ∀ r, 0 ≤ C r)
    (hB : ∀ r, 0 ≤ B r) {A L K ρ : ℝ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K) (hKρ : K ≤ ρ)
    (hψB : ∀ r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ (ψ y : ℂ)) x‖ ≤ P r * L ^ r)
    (hχB : ∀ r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ (χ y : ℂ)) x‖ ≤ C r * L ^ r)
    (hphaseB : ∀ i r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ ((partialDeriv φ y i : ℝ) : ℂ)) x‖ ≤ C r * L ^ r)
    (hVB : ∀ l j r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ C r * L ^ r)
    (hDB : ∀ l ij r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ C r * L ^ r)
    (hSB : ∀ l ij r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ C r * L ^ r)
    (vg : Fin n → List (Fin n) → L2) (va : (Fin n × Fin n) → List (Fin n) → L2)
    (hvg : ∀ j is, is.length < k + 1 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (vg j is) (vg j (i :: is)))
    (hva : ∀ j is, is.length < k + 1 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (va j is) (va j (i :: is)))
    (hgmem : MemMatrixFourierSobolev ((k + 1 : ℕ) : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])))
    (hamem : MemMatrixFourierSobolev ((k + 1 : ℕ) : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])))
    (hgB : ∀ p, p ≤ k + 1 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])) ≤ B p * A * K ^ p)
    (haB : ∀ p, p ≤ k + 1 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])) ≤ B p * A * K ^ p)
    (hgrep : ∀ j w, w.length ≤ k + 1 → vg j w =ᵐ[volume]
      euclideanCoordinateDerivList w (fun x ↦ g x j))
    (harep : ∀ ij w, w.length ≤ k + 1 → va ij w =ᵐ[volume]
      euclideanCoordinateDerivList w (fun x ↦ a x ij.1 ij.2)) :
    ∃ U : PiLp 2 (fun _ : Fin N ↦ L2),
      (∀ l, U l =ᵐ[volume] fun x ↦
        (waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
          completedVariationComplex F (modulatedWave ρ φ g)
            (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y)) x)) l) ∧
      MemMatrixFourierSobolev s U ∧ matrixFourierSobolevNorm s U ≤
        reconstructionDisplacementConstant n N k P C B * A * ρ * K ^ s := by
  let c (l : Fin N) : ReconstructionDisplacementSlot n → E → ℂ
    | .inl j => reconstructionValueEntry F l j
    | .inr (.inl ij) => reconstructionDerivativeEntry F l ij
    | .inr (.inr (.inl ij)) => fun x ↦
        reconstructionDerivativeEntry F l ij x * ((partialDeriv φ x ij.1 : ℝ) : ℂ)
    | .inr (.inr (.inr ij)) => fun x ↦ (χ x : ℂ) * reconstructionSourceEntry F l ij x
  let f : ReconstructionDisplacementSlot n → E → ℂ
    | .inl j => fun x ↦ g x j
    | .inr (.inl ij) => fun x ↦ g x ij.2
    | .inr (.inr (.inl ij)) => fun x ↦ g x ij.2
    | .inr (.inr (.inr ij)) => fun x ↦ a x ij.1 ij.2
  let v : ReconstructionDisplacementSlot n → List (Fin n) → L2
    | .inl j => vg j
    | .inr (.inl ij) => vg ij.2
    | .inr (.inr (.inl ij)) => vg ij.2
    | .inr (.inr (.inr ij)) => va ij
  let q : ReconstructionDisplacementSlot n → ℂ
    | .inl _ => 1
    | .inr (.inl _) => 1
    | .inr (.inr (.inl _)) => Complex.I * (ρ : ℂ)
    | .inr (.inr (.inr _)) => 1
  have hc : ∀ l j, ContDiffOn ℝ ∞ (c l j) Ω := by
    rintro l (j | (ij | (ij | ij)))
    · exact hV l j
    · exact hD l ij
    · exact (hD l ij).mul (hphase ij.1)
    · exact hχ.mul (hS l ij)
  have hcb : ∀ l j r, r ≤ k → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (c l j) x‖ ≤
      reconstructionDisplacementBudget C j r * L ^ r := by
    rintro l (j | (ij | (ij | ij)))
    · exact hVB l j
    · exact hDB l ij
    · exact reconstructionProductBudget_mul hΩ (hD l ij) (hphase ij.1) C C hC hC
        (by linarith) k (hDB l ij) (hphaseB ij.1)
    · exact reconstructionProductBudget_mul hΩ hχ (hS l ij) C C hC hC
        (by linarith) k hχB (hSB l ij)
  have hv : ∀ j is, is.length < k + 1 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v j is) (v j (i :: is)) := by
    rintro (j | (ij | (ij | ij)))
    · exact hvg j
    · exact hvg ij.2
    · exact hvg ij.2
    · exact hva ij
  have hvmem : ∀ j, MemFourierSobolev ((k + 1 : ℕ) : ℝ) (v j []) := by
    rintro (j | (ij | (ij | ij)))
    · exact hgmem j
    · exact hgmem ij.2
    · exact hgmem ij.2
    · exact hamem ij
  have hvB : ∀ j p, p ≤ k + 1 → fourierSobolevNorm (p : ℝ) (v j []) ≤ B p * A * K ^ p := by
    rintro (j | (ij | (ij | ij))) p hp
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput vg (fun _ ↦ [])) j).trans (hgB p hp)
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput vg (fun _ ↦ [])) ij.2).trans (hgB p hp)
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput vg (fun _ ↦ [])) ij.2).trans (hgB p hp)
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput va (fun _ ↦ [])) ij).trans (haB p hp)
  obtain ⟨U, hU, hm, hb⟩ := exists_reconstructionJetSum_bound k (k + 1) 1 hk hs hsk hΩ
    (fun x ↦ (ψ x : ℂ)) c f q reconstructionDisplacementWord hψ hψs hsupp hc P
    (reconstructionDisplacementBudget C) (fun _ ↦ B) hP
    (by
      rintro (j | (ij | (ij | ij)))
      · exact hC
      · exact hC
      · exact reconstructionProductBudget_nonneg hC hC
      · exact reconstructionProductBudget_nonneg hC hC)
    (fun _ ↦ hB) hA hL hLK
    (by
      have hρ : 0 ≤ ρ := by linarith
      rintro (j | (ij | (ij | ij))) <;>
        simp only [q, reconstructionDisplacementWord, List.length_nil, List.length_cons,
          Nat.zero_add, pow_zero, pow_one, norm_one, one_mul, mul_one, norm_mul, Complex.norm_I,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
      · linarith
      · exact hKρ
      · exact le_rfl
      · linarith)
    hψB hcb v hv hvmem hvB
    (by rintro (j | (ij | (ij | ij))) <;> simp [reconstructionDisplacementWord])
    (by
      rintro (j | (ij | (ij | ij)))
      · exact hgrep j [] (by simp)
      · exact hgrep ij.2 [ij.1] (by simp)
      · exact hgrep ij.2 [] (by simp)
      · exact harep ij [] (by simp))
  refine ⟨U, ?_, hm, ?_⟩
  · intro l
    filter_upwards [hU l] with x hx
    rw [hx, demodulated_completedVariationComplex_coordinate F χ ψ a (hφ x) (hg x) l]
    simp only [Fintype.sum_sum_type, c, f, q, reconstructionDisplacementWord,
      euclideanCoordinateDerivList, one_mul, ← Finset.mul_sum, partialDeriv]
    simp only [mul_assoc]
    abel
  · simpa only [reconstructionDisplacementConstant, Fintype.card_fin, pow_one] using hb

end JanetCartan.ResponseTransfer
