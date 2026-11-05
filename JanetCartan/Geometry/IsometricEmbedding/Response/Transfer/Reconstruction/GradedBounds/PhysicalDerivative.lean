module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.Displacement
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.PhysicalTerms
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.JetSumDifferential

/-! # The physical derivative of the same completed variation

The observation cutoff is applied after differentiation, and the carrier term
is retained in `app:ch_response:eq:response-graded-derivative`.
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

set_option maxHeartbeats 800000 in
/-- The SAME completed variation has the physical derivative representative and bound
of `app:ch_response:eq:response-graded-derivative`. Only primitive coefficient,
cutoff and phase-gradient budgets are assumed; products and derivative envelope
bounds are derived. The parent must instantiate the supplied scalar root jets.
No global normal-rank hypothesis is required. -/
theorem completedVariationComplex_physicalCoordinate_graded
    (k : ℕ) (i : Fin n) (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    (F : E → Euclidean N) {Ω : Set E} (hΩ : IsOpen Ω)
    (φ χ ψ : E → ℝ) (g : E → EuclideanSpace ℂ (Fin n))
    (a : E → Matrix (Fin n) (Fin n) ℂ)
    (hφ : Differentiable ℝ φ) (hg : ContDiff ℝ ∞ g)
    (ha : ∀ j l, ContDiff ℝ ∞ (fun x ↦ a x j l))
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
    (hχB : ∀ r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ (χ y : ℂ)) x‖ ≤ C r * L ^ r)
    (hphaseB : ∀ i r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ ((partialDeriv φ y i : ℝ) : ℂ)) x‖ ≤ C r * L ^ r)
    (hVB : ∀ l j r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ C r * L ^ r)
    (hDB : ∀ l ij r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ C r * L ^ r)
    (hSB : ∀ l ij r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ C r * L ^ r)
    (vg : Fin n → List (Fin n) → L2) (va : (Fin n × Fin n) → List (Fin n) → L2)
    (hvg : ∀ j is, is.length < k + 2 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (vg j is) (vg j (i :: is)))
    (hva : ∀ j is, is.length < k + 2 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (va j is) (va j (i :: is)))
    (hgmem : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])))
    (hamem : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])))
    (hgB : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])) ≤ B p * A * K ^ p)
    (haB : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])) ≤ B p * A * K ^ p)
    (hgrep : ∀ j w, w.length ≤ k + 2 → vg j w =ᵐ[volume]
      euclideanCoordinateDerivList w (fun x ↦ g x j))
    (harep : ∀ ij w, w.length ≤ k + 2 → va ij w =ᵐ[volume]
      euclideanCoordinateDerivList w (fun x ↦ a x ij.1 ij.2)) :
    ∃ U : PiLp 2 (fun _ : Fin N ↦ L2),
      (∀ l, U l =ᵐ[volume] fun x ↦
        (waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
          fderiv ℝ (completedVariationComplex F (modulatedWave ρ φ g)
            (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y))) x
            (EuclideanSpace.single i 1))) l) ∧
      MemMatrixFourierSobolev s U ∧ matrixFourierSobolevNorm s U ≤
        reconstructionPhysicalTermConstant n N k (reconstructionDisplacementWord (n := n))
          P C (reconstructionDisplacementBudget C) (fun _ ↦ B) * A * ρ ^ 2 * K ^ s := by
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
  have hcb : ∀ l j r, r ≤ k + 1 → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (c l j) x‖ ≤
      reconstructionDisplacementBudget C j r * L ^ r := by
    rintro l (j | (ij | (ij | ij)))
    · exact hVB l j
    · exact hDB l ij
    · exact reconstructionProductBudget_mul hΩ (hD l ij) (hphase ij.1) C C hC hC
        (by linarith) (k + 1) (hDB l ij) (hphaseB ij.1)
    · exact reconstructionProductBudget_mul hΩ hχ (hS l ij) C C hC hC
        (by linarith) (k + 1) hχB (hSB l ij)
  have hv : ∀ j is, is.length < k + 2 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v j is) (v j (i :: is)) := by
    rintro (j | (ij | (ij | ij)))
    · exact hvg j
    · exact hvg ij.2
    · exact hvg ij.2
    · exact hva ij
  have hvmem : ∀ j, MemFourierSobolev ((k + 2 : ℕ) : ℝ) (v j []) := by
    rintro (j | (ij | (ij | ij)))
    · exact hgmem j
    · exact hgmem ij.2
    · exact hgmem ij.2
    · exact hamem ij
  have hvB : ∀ j p, p ≤ k + 2 → fourierSobolevNorm (p : ℝ) (v j []) ≤ B p * A * K ^ p := by
    rintro (j | (ij | (ij | ij))) p hp
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput vg (fun _ ↦ [])) j).trans (hgB p hp)
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput vg (fun _ ↦ [])) ij.2).trans (hgB p hp)
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput vg (fun _ ↦ [])) ij.2).trans (hgB p hp)
    · exact (fourierSobolevNorm_coordinate_le _ (reconstructionJetInput va (fun _ ↦ [])) ij).trans (haB p hp)
  obtain ⟨U, hU, hm, hb⟩ := exists_reconstructionPhysicalJetSum_bound k (k + 2) hk hs hsk hΩ
    (fun x ↦ (ψ x : ℂ)) (fun x ↦ ((partialDeriv φ x i : ℝ) : ℂ)) c f q
    reconstructionDisplacementWord i hψ hψs hsupp (hphase i) hc P C
    (reconstructionDisplacementBudget C) (fun _ ↦ B) hP hC
    (by
      rintro (j | (ij | (ij | ij)))
      · exact hC
      · exact hC
      · exact reconstructionProductBudget_nonneg hC hC
      · exact reconstructionProductBudget_nonneg hC hC)
    (fun _ ↦ hB) hA hL hLK hKρ
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
    hψB (fun r hr ↦ hphaseB i r (by omega)) hcb v hv hvmem hvB
    (by rintro (j | (ij | (ij | ij))) <;> simp [reconstructionDisplacementWord])
    (by
      rintro (j | (ij | (ij | ij))) z hz
      · exact hgrep j z hz
      · exact hgrep ij.2 z hz
      · exact hgrep ij.2 z hz
      · exact harep ij z hz)
  have hf : ∀ j, ContDiff ℝ ∞ (f j) := by
    rintro (j | (ij | (ij | ij)))
    · exact (contDiff_piLp 2).mp hg j
    · exact (contDiff_piLp 2).mp hg ij.2
    · exact (contDiff_piLp 2).mp hg ij.2
    · exact ha ij.1 ij.2
  have he (l : Fin N) : (fun x ↦ reconstructionAmplitude F ρ φ χ g a x l) =
      fun x ↦ ∑ j, q j * (c l j x * euclideanCoordinateDerivList
        (reconstructionDisplacementWord j) (f j) x) := by
    funext x
    rw [reconstructionAmplitude_coordinate]
    simp only [Fintype.sum_sum_type, c, f, q, reconstructionDisplacementWord,
      euclideanCoordinateDerivList, one_mul, mul_add, Finset.sum_add_distrib,
      partialDeriv, ← Finset.mul_sum]
    simp only [mul_assoc, mul_left_comm, mul_comm]
    simp only [Finset.mul_sum]
    abel
  refine ⟨U, ?_, hm, ?_⟩
  · intro l
    filter_upwards [hU l] with x hx
    rw [hx]
    by_cases hz : ψ x = 0
    · simp [hz]
    have hxΩ : x ∈ Ω := hsupp (subset_tsupport _ (by simpa using hz))
    have hd l := reconstructionJetSum_differential (c l) f q reconstructionDisplacementWord
      (fun j ↦ ((hc l j).contDiffAt (hΩ.mem_nhds hxΩ)).differentiableAt (by simp)) hf
    have hcoord l : DifferentiableAt ℝ (fun y ↦ reconstructionAmplitude F ρ φ χ g a y l) x := by
      rw [he]; exact (hd l).1
    have hamp : DifferentiableAt ℝ (reconstructionAmplitude F ρ φ χ g a) x :=
      (differentiableAt_piLp 2).mpr hcoord
    rw [demodulated_physicalDerivative_completedVariationComplex F χ ψ a hφ
      (hg.differentiable (by simp)) x (EuclideanSpace.single i 1) hamp]
    have hproj := ((PiLp.proj 2 (fun _ : Fin N ↦ ℂ) l :
      EuclideanSpace ℂ (Fin N) →L[ℝ] ℂ).hasFDerivAt.comp x hamp.hasFDerivAt).fderiv
    have hde : (fderiv ℝ (reconstructionAmplitude F ρ φ χ g a) x
        (EuclideanSpace.single i 1)) l =
        ∑ j, q j * (fderiv ℝ (c l j) x (EuclideanSpace.single i 1) *
          euclideanCoordinateDerivList (reconstructionDisplacementWord j) (f j) x +
          c l j x * euclideanCoordinateDerivList (i :: reconstructionDisplacementWord j) (f j) x) := by
      have heval : fderiv ℝ (fun y ↦ reconstructionAmplitude F ρ φ χ g a y l) x
          (EuclideanSpace.single i 1) =
          (fderiv ℝ (reconstructionAmplitude F ρ φ χ g a) x (EuclideanSpace.single i 1)) l :=
        congrArg (fun T : E →L[ℝ] ℂ ↦ T (EuclideanSpace.single i 1)) hproj
      rw [← heval]
      rw [he]
      exact (hd l).2 i
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hde]
    rw [show reconstructionAmplitude F ρ φ χ g a x l = _ from congrFun (he l) x]
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib, partialDeriv]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simpa only [Fintype.card_fin] using hb

/-- The complete physical differential, in the Hilbert norm of all spatial
and ambient coordinates, satisfies `app:ch_response:eq:response-graded-derivative`.
It is the demodulated derivative of the same `completedVariationComplex` as the
displacement theorem, with the observation cutoff outside differentiation. -/
theorem completedVariationComplex_physicalDerivative_graded
    (k : ℕ) (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    (F : E → Euclidean N) {Ω : Set E} (hΩ : IsOpen Ω)
    (φ χ ψ : E → ℝ) (g : E → EuclideanSpace ℂ (Fin n))
    (a : E → Matrix (Fin n) (Fin n) ℂ)
    (hφ : Differentiable ℝ φ) (hg : ContDiff ℝ ∞ g)
    (ha : ∀ j l, ContDiff ℝ ∞ (fun x ↦ a x j l))
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
    (hχB : ∀ r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ (χ y : ℂ)) x‖ ≤ C r * L ^ r)
    (hphaseB : ∀ i r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ ((partialDeriv φ y i : ℝ) : ℂ)) x‖ ≤ C r * L ^ r)
    (hVB : ∀ l j r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ C r * L ^ r)
    (hDB : ∀ l ij r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ C r * L ^ r)
    (hSB : ∀ l ij r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ C r * L ^ r)
    (vg : Fin n → List (Fin n) → L2) (va : (Fin n × Fin n) → List (Fin n) → L2)
    (hvg : ∀ j is, is.length < k + 2 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (vg j is) (vg j (i :: is)))
    (hva : ∀ j is, is.length < k + 2 → ∀ i,
      HasEuclideanL2CoordinateDerivative i (va j is) (va j (i :: is)))
    (hgmem : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])))
    (hamem : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])))
    (hgB : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])) ≤ B p * A * K ^ p)
    (haB : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])) ≤ B p * A * K ^ p)
    (hgrep : ∀ j w, w.length ≤ k + 2 → vg j w =ᵐ[volume]
      euclideanCoordinateDerivList w (fun x ↦ g x j))
    (harep : ∀ ij w, w.length ≤ k + 2 → va ij w =ᵐ[volume]
      euclideanCoordinateDerivList w (fun x ↦ a x ij.1 ij.2)) :
    ∃ U : PiLp 2 (fun _ : Fin n × Fin N ↦ L2),
      (∀ l, U l =ᵐ[volume] fun x ↦
        (waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
          fderiv ℝ (completedVariationComplex F (modulatedWave ρ φ g)
            (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y))) x
            (EuclideanSpace.single l.1 1))) l.2) ∧
      MemMatrixFourierSobolev s U ∧ matrixFourierSobolevNorm s U ≤
        ((n : ℝ) * N * reconstructionPhysicalTermConstant n N k
          (reconstructionDisplacementWord (n := n)) P C (reconstructionDisplacementBudget C)
          (fun _ ↦ B)) * A * ρ ^ 2 * K ^ s := by
  have hi (i : Fin n) := completedVariationComplex_physicalCoordinate_graded k i hk hs hsk
    F hΩ φ χ ψ g a hφ hg ha hψ hψs hsupp hχ hphase hV hD hS P C B hP hC hB
    hA hL hLK hKρ hψB hχB hphaseB hVB hDB hSB vg va hvg hva hgmem hamem hgB haB hgrep harep
  choose R hR hm hb using hi
  let U : PiLp 2 (fun _ : Fin n × Fin N ↦ L2) := WithLp.toLp 2 (fun ij ↦ R ij.1 ij.2)
  refine ⟨U, fun ij ↦ hR ij.1 ij.2, fun ij ↦ hm ij.1 ij.2,
    (matrixFourierSobolevNorm_le_sum s U).trans ?_⟩
  calc
    _ ≤ ∑ _ij : Fin n × Fin N,
        reconstructionPhysicalTermConstant n N k (reconstructionDisplacementWord (n := n))
          P C (reconstructionDisplacementBudget C) (fun _ ↦ B) * A * ρ ^ 2 * K ^ s := by
      apply Finset.sum_le_sum
      intro ij _
      exact (fourierSobolevNorm_coordinate_le s (R ij.1) ij.2).trans (hb ij.1)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]; ring

end JanetCartan.ResponseTransfer
