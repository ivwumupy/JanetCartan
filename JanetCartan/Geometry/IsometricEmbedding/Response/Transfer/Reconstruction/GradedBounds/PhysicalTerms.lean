module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.DirectionalTerms

/-!
# Hilbert bounds for the three physical product-rule terms

The carrier, coefficient derivative, and envelope derivative in
`app:ch_response:eq:response-graded-derivative`. Coefficient derivatives consume
one additional primitive jet, and envelope derivatives consume one additional
root Sobolev order. No derivative-envelope estimate is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.IsometricEmbedding.Reconstruction
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Scale-independent sum of the physical product-rule term constants in
`app:ch_response:eq:response-graded-derivative`. -/
def reconstructionPhysicalTermConstant {J : Type*} [Fintype J]
    (d M k : ℕ) (w : J → List (Fin d)) (P H : ℕ → ℝ) (C B : J → ℕ → ℝ) : ℝ :=
  (M : ℝ) * ∑ j,
    (reconstructionScalarTermConstant d k (w j).length
      (reconstructionProductBudget P (reconstructionProductBudget H (C j))) (B j) +
    reconstructionScalarTermConstant d k (w j).length
      (reconstructionProductBudget P (fun r ↦ C j (r + 1))) (B j) +
    reconstructionScalarTermConstant d k ((w j).length + 1)
      (reconstructionProductBudget P (C j)) (B j))

set_option maxHeartbeats 800000 in
/-- Actual L² representatives of the three product-rule terms of the physical
reconstruction. The phase factor is `I * ρ`, and the observation cutoff remains
outside every derivative (`app:ch_response:eq:response-graded-derivative`). -/
theorem exists_reconstructionPhysicalJetSum_bound {I J : Type*} [Fintype I] [Fintype J]
    (k m : ℕ) (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    {Ω : Set E} (hΩ : IsOpen Ω) (ψ p : E → ℂ) (c : I → J → E → ℂ)
    (f : J → E → ℂ) (q : J → ℂ) (w : J → List (Fin d)) (i : Fin d)
    (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Ω)
    (hp : ContDiffOn ℝ ∞ p Ω) (hc : ∀ l j, ContDiffOn ℝ ∞ (c l j) Ω)
    (P H : ℕ → ℝ) (C B : J → ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hH : ∀ r, 0 ≤ H r)
    (hC : ∀ j r, 0 ≤ C j r) (hB : ∀ j r, 0 ≤ B j r)
    {A L K ρ : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K) (hKρ : K ≤ ρ)
    (hgrade : ∀ j, ‖q j‖ * K ^ (w j).length ≤ ρ)
    (hψB : ∀ r, r ≤ k → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r ψ x‖ ≤ P r * L ^ r)
    (hpB : ∀ r, r ≤ k → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r p x‖ ≤ H r * L ^ r)
    (hcB : ∀ l j r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (c l j) x‖ ≤ C j r * L ^ r)
    (v : J → List (Fin d) → L2)
    (hv : ∀ j is, is.length < m → ∀ a,
      HasEuclideanL2CoordinateDerivative a (v j is) (v j (a :: is)))
    (hu : ∀ j, MemFourierSobolev (m : ℝ) (v j []))
    (hub : ∀ j r, r ≤ m → fourierSobolevNorm (r : ℝ) (v j []) ≤ B j r * A * K ^ r)
    (hkm : ∀ j, k + ((w j).length + 1) ≤ m)
    (hrep : ∀ j z, z.length ≤ m → v j z =ᵐ[volume] euclideanCoordinateDerivList z (f j)) :
    ∃ R : PiLp 2 (fun _ : I ↦ L2),
      (∀ l, R l =ᵐ[volume] fun x ↦ ∑ j, q j * (ψ x *
        (Complex.I * (ρ : ℂ) * p x * c l j x * euclideanCoordinateDerivList (w j) (f j) x +
        fderiv ℝ (c l j) x (EuclideanSpace.single i 1) * euclideanCoordinateDerivList (w j) (f j) x +
        c l j x * euclideanCoordinateDerivList (i :: w j) (f j) x))) ∧
      MemMatrixFourierSobolev s R ∧ matrixFourierSobolevNorm s R ≤
        reconstructionPhysicalTermConstant d (Fintype.card I) k w P H C B * A * ρ ^ 2 * K ^ s := by
  classical
  let c' (l : I) : J ⊕ (J ⊕ J) → E → ℂ
    | .inl j => fun x ↦ p x * c l j x
    | .inr (.inl j) => reconstructionNormalizedDirectionalCoefficient L (c l j)
        (EuclideanSpace.single i 1)
    | .inr (.inr j) => c l j
  let f' : J ⊕ (J ⊕ J) → E → ℂ := Sum.elim f (Sum.elim f f)
  let v' : J ⊕ (J ⊕ J) → List (Fin d) → L2 := Sum.elim v (Sum.elim v v)
  let B' : J ⊕ (J ⊕ J) → ℕ → ℝ := Sum.elim B (Sum.elim B B)
  let C' : J ⊕ (J ⊕ J) → ℕ → ℝ
    | .inl j => reconstructionProductBudget H (C j)
    | .inr (.inl j) => fun r ↦ C j (r + 1)
    | .inr (.inr j) => C j
  let q' : J ⊕ (J ⊕ J) → ℂ
    | .inl j => (Complex.I * (ρ : ℂ)) * q j
    | .inr (.inl j) => (L : ℂ) * q j
    | .inr (.inr j) => q j
  let w' : J ⊕ (J ⊕ J) → List (Fin d)
    | .inl j => w j
    | .inr (.inl j) => w j
    | .inr (.inr j) => i :: w j
  have hL0 : 0 < L := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hc' : ∀ l j, ContDiffOn ℝ ∞ (c' l j) Ω := by
    rintro l (j | (j | j))
    · exact hp.mul (hc l j)
    · exact reconstructionNormalizedDirectionalCoefficient_contDiffOn hΩ (hc l j) L _
    · exact hc l j
  have hc'B : ∀ l j r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (c' l j) x‖ ≤ C' j r * L ^ r := by
    rintro l (j | (j | j))
    · exact reconstructionProductBudget_mul hΩ hp (hc l j) H (C j) hH (hC j)
        hL0.le k hpB (fun r hr ↦ hcB l j r (by omega))
    · exact reconstructionNormalizedDirectionalCoefficient_budget hΩ (hc l j) (C j)
        hL0 k (hcB l j) _ (by simp)
    · exact fun r hr ↦ hcB l j r (by omega)
  have hgrade' : ∀ j, ‖q' j‖ * K ^ (w' j).length ≤ ρ ^ 2 := by
    rintro (j | (j | j))
    · simp only [q', w', norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hρ0]
      calc
        _ = ρ * (‖q j‖ * K ^ (w j).length) := by ring
        _ ≤ ρ * ρ := mul_le_mul_of_nonneg_left (hgrade j) hρ0
        _ = _ := by ring
    · simp only [q', w', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
      calc
        _ = L * (‖q j‖ * K ^ (w j).length) := by ring
        _ ≤ ρ * ρ := mul_le_mul (hLK.trans hKρ) (hgrade j)
          (mul_nonneg (norm_nonneg _) (pow_nonneg hK0 _)) hρ0
        _ = _ := by ring
    · simp only [q', w', List.length_cons, pow_succ]
      calc
        _ = K * (‖q j‖ * K ^ (w j).length) := by ring
        _ ≤ ρ * ρ := mul_le_mul hKρ (hgrade j)
          (mul_nonneg (norm_nonneg _) (pow_nonneg hK0 _)) hρ0
        _ = _ := by ring
  obtain ⟨R, hR, hm, hb⟩ := exists_reconstructionJetSum_bound k m 2 hk hs hsk hΩ ψ c'
    f' q' w' hψ hψs hsupp hc' P C' B' hP
    (by rintro (j | (j | j)); exact reconstructionProductBudget_nonneg hH (hC j)
        ; exact fun r ↦ hC j (r + 1); exact hC j)
    (by rintro (j | (j | j)) <;> exact hB j)
    hA hL hLK hgrade' hψB hc'B v'
    (by rintro (j | (j | j)) <;> exact hv j)
    (by rintro (j | (j | j)) <;> exact hu j)
    (by rintro (j | (j | j)) <;> exact hub j)
    (by rintro (j | (j | j)) <;> simp only [w', List.length_cons] <;> have := hkm j <;> omega)
    (by rintro (j | (j | j)) <;> apply hrep j <;>
        simp only [w', List.length_cons] <;> have := hkm j <;> omega)
  refine ⟨R, ?_, hm, ?_⟩
  · intro l
    filter_upwards [hR l] with x hx
    rw [hx]
    simp only [Fintype.sum_sum_type, q', c', f', Sum.elim_inl, Sum.elim_inr, w',
      reconstructionNormalizedDirectionalCoefficient, Complex.real_smul, Complex.ofReal_inv,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
    field_simp
    ring
  · simpa only [reconstructionPhysicalTermConstant, Fintype.sum_sum_type, w', C', B',
      Sum.elim_inl, Sum.elim_inr, List.length_cons, Finset.sum_add_distrib, add_assoc] using hb

end JanetCartan.IsometricEmbedding.Reconstruction
