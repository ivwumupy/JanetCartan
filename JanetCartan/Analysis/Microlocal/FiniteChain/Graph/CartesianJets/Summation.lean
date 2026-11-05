module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.CartesianJets.Transfer

/-!
# A common summable majorant for the Cartesian graph jets

For `app:ch_regular:eq:chain-tail`, the physical shell producer supplies
nonnegative summable derivative bounds through order `m`. A finite Leibniz
combination gives one majorant for all matrix channels and all existing
`JetIndex d m`. Its total sum is computed exactly. The cutoff profile and the
coordinate constants are fixed independently of accuracy and physical scales.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
open Set
namespace JanetCartan.FiniteChain.Graph.CartesianJets
open JanetCartan.RetardedSobolev.Spaces Retarded.KernelDecay FourierIntegral
variable {n r d m : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- Choose the cutoff profile from its actual derivatives once, before any
shell bounds or accuracy are selected (`app:ch_regular:eq:chain-tail`). -/
def cutoffDerivativeProfile {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ) : ℕ → ℝ :=
  Classical.choose (exists_cutoff_derivative_profile hψ hsψ)

/-- The chosen fixed cutoff profile is nonnegative
(`app:ch_regular:eq:chain-tail`). -/
theorem cutoffDerivativeProfile_nonneg {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ) (j : ℕ) :
    0 ≤ cutoffDerivativeProfile hψ hsψ j :=
  (Classical.choose_spec (exists_cutoff_derivative_profile hψ hsψ)).1 j

/-- The profile bounds all actual cutoff differentials
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_cutoff_le_profile {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ) (j : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ j ψ x‖ ≤ cutoffDerivativeProfile hψ hsψ j :=
  (Classical.choose_spec (exists_cutoff_derivative_profile hψ hsψ)).2 j x

/-- Summing the explicit majorant commutes with its finite Leibniz formula.
Only orders at most `m` must be summable. This computes the finite combination
of physical derivative sums used in `app:ch_regular:eq:chain-tail`. -/
theorem hasSum_jetMajorant {ι : Type*}
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n) (H : ℕ → ℝ)
    (B : ℕ → ι → ℝ) (hs : ∀ j ≤ m, Summable (B j)) :
    HasSum (fun α => jetMajorant J H (fun j => B j α) m)
      (jetMajorant J H (fun j => ∑' α, B j α) m) := by
  unfold jetMajorant
  apply hasSum_sum
  intro k hk
  apply HasSum.mul_right
  unfold derivativeConvolution
  apply hasSum_sum
  intro j _
  exact (hs (k - j) ((Nat.sub_le _ _).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))).hasSum.mul_left _

/-- Every Cartesian jet of the matrix family has the same explicit
nonnegative summable bound. The sum is exactly a fixed finite combination
of the sums supplied by the physical shell bridge; no operator estimate or
Cartesian jet estimate is assumed (`app:ch_regular:eq:chain-tail`). -/
theorem summable_cutMatrixEntry_jet_majorant
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {ψ : Euclidean n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (K : (ℕ × ℕ) → Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (hK : ∀ α, ContDiff ℝ ∞ (Function.uncurry (K α)))
    (B : ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ j ≤ m, ∀ α, 0 ≤ B j α) (hs : ∀ j ≤ m, Summable (B j))
    (hb : ∀ α x, x ∈ tsupport ψ → ∀ y, ∀ j ≤ m,
      ∀ v : Fin j → Euclidean n, (∀ l, ‖v l‖ ≤ 1) →
        ‖iteratedFDeriv ℝ j (fun z => K α z y) x v‖ ≤ B j α) :
    let C := fun α => jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun j => B j α) m
    (∀ α, 0 ≤ C α) ∧ Summable C ∧
      (∑' α, C α) = jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun j => ∑' α, B j α) m ∧
      ∀ α (a b : Fin r) (i : JetIndex d m) (p y : (Fin d → ℝ) × ℝ),
        ‖jet i (fun x => (ψ (J x) : ℂ) * K α (J x) (J (y.2, y.1)) a b) p‖ ≤ C α := by
  dsimp only
  have hsum := hasSum_jetMajorant J (cutoffDerivativeProfile hψ hsψ) B hs
  refine ⟨fun α => jetMajorant_nonneg J (cutoffDerivativeProfile_nonneg hψ hsψ)
    (fun j hj => hB j hj α), hsum.summable, hsum.tsum_eq, ?_⟩
  intro α a b i p y
  exact norm_cutMatrixEntry_jet_le J hψ (hK α)
    (cutoffDerivativeProfile_nonneg hψ hsψ) (fun j hj => hB j hj α)
    (fun j _ => norm_iteratedFDeriv_cutoff_le_profile hψ hsψ j) (hb α) a b i p y

/-- Monotonicity of the fixed finite combination, used to retain the physical
powers in `app:ch_regular:eq:chain-tail`. -/
theorem jetMajorant_mono
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {H B D : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hBD : ∀ j ≤ m, B j ≤ D j) :
    jetMajorant J H B m ≤ jetMajorant J H D m := by
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (hBD (k - j) ((Nat.sub_le _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
    (mul_nonneg (Nat.cast_nonneg _) (hH j))

/-- A common physical or shell prefactor is retained exactly once under the
finite cutoff and coordinate combination (`app:ch_regular:eq:chain-tail`). -/
theorem jetMajorant_mul_right
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (H B : ℕ → ℝ) (m : ℕ) (P : ℝ) :
    jetMajorant J H (fun j => B j * P) m = jetMajorant J H B m * P := by
  simp only [jetMajorant, derivativeConvolution, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The graded physical estimate keeps its full accuracy factor. Only the
fixed output order replaces `j` by `m`; neither the coordinate map nor the
fixed cutoff introduces an accuracy-dependent power of `ρ` or `L`
(`app:ch_regular:eq:chain-tail`). -/
theorem jetMajorant_le_grades
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {H B D : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hD : ∀ j ≤ m, 0 ≤ D j)
    {ρ L P : ℝ} (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (a : ℝ) (b q : ℕ)
    (hb : ∀ j ≤ m, B j ≤ D j * ρ ^ ((j : ℝ) + a) * L ^ b * (L / ρ) ^ q * P) :
    jetMajorant J H B m ≤
      jetMajorant J H D m * ρ ^ ((m : ℝ) + a) * L ^ b * (L / ρ) ^ q * P := by
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hpow : ∀ j ≤ m, ρ ^ ((j : ℝ) + a) ≤ ρ ^ ((m : ℝ) + a) := by
    intro j hj
    apply Real.rpow_le_rpow_of_exponent_le hρ
    have hj' : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
    linarith
  calc
    _ ≤ jetMajorant J H
        (fun j => D j * (ρ ^ ((m : ℝ) + a) * L ^ b * (L / ρ) ^ q * P)) m := by
      apply jetMajorant_mono J hH
      intro j hj
      apply (hb j hj).trans
      calc
        _ ≤ D j * ρ ^ ((m : ℝ) + a) * L ^ b * (L / ρ) ^ q * P := by
          gcongr
          exact hD j hj
        _ = _ := by ring
    _ = _ := by rw [jetMajorant_mul_right]; ring

/-- The total common jet bound retains the graded `ρ/L` estimate of the
physical derivative sums. The fixed losses are independent of accuracy `q`
(`app:ch_regular:eq:chain-tail`). -/
theorem tsum_jetMajorant_le_grades {ι : Type*}
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {H D : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hD : ∀ j ≤ m, 0 ≤ D j)
    (B : ℕ → ι → ℝ) (hs : ∀ j ≤ m, Summable (B j))
    {ρ L P : ℝ} (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (a : ℝ) (b q : ℕ)
    (hb : ∀ j ≤ m, (∑' α, B j α) ≤
      D j * ρ ^ ((j : ℝ) + a) * L ^ b * (L / ρ) ^ q * P) :
    (∑' α, jetMajorant J H (fun j => B j α) m) ≤
      jetMajorant J H D m * ρ ^ ((m : ℝ) + a) * L ^ b * (L / ρ) ^ q * P := by
  rw [(hasSum_jetMajorant J H B hs).tsum_eq]
  exact jetMajorant_le_grades J hH hD hρ hL hP a b q hb

end JanetCartan.FiniteChain.Graph.CartesianJets
