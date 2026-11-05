module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedBounds.Coefficients
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Jets.Normalized
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Frequency.Comparison

/-!
# Original phase derivatives for the weighted density

The mixed phase differential in `app:ch_regular_base:eq:actual-matrix-inverse`
is the diagonal averaged Jacobian. Its normalized jets cost exactly two original
phase derivatives. This supplies the phase slot of the weighted coefficient.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 200000
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison WholeImageGeometry LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- The joint mixed differential used only as a coordinate-free representative
of `S_{xη}` in `app:ch_regular_base:eq:actual-matrix-inverse`. -/
def weightedPhaseDifferential (S : E → E → ℝ) (x u : E) : E →L[ℝ] E :=
  averagedJacobian S x x u

/-- Smoothness of the mixed differential follows from local original phase
smoothness, for `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem weightedPhaseDifferential_contDiffOn {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) :
    ContDiffOn ℝ ∞ (Function.uncurry (weightedPhaseDifferential S)) (X ×ˢ D) := by
  have hd : ContDiffOn ℝ ∞ (fun q : E × E ↦ (q.1, q.1, q.2)) (X ×ˢ D) :=
    contDiffOn_fst.prodMk (contDiffOn_fst.prodMk contDiffOn_snd)
  have h := (averagedJacobian_contDiffOn hX hD hcX hS).comp hd (fun _ hq ↦ ⟨hq.1, hq⟩)
  exact h

/-- Identification with the literal density from the manuscript. No determinant
identity is assumed (`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem phaseJacobian_eq_abs_weightedPhaseDifferential {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x u : E} (hx : x ∈ X) (hu : u ∈ D) :
    phaseJacobian S x u = |(weightedPhaseDifferential S x u).det| := by
  have hg := (averagedGradient_contDiffOn hX hD hcX hS).contDiffAt
    (x := (x, x, u))
    ((hX.prod (hX.prod hD)).mem_nhds ⟨hx, hx, hu⟩)
  have hd := (hg.comp u (contDiffAt_const.prodMk
    (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have he : averagedGradient S x x = fun v ↦ gradient (fun z ↦ S z v) x := by
    funext v
    simp [averagedGradient, averagedPhaseDifferential, gradient]
  change DifferentiableAt ℝ (averagedGradient S x x) u at hd
  rw [he] at hd
  exact congrArg abs (averagedGradient_diagonal_det S x u hd).symm

/-- The primitive mixed second-jet bound controls the coordinate-free phase
slot; this supplies global growth of the weighted graph without assuming a
bound on its density (`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem norm_weightedPhaseDifferential_le {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) {B : ℝ}
    (hb : ∀ x ∈ X, ∀ u ∈ D,
      ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B)
    {x u : E} (hx : x ∈ X) (hu : u ∈ D) :
    ‖weightedPhaseDifferential S x u‖ ≤ B :=
  norm_averagedJacobian_le_of_mixed_bound hX hD hcX hS hb hx hx hu

/-- Normalized jets of the actual mixed phase differential require only the
original normalized phase jets through `N+2`. The factor `3^(N+1)` is fixed
before the phase and shell. Consumer: normalized weighted amplitude bounds in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem normalized_weightedPhaseDifferential_jets_le (N : ℕ) (B : ℝ)
    {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {ρ : ℝ} (hρ : ρ ≠ 0) (a b : ℝ)
    (hb : ∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N + 2,
      ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedPhase ρ S)) z‖ ≤ B)
    {z : E × E} (hz : z ∈ X ×ˢ normalizedSourceBand D ρ a b)
    {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k
      (fun q : E × E ↦ weightedPhaseDifferential S q.1 (ρ • q.2)) z‖ ≤
      (3 : ℝ)^(N + 1) * |B| := by
  let L : (E × E) →L[ℝ] NormalVariables n :=
    (ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.id ℝ (E × E))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro q
    change max ‖q.1‖ ‖q‖ ≤ 1 * ‖q‖
    simpa using max_le (norm_fst_le q) le_rfl
  let V := X ×ˢ (X ×ˢ normalizedSourceBand D ρ a b)
  have hV : IsOpen V := hX.prod (hX.prod (isOpen_normalizedSourceBand hD ρ a b))
  have hLz : L z ∈ V := ⟨hz.1, hz⟩
  have hf := normalizedAveragedJacobian_contDiffOn_band hX hD hcX hS ρ a b
  have hlinear := norm_iteratedFDeriv_comp_linear_on_open_le L hV hf hLz k
  change ‖iteratedFDeriv ℝ k
    (fun q : E × E ↦ weightedPhaseDifferential S q.1 (ρ • q.2)) z‖ ≤ _ at hlinear
  apply hlinear.trans
  apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)).trans
  apply (norm_iteratedFDeriv_normalizedAveragedJacobian_le hX hD hcX hS hρ a b hLz k).trans
  exact averagedGradient_jets_le_of_phase_jets N B hX
    (isOpen_normalizedSourceBand hD ρ a b) hcX
    ((normalizedPhase_contDiffOn hS ρ).mono (fun _ hq ↦ ⟨hq.1, hq.2.1⟩))
    hb hLz (by omega)

end JanetCartan.FourierIntegral.UncutNormal
