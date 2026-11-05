module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.Difference

/-!
# Reserve-preserving actual inverse-transpose jets

Primitive joint phase jets give `Y` with one-order loss and the transverse
mixed coefficient with two-order loss. Inversion preserves that entire reserve.
All derivatives include the full physical position and hence adapted time.
The scalar constants precede the phase, displacement, current band and scale.
The consumer is `PhysicalMean.sampledAdjointMomentTemplate_physical_jet_le`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff

namespace JanetCartan.PhysicalAdjointGeometry
open ResponseTransfer.GradedPrimitives

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {m : ℕ}

/-- Fixed all-order mixed coefficient constants, before histories and samples
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
def mixedJetConstant (A : ℕ → ℝ) (j : ℕ) : ℝ := 2 ^ (j + 1) * A (j + 2)

/-- Primitive phase constants are the only variable inputs to the fixed mixed
jet constant (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem mixedJetConstant_nonneg {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (j : ℕ) :
    0 ≤ mixedJetConstant A j := mul_nonneg (by positivity) (hA _)

/-- The literal averaged coefficient retains all but one primitive phase
order (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_averagedCovector_reserve_le
    {S : X × Euclidean m → ℝ} {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω)
    {A : ℕ → ℝ} {T : ℝ} {R k : ℕ} (hR : 1 ≤ R)
    (hjet : ∀ j ≤ k + 1, ∀ p ∈ Ω,
      ‖iteratedFDeriv ℝ j S p‖ ≤ A j * T ^ (j - R))
    {q : Point X m} (hq : q ∈ V) :
    ‖iteratedFDeriv ℝ k (averagedCovector S) q‖ ≤
      (2 ^ k * A (k + 1)) * T ^ (k - (R - 1)) := by
  have hb := norm_jet_averagedCovector_le hΩ hV hS hseg hjet hq
  have he : k + 1 - R = k - (R - 1) := by omega
  simpa only [he, mul_assoc] using hb

/-- Every ambient derivative of the actual averaged mixed transpose retains
all but two primitive phase orders. Time is not a frozen norm parameter
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_mixedTranspose_reserve_le
    {W : Euclidean m →L[ℝ] X} (hW : ‖W‖ ≤ 1)
    {S : X × Euclidean m → ℝ} {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω)
    {A : ℕ → ℝ} {T : ℝ} {R k : ℕ} (hR : 2 ≤ R)
    (hjet : ∀ j ≤ k + 2, ∀ p ∈ Ω,
      ‖iteratedFDeriv ℝ j S p‖ ≤ A j * T ^ (j - R))
    {q : Point X m} (hq : q ∈ V) :
    ‖iteratedFDeriv ℝ k (mixedTranspose W (averagedCovector S)) q‖ ≤
      mixedJetConstant A k * T ^ (k - (R - 2)) := by
  have hs := (contDiffOn_averagedCovector hΩ hV hS hseg).contDiffAt (hV.mem_nhds hq)
  apply (norm_jet_mixedTranspose_le hW hs k).trans
  have hb := norm_jet_averagedCovector_le hΩ hV hS hseg hjet hq (k := k + 1)
  have he : k + 1 + 1 - R = k - (R - 2) := by omega
  simpa only [he, mixedJetConstant, Nat.add_assoc, mul_assoc] using hb

/-- Positive-order inverse jets are proved by the reserve-preserving inverse
chain rule, from the primitive phase and the actual zeroth inverse value.
The latter is supplied by `exists_current_mixed_inverse`, not postulated for
the finished geometry (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_mixedInverse_reserve_le
    {W : Euclidean m →L[ℝ] X} (hW : ‖W‖ ≤ 1)
    {S : X × Euclidean m → ℝ} {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω)
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {T : ℝ} (hT : 1 ≤ T)
    {R k : ℕ} (hR : 2 ≤ R)
    (hjet : ∀ j ≤ k + 2, ∀ p ∈ Ω,
      ‖iteratedFDeriv ℝ j S p‖ ≤ A j * T ^ (j - R))
    {q : Point X m} (hq : q ∈ V)
    (hu : IsUnit (mixedTranspose W (averagedCovector S) q))
    (hM : ‖Ring.inverse (mixedTranspose W (averagedCovector S) q)‖ ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun p ↦ Ring.inverse (mixedTranspose W (averagedCovector S) p)) q‖ ≤
      inverseConstant 2 (mixedJetConstant A) k * T ^ (k - (R - 2)) := by
  have hs := contDiffOn_averagedCovector hΩ hV hS hseg
  have hC := (contDiffOn_mixedTranspose hV hs W).contDiffAt (hV.mem_nhds hq)
  apply norm_jet_inverse_le (hC.of_le (by simp : (k : ℕ∞ω) ≤ ∞)) le_rfl hu hM
    (mixedJetConstant A) (mixedJetConstant_nonneg hA) hT (R - 2)
  intro j _ hj
  exact norm_jet_mixedTranspose_reserve_le hW hΩ hV hS hseg hR
    (fun l hl p hp ↦ hjet l (by omega) p hp) hq

/-- The exact physical trade field has the same reserve as the actual inverse.
No frequency derivative is required and no factor of its input band occurs
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_tradeDirection_reserve_le
    {W : Euclidean m →L[ℝ] X} (hW : ‖W‖ ≤ 1)
    {S : X × Euclidean m → ℝ} {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω)
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {T : ℝ} (hT : 1 ≤ T)
    {R k : ℕ} (hR : 2 ≤ R)
    (hjet : ∀ j ≤ k + 2, ∀ p ∈ Ω,
      ‖iteratedFDeriv ℝ j S p‖ ≤ A j * T ^ (j - R))
    {q : Point X m} (hq : q ∈ V)
    (hu : IsUnit (mixedTranspose W (averagedCovector S) q))
    (hM : ‖Ring.inverse (mixedTranspose W (averagedCovector S) q)‖ ≤ 2) :
    ‖iteratedFDeriv ℝ k (tradeDirection W (averagedCovector S)) q‖ ≤
      inverseConstant 2 (mixedJetConstant A) k * T ^ (k - (R - 2)) := by
  let P : (Euclidean m →L[ℝ] Euclidean m) →L[ℝ] (Euclidean m →L[ℝ] X) :=
    ContinuousLinearMap.compL ℝ (Euclidean m) (Euclidean m) X W
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro A
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right hW (norm_nonneg A))
  have hs := contDiffOn_averagedCovector hΩ hV hS hseg
  have hC := (contDiffOn_mixedTranspose hV hs W).contDiffAt (hV.mem_nhds hq)
  have hi := (contDiffOn_ringInverse_units.contDiffAt (Units.isOpen.mem_nhds hu)).comp q hC
  have hb := P.norm_iteratedFDeriv_comp_left hi (by simp : (k : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ k (tradeDirection W (averagedCovector S)) q‖ ≤ _ at hb
  apply (hb.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))).trans
  simpa only [one_mul, Function.comp_def] using
    norm_jet_mixedInverse_reserve_le hW hΩ hV hS hseg hA hT hR hjet hq hu hM

end JanetCartan.PhysicalAdjointGeometry
