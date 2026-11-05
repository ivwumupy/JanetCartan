module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteHistoryBounds.Prefix
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.Construction.Displacement
public import JanetCartan.Geometry.IsometricEmbedding.Scales
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs

/-!
# Bounds for constructed finite prefixes

Section 9 (`main:eq:displacement-budget`, `main:eq:final-Cr`) needs only the
already constructed corrections. These results take `Fin j` data, prove the
hypotheses for their zero extension, and apply the checked band-history bounds.
They supply `Iteration/AdaptiveConstruction` and `Iteration/LocalExistence` with
uniform profiles and a reference-neighborhood threshold chosen before the
prefix. They do not construct the corrections or assert unconditional existence.
The unit-torus physical frequency and the chosen Hilbert codomain norm (including
Frobenius tensor norms) are those of the existing Fourier API.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.FiniteHistoryBounds

/-- `main:eq:final-Cr`: the Fourier constant depends only on dimension and order,
not on the accuracy, stage, initial scale, or particular increment. -/
def derivativeConstant (n r : ℕ) : ℝ :=
  historyL2Constant n r * (2 : ℝ) ^ ((r : ℝ) + (n : ℝ) / 2)

/-- `main:eq:final-Cr`: positivity needed for prospective displacement budgets. -/
theorem derivativeConstant_nonneg (n r : ℕ) : 0 ≤ derivativeConstant n r :=
  mul_nonneg (historyL2Constant_nonneg n r) (Real.rpow_nonneg (by norm_num) _)

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- `main:eq:final-Cr`: the sharp displayed estimate from exact support and the
absorbed L² budget alone. In particular no accuracy-dependent derivative constant
from the finite step is used. The estimate holds on every physical set. -/
theorem cNorm_increment_le (s : Set (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    {R k : ℝ} {u : Torus n → F} (hR : 1 ≤ R)
    (hu : IsSmoothPeriodic u) (hsupport : HasFourierSupport (2 * R ^ bandExponent) u)
    (hL2 : periodicL2Norm u ≤ R ^ (-k + displacementLoss n + 1)) :
    cNorm s r (periodicLift u) ≤ derivativeConstant n r *
      R ^ (-k + displacementLoss n + 1 + bandExponent * ((r : ℝ) + (n : ℝ) / 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hband : 1 ≤ 2 * R ^ bandExponent :=
    one_le_mul_of_one_le_of_one_le (by norm_num)
      (Real.one_le_rpow hR (by norm_num [bandExponent]))
  calc
    _ ≤ cNorm (fundamentalCell n) r (periodicLift u) :=
      BandHistory.cNorm_periodicLift_le_cell s r hu
    _ ≤ historyL2Constant n r * (2 * R ^ bandExponent) ^
        ((r : ℝ) + (n : ℝ) / 2) * periodicL2Norm u :=
      cNorm_periodicLift_le_of_hasFourierSupport hu hband hsupport r
    _ ≤ historyL2Constant n r * (2 * R ^ bandExponent) ^
        ((r : ℝ) + (n : ℝ) / 2) * R ^ (-k + displacementLoss n + 1) :=
      mul_le_mul_of_nonneg_left hL2
        (mul_nonneg (historyL2Constant_nonneg n r) (Real.rpow_nonneg (by positivity) _))
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hR0.le _),
        ← Real.rpow_mul hR0.le,
        Real.rpow_add hR0 (-k + displacementLoss n + 1)
          (bandExponent * ((r : ℝ) + (n : ℝ) / 2))]
      unfold derivativeConstant
      ring

/-- `main:eq:history-bernstein`: baseline decay on a physical set for each member
of an actual finite prefix. No bounds on subsequent increments occur. -/
theorem cNorm_prefix_increment_le (s : Set (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    {j : ℕ} {R k₀ : ℝ} {u : Fin j → Torus n → F} {k : Fin j → ℝ}
    (hR : 2 ≤ R) (hsmooth : ∀ i, IsSmoothPeriodic (u i))
    (hsupport : ∀ i : Fin j, HasFourierSupport (2 * historyScale R growthExponent i ^ bandExponent)
      (u i))
    (hL2 : ∀ i, periodicL2Norm (u i) ≤
      historyScale R growthExponent i ^ (-k i + displacementLoss n + 1))
    (hk : ∀ i, k₀ ≤ k i) (i : Fin j) :
    cNorm s r (periodicLift (u i)) ≤ derivativeConstant n r *
      historyScale R growthExponent i ^
        (-(k₀ - (displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2)) - 1)) := by
  have h := periodic_history_increment_bound r (v := growthExponent) (b := bandExponent)
    (B := displacementLoss n) hR (by norm_num [growthExponent])
    (by norm_num [bandExponent]) (by norm_num : (1 : ℝ) ≤ 2)
    (isSmoothPeriodic_extendByZero hsmooth) (hasFourierSupport_extendByZero hsupport)
    (periodicL2Norm_extendByZero_le (by linarith : 0 ≤ R) hL2)
    (le_extendOrder hk) i
  exact (BandHistory.cNorm_periodicLift_le_cell s r (hsmooth i)).trans
    (by simpa only [extendByZero_coe, derivativeConstant] using h)

/-- `main:eq:history-current`: one profile controls every finite prefix of the
fixed initial map. Its constants precede both the scale and the length; only
orders from the existing prefix are supplied. -/
theorem exists_prefix_derivative_profile
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {G : EuclideanSpace ℝ (Fin n) → F} (hG : ∀ x ∈ K, ContDiffAt ℝ ∞ G x)
    (rStar : ℕ) {k₀ : ℝ}
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < k₀) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧ ∀ R, 2 ≤ R →
      ∀ (j : ℕ) (u : Fin j → Torus n → F) (k : Fin j → ℝ),
      (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i : Fin j, HasFourierSupport (2 * historyScale R growthExponent i ^ bandExponent) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤
        historyScale R growthExponent i ^ (-k i + displacementLoss n + 1)) →
      (∀ i, k₀ ≤ k i) → ∀ W ⊆ K,
        HasDerivativeProfile W (currentMap G u) rStar
          (historyScale R growthExponent j ^ coefficientExponent) C := by
  obtain ⟨C, hC, hprofile⟩ := exists_periodic_history_derivative_profile (F := F) hK hG
    rStar (L := 2) (v := growthExponent) (b := bandExponent) (B := displacementLoss n) (k₀ := k₀)
    (by norm_num [growthExponent]) (by norm_num [bandExponent]) (by norm_num)
    (by linarith)
  refine ⟨C, hC, ?_⟩
  intro R hR j u k hsmooth hsupport hL2 hk W hWK
  have h := hprofile R hR (extendByZero u) (extendOrder k₀ k)
    (isSmoothPeriodic_extendByZero hsmooth) (hasFourierSupport_extendByZero hsupport)
    (periodicL2Norm_extendByZero_le (by linarith) hL2) (le_extendOrder hk) W hWK j
  simpa only [currentHistoryMap_extendByZero, ← scale_windows.2.2.1] using h

/-- `main:eq:displacement-budget`: the explicit geometric budget bounds the
actual finite displacement on a compact physical set. -/
theorem cNorm_prefix_displacement_le
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsCompact s) (r : ℕ)
    {j : ℕ} {R k₀ : ℝ} {u : Fin j → Torus n → F} {k : Fin j → ℝ}
    (hR : 2 ≤ R)
    (horder : displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2) + 2 < k₀)
    (hsmooth : ∀ i, IsSmoothPeriodic (u i))
    (hsupport : ∀ i : Fin j, HasFourierSupport (2 * historyScale R growthExponent i ^ bandExponent)
      (u i))
    (hL2 : ∀ i, periodicL2Norm (u i) ≤
      historyScale R growthExponent i ^ (-k i + displacementLoss n + 1))
    (hk : ∀ i, k₀ ≤ k i) (G : EuclideanSpace ℝ (Fin n) → F) :
    cNorm s r (currentMap G u - G) ≤ historyBound (derivativeConstant n r) R growthExponent
      (k₀ - (displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2)) - 1) := by
  rw [← currentHistoryMap_extendByZero]
  change cNorm s r (fun x ↦ (G x + ∑ i ∈ Finset.range j,
    periodicLift (extendByZero u i) x) - G x) ≤ _
  simp only [add_sub_cancel_left]
  apply cNorm_finiteHistory_le_historyBound hs
    (fun i _ ↦ (isSmoothPeriodic_extendByZero hsmooth i).2.of_le (by simp))
    (by linarith) (by norm_num [growthExponent]) (by linarith) (derivativeConstant_nonneg n r)
  intro i hi
  simpa only [extendByZero, dite_eq_left hi] using
    cNorm_prefix_increment_le s r hR hsmooth hsupport hL2 hk ⟨i, hi⟩

/-- `main:eq:displacement-budget`: a prospective scale threshold keeps every
actual prefix within half the reference radius. The core, map, increments and
length are all chosen after the threshold. The baseline order is fixed once. -/
theorem exists_initialScale_for_prefix_neighborhood (rStar : ℕ) {k₀ ε : ℝ}
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < k₀)
    (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R, T ≤ R →
      ∀ (s : Set (EuclideanSpace ℝ (Fin n))) (G : EuclideanSpace ℝ (Fin n) → F)
        (j : ℕ) (u : Fin j → Torus n → F) (k : Fin j → ℝ),
      IsCompact s → (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i : Fin j, HasFourierSupport (2 * historyScale R growthExponent i ^ bandExponent) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤
        historyScale R growthExponent i ^ (-k i + displacementLoss n + 1)) →
      (∀ i, k₀ ≤ k i) → cNorm s rStar (currentMap G u - G) < ε / 2 := by
  obtain ⟨T, hT, hnear⟩ := exists_initialScale_for_finiteHistory
    (E := EuclideanSpace ℝ (Fin n)) (F := F) (v := growthExponent) (derivativeConstant n rStar)
    (derivativeConstant_nonneg n rStar) (by norm_num [growthExponent])
    (μ := k₀ - (displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2)) - 1)
    (by linarith) hε
  refine ⟨T, hT, ?_⟩
  intro R hR s G j u k hs hsmooth hsupport hL2 hk
  rw [← currentHistoryMap_extendByZero]
  apply hnear R hR s rStar j G (fun i ↦ periodicLift (extendByZero u i)) hs
    (fun i _ ↦ (isSmoothPeriodic_extendByZero hsmooth i).2.of_le (by simp))
  intro i hi
  simpa only [extendByZero, dite_eq_left hi] using
    cNorm_prefix_increment_le s rStar (hT.trans hR) hsmooth hsupport hL2 hk ⟨i, hi⟩

/-- Section 9, `main:eq:displacement-budget`: reference-neighborhood persistence
on the actual closed core, for every prefix satisfying its prospective budgets.
The order hypothesis is exactly `main:eq:k-history`; no future step is assumed. -/
theorem exists_initialScale_for_core_neighborhood (D : LocalDomain) (rStar kmin : ℕ)
    {ε : ℝ}
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kmin)
    (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R, T ≤ R →
      ∀ (G : EuclideanSpace ℝ (Fin n) → F) (j : ℕ)
        (u : Fin j → Torus n → F) (k : Fin j → ℕ),
      (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i : Fin j, HasFourierSupport (2 * historyScale R growthExponent i ^ bandExponent) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤
        historyScale R growthExponent i ^ (-(k i : ℝ) + displacementLoss n + 1)) →
      (∀ i, kmin ≤ k i) → cNorm (D.core n) rStar (currentMap G u - G) < ε / 2 := by
  obtain ⟨T, hT, hnear⟩ := exists_initialScale_for_prefix_neighborhood (F := F) rStar horder hε
  refine ⟨T, hT, ?_⟩
  intro R hR G j u k hsmooth hsupport hL2 hk
  exact hnear R hR (D.core n) G j u (fun i ↦ (k i : ℝ)) (isCompact_closedBall _ _)
    hsmooth hsupport hL2 (fun i ↦ Nat.cast_le.mpr (hk i))

end JanetCartan.FiniteHistoryBounds
