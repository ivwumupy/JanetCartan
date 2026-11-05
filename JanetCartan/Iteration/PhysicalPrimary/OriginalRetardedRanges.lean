module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedPrimitives
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedRangesTemplate

/-! Exact signed/whole source bands and inactive gaps on the native box and
whole parameter window. All fields are consequences of the SAME original
current and multiplier; source and adjoint signs remain independent. Consumer:
complete residual53/final solver50 (`app:ch_response:eq:fixed-factor-transfer`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.PhysicalPrimary.OriginalRetardedRanges
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral

/-- Native signed incidence selects the entire phase function before applying
its two arguments. Both choices still have the same positive differential norm. -/
theorem unsigned_source_band_of_function_choice {d : ℕ} (negative : Bool)
    (φ : Euclidean (d+1) → (Euclidean 3 × Euclidean d) → ℝ)
    {K : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d))} {lo hi : ℝ}
    (h : ∀ q ∈ K,
      lo ≤ ‖fderiv ℝ (fun y ↦ (if negative then (fun y b ↦ -φ y b) else φ) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ (if negative then (fun y b ↦ -φ y b) else φ) y q.2) q.1‖ ≤ hi) :
    ∀ q ∈ K,
      lo ≤ ‖fderiv ℝ (fun y ↦ φ y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ φ y q.2) q.1‖ ≤ hi := by
  cases negative <;> simpa only [Bool.false_eq_true, ↓reduceIte, fderiv_fun_neg, norm_neg] using h

/-- The original pointwise signed source gap is unchanged when the native
constructor selects the whole signed phase function before evaluating it. -/
theorem source_gap_of_pointwise_signed_phase {d : ℕ}
    (negative : Bool) (φ : Euclidean (d+1) → (Euclidean 3 × Euclidean d) → ℝ)
    {X : Set (Euclidean (d+1))} {C : Set (Euclidean 3 × Euclidean d)}
    {χ : (Euclidean 3 × Euclidean d) → ℝ} {β : Euclidean (d+1) → ℂ} {gap : ℝ}
    (h : ∀ y ∈ X, ∀ c ∈ C, c ∈ tsupport (fun c ↦ 1-χ c) → ∀ ξ ∈ tsupport β,
      gap ≤ dist (NormedSpace.normalize (gradient (fun v ↦ if negative then -φ v c else φ v c) y))
        (NormedSpace.normalize ξ)) :
    ∀ y ∈ X, ∀ c ∈ C, c ∈ tsupport (fun c ↦ 1-χ c) → ∀ ξ ∈ tsupport β,
      gap ≤ dist (NormedSpace.normalize (gradient
        (fun v ↦ (if negative then (fun y b ↦ -φ y b) else φ) v c) y))
        (NormedSpace.normalize ξ) := by
  cases negative <;> simpa only [Bool.false_eq_true, ↓reduceIte] using h

/-- Restrict the actual original source gap to the whole native half-box and
whole source window; no physical or parameter mask is contracted. -/
theorem original_gap_on_native_box {d : ℕ}
    (e : Euclidean (d+1) ≃L[ℝ] Euclidean (d+1)) (z : RootState (Euclidean d))
    (φ : Euclidean (d+1) → (Euclidean 3 × Euclidean d) → ℝ)
    (χ : (Euclidean 3 × Euclidean d) → ℝ) (β : Euclidean (d+1) → ℂ)
    {X : Set (Euclidean (d+1))} {C V : Set (Euclidean 3 × Euclidean d)} {ε gap : ℝ}
    (hε : 0 < ε)
    (hphysical : MapsTo e.symm (closure (elapsedPhysicalBox z ε)) X)
    (hVC : closure V ⊆ C)
    (hgap : ∀ y, e.symm y ∈ X → ∀ c ∈ C, c ∈ tsupport (fun c ↦ 1-χ c) →
      ∀ ξ ∈ tsupport β, gap ≤ dist (NormedSpace.normalize (gradient (fun v ↦ φ v c) y))
        (NormedSpace.normalize ξ)) :
    ∀ c ∈ V, c ∈ tsupport (fun c ↦ 1-χ c) →
      ∀ y ∈ elapsedPhysicalBox z (ε/2), ∀ ξ ∈ tsupport β,
        gap ≤ dist (NormedSpace.normalize (gradient (fun v ↦ φ v c) y))
          (NormedSpace.normalize ξ) := by
  intro c hc hχ y hy ξ hξ
  exact hgap y (hphysical (OriginalRetardedPrimitives.half_box_subset_full_closure z hε hy))
    c (hVC (subset_closure hc)) hχ ξ hξ

/-- The factor-two source margin absorbs the ACTUAL original transported
adjoint momentum throughout the entire elapsed operator interval. -/
theorem original_adjoint_gap_on_native_box {d : ℕ}
    (z : RootState (Euclidean d)) (φ : Euclidean (d+1) → (Euclidean 3 × Euclidean d) → ℝ)
    (χ : (Euclidean 3 × Euclidean d) → ℝ) (β : Euclidean (d+1) → ℂ)
    (Ψ : TwoTimePhase d) {V : Set (Euclidean 3 × Euclidean d)} {F : Set (Euclidean (d+1))}
    {ε mask gap γ : ℝ} (hmask : 0 ≤ mask) (hmargin : 2*γ ≤ gap)
    (hβ : tsupport β ⊆ F)
    (hgap : ∀ c ∈ V, c ∈ tsupport (fun c ↦ 1-χ c) →
      ∀ y ∈ elapsedPhysicalBox z (ε/2), ∀ ξ ∈ tsupport β,
        gap ≤ dist (NormedSpace.normalize (gradient (fun v ↦ φ v c) y)) (NormedSpace.normalize ξ))
    (hmomentum : ∀ t ∈ Icc (0 : ℝ) mask, ∀ y ∈ elapsedPhysicalBox z (ε/2), ∀ ξ ∈ F,
      dist (NormedSpace.normalize (gradient (fun v ↦ elapsedPhase Ψ t v ξ) y))
        (NormedSpace.normalize ξ) ≤ γ) :
    ∀ c ∈ V, c ∈ tsupport (fun c ↦ 1-χ c) → ∀ t ∈ Icc 0 (3*mask/4),
      ∀ y ∈ elapsedPhysicalBox z (ε/2), ∀ ξ ∈ tsupport β,
        γ ≤ dist (NormedSpace.normalize (gradient (fun v ↦ φ v c) y))
          (NormedSpace.normalize (gradient (fun v ↦ elapsedPhase Ψ t v ξ) y)) := by
  intro c hc hχ t ht y hy ξ hξ
  have ht' : t ∈ Icc (0 : ℝ) mask := ⟨ht.1,by linarith [ht.2]⟩
  exact OriginalIncidence.original_signed_gap_of_graph_transport
    (gradient (fun v ↦ φ v c) y) ξ (gradient (fun v ↦ elapsedPhase Ψ t v ξ) y)
    hmargin (hgap c hc hχ y hy ξ hξ) (hmomentum t ht' y hy ξ (hβ hξ))

/-- The actual positive common margin also fits the untransported branch. -/
theorem common_le_original_gap {γ gap : ℝ} (hγ : 0 < γ) (hgap : 2*γ ≤ gap) : γ ≤ gap := by
  linarith

/-- The existing native threshold is positive without selecting a new cutoff. -/
theorem original_threshold_pos {L : ℝ} (hL : 1 ≤ L) : 0 < L := zero_lt_one.trans_le hL

retain_original_native_source_ranges

end JanetCartan.PhysicalPrimary.OriginalRetardedRanges
