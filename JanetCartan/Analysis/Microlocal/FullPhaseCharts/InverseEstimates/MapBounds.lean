module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.PhaseBounds

/-!
# Transfer from primitive phase jets to the map norm

The `F`-order accounting in the last paragraph of
`app:ch_seed:prop:seed-phase-charts` uses primitive phase/carrier order `r+3`
from the map through `r+6`. This module records that precise conditional
transfer. The primitive budget is an explicit obligation of the Hamilton
phase/carrier construction, not an inverse or forward-chart bound.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.InverseEstimates
variable {R D X E : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [FiniteDimensional ℝ R] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {A₀ B₁ : Type} [NormedAddCommGroup A₀] [NormedSpace ℝ A₀]
  [NormedAddCommGroup B₁] [NormedSpace ℝ B₁]

/-- The `r+6` map budget for both the inverse and its first epsilon derivative
in `app:ch_seed:eq:seed-phase-tame` and `app:ch_seed:prop:seed-phase-charts`.
The only high-norm premise is the primitive phase/carrier `r+3` budget, whose
actual producer is the Hamilton phase and carrier construction. All inverse
and forward-chart estimates are discharged here by `PhaseBounds`. -/
theorem exists_carrierQuotient_inverse_epsilon_map_bound
    (a : ((R × D) × ℝ) × X) (b : ((R × D) × X) × E)
    (d : ((R × D) × ℝ) × X × X) (c : (ℝ × (R × X × X)) × D)
    {ρ σ τ κ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hτ : 0 < τ) (hκ : 0 < κ)
    {V : Set (R × D)} {I W T : Set ℝ} {U B : Set X} {Z : Set E}
    (hV : IsOpen V) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hU : IsOpen U) (hZ : IsOpen Z) (hB : IsOpen B)
    (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (ha : closedBall a ρ ⊆ (V ×ˢ I) ×ˢ U)
    (hp : closedBall a.1.1 ρ ⊆ V)
    (hb : closedBall b σ ⊆ (V ×ˢ U) ×ˢ Z)
    (hd : closedBall d τ ⊆ (V ×ˢ I) ×ˢ B ×ˢ B)
    (hphysical : ∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ T, y + t • (x - y) ∈ U)
    (hsegments : ∀ q ∈ closedBall d τ, ∀ t ∈ Icc (0 : ℝ) 1,
      jointPhysicalSegment t q ∈ closedBall a ρ)
    (hcoord : MapsTo quotientChartReindex (closedBall c κ) (closedBall d τ))
    (O : X →L[ℝ] D) (G : D ≃L[ℝ] D)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (r : ℕ) (KF : Set A₀) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ C > (0 : ℝ), ∀ (F : A₀ → B₁) (S : ((R × D) × X) → E → ℝ) (z v : R × D → E)
      (g : (ℝ × (R × X × X)) × D → D) (J K : Set ((ℝ × (R × X × X)) × D)),
      ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ U) ×ˢ Z) →
      ContDiffOn ℝ ∞ z V → ContDiffOn ℝ ∞ v V →
      cNorm (closedBall b σ) 3 (Function.uncurry S) ≤ N →
      cNorm (closedBall a.1.1 ρ) 3 z ≤ M →
      cNorm (closedBall a.1.1 ρ) 3 v ≤ M →
      (∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ W, z p + (t * ε) • v p ∈ Z) →
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (carrierSubstitution z v t)
        (closedBall a ρ) (closedBall b σ)) →
      cNorm (closedBall b σ) (r + 3) (Function.uncurry S) +
        cNorm (closedBall a.1.1 ρ) (r + 3) z +
        cNorm (closedBall a.1.1 ρ) (r + 3) v ≤ B₀ * (1 + cNorm KF (r + 6) F) →
      IsOpen J → IsCompact K → K ⊆ J → ContDiffOn ℝ ∞ g J →
      MapsTo (inverseGraph g) K (closedBall c κ) →
      (∀ q ∈ closedBall c κ,
        ‖(G.symm : D →L[ℝ] D).comp
          (fderiv ℝ (fun u ↦ carrierQuotientChart O S z v (q.1, u)) q.2) -
          ContinuousLinearMap.id ℝ D‖ ≤ 1 / 2) →
      (∀ q ∈ J, carrierQuotientChart O S z v (inverseGraph g q) = q.2) →
      cNorm K r g + cNorm K r (fun q : (ℝ × (R × X × X)) × D ↦
        deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1) ≤
        C * (1 + cNorm KF (r + 6) F) := by
  obtain ⟨C, hC, hbnd⟩ := exists_carrierQuotient_inverse_epsilon_oneHigh
    a b d c hρ hσ hτ hκ hV hI hzero hU hZ hB hW hIW hT hIT
    ha hp hb hd hphysical hsegments hcoord O G hM hN r
  refine ⟨C * (1 + B₀), by positivity, ?_⟩
  intro F S z v g J K hS hz hv hSN hzM hvM hshift hmap hbudget
    hJ hK hKJ hg hrange hgap heq
  apply (hbnd S z v g J K hS hz hv hSN hzM hvM hshift hmap
    hJ hK hKJ hg hrange hgap heq).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hF := cNorm_nonneg KF (r + 6) F
  linarith

end JanetCartan.FullPhaseCharts.InverseEstimates
