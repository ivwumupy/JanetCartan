module
public import JanetCartan.Iteration.PhysicalPairs.CombinedNode
public import JanetCartan.Iteration.PhysicalPrimary.Basic
/-! # Use the existing observation only as a Schwartz representative

The actual source application supplies global smoothness of ψ times its SAME
raw combined wave. The ordinary primary cutoff and all source masks remain
unchanged. Exact germs transfer derivatives on the original observation plateau;
no estimate of raw displacement outside that plateau is substituted for an
R-scale derivative-amplitude estimate (`app:ch_pairs:lem:pairs-ledger`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.ObservedSchwartz
open UniformStep
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "H" => EuclideanSpace ℂ (Fin N)

/-- No new cutoff: this represents the already chosen ψ times the same raw wave.
The actual source producer must prove the smoothness input internally. -/
def wave (ψ : E → ℝ) (hc : HasCompactSupport ψ) (Z : E → H)
    (hZ : ContDiff ℝ ∞ (fun x ↦ ψ x • Z x)) : SchwartzMap E H :=
  (hc.smul_right (f' := Z)).toSchwartzMap hZ

@[simp] theorem wave_apply (ψ : E → ℝ) (hc : HasCompactSupport ψ) (Z : E → H)
    (hZ : ContDiff ℝ ∞ (fun x ↦ ψ x • Z x)) (x : E) :
    wave ψ hc Z hZ x = ψ x • Z x := rfl

theorem wave_eventuallyEq (ψ : E → ℝ) (hc : HasCompactSupport ψ) (Z : E → H)
    (hZ : ContDiff ℝ ∞ (fun x ↦ ψ x • Z x)) {x : E}
    (hψ : ψ =ᶠ[𝓝 x] fun _ ↦ 1) : (wave ψ hc Z hZ : E → H) =ᶠ[𝓝 x] Z := by
  filter_upwards [hψ] with y hy
  simp only [wave_apply, hy, one_smul]

/-- A germ is enough for the full derivative, not just its principal part. -/
theorem amplitude_eq_of_germ (Z W : E → H) (θ : E → ℝ) {x : E}
    (h : Z =ᶠ[𝓝 x] W) :
    sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) () x =
      sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ ↦ θ) () x := by
  unfold sampledDerivativeAmplitude sampledDerivative partialDeriv
  rw [h.fderiv_eq]

/-- The original selected spatial cell works with the ENTIRE doubled parameter
window. No nonzero inner angular factor is used to admit the baseline. -/
theorem doubled_product (c : Euclidean 3 × Euclidean (n-1)) (σ : ℝ) :
    ball (0 : E) σ ×ˢ ball c (2*σ) ⊆ closedBall ((0 : E),c) (2*σ) := by
  intro p hp
  have hσ : 0 < σ := lt_of_le_of_lt dist_nonneg hp.1
  rw [← closedBall_prod_same]
  exact ⟨ball_subset_closedBall ((ball_subset_ball (by linarith : σ ≤ 2*σ)) hp.1),
    ball_subset_closedBall hp.2⟩

theorem slice_in_space {X U : Set E} {V : Set (Euclidean 3 × Euclidean (n-1))}
    {Ω : Set (E × (Euclidean 3 × Euclidean (n-1)))}
    (hs : ∀ p ∈ Ω, p.1 ∈ U) (hp : X ×ˢ V ⊆ Ω)
    {c : Euclidean 3 × Euclidean (n-1)} (hc : c ∈ V) : X ⊆ U :=
  fun x hx ↦ hs (x,c) (hp ⟨hx,hc⟩)

/-- The original aggregate cutoff erases the representational choice globally
provided its nonzero locus stays on the EXISTING observation plateau. The actual
application must prove that inclusion from Dsmooth, not from a new cutoff. -/
theorem cutoff_sampledPrimary_eq {ι : Type*} [Fintype ι] (χ : E → ℝ) (ψ : ι → E → ℝ)
    (b : ℝ) (μ : ι → ℝ) (Z : ι → E → H)
    (h : ∀ i x, χ x ≠ 0 → ψ i x = 1) :
    (fun x ↦ χ x • sampledPrimary b μ (fun i y ↦ ψ i y • Z i y) x) =
      (fun x ↦ χ x • sampledPrimary b μ Z x) := by
  funext x
  by_cases hx : χ x = 0
  · simp only [hx, zero_smul]
  · have hψ (i) : ψ i x = 1 := h i x hx
    simp only [sampledPrimary, Pi.smul_apply, Finset.sum_apply, Function.comp_apply,
      hψ, one_smul]
end JanetCartan.PhysicalPairs.ObservedSchwartz
end
