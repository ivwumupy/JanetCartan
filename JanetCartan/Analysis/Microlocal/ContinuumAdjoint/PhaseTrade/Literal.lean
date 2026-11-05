module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.Smooth
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.Differential

/-!
# Smoothness of the literal phase coefficients

For `app:ch_background:eq:bg-derivative-trade`, this leaf instantiates the
rational coefficient operations with the differentiated phase and carrier.
The Hamilton phase, its smooth extension on the buffered chart, the smooth
carrier and the transverse gap remain the consumer's analytic inputs.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint

private theorem matrix_smooth {a b : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Matrix (Fin a) (Fin b) ℝ}
    {N : ℕ∞ω} (hf : ∀ i j, ContDiff ℝ N (fun x ↦ f x i j)) : ContDiff ℝ N f := by
  let e : (Fin a × Fin b → ℝ) ≃ₗ[ℝ] Matrix (Fin a) (Fin b) ℝ :=
    { toFun := fun g i j ↦ g (i, j)
      invFun := fun A ij ↦ A ij.1 ij.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact e.toContinuousLinearEquiv.contDiff.comp (contDiff_pi.mpr fun ij ↦ hf ij.1 ij.2)

/-- Smoothness of the literal mixed phase matrix in
`app:ch_background:eq:bg-derivative-trade`, deduced from the phase and carrier. -/
theorem contDiff_transversePhaseMatrix {n p : ℕ} {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean p ↦
      transversePhaseMatrix S q.1 (ζ q.2)) := by
  apply matrix_smooth
  intro i j
  have hd : ContDiff ℝ ∞ (fun q : (Euclidean n × Euclidean (n-1)) × Euclidean n ↦
      S q.2 q.1.2) := hS.comp (contDiff_snd.prodMk contDiff_fst.snd)
  have hdx : ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean (n-1) ↦
      partialDeriv (fun y ↦ S y q.2) q.1 i) :=
    hd.fderiv_apply contDiff_fst contDiff_const (by simp)
  have hdx' : ContDiff ℝ ∞
      (fun q : (Euclidean n × Euclidean p) × Euclidean (n-1) ↦
        partialDeriv (fun y ↦ S y q.2) q.1.1 i) :=
    hdx.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hdx'.fderiv_apply (hζ.comp contDiff_snd) contDiff_const (by simp)

/-- Joint physical/carrier smoothness of the literal footpoint coordinates in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiff_transverseFootpoint_entry {n p : ℕ} {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ) (j : Fin (n-1)) :
    ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean p ↦ transverseFootpoint S ζ q.1 q.2 j) := by
  have hs : ContDiff ℝ ∞ (fun q : (Euclidean n × Euclidean p) × Euclidean (n-1) ↦
      S q.1.1 q.2) := hS.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hs.fderiv_apply (hζ.comp contDiff_snd) contDiff_const (by simp)

/-- Joint smoothness of the actual `D_z Y`, retaining all carrier derivatives,
for `app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiff_transverseFootpointCarrierMatrix {n p : ℕ}
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean p ↦
      transverseFootpointCarrierMatrix S ζ q.1 q.2) := by
  apply matrix_smooth
  intro l j
  have hY := contDiff_transverseFootpoint_entry hS hζ j
  have hY' : ContDiff ℝ ∞ (fun q : (Euclidean n × Euclidean p) × Euclidean p ↦
      transverseFootpoint S ζ q.1.1 q.2 j) :=
    hY.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hY'.fderiv_apply contDiff_snd contDiff_const (by simp)

/-- The two differentiated inputs to the rational operation of
`app:ch_background:eq:bg-derivative-trade`. This is a definition from `S, ζ`,
not an input record of desired phase identities or estimates. -/
def transversePhaseInputs {n p : ℕ} (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean p → Euclidean (n - 1)) (q : Euclidean n × Euclidean p) :
    TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ :=
  (transversePhaseMatrix S q.1 (ζ q.2), transverseFootpointCarrierMatrix S ζ q.1 q.2)

/-- Smoothness of the literal paired phase inputs for the one-high estimate in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiff_transversePhaseInputs {n p : ℕ}
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (transversePhaseInputs S ζ) :=
  (contDiff_transversePhaseMatrix hS hζ).prodMk
    (contDiff_transverseFootpointCarrierMatrix hS hζ)

/-- Smoothness of the actual phase left inverse on the set with the transverse
gap (`app:ch_background:eq:bg-derivative-trade`). -/
theorem contDiffOn_transversePhaseLeftInverse {n p : ℕ}
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ)
    {U : Set (Euclidean n × Euclidean p)} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q ∈ U, TransverseGap δ (transversePhaseMatrix S q.1 (ζ q.2))) :
    ContDiffOn ℝ ∞ (fun q ↦ transverseLeftInverse (transversePhaseMatrix S q.1 (ζ q.2))) U :=
  contDiffOn_transverseLeftInverse hδ hgap (contDiff_transversePhaseMatrix hS hζ).contDiffOn

set_option maxHeartbeats 800000 in
/-- Smoothness of the literal `V = (D_z Y) L` on the transverse-gap domain in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiffOn_transversePhaseCarrierCoefficient {n p : ℕ}
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ)
    {U : Set (Euclidean n × Euclidean p)} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q ∈ U, TransverseGap δ (transversePhaseMatrix S q.1 (ζ q.2))) :
    ContDiffOn ℝ ∞ (fun q ↦ transversePhaseCarrierCoefficient S ζ q.1 q.2) U := by
  intro q hq
  exact (contDiffAt_transverseCarrierCoefficient (n := n) (p := p)
    (q := transversePhaseInputs S ζ q) hδ (hgap q hq)).comp_contDiffWithinAt q
    (contDiff_transversePhaseInputs hS hζ).contDiffAt.contDiffWithinAt

/-- The literal left inverse obeys the uniform one-high bound in terms of the
actual mixed phase matrix. Estimating this input from primitive `S, ζ` jets is a
separate quantitative chain-rule step in `app:ch_background:eq:bg-derivative-trade`. -/
theorem exists_cNorm_transversePhaseLeftInverse_le_inputs {n p : ℕ}
    (q₀ : Euclidean n × Euclidean p) {ρ : ℝ} (hρ : 0 < ρ)
    (M : ℝ) {δ : ℝ} (hδ : 0 < δ) {r k : ℕ} (hrk : r ≤ k) :
    ∃ C > 0, ∀ (S : Euclidean n → Euclidean (n - 1) → ℝ)
      (ζ : Euclidean p → Euclidean (n - 1)),
      ContDiff ℝ ∞ (Function.uncurry S) → ContDiff ℝ ∞ ζ →
      (∀ q ∈ Metric.closedBall q₀ ρ,
        ‖transversePhaseMatrix S q.1 (ζ q.2)‖ ≤ M ∧
          TransverseGap δ (transversePhaseMatrix S q.1 (ζ q.2))) →
      cNorm (Metric.closedBall q₀ ρ) r
        (fun q ↦ transverseLeftInverse (transversePhaseMatrix S q.1 (ζ q.2))) ≤
      C * (1 + cNorm (Metric.closedBall q₀ ρ) k
        (fun q ↦ transversePhaseMatrix S q.1 (ζ q.2))) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_transverseLeftInverse_le_tame (n := n) q₀ hρ M hδ hrk
  exact ⟨C, hC, fun S ζ hS hζ hgap ↦ hb _ (contDiff_transversePhaseMatrix hS hζ) hgap⟩

set_option maxHeartbeats 800000 in
/-- The literal carrier coefficient obeys the uniform one-high rational bound.
The right side still measures the differentiated inputs; the primitive phase
and carrier chain-rule estimate is not asserted here.
Source: `app:ch_background:eq:bg-derivative-trade`. -/
theorem exists_cNorm_transversePhaseCarrierCoefficient_le_inputs {n p : ℕ}
    (q₀ : Euclidean n × Euclidean p) {ρ : ℝ} (hρ : 0 < ρ)
    (M B : ℝ) {δ : ℝ} (hδ : 0 < δ) {r k : ℕ} (hrk : r ≤ k) :
    ∃ C > 0, ∀ (S : Euclidean n → Euclidean (n - 1) → ℝ)
      (ζ : Euclidean p → Euclidean (n - 1)),
      ContDiff ℝ ∞ (Function.uncurry S) → ContDiff ℝ ∞ ζ →
      (∀ q ∈ Metric.closedBall q₀ ρ,
        (‖transversePhaseMatrix S q.1 (ζ q.2)‖ ≤ M ∧
          TransverseGap δ (transversePhaseMatrix S q.1 (ζ q.2))) ∧
          ‖transverseFootpointCarrierMatrix S ζ q.1 q.2‖ ≤ B) →
      cNorm (Metric.closedBall q₀ ρ) r
        (fun q ↦ transversePhaseCarrierCoefficient S ζ q.1 q.2) ≤
      C * (1 + cNorm (Metric.closedBall q₀ ρ) k (transversePhaseInputs S ζ)) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_transverseCarrierCoefficient_le_tame (n := n) (p := p) q₀ hρ M B hδ hrk
  refine ⟨C, hC, ?_⟩
  intro S ζ hS hζ hgap
  simpa only [transverseCarrierCoefficient, transversePhaseInputs,
    transversePhaseCarrierCoefficient] using
    hb (transversePhaseInputs S ζ) (contDiff_transversePhaseInputs hS hζ) hgap

end JanetCartan.ContinuumAdjoint
