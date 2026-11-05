module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FamilyConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ZeroEnergy

/-!
# Differentiating the literal zero-energy restriction

The chain rules needed by `exists_finite_carrierPhase_assembly`, for Steps 1–2 of
`app:ch_seed:prop:seed-actual-menu`. Comparisons are inputs on the full Hamilton
phase, before restriction to the frozen patches.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.ActualCarriers
open HamiltonPhase

variable {E U Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {H H₀ : HomogeneousSymbol E} {Φ : HamiltonFlow H U} {Φ₀ : HamiltonFlow H₀ U}

omit [CompleteSpace E] in
/-- Joint smoothness survives the exact `e = 0` restriction
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem contDiffOn_carrierPhase (C : ProjectionChart Φ) {ζ : Z → U}
    {B : Set E} {W : Set Z}
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hmap : ∀ x ∈ B, ∀ z ∈ W, (x, (0, ζ z)) ∈ C.target) :
    ContDiffOn ℝ ∞ (fun q : E × Z ↦ carrierPhase C ζ q.1 q.2) (B ×ˢ W) := by
  exact (C.contDiffOn_phase hC).comp
    (contDiffOn_fst.prodMk (contDiffOn_const.prodMk
      (hζ.comp contDiffOn_snd (fun _ h ↦ h.2)))) (fun q h ↦ hmap q.1 h.1 q.2 h.2)

/-- Joint smoothness of the actual carrier gradients follows by restriction of
transported momentum (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem contDiffOn_carrierGradient (C : ProjectionChart Φ) {ζ : Z → U}
    {B : Set E} {W : Set Z}
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hmap : ∀ x ∈ B, ∀ z ∈ W, (x, (0, ζ z)) ∈ C.target) :
    ContDiffOn ℝ ∞ (fun q : E × Z ↦ gradient (fun y ↦ carrierPhase C ζ y q.2) q.1)
      (B ×ˢ W) := by
  have hs : ContDiffOn ℝ ∞ (fun q : E × Z ↦ C.chartMomentum (q.1, (0, ζ q.2)))
      (B ×ˢ W) := (C.contDiffOn_chartMomentum hp hC).comp
    (contDiffOn_fst.prodMk (contDiffOn_const.prodMk
      (hζ.comp contDiffOn_snd (fun _ h ↦ h.2)))) (fun q h ↦ hmap q.1 h.1 q.2 h.2)
  apply hs.congr
  intro q hq
  exact (hasGradientAt_carrierPhase C ζ (hmap q.1 hq.1 q.2 hq.2)).gradient

/-- Chain rule for the parameter derivative of the physical carrier gradient
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem hasFDerivAt_carrierGradient_parameter (C : ProjectionChart Φ) {ζ : Z → U}
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target) {x : E} {z : Z}
    (hζ : DifferentiableAt ℝ ζ z) (hz : (x, (0, ζ z)) ∈ C.target) :
    HasFDerivAt (fun w ↦ gradient (fun y ↦ carrierPhase C ζ y w) x)
      ((fderiv ℝ C.chartMomentum (x, (0, ζ z))).comp
        ((0 : Z →L[ℝ] E).prod ((0 : Z →L[ℝ] ℝ).prod (fderiv ℝ ζ z)))) z := by
  have hm := ((C.contDiffOn_chartMomentum hp hC).contDiffAt
    (C.isOpen_target.mem_nhds hz)).differentiableAt (by simp)
  have hg := (hasFDerivAt_const x z).prodMk
    ((hasFDerivAt_const (0 : ℝ) z).prodMk hζ.hasFDerivAt)
  apply (hm.hasFDerivAt.comp z hg).congr_of_eventuallyEq
  have hn := (continuousAt_const.prodMk
    (continuousAt_const.prodMk hζ.continuousAt)).preimage_mem_nhds
      (C.isOpen_target.mem_nhds hz)
  filter_upwards [hn] with w hw
  exact (hasGradientAt_carrierPhase C ζ hw).gradient

/-- A full-phase first-derivative comparison gives the parameter derivative
comparison with precisely the spatial-patch derivative factor
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem norm_carrierGradient_parameter_sub_le
    (C : ProjectionChart Φ) (C₀ : ProjectionChart Φ₀) {ζ : Z → U}
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    (hp₀ : ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters))
    (hC₀ : ContDiffOn ℝ ∞ C₀.coordinates C₀.target)
    {x : E} {z : Z} (hζ : DifferentiableAt ℝ ζ z)
    (hz : (x, (0, ζ z)) ∈ C.target) (hz₀ : (x, (0, ζ z)) ∈ C₀.target)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomp : ‖fderiv ℝ C.chartMomentum (x, (0, ζ z)) -
      fderiv ℝ C₀.chartMomentum (x, (0, ζ z))‖ ≤ ε) :
    ‖fderiv ℝ (fun w ↦ gradient (fun y ↦ carrierPhase C ζ y w) x) z -
      fderiv ℝ (fun w ↦ gradient (fun y ↦ carrierPhase C₀ ζ y w) x) z‖ ≤
        ε * ‖fderiv ℝ ζ z‖ := by
  rw [(hasFDerivAt_carrierGradient_parameter C hp hC hζ hz).fderiv,
    (hasFDerivAt_carrierGradient_parameter C₀ hp₀ hC₀ hζ hz₀).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg _))
  intro v
  have hb := (fderiv ℝ C.chartMomentum (x, (0, ζ z)) -
    fderiv ℝ C₀.chartMomentum (x, (0, ζ z))).le_opNorm
      (0, (0, fderiv ℝ ζ z v))
  have hn : ‖((0 : E), ((0 : ℝ), fderiv ℝ ζ z v))‖ = ‖fderiv ℝ ζ z v‖ := by
    simp [Prod.norm_def]
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply] at *
  rw [hn] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right hcomp (norm_nonneg _)).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left ((fderiv ℝ ζ z).le_opNorm v) hε))

/-- The affine frozen full phase has its stated positive-sign covector as
physical gradient. This checks the sign before any carrier restriction
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem chartMomentum_eq_of_phase_linear (C₀ : ProjectionChart Φ₀)
    (κ : (ℝ × U) → E)
    (hlinear : ∀ q ∈ C₀.target, phase C₀.coordinates q = ⟪κ q.2, q.1⟫_ℝ)
    {q : E × (ℝ × U)} (hq : q ∈ C₀.target) : C₀.chartMomentum q = κ q.2 := by
  have he : (fun x ↦ phase C₀.coordinates (x, q.2)) =ᶠ[𝓝 q.1]
      (fun x ↦ ⟪κ q.2, x⟫_ℝ) := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (C₀.isOpen_target.mem_nhds hq)
    filter_upwards [hn] with x hx using hlinear _ hx
  have hg : HasGradientAt (fun x ↦ ⟪κ q.2, x⟫_ℝ) (κ q.2) q.1 :=
    (innerSL ℝ (κ q.2)).hasFDerivAt
  rw [← C₀.gradient_phase_eq_chartMomentum hq]
  exact (hg.congr_of_eventuallyEq he).gradient

end JanetCartan.ActualCarriers
