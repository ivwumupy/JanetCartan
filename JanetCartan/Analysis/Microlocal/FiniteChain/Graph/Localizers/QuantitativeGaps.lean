module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Gaps

/-!
# Quantitative chart control of the joint gradient

For `app:ch_regular:lem:finite-chain`, inverse mixed bounds and Lipschitz bounds
on first phase derivatives control distance from the canonical image by the
actual packed derivative. These low geometric constants can be shared by an
arbitrary phase family; compactness of that family is not assumed. The parent
chart construction supplies these geometric inequalities on the actual domain.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph
open Set
open FourierIntegral

/-- An explicit low geometric loss for the graph gradient gap
(`app:ch_regular:lem:finite-chain`). -/
def graphGapConstant (A B : ℝ) : ℝ :=
  3 + A * (B + 2) + B * (A * (B + 2) + 1)

/-- The geometric loss is strictly positive for nonnegative inverse and
Lipschitz bounds (`app:ch_regular:lem:finite-chain`). -/
theorem graphGapConstant_pos {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 < graphGapConstant A B := by
  unfold graphGapConstant
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quantitative forward distance to the actual canonical image. `hinv` is the
inverse mixed bound in the base variable, `hξlip` and `hulip` are low first-jet
bounds. The parent supplies them on its conic chart; no phase is differentiated
outside that chart (`app:ch_regular:eq:joint-stationary`). -/
theorem forward_chart_distance_le_jointDerivative
    (φ : E → E → ℝ) (x y u z ξ η ζ v ω : E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (u, ξ))
    (hchart : ForwardRelation φ y η v ω)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hinv : ‖u-v‖ ≤ A * ‖fderiv ℝ (φ u) η - fderiv ℝ (φ v) η‖)
    (hξlip : ‖fderiv ℝ (φ u) η - fderiv ℝ (φ u) ξ‖ ≤ B * ‖η-ξ‖)
    (hulip : ‖fderiv ℝ (fun w => φ w η) v - fderiv ℝ (fun w => φ w ξ) u‖ ≤
      B * (‖u-v‖ + ‖η-ξ‖)) :
    dist (x, ζ) (v, ω) ≤ graphGapConstant A B *
      ‖fderiv ℝ (jointPhase false φ x y) ((u,z),ξ,η,ζ)‖ := by
  let G := ‖fderiv ℝ (jointPhase false φ x y) ((u,z),ξ,η,ζ)‖
  have hG : 0 ≤ G := by positivity
  obtain ⟨h1,h2,h3,h4,h5⟩ := forward_joint_derivative_bounds φ x y ((u,z),ξ,η,ζ) hφ
  change ‖fderiv ℝ (fun w => φ w ξ) u - innerSL ℝ ζ‖ ≤ G at h1
  change ‖η-ξ‖ ≤ G at h2
  change ‖fderiv ℝ (φ u) ξ - innerSL ℝ z‖ ≤ G at h3
  change ‖z-y‖ ≤ G at h4
  change ‖x-u‖ ≤ G at h5
  have hres : ‖fderiv ℝ (φ u) η - fderiv ℝ (φ v) η‖ ≤ (B+2)*G := by
    rw [hchart.2]
    have ht1 := norm_sub_le_norm_sub_add_norm_sub
      (fderiv ℝ (φ u) η) (fderiv ℝ (φ u) ξ) (innerSL ℝ y)
    have ht2 := norm_sub_le_norm_sub_add_norm_sub
      (fderiv ℝ (φ u) ξ) (innerSL ℝ z) (innerSL ℝ y)
    rw [← map_sub, innerSL_apply_norm] at ht2
    have hb := mul_le_mul_of_nonneg_left h2 hB
    linarith
  have huv : ‖u-v‖ ≤ A*(B+2)*G := by
    have hh := hinv.trans (mul_le_mul_of_nonneg_left hres hA)
    simpa only [mul_assoc] using hh
  have hxv : ‖x-v‖ ≤ (1+A*(B+2))*G := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x u v
    linarith
  have hζω : ‖ζ-ω‖ ≤ (1+B*(A*(B+2)+1))*G := by
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (innerSL ℝ ζ) (fderiv ℝ (fun w => φ w ξ) u) (innerSL ℝ ω)
    rw [← map_sub, innerSL_apply_norm,
      norm_sub_rev (innerSL ℝ ζ) (fderiv ℝ (fun w => φ w ξ) u), ← hchart.1,
      norm_sub_rev (fderiv ℝ (fun w => φ w ξ) u) (fderiv ℝ (fun w => φ w η) v)] at ht
    have hb := mul_le_mul_of_nonneg_left (add_le_add huv h2) hB
    nlinarith
  rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
  apply max_le
  · refine hxv.trans ?_
    apply mul_le_mul_of_nonneg_right _ hG
    unfold graphGapConstant
    have : 0 ≤ B*(A*(B+2)+1) := by positivity
    linarith
  · refine hζω.trans ?_
    apply mul_le_mul_of_nonneg_right _ hG
    unfold graphGapConstant
    have : 0 ≤ A*(B+2) := by positivity
    linarith

/-- Quantitative distance to the literal inverse graph. The mixed inverse is
now used in the covector variable at the input base. Both base equations remain
in the bound (`app:ch_regular:lem:finite-chain`). -/
theorem reverse_chart_distance_le_jointDerivative
    (φ : E → E → ℝ) (x y u z ξ η ζ w θ : E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (u, ξ))
    (hchart : ForwardRelation φ w θ y η)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hinv : ‖ξ-θ‖ ≤ A *
      ‖fderiv ℝ (fun v => φ v ξ) y - fderiv ℝ (fun v => φ v θ) y‖)
    (hulip : ‖fderiv ℝ (fun v => φ v ξ) y - fderiv ℝ (fun v => φ v ξ) u‖ ≤
      B * ‖u-y‖)
    (hξlip : ‖fderiv ℝ (φ y) θ - fderiv ℝ (φ u) ξ‖ ≤ B * (‖u-y‖ + ‖ξ-θ‖)) :
    dist (x, ζ) (w, θ) ≤ graphGapConstant A B *
      ‖fderiv ℝ (jointPhase true φ x y) ((u,z),ξ,η,ζ)‖ := by
  let G := ‖fderiv ℝ (jointPhase true φ x y) ((u,z),ξ,η,ζ)‖
  have hG : 0 ≤ G := by positivity
  obtain ⟨h1,h2,h3,h4,h5⟩ := reverse_joint_derivative_bounds φ x y ((u,z),ξ,η,ζ) hφ
  change ‖innerSL ℝ η - fderiv ℝ (fun v => φ v ξ) u‖ ≤ G at h1
  change ‖ξ-ζ‖ ≤ G at h2
  change ‖innerSL ℝ z - fderiv ℝ (φ u) ξ‖ ≤ G at h3
  change ‖u-y‖ ≤ G at h4
  change ‖x-z‖ ≤ G at h5
  have hres : ‖fderiv ℝ (fun v => φ v ξ) y - fderiv ℝ (fun v => φ v θ) y‖ ≤
      (B+2)*G := by
    rw [hchart.1]
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (fderiv ℝ (fun v => φ v ξ) y) (fderiv ℝ (fun v => φ v ξ) u) (innerSL ℝ η)
    rw [norm_sub_rev (fderiv ℝ (fun v => φ v ξ) u)] at ht
    have hb := mul_le_mul_of_nonneg_left h4 hB
    linarith
  have hξθ : ‖ξ-θ‖ ≤ A*(B+2)*G := by
    have hh := hinv.trans (mul_le_mul_of_nonneg_left hres hA)
    simpa only [mul_assoc] using hh
  have hxw : ‖x-w‖ ≤ (2+B*(A*(B+2)+1))*G := by
    have ht1 := norm_sub_le_norm_sub_add_norm_sub x z w
    have ht2 := norm_sub_le_norm_sub_add_norm_sub
      (innerSL ℝ z) (fderiv ℝ (φ u) ξ) (innerSL ℝ w)
    rw [← map_sub, innerSL_apply_norm, ← hchart.2,
      norm_sub_rev (fderiv ℝ (φ u) ξ)] at ht2
    have hb := mul_le_mul_of_nonneg_left (add_le_add h4 hξθ) hB
    nlinarith
  have hζθ : ‖ζ-θ‖ ≤ (1+A*(B+2))*G := by
    have ht := norm_sub_le_norm_sub_add_norm_sub ζ ξ θ
    rw [norm_sub_rev ζ ξ] at ht
    linarith
  rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
  apply max_le
  · refine hxw.trans ?_
    apply mul_le_mul_of_nonneg_right _ hG
    unfold graphGapConstant
    have : 0 ≤ A*(B+2) := by positivity
    linarith
  · refine hζθ.trans ?_
    apply mul_le_mul_of_nonneg_right _ hG
    unfold graphGapConstant
    have : 0 ≤ B*(A*(B+2)+1) := by positivity
    linarith

end JanetCartan.FiniteChain.Graph
