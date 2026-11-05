module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.SelectorBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.CoordinateDerivatives

/-!
# Ordered target derivatives followed by source jets

The joint grades are converted to the exact `normalMatrixDerivList` / source
`iteratedFDeriv` expression consumed by `GraphDecay.hAj`, without changing the
frequency exponent. Source: `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

open NormalComparison

variable {X Y F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Freezing a parameter or position restricts joint jets along an affine
contraction. This is the restriction step in `GraphDecay.hAj` for
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_affine_contraction_le
    (T : X →L[ℝ] Y) (hT : ‖T‖ ≤ 1) (a : Y)
    {f : Y → F} {U : Set Y} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (j : ℕ) {x : X} (hx : a + T x ∈ U) :
    ‖iteratedFDeriv ℝ j (fun w ↦ f (a + T w)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (a + T x)‖ := by
  have hpre : IsOpen ((fun y : Y ↦ a + y) ⁻¹' U) :=
    hU.preimage (continuous_const.add continuous_id)
  have ht : ContDiffOn ℝ ∞ (fun y : Y ↦ f (a + y)) ((fun y : Y ↦ a + y) ⁻¹' U) :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun _ hy ↦ hy)
  have h := ParameterAmplitudeBudget.norm_jet_comp_contraction_le T hT hpre
    (ht.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) le_rfl hx
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_left] using h

/-- Restriction to the spatial variables at a fixed parameter costs no extra
order or scale power in `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_fixed_parameter_le
    {f : X × Y → F} {C : Set X} (hC : IsOpen C)
    (hf : ContDiffOn ℝ ∞ f (C ×ˢ Set.univ))
    {c : X} (hc : c ∈ C) (y : Y) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun w ↦ f (c, w)) y‖ ≤
      ‖iteratedFDeriv ℝ j f (c, y)‖ := by
  let T : Y →L[ℝ] X × Y := (0 : Y →L[ℝ] X).prod (ContinuousLinearMap.id ℝ Y)
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro w
    simp [T, Prod.norm_def]
  have h := norm_iteratedFDeriv_affine_contraction_le T hT (c, (0 : Y))
    (hC.prod isOpen_univ) hf j (x := y) (by simpa [T] using hc)
  simpa [T] using h

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "M" => Matrix (Fin r) (Fin r) ℂ

/-- Joint smoothness survives the actual ordered target derivatives; the source
variable remains a spectator throughout. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiff_normalMatrixDerivList_joint {f : E × E → M}
    (hf : ContDiff ℝ ∞ f) (β : List (Fin n)) :
    ContDiff ℝ ∞ (fun p : E × E ↦ normalMatrixDerivList β (fun x ↦ f (x, p.2)) p.1) := by
  induction β with
  | nil => exact hf
  | cons i β ih =>
      have h := contDiffOn_parameterFDeriv isOpen_univ isOpen_univ
        (by simpa only [Set.univ_prod_univ] using ih.contDiffOn)
        (EuclideanSpace.single i (1 : ℝ))
      simpa only [Set.univ_prod_univ, contDiffOn_univ, normalMatrixDerivList] using h

/-- The target derivative list spends exactly its length in joint physical
jets. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_normalMatrixDerivList_joint_le {f : E × E → M}
    (hf : ContDiff ℝ ∞ f) (β : List (Fin n)) (j : ℕ) (p : E × E) :
    ‖iteratedFDeriv ℝ j (fun z : E × E ↦
      normalMatrixDerivList β (fun x ↦ f (x, z.2)) z.1) p‖ ≤
      ‖iteratedFDeriv ℝ (j + β.length) f p‖ := by
  induction β generalizing j with
  | nil => simp [normalMatrixDerivList]
  | cons i β ih =>
      have h := norm_iteratedFDeriv_parameterFDeriv_le isOpen_univ
        (contDiff_normalMatrixDerivList_joint hf β).contDiffOn (Set.mem_univ p)
        (EuclideanSpace.single i (1 : ℝ)) j
      simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, one_mul] at h
      apply h.trans
      have hj := ih (j + 1)
      have hexp : j + 1 + β.length = j + (i :: β).length := by simp; omega
      rw [hexp] at hj
      exact hj

/-- Exact mixed target/source derivative conversion used by both directions
of `GraphDecay`. No frequency loss occurs at this step. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_sourceJet_normalMatrixDerivList_le_joint {f : E × E → M}
    (hf : ContDiff ℝ ∞ f) (β : List (Fin n)) (j : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β (fun v ↦ f (v, w)) x) y‖ ≤
      ‖iteratedFDeriv ℝ (j + β.length) f (x, y)‖ := by
  exact (norm_iteratedFDeriv_fixed_parameter_le isOpen_univ
    (by simpa only [Set.univ_prod_univ] using
      (contDiff_normalMatrixDerivList_joint hf β).contDiffOn)
    (Set.mem_univ x) y j).trans
    (norm_iteratedFDeriv_normalMatrixDerivList_joint_le hf β j (x, y))

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
