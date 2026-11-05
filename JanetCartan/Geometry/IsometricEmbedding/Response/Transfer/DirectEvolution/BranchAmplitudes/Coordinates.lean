module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.LocalExpressions
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.ModifiedLow.SymbolBudget
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Fixed-parameter matrix amplitudes in the original normalized covector

The compact IBP expressions have values in `M × ℝ` and variables
`((x,c),(z,θ))`. The low graph calculus uses matrix amplitudes in `((x,z),θ)`.
This is the literal restriction/projection between those interfaces, for
`new:eq:carrier-ibp` and `app:ch_response:eq:direct-envelope-profile`.
Neither the phase nor the frequency is changed. The fixed coordinate norm
cost is independent of the parameter, frequency and coefficient scale.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
open FourierIntegral.FullAmplitudePrimitiveBudget.Local

variable {n : ℕ} {P M : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- The linear part of the fixed-parameter slice of the joint variables
in `new:eq:carrier-ibp`. -/
def normalizedSliceLinear : Point n →L[ℝ] ((Euclidean n × P) × CarrierVariables n) :=
  (((ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp
      (ContinuousLinearMap.fst ℝ (Euclidean n × Euclidean n) (Euclidean n))).prod 0).prod
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean n) (Euclidean n)).symm.toContinuousLinearMap.comp
      (((ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
          (ContinuousLinearMap.fst ℝ (Euclidean n × Euclidean n) (Euclidean n))).prod
        (ContinuousLinearMap.snd ℝ (Euclidean n × Euclidean n) (Euclidean n))))

/-- Fix only the carrier parameter, retaining both physical positions and
the original normalized covector (`new:eq:carrier-ibp`). -/
def normalizedSlice (c : P) (p : Point n) : (Euclidean n × P) × CarrierVariables n :=
  ((p.1.1, c), WithLp.toLp 2 (p.1.2, p.2))

/-- The fixed-parameter slice is affine with a parameter-independent linear
part. This is why restricting joint jets costs no scale power. -/
theorem normalizedSlice_eq_affine (c : P) :
    normalizedSlice (n := n) c = fun p => normalizedSliceLinear p + ((0, c), 0) := by
  funext p
  simp [normalizedSlice, normalizedSliceLinear]

/-- Smoothness of the literal coordinate slice used to restore the graph
amplitude in `new:eq:carrier-ibp`. -/
theorem contDiff_normalizedSlice (c : P) : ContDiff ℝ ∞ (normalizedSlice (n := n) c) := by
  rw [normalizedSlice_eq_affine]
  exact (normalizedSliceLinear (n := n) (P := P)).contDiff.add contDiff_const

/-- The matrix component of a joint expression at fixed parameter. All
parameter differentiations have already occurred in the expression itself;
this operation does not commute them past the operator. -/
def matrixSlice (c : P) (g : ((Euclidean n × P) × CarrierVariables n) → M × ℝ) :
    Point n → M := fun p => (g (normalizedSlice c p)).1

/-- Smoothness on the same supported box passes to the literal matrix slice.
Source: restoration of the carrier after `new:eq:carrier-ibp`. -/
theorem contDiffOn_matrixSlice {U : Set ((Euclidean n × P) × CarrierVariables n)}
    {g : ((Euclidean n × P) × CarrierVariables n) → M × ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (c : P) :
    ContDiffOn ℝ ∞ (matrixSlice c g) (normalizedSlice c ⁻¹' U) :=
  (hg.comp (contDiff_normalizedSlice c).contDiffOn (fun _ h => h)).fst

/-- Restricting a joint jet to the two-position matrix amplitude has only
the fixed linear-coordinate norm cost. The estimate is local; no global
critical geometry is required (`new:eq:carrier-coefficient`). -/
theorem norm_iteratedFDeriv_matrixSlice_le
    {U : Set ((Euclidean n × P) × CarrierVariables n)} (hU : IsOpen U)
    {g : ((Euclidean n × P) × CarrierVariables n) → M × ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (c : P) {p : Point n}
    (hp : normalizedSlice c p ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (matrixSlice c g) p‖ ≤
      ‖iteratedFDeriv ℝ j g (normalizedSlice c p)‖ *
        ‖normalizedSliceLinear (n := n) (P := P)‖ ^ j := by
  let v : (Euclidean n × P) × CarrierVariables n := ((0, c), 0)
  let F := fun y => (g (y + v)).1
  have hV : IsOpen ((fun y => y + v) ⁻¹' U) := hU.preimage (continuous_id.add continuous_const)
  have hF : ContDiffOn ℝ ∞ F ((fun y => y + v) ⁻¹' U) :=
    (hg.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ h => h)).fst
  have hp' : normalizedSliceLinear p ∈ (fun y => y + v) ⁻¹' U := by
    simpa only [normalizedSlice_eq_affine, v, mem_preimage] using hp
  have h := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (normalizedSliceLinear (n := n) (P := P)) hV hF hp' j
  change ‖iteratedFDeriv ℝ j (fun y => (g (normalizedSliceLinear y + v)).1) p‖ ≤ _ at h
  have he : (fun y => (g (normalizedSliceLinear y + v)).1) = matrixSlice c g := by
    funext y
    change (g (normalizedSliceLinear y + v)).1 = (g (normalizedSlice c y)).1
    rw [normalizedSlice_eq_affine]
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
  change ‖iteratedFDeriv ℝ j ((fun y => (g y).1) ∘ (fun y => y + v))
    (normalizedSliceLinear p)‖ ≤ _
  simp only [Function.comp_def]
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => (g y).1) j v]
  have hproj := (ContinuousLinearMap.fst ℝ M ℝ).norm_iteratedFDeriv_comp_left
    (hg.contDiffAt (hU.mem_nhds hp)) (by simp : (j : ℕ∞ω) ≤ ∞)
  have hb := hproj.trans (mul_le_mul_of_nonneg_right
    (ContinuousLinearMap.norm_fst_le ℝ M ℝ) (norm_nonneg _))
  simpa only [normalizedSlice_eq_affine, Function.comp_def, ContinuousLinearMap.coe_fst',
    one_mul, v] using hb

end JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
