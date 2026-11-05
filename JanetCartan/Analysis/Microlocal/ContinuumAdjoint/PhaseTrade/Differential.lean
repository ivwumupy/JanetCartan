module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Literal rectangular phase derivatives

The three identities in `app:ch_background:eq:bg-derivative-trade`, for the
actual phase `Φ(x,z,η) = d_ζ S(x,ζ(z))[η]`. Smoothness and the transverse gap
remain inputs from the Hamilton construction. The carrier chain rule retains
`Dζ`; none of the identities is an input field.
-/

@[expose] public noncomputable section

open Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint

variable {n p : ℕ}

/-- The actual footpoint coordinates `d_ζ S(x,ζ(z))` in
`app:ch_background:eq:bg-derivative-trade`. -/
def transverseFootpoint (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean p → Euclidean (n - 1)) (x : Euclidean n) (z : Euclidean p) :
    Fin (n - 1) → ℝ := fun j ↦ partialDeriv (S x) (ζ z) j

/-- The literal transport phase in `app:ch_background:eq:bg-derivative-trade`.
The transverse covector is physical, with no torus normalization. -/
def transverseTransportPhase (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean p → Euclidean (n - 1)) (x : Euclidean n) (z : Euclidean p)
    (η : Euclidean (n - 1)) : ℝ := fderiv ℝ (S x) (ζ z) η

/-- The actual rectangular matrix `D_ζ d_x S` in
`app:ch_background:eq:bg-derivative-trade`. -/
def transversePhaseMatrix (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (x : Euclidean n) (ξ : Euclidean (n - 1)) : TransverseMatrix n :=
  fun i j ↦ partialDeriv (fun ξ' ↦ partialDeriv (fun y ↦ S y ξ') x i) ξ j

/-- The actual carrier derivative `D_z Y` in
`app:ch_background:eq:bg-derivative-trade`. -/
def transverseFootpointCarrierMatrix (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean p → Euclidean (n - 1)) (x : Euclidean n) (z : Euclidean p) :
    Matrix (Fin p) (Fin (n - 1)) ℝ :=
  fun l j ↦ partialDeriv (fun w ↦ transverseFootpoint S ζ x w j) z l

private theorem dual_apply_eq_sum {m : ℕ} (f : Euclidean m →L[ℝ] ℝ)
    (v : Euclidean m) : f v = ∑ j, f (EuclideanSpace.single j 1) * v j := by
  have h := congrArg f ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v)
  simpa [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, mul_comm] using h.symm

/-- `Φ = Y · η` for the literal footpoint, with no hypotheses; source:
`app:ch_background:eq:bg-derivative-trade`. -/
theorem transverseTransportPhase_eq_dotProduct
    (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean p → Euclidean (n - 1)) (x : Euclidean n) (z : Euclidean p)
    (η : Euclidean (n - 1)) :
    transverseTransportPhase S ζ x z η = transverseFootpoint S ζ x z ⬝ᵥ (fun j ↦ η j) :=
  dual_apply_eq_sum _ _

private theorem mixed_slice_derivatives_comm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : E → F → ℝ} {x : E} {ξ : F}
    (hS : ContDiffAt ℝ 2 (Function.uncurry S) (x, ξ)) (v : E) (w : F) :
    fderiv ℝ (fun y ↦ fderiv ℝ (S y) ξ w) x v =
      fderiv ℝ (fun ξ' ↦ fderiv ℝ (fun y ↦ S y ξ') x v) ξ w := by
  let f := Function.uncurry S
  have heq₁ : (fun y ↦ fderiv ℝ (S y) ξ w) =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ f (y, ξ) (0, w)) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).tendsto.eventually
      (hS.eventually (by norm_num))] with y hy
    exact congrArg (fun L : F →L[ℝ] ℝ ↦ L w)
      ((hy.differentiableAt (by norm_num)).hasFDerivAt.comp ξ
        (hasFDerivAt_prodMk_right y ξ)).fderiv
  have heq₂ : (fun ξ' ↦ fderiv ℝ (fun y ↦ S y ξ') x v) =ᶠ[𝓝 ξ]
      (fun ξ' ↦ fderiv ℝ f (x, ξ') (v, 0)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).tendsto.eventually
      (hS.eventually (by norm_num))] with ξ' hξ'
    exact congrArg (fun L : E →L[ℝ] ℝ ↦ L v)
      ((hξ'.differentiableAt (by norm_num)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x ξ')).fderiv
  have hd := (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [heq₁.fderiv_eq, heq₂.fderiv_eq]
  have hleft := ((ContinuousLinearMap.apply ℝ ℝ ((0 : E), w)).hasFDerivAt.comp x
    (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x ξ))).fderiv
  have hright := ((ContinuousLinearMap.apply ℝ ℝ (v, (0 : F))).hasFDerivAt.comp ξ
    (hd.hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right x ξ))).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hleft hright
  rw [hleft, hright]
  exact hS.isSymmSndFDerivAt (by norm_num) (v, 0) (0, w)

/-- The physical phase derivative is the actual rectangular mixed matrix
times `η`; source: `app:ch_background:eq:bg-derivative-trade`. -/
theorem partialDeriv_transverseTransportPhase_physical
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    (ζ : Euclidean p → Euclidean (n - 1)) {x : Euclidean n} (z : Euclidean p)
    (hS : ContDiffAt ℝ 2 (Function.uncurry S) (x, ζ z))
    (η : Euclidean (n - 1)) (i : Fin n) :
    partialDeriv (fun y ↦ transverseTransportPhase S ζ y z η) x i =
      (transversePhaseMatrix S x (ζ z) *ᵥ (fun j ↦ η j)) i := by
  unfold partialDeriv transverseTransportPhase
  rw [mixed_slice_derivatives_comm hS]
  exact dual_apply_eq_sum _ _

/-- The initial covector is recovered by the Gram left inverse of the actual
phase matrix; source: `app:ch_background:eq:bg-derivative-trade`. -/
theorem transverseTransportPhase_initial_trade
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    (ζ : Euclidean p → Euclidean (n - 1)) {x : Euclidean n} (z : Euclidean p)
    (hS : ContDiffAt ℝ 2 (Function.uncurry S) (x, ζ z))
    {δ : ℝ} (hδ : 0 < δ) (hgap : TransverseGap δ (transversePhaseMatrix S x (ζ z)))
    (η : Euclidean (n - 1)) :
    transverseLeftInverse (transversePhaseMatrix S x (ζ z)) *ᵥ
      (fun i ↦ partialDeriv (fun y ↦ transverseTransportPhase S ζ y z η) x i) =
        fun j ↦ η j := by
  simp_rw [partialDeriv_transverseTransportPhase_physical ζ z hS]
  exact transverseLeftInverse_mulVec hδ hgap _

private theorem fderiv_transverseTransportPhase_carrier
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)} {x : Euclidean n} {z : Euclidean p}
    (hS : ContDiffAt ℝ 2 (S x) (ζ z)) (hζ : DifferentiableAt ℝ ζ z)
    (η : Euclidean (n - 1)) (v : Euclidean p) :
    fderiv ℝ (fun w ↦ transverseTransportPhase S ζ x w η) z v =
      fderiv ℝ (fderiv ℝ (S x)) (ζ z) (fderiv ℝ ζ z v) η := by
  have hd := (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := ((ContinuousLinearMap.apply ℝ ℝ η).hasFDerivAt.comp z
    (hd.hasFDerivAt.comp z hζ.hasFDerivAt)).fderiv
  exact congrArg (fun L : Euclidean p →L[ℝ] ℝ ↦ L v) h

/-- The actual carrier derivative contains the carrier Jacobian. This is the
chain rule behind `V_ℓ` in `app:ch_background:eq:bg-derivative-trade`. -/
theorem transverseFootpointCarrierMatrix_eq_hessian
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)} {x : Euclidean n} {z : Euclidean p}
    (hS : ContDiffAt ℝ 2 (S x) (ζ z)) (hζ : DifferentiableAt ℝ ζ z)
    (l : Fin p) (j : Fin (n - 1)) :
    transverseFootpointCarrierMatrix S ζ x z l j =
      fderiv ℝ (fderiv ℝ (S x)) (ζ z) (partialDeriv ζ z l)
        (EuclideanSpace.single j 1) :=
  fderiv_transverseTransportPhase_carrier hS hζ _ _

/-- The raw carrier phase derivative is `(D_z Y) η`, before applying the left
inverse; source: `app:ch_background:eq:bg-derivative-trade`. -/
theorem partialDeriv_transverseTransportPhase_carrier
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)} {x : Euclidean n} {z : Euclidean p}
    (hS : ContDiffAt ℝ 2 (S x) (ζ z)) (hζ : DifferentiableAt ℝ ζ z)
    (η : Euclidean (n - 1)) (l : Fin p) :
    partialDeriv (fun w ↦ transverseTransportPhase S ζ x w η) z l =
      (transverseFootpointCarrierMatrix S ζ x z *ᵥ (fun j ↦ η j)) l := by
  unfold partialDeriv
  rw [fderiv_transverseTransportPhase_carrier hS hζ]
  simp only [Matrix.mulVec, dotProduct, transverseFootpointCarrierMatrix_eq_hessian hS hζ]
  exact dual_apply_eq_sum _ _

/-- The literal `V = (D_z Y) L` in
`app:ch_background:eq:bg-derivative-trade`. -/
def transversePhaseCarrierCoefficient (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean p → Euclidean (n - 1)) (x : Euclidean n) (z : Euclidean p) :
    Matrix (Fin p) (Fin n) ℝ :=
  transverseFootpointCarrierMatrix S ζ x z *
    transverseLeftInverse (transversePhaseMatrix S x (ζ z))

/-- The carrier derivative trades for physical derivatives, using the actual
phase matrix and the actual carrier derivative, as in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem transverseTransportPhase_carrier_trade
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)} {x : Euclidean n} {z : Euclidean p}
    (hS : ContDiffAt ℝ 2 (Function.uncurry S) (x, ζ z))
    (hζ : DifferentiableAt ℝ ζ z)
    {δ : ℝ} (hδ : 0 < δ) (hgap : TransverseGap δ (transversePhaseMatrix S x (ζ z)))
    (η : Euclidean (n - 1)) (l : Fin p) :
    partialDeriv (fun w ↦ transverseTransportPhase S ζ x w η) z l =
      ∑ i, transversePhaseCarrierCoefficient S ζ x z l i *
        partialDeriv (fun y ↦ transverseTransportPhase S ζ y z η) x i := by
  have hSx : ContDiffAt ℝ 2 (S x) (ζ z) :=
    hS.comp (ζ z) (contDiffAt_const.prodMk contDiffAt_id)
  rw [partialDeriv_transverseTransportPhase_carrier hSx hζ]
  change _ = ((transverseFootpointCarrierMatrix S ζ x z *
    transverseLeftInverse (transversePhaseMatrix S x (ζ z))) *ᵥ _) l
  rw [← Matrix.mulVec_mulVec, transverseTransportPhase_initial_trade ζ z hS hδ hgap]

end JanetCartan.ContinuumAdjoint
