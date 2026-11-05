module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.AllData

/-!
# Scalar specialization of spatial graph transfer

The one-dimensional Euclidean fiber is identified with the scalar Lebesgue
L² space used by `HasSpatialAmplitudeTransfer`. This retains the same measure,
coordinate, and distribution conventions in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral Pseudodifferential
variable {n : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin 1)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The literal single-fiber/scalar identification for
`app:ch_response:eq:direct-envelope-profile`, with unchanged Lebesgue measure. -/
def scalarGraphL2Equiv : H ≃L[ℂ] L2 :=
  (finiteL2CoordinateIsometry volume).toContinuousLinearEquiv.trans
    (PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 ↦ L2))

/-- The scalar identification is the existing coordinate projection, as needed
by `HasEuclideanL2CoordinateDerivative` in the spatial profile. -/
theorem scalarGraphL2Equiv_apply (u : H) :
    scalarGraphL2Equiv u = finiteL2CoordinateIsometry volume u 0 := rfl

/-- The scalar and single-fiber weak derivative conventions agree exactly,
for `app:ch_response:eq:direct-envelope-profile`. -/
theorem scalarGraphL2Equiv_derivative_iff (i : Fin n) (u v : H) :
    HasEuclideanL2CoordinateDerivative i (scalarGraphL2Equiv u) (scalarGraphL2Equiv v) ↔
      lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (u : 𝓢'(E, V)) = (v : 𝓢'(E, V)) := by
  constructor
  · intro h
    ext φ : 1
    apply PiLp.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    have he := congrArg (fun D : 𝓢'(E, ℂ) ↦ D φ) h
    change ((scalarGraphL2Equiv u : L2) : 𝓢'(E, ℂ))
        (-lineDerivOp (EuclideanSpace.basisFun (Fin n) ℝ i) φ) =
      ((scalarGraphL2Equiv v : L2) : 𝓢'(E, ℂ)) φ at he
    simp only [scalarGraphL2Equiv_apply, graphL2_coordinate_distribution,
      EuclideanSpace.basisFun_apply] at he
    exact he
  · intro h
    exact graphL2_coordinate_derivative h 0

/-- Scalar realization of a bounded operator on the actual one-dimensional
Euclidean fiber. Consumed by `HasSpatialAmplitudeTransfer`. -/
def scalarGraphOperator (T : H →L[ℂ] H) : L2 →L[ℂ] L2 :=
  scalarGraphL2Equiv.toContinuousLinearMap.comp
    (T.comp scalarGraphL2Equiv.symm.toContinuousLinearMap)

/-- Conjugation preserves the proved vector transfer identity. This is only
the scalar-coordinate conversion; the literal all-data identities below supply
its derivative premise. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem scalarGraphOperator_derivative (T U : H →L[ℂ] H)
    (W : Fin n → H →L[ℂ] H) (i : Fin n) (u : L2) (du : Fin n → L2)
    (h : lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (T (scalarGraphL2Equiv.symm u) : 𝓢'(E, V)) =
      (U (scalarGraphL2Equiv.symm u) + ∑ j, W j (scalarGraphL2Equiv.symm (du j)) : H)) :
    HasEuclideanL2CoordinateDerivative i (scalarGraphOperator T u)
      (scalarGraphOperator U u + ∑ j, scalarGraphOperator (W j) (du j)) := by
  have he := (scalarGraphL2Equiv_derivative_iff i _ _).mpr h
  simpa only [map_add, map_sum, scalarGraphOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe] using he

/-- Forward transfer on scalar Euclidean Lebesgue L², with the
literal bounded single-fiber operators transported by `scalarGraphL2Equiv`.
This is the scalar specialization consumed by `HasSpatialAmplitudeTransfer`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem forwardGraph_allData_scalar_derivative
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {Φ : E → E → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ))
    {A : FullAmplitude n 1} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B : E → E → Matrix (Fin n) (Fin n) ℝ} (i : Fin n)
    (hB : ∀ j, ContDiff ℝ ∞ (fun p : E × E ↦ B p.1 p.2 i j))
    (hgrad : ∀ x δ, partialDeriv (fun z ↦ Φ z δ) x i = ∑ j, B x δ i j * δ j)
    (T U : H →L[ℂ] H) (W : Fin n → H →L[ℂ] H)
    (hT : ∀ t : graphTestSpace n 1, T (graphTestToLp t) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator Φ A (fun y ↦ (t.val y).ofLp) x))
    (hU : ∀ t : graphTestSpace n 1, U (graphTestToLp t) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator Φ (forwardRemainderAmplitude B A i)
        (fun y ↦ (t.val y).ofLp) x))
    (hW : ∀ j (t : graphTestSpace n 1), W j (graphTestToLp t) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator Φ (forwardDatumAmplitude B A i j)
        (fun y ↦ (t.val y).ofLp) x))
    (u : L2) (du : Fin n → L2)
    (hdu : ∀ j, HasEuclideanL2CoordinateDerivative j u (du j)) :
    HasEuclideanL2CoordinateDerivative i (scalarGraphOperator T u)
      (scalarGraphOperator U u + ∑ j, scalarGraphOperator (W j) (du j)) := by
  apply scalarGraphOperator_derivative T U W i u du
  apply forwardGraph_allData_derivative hX hY hF hΦ hA i hB hgrad T U W hT hU hW
  intro j
  apply (scalarGraphL2Equiv_derivative_iff j _ _).mp
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hdu j

/-- Reverse transfer on scalar Euclidean Lebesgue L², with the
literal bounded single-fiber operators transported by `scalarGraphL2Equiv`.
This is the scalar specialization consumed by `HasSpatialAmplitudeTransfer`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseGraph_allData_scalar_derivative
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : E → E → ℝ} {ζ : E} {ρ : ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ)))
    {A : FullAmplitude n 1} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B C : E → E → Matrix (Fin n) (Fin n) ℝ} (i : Fin n)
    (hC : ∀ j, ContDiff ℝ ∞ (fun p : E × E ↦ C p.1 p.2 i j))
    (hinv : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), C x δ * B x δ = 1)
    (hgrad : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l)
    (T U : H →L[ℂ] H) (W : Fin n → H →L[ℂ] H)
    (hT : ∀ t : graphTestSpace n 1, T (graphTestToLp t) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ A
        (fun x ↦ (t.val x).ofLp) y))
    (hU : ∀ t : graphTestSpace n 1, U (graphTestToLp t) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ
        (ReverseDerivative.remainderAmplitude C A i) (fun x ↦ (t.val x).ofLp) y))
    (hW : ∀ j (t : graphTestSpace n 1), W j (graphTestToLp t) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ
        (ReverseDerivative.datumAmplitude C A i j) (fun x ↦ (t.val x).ofLp) y))
    (u : L2) (du : Fin n → L2)
    (hdu : ∀ j, HasEuclideanL2CoordinateDerivative j u (du j)) :
    HasEuclideanL2CoordinateDerivative i (scalarGraphOperator T u)
      (scalarGraphOperator U u + ∑ j, scalarGraphOperator (W j) (du j)) := by
  apply scalarGraphOperator_derivative T U W i u du
  apply reverseGraph_allData_derivative hX hY hF hΦ hA i hC hinv hgrad T U W hT hU hW
  intro j
  apply (scalarGraphL2Equiv_derivative_iff j _ _).mp
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hdu j

end JanetCartan.ResponseTransfer.SpatialRealization
