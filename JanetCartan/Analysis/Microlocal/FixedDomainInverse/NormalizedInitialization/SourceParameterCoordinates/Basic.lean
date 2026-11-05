module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.UniformPhase.Sobolev

/-!
# The original product parameters of the normalized source

The fixed split of `Euclidean (3+d)` into the original label and covector
transfers genuine source derivatives. The existing full-source coordinate
lemmas supply both norm bounds and the ordered-word identities. Here they are
applied to the source list jets and the normalized carrier jet used by the
same-inverse remainder in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.FixedDomainInverse
open ResponseTransfer.FullSourceEnvelopes
open ResponseTransfer.Complement ResponseTransfer.Complement.ParameterDerivatives
open Pseudodifferential

variable {d r : ℕ}
local notation "P" => Euclidean 3 × Euclidean d
local notation "Pc" => Euclidean (3+d)
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "splitP" => (EuclideanSpace.finAddEquivProd : Pc ≃L[ℝ] P)

private theorem parameterListJet_comp_equiv
    {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : X ≃L[ℝ] Y) (f : Y → Z) (vs : List X) (c : X) :
    parameterListJet (f ∘ e) vs c = parameterListJet f (vs.map e) (e c) := by
  have hm : List.ofFn (fun i : Fin vs.length ↦ e (vs.get i)) = vs.map e := by
    change List.ofFn ((e : X → Y) ∘ vs.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  calc
    _ = iteratedFDeriv ℝ vs.length f (e c) (fun i ↦ e (vs.get i)) := by
      unfold parameterListJet
      rw [externalCoordinate_jet]
      rfl
    _ = _ := by
      rw [← hm, parameterListJet_ofFn]

/-- Exact forward transport of the original source list jet. In particular,
the derivative order and the spatial function do not change
(`app:ch_response:eq:response-graded-source`). -/
theorem fullSource_parameterListJet_pullback
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : P → Z) (vs : List Pc) (c : Pc) :
    parameterListJet (f ∘ splitP) vs c =
      parameterListJet f (vs.map splitP) (splitP c) :=
  parameterListJet_comp_equiv splitP f vs c

/-- The inverse coordinate map transports the same ordered source list jet;
no differentiability of an output is an extra premise
(`app:ch_response:thm:response-literal-transfer`). -/
theorem fullSource_parameterListJet_pullback_symm
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : Pc → Z) (vs : List P) (c : P) :
    parameterListJet (f ∘ (splitP).symm) vs c =
      parameterListJet f (vs.map (splitP).symm) ((splitP).symm c) :=
  parameterListJet_comp_equiv (splitP).symm f vs c

/-- The literal normalized derivative of the original full product-parameter
source. Its Euclidean counterpart is `parameterCarrierJet`; the spatial
function and carrier frequency are identical
(`app:ch_response:eq:response-graded-reduced`). -/
def productParameterCarrierJet (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → P) (c : P) : E → F :=
  fun x ↦ ResponseTransfer.carrier (-ρ) (φ c) x •
    iteratedFDeriv ℝ k (fun a ↦ ResponseTransfer.carrier ρ (φ a) x • f a x) c v

/-- Exact forward coordinate identity for the normalized original source;
it preserves every spatial value and the original carrier frequency
(`app:ch_response:eq:response-graded-reduced`). -/
theorem parameterCarrierJet_split_eq_product
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → Pc) (c : Pc) :
    parameterCarrierJet ρ (fun a ↦ φ (splitP a)) (fun a ↦ f (splitP a)) k v c =
      productParameterCarrierJet ρ φ f k (fun i ↦ splitP (v i)) (splitP c) := by
  funext x
  simp only [parameterCarrierJet, parameterSourceFunction, productParameterCarrierJet]
  congr 1
  exact congrArg (fun D ↦ D v)
    (externalCoordinate_jet splitP (fun a ↦ ResponseTransfer.carrier ρ (φ a) x • f a x) c k)

/-- Exact inverse-coordinate identity for the original normalized source jet
(`app:ch_response:eq:response-graded-reduced`). -/
theorem productParameterCarrierJet_eq_coordinate
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → P) (c : P) :
    productParameterCarrierJet ρ φ f k v c =
      parameterCarrierJet ρ (fun a ↦ φ (splitP a)) (fun a ↦ f (splitP a)) k
        (fun i ↦ (splitP).symm (v i)) ((splitP).symm c) := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (parameterCarrierJet_split_eq_product ρ φ f k
      (fun i ↦ (splitP).symm (v i)) ((splitP).symm c)).symm

/-- Unit product directions have unit Euclidean representatives after the
fixed factor one-half. This changes no frequency or scale exponent
(`app:ch_response:thm:response-literal-transfer`). -/
theorem fullSource_parameterTuple_unit {k : ℕ} (v : Fin k → P)
    (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∀ i, ‖(2 : ℝ)⁻¹ • (splitP).symm (v i)‖ ≤ 1 := by
  intro i
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)]
  linarith [fullSource_coordinate_norm_bounds.2 (v i), hv i]

/-- Normalizing the inverse-coordinate directions costs precisely `2^k`.
The normalized source has the same carrier and the same original amplitude
(`app:ch_response:eq:response-graded-reduced`). -/
theorem productParameterCarrierJet_eq_unit_coordinate
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → P) (c : P) :
    productParameterCarrierJet ρ φ f k v c = (2 : ℝ)^k •
      parameterCarrierJet ρ (fun a ↦ φ (splitP a)) (fun a ↦ f (splitP a)) k
        (fun i ↦ (2 : ℝ)⁻¹ • (splitP).symm (v i)) ((splitP).symm c) := by
  rw [productParameterCarrierJet_eq_coordinate]
  funext x
  simp only [Pi.smul_apply, parameterCarrierJet]
  have hscale := (iteratedFDeriv ℝ k
    (fun a ↦ parameterSourceFunction ρ (fun a ↦ φ (splitP a))
      (fun a ↦ f (splitP a)) a x) ((splitP).symm c)).map_smul_univ
        (fun _ ↦ (2 : ℝ)⁻¹) (fun i ↦ (splitP).symm (v i))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hscale
  rw [hscale, smul_comm _ ((2 : ℝ)⁻¹ ^ k), smul_smul]
  simp

/-- The original carrier times its normalized jet is exactly the derivative
of the whole source, including derivatives of its phase
(`app:ch_response:thm:response-literal-transfer`). -/
theorem carrier_mul_productParameterCarrierJet
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → P) (c : P) (x : E) :
    ResponseTransfer.carrier ρ (φ c) x • productParameterCarrierJet ρ φ f k v c x =
      iteratedFDeriv ℝ k (fun a ↦ ResponseTransfer.carrier ρ (φ a) x • f a x) c v := by
  simp only [productParameterCarrierJet, smul_smul]
  rw [mul_comm, ResponseTransfer.carrier_neg_mul, one_smul]

end JanetCartan.FixedDomainInverse
