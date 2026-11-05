module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.GraphIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.ParameterTransfer

/-!
# Joint scalar amplitude expressions for parameter transfer

The expression directions in `app:ch_response:eq:direct-envelope-profile`
act on the actual joint parameter/output/source/frequency amplitude. Their
interpretation as parameter and source derivatives is proved by the chain
rule. Smoothness and common physical supports are preserved by these
operations; no operator identity is included in the admissibility predicate.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NearCarrierParameter
open IsometricEmbedding.Response.NearCarrier
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)

/-- Joint full-amplitude variables, with both physical positions, for
`app:ch_response:eq:direct-envelope-profile`. -/
abbrev JointAmplitudePoint (d p : ℕ) :=
  (EuclideanSpace ℝ (Fin p) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ×
    EuclideanSpace ℝ (Fin d)

local notation "Z" => JointAmplitudePoint d p

/-- Only the carrier parameter moves in this amplitude direction. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
def parameterAmplitudeDirection (v : P) : Z := ((v, (0, 0)), 0)

/-- The source direction retains the output position and covector. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
def sourceAmplitudeDirection (j : Fin d) : Z := ((0, (0, EuclideanSpace.single j 1)), 0)

/-- Local smoothness and uniform physical carriers of a scalar full amplitude.
This is the support predicate of `HasParameterAmplitudeTransfer`; it contains
no estimate and no derivative of an output (`app:ch_response:eq:direct-envelope-profile`). -/
def ParameterAmplitudeAdmissible (U : Set P) (X Y F : Set E) (b : Z → ℂ) : Prop :=
  ContDiffOn ℝ ∞ b ((U ×ˢ univ) ×ˢ univ) ∧
    (∀ c ∈ U, ∀ δ ∈ F, tsupport (fun z : E × E ↦ b ((c, z), δ)) ⊆ X ×ˢ Y) ∧
    ∀ c ∈ U, ∀ z δ, δ ∉ F → b ((c, z), δ) = 0

/-- The joint parameter direction is exactly differentiation of the frozen
physical/frequency slice (`app:ch_response:eq:direct-envelope-profile`). -/
theorem fderiv_parameterAmplitudeDirection {b : Z → ℂ} {c : P} {z : E × E} {δ : E}
    (hb : DifferentiableAt ℝ b ((c, z), δ)) (v : P) :
    fderiv ℝ b ((c, z), δ) (parameterAmplitudeDirection v) =
      fderiv ℝ (fun a ↦ b ((a, z), δ)) c v := by
  have h := hb.hasFDerivAt.comp c
    (((hasFDerivAt_id (𝕜 := ℝ) c).prodMk (hasFDerivAt_const (𝕜 := ℝ) z c)).prodMk (hasFDerivAt_const (𝕜 := ℝ) δ c))
  simpa [parameterAmplitudeDirection, Function.comp_def, Prod.zero_eq_mk] using
    (congrArg (fun L : P →L[ℝ] ℂ ↦ L v) h.fderiv).symm

/-- The joint source direction is the actual second-position derivative,
not an output derivative (`app:ch_response:eq:direct-envelope-profile`). -/
theorem fderiv_sourceAmplitudeDirection {b : Z → ℂ} {c : P} {z : E × E} {δ : E}
    (hb : DifferentiableAt ℝ b ((c, z), δ)) (j : Fin d) :
    fderiv ℝ b ((c, z), δ) (sourceAmplitudeDirection j) =
      fderiv ℝ (fun y ↦ b ((c, (z.1, y)), δ)) z.2 (EuclideanSpace.single j 1) := by
  have h := hb.hasFDerivAt.comp z.2
    (((hasFDerivAt_const (𝕜 := ℝ) c z.2).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) z.2))).prodMk
        (hasFDerivAt_const (𝕜 := ℝ) δ z.2))
  simpa [sourceAmplitudeDirection, Function.comp_def] using
    (congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1)) h.fderiv).symm

namespace ParameterAmplitudeAdmissible
variable {U : Set (EuclideanSpace ℝ (Fin p))}
  {X Y F : Set (EuclideanSpace ℝ (Fin d))} {b q b' : JointAmplitudePoint d p → ℂ}

/-- Admissibility implies the pointwise derivative needed by the slice chain
rules (`app:ch_response:eq:direct-envelope-profile`). -/
theorem differentiableAt (hb : ParameterAmplitudeAdmissible U X Y F b)
    (hU : IsOpen U) {c : P} (hc : c ∈ U) (z : E × E) (δ : E) :
    DifferentiableAt ℝ b ((c, z), δ) :=
  (hb.1.contDiffAt (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds
    ⟨⟨hc, mem_univ _⟩, mem_univ _⟩)).differentiableAt (by simp)

/-- Smooth coefficient multiplication preserves the full physical carriers
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem mul (hb : ParameterAmplitudeAdmissible U X Y F b)
    (hq : ContDiffOn ℝ ∞ q ((U ×ˢ univ) ×ˢ univ)) :
    ParameterAmplitudeAdmissible U X Y F (fun z ↦ q z * b z) :=
  ⟨hq.mul hb.1, (fun c hc δ hδ ↦ tsupport_mul_subset_right.trans (hb.2.1 c hc δ hδ)),
    fun c hc z δ hδ ↦ by dsimp only; rw [hb.2.2 c hc z δ hδ, mul_zero]⟩

/-- Addition preserves the common physical carriers in the full remainder
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem add (hb : ParameterAmplitudeAdmissible U X Y F b)
    (hb' : ParameterAmplitudeAdmissible U X Y F b') :
    ParameterAmplitudeAdmissible U X Y F (fun z ↦ b z + b' z) :=
  ⟨hb.1.add hb'.1, (fun c hc δ hδ ↦ (tsupport_add _ _).trans
    (union_subset (hb.2.1 c hc δ hδ) (hb'.2.1 c hc δ hδ))),
    fun c hc z δ hδ ↦ by dsimp only; rw [hb.2.2 c hc z δ hδ, hb'.2.2 c hc z δ hδ, add_zero]⟩

/-- Finite sums preserve the common smooth carriers; used for the complete
source divergence (`app:ch_response:eq:direct-envelope-profile`). -/
theorem sum {ι : Type*} [Fintype ι] {f : ι → Z → ℂ}
    (hf : ∀ i, ParameterAmplitudeAdmissible U X Y F (f i)) :
    ParameterAmplitudeAdmissible U X Y F (fun z ↦ ∑ i, f i z) := by
  classical
  have hzero : ParameterAmplitudeAdmissible U X Y F (fun _ : Z ↦ (0 : ℂ)) :=
    ⟨contDiffOn_const, (by simp [tsupport]), (by simp)⟩
  have aux (s : Finset ι) : ParameterAmplitudeAdmissible U X Y F (fun z ↦ ∑ i ∈ s, f i z) := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (hf i).add ih
  exact aux Finset.univ

/-- The parameter derivative retains common physical support because the
support statement holds on an open neighborhood. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem parameterDerivative (hb : ParameterAmplitudeAdmissible U X Y F b)
    (hU : IsOpen U) (hX : IsClosed X) (hY : IsClosed Y) (v : P) :
    ParameterAmplitudeAdmissible U X Y F
      (fun z ↦ fderiv ℝ b z (parameterAmplitudeDirection v)) := by
  refine ⟨(hb.1.fderiv_of_isOpen ((hU.prod isOpen_univ).prod isOpen_univ)
    (by simp)).clm_apply contDiffOn_const, ?_, ?_⟩
  · intro c hc δ hδ
    have he : (fun z ↦ fderiv ℝ b ((c, z), δ) (parameterAmplitudeDirection v)) =
        fun z ↦ fderiv ℝ (fun a ↦ b ((a, z), δ)) c v :=
      funext fun z ↦ fderiv_parameterAmplitudeDirection (hb.differentiableAt hU hc z δ) v
    rw [he]
    exact tsupport_parameterKernel (k := fun a z δ ↦ b ((a, z), δ))
      (δ := δ) hU hX hY (fun a ha ↦ hb.2.1 a ha δ hδ) hc v
  
  · intro c hc z δ hδ
    dsimp only
    rw [fderiv_parameterAmplitudeDirection (hb.differentiableAt hU hc z δ)]
    have he : (fun a ↦ b ((a, z), δ)) =ᶠ[nhds c] (fun _ ↦ (0 : ℂ)) := by
      filter_upwards [hU.mem_nhds hc] with a ha
      exact hb.2.2 a ha z δ hδ
    rw [he.fderiv_eq]
    simp

/-- Source differentiation preserves the entire physical support, including
cutoffs in both positions (`app:ch_response:eq:direct-envelope-profile`). -/
theorem sourceDerivative (hb : ParameterAmplitudeAdmissible U X Y F b)
    (hU : IsOpen U) (j : Fin d) :
    ParameterAmplitudeAdmissible U X Y F
      (fun z ↦ fderiv ℝ b z (sourceAmplitudeDirection j)) := by
  refine ⟨(hb.1.fderiv_of_isOpen ((hU.prod isOpen_univ).prod isOpen_univ)
    (by simp)).clm_apply contDiffOn_const, ?_, ?_⟩
  · intro c hc δ hδ
    have hd (z : E × E) : DifferentiableAt ℝ (fun w : E × E ↦ b ((c, w), δ)) z :=
      (hb.differentiableAt hU hc z δ).comp z
        ((differentiableAt_const c |>.prodMk differentiableAt_id).prodMk (differentiableAt_const δ))
    have he : (fun z ↦ fderiv ℝ b ((c, z), δ) (sourceAmplitudeDirection j)) =
        fun z ↦ sourceKernelDerivative (fun w δ ↦ b ((c, w), δ)) j z δ := by
      funext z
      rw [fderiv_sourceAmplitudeDirection (hb.differentiableAt hU hc z δ) j,
        sourceKernelDerivative_eq (hd z) j]
    rw [he]
    exact (tsupport_sourceKernelDerivative _ j δ).trans (hb.2.1 c hc δ hδ)
  · intro c hc z δ hδ
    dsimp only
    rw [fderiv_sourceAmplitudeDirection (hb.differentiableAt hU hc z δ)]
    have he : (fun y ↦ b ((c, (z.1, y)), δ)) = fun _ ↦ (0 : ℂ) :=
      funext fun y ↦ hb.2.2 c hc (z.1, y) δ hδ
    rw [he]
    simp

end ParameterAmplitudeAdmissible

/-- The exact list of source-divergence terms in the parameter remainder.
The primitive coefficient already carries the forward/reverse sign. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
def parameterSourceTerms {ι : Type*} (idx : Fin d → ι) :
    List (Z × ι × (ℂ →L[ℝ] ℂ →L[ℝ] ℂ)) :=
  List.ofFn fun j ↦ (sourceAmplitudeDirection j, idx j, ContinuousLinearMap.mul ℝ ℂ)

/-- The expression remainder is exactly the joint parameter derivative plus
the full signed source divergence. No amplitude derivative is postulated.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem evaluate_parameterSourceTerms {ι : Type*}
    (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι) (v : P) (idx : Fin d → ι) (z : Z) :
    (b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)).evaluate a z =
      fderiv ℝ (b.evaluate a) z (parameterAmplitudeDirection v) +
        ∑ j, fderiv ℝ (fun w ↦ a (idx j) w * b.evaluate a w) z (sourceAmplitudeDirection j) := by
  rw [AmplitudeExpression.evaluate_divergenceTransfer]
  simp [parameterSourceTerms, List.map_ofFn, List.sum_ofFn, add_comm]

/-- The full expression remainder preserves local smoothness and support,
from primitive coefficient smoothness. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem admissible_parameterSourceTerms {ι : Type*}
    {U : Set P} (hU : IsOpen U) {X Y F : Set E} (hX : IsClosed X) (hY : IsClosed Y)
    (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι) (v : P) (idx : Fin d → ι)
    (hb : ParameterAmplitudeAdmissible U X Y F (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ)) :
    ParameterAmplitudeAdmissible U X Y F
      ((b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)).evaluate a) := by
  have he := funext (evaluate_parameterSourceTerms a b v idx)
  rw [he]
  exact (hb.parameterDerivative hU hX hY v).add
    (ParameterAmplitudeAdmissible.sum fun j ↦ (hb.mul (ha j)).sourceDerivative hU j)

end JanetCartan.ResponseTransfer.NearCarrierParameter
