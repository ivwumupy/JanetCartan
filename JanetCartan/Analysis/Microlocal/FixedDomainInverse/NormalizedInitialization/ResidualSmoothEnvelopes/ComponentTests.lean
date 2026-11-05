module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothRealization
public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.JointRegularity

/-!
# Scalar components of supported residual data

The measured residual words in `app:ch_regular:lem:finite-chain` must preserve
one jointly smooth envelope. These scalar tests reduce the actual vector
source to the existing fixed-response joint regularity theorem. The physical
coordinate witness and the original compact source support are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes

open RetardedSobolev.Spaces FourierIntegral Pseudodifferential
open RegularSector.FiniteAssembly ResponseSmoothParameters

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- A scalar basis component vanishes outside the original compact source
support (`app:ch_regular:lem:finite-chain`). -/
theorem scalar_basis_source_support
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    {X : Set E} (hX : IsCompact X) (j : Fin r)
    (u : supportedTests (e ⁻¹' X)) :
    tsupport (fun x : E ↦ u.val.val (e.symm x) • EuclideanSpace.single j (1 : ℂ)) ⊆ X := by
  apply closure_minimal _ hX.isClosed
  intro x hx
  by_contra hxX
  have hu : u.val.val (e.symm x) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hz ↦ hxX (by simpa using u.property hz)
  exact hx (by simp only [hu, zero_smul])

/-- Insert one scalar source component in the original physical chart.
Consumer: the joint smooth representative of the measured residual word in
`app:ch_regular:lem:finite-chain`. -/
def componentGraphTest (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    {X : Set E} (hX : IsCompact X) (j : Fin r) :
    supportedTests (e ⁻¹' X) →ₗ[ℂ] graphTestSpace (d + 1) r where
  toFun u := ⟨fun x ↦ u.val.val (e.symm x) • EuclideanSpace.single j 1,
    (u.val.property.1.comp e.symm.contDiff).smul contDiff_const,
    hX.of_isClosed_subset (isClosed_tsupport _) (scalar_basis_source_support e hX j u)⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    exact add_smul _ _ _
  map_smul' a u := by
    apply Subtype.ext
    funext x
    exact mul_smul _ _ _

/-- The scalar component has its literal physical pointwise formula.
Source: `app:ch_regular:lem:finite-chain`. -/
@[simp] theorem componentGraphTest_apply
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    {X : Set E} (hX : IsCompact X) (j : Fin r)
    (u : supportedTests (e ⁻¹' X)) (x : E) :
    (componentGraphTest e hX j u).val x =
      u.val.val (e.symm x) • EuclideanSpace.single j (1 : ℂ) := rfl

/-- The component has the original compact spatial support.
Source: `app:ch_regular:lem:finite-chain`. -/
theorem componentGraphTest_tsupport
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    {X : Set E} (hX : IsCompact X) (j : Fin r)
    (u : supportedTests (e ⁻¹' X)) :
    tsupport (componentGraphTest e hX j u).val ⊆ X :=
  scalar_basis_source_support e hX j u

/-- The same jointly smooth vector family is a finite sum of scalar tests
with unchanged source support. Consumer: joint residual regularity in
`app:ch_regular:lem:finite-chain`. -/
theorem exists_supported_graph_components
    {p : ℕ} (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    {X : Set E} (hX : IsCompact X)
    (f : Euclidean p → graphTestSpace (d + 1) r)
    (hf : ContDiff ℝ ∞ (fun w : E × Euclidean p ↦ (f w.2).val w.1))
    (hs : ∀ a, tsupport (f a).val ⊆ X) :
    ∃ g : Fin r → Euclidean p → supportedTests (e ⁻¹' X),
      (∀ j, ContDiff ℝ ∞ (fun w : Euclidean p × (ℝ × (Fin d → ℝ)) ↦ (g j w.1).val.val w.2)) ∧
      ∀ a, f a = ∑ j, componentGraphTest e hX j (g j a) := by
  classical
  have hK : IsCompact (e ⁻¹' X) := e.toHomeomorph.isCompact_preimage.mpr hX
  let entry (j : Fin r) : F →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun v := v j
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  have hscalar (j : Fin r) : ContDiff ℝ ∞
      (fun w : Euclidean p × (ℝ × (Fin d → ℝ)) ↦ (f w.1).val (e w.2) j) :=
    (entry j).contDiff.comp (hf.comp
      ((e.contDiff.comp contDiff_snd).prodMk contDiff_fst))
  have hss (j : Fin r) (a : Euclidean p) :
      tsupport (fun x ↦ (f a).val (e x) j) ⊆ e ⁻¹' X := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    have hz : (f a).val (e x) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hn (hs a h)
    exact hx (congrArg (fun v : F ↦ v j) hz)
  let tests (j : Fin r) (a : Euclidean p) : supportedTests (e ⁻¹' X) :=
    ⟨⟨fun x ↦ (f a).val (e x) j,
      (hscalar j).comp (contDiff_const.prodMk contDiff_id),
      hK.of_isClosed_subset (isClosed_tsupport _) (hss j a)⟩, hss j a⟩
  refine ⟨tests, hscalar, fun a ↦ ?_⟩
  apply Subtype.ext
  funext x
  apply PiLp.ext
  intro i
  simp [componentGraphTest, tests, Finset.sum_apply, Pi.single_apply, mul_ite]


end JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes
