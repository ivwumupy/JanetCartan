module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Matrices
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Coordinates of finite vector-valued Lebesgue L²

The coordinate isometry needed to use the Hilbert sums in
`app:ch_regular_base:eq:fio-input` on literal finite vector-valued data.
The measure is unchanged; this does not identify torus and Euclidean data.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace
namespace JanetCartan.Pseudodifferential
variable {X I : Type*} [MeasurableSpace X] [Fintype I] (μ : Measure X)

/-- Coordinate extraction on L² for `app:ch_regular_base:eq:fio-input`. -/
def finiteL2Coordinates : Lp (EuclideanSpace ℂ I) 2 μ →L[ℂ]
    PiLp 2 (fun _ : I ↦ Lp ℂ 2 μ) :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ (PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ ℂ) i).compLpL 2 μ)

/-- Coordinates of actual representatives, for `app:ch_regular_base:eq:fio-input`. -/
theorem finiteL2Coordinates_apply_ae (f : Lp (EuclideanSpace ℂ I) 2 μ) (i : I) :
    finiteL2Coordinates μ f i =ᵐ[μ] fun x ↦ f x i :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ ℂ) i).coeFn_compLpL f

/-- The finite coordinate map preserves the Hilbert inner product in
`app:ch_regular_base:eq:fio-input`. -/
theorem finiteL2Coordinates_inner (f g : Lp (EuclideanSpace ℂ I) 2 μ) :
    ⟪finiteL2Coordinates μ f, finiteL2Coordinates μ g⟫ = ⟪f, g⟫ := by
  rw [PiLp.inner_apply, L2.inner_def]
  have he (i : I) :
      ⟪finiteL2Coordinates μ f i, finiteL2Coordinates μ g i⟫ =
        ∫ x, ⟪f x i, g x i⟫ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [finiteL2Coordinates_apply_ae μ f i,
      finiteL2Coordinates_apply_ae μ g i] with x hx hy
    rw [hx, hy]
  simp_rw [he, PiLp.inner_apply]
  symm
  apply integral_finsetSum
  intro i _
  apply (L2.integrable_inner (𝕜 := ℂ) (finiteL2Coordinates μ f i)
    (finiteL2Coordinates μ g i)).congr
  filter_upwards [finiteL2Coordinates_apply_ae μ f i,
    finiteL2Coordinates_apply_ae μ g i] with x hx hy
  rw [hx, hy]

/-- Every finite family of scalar L² classes comes from vector L², for
`app:ch_regular_base:eq:fio-input`. -/
theorem finiteL2Coordinates_surjective : Function.Surjective (finiteL2Coordinates (I := I) μ) := by
  intro f
  let u : X → EuclideanSpace ℂ I := fun x ↦ WithLp.toLp 2 (fun i ↦ f i x)
  have hu : MemLp u 2 μ := MemLp.of_eval_piLp (fun i ↦ Lp.memLp (f i))
  refine ⟨hu.toLp u, ?_⟩
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae μ (hu.toLp u) i, hu.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Exact coordinate L² isometry for the finite matrix calculus
(`app:ch_regular_base:eq:fio-input`). -/
def finiteL2CoordinateIsometry : Lp (EuclideanSpace ℂ I) 2 μ ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : I ↦ Lp ℂ 2 μ) :=
  LinearIsometryEquiv.ofSurjective
    ((finiteL2Coordinates (I := I) μ).toLinearMap.isometryOfInner
      (fun f g ↦ finiteL2Coordinates_inner μ f g))
    (finiteL2Coordinates_surjective μ)

/-- Coordinate extraction of a specified vector representative, used by the
literal kernel identification in `app:ch_regular_base:thm:actual-calculus`. -/
theorem finiteL2CoordinateIsometry_toLp (u : X → EuclideanSpace ℂ I) (hu : MemLp u 2 μ) :
    finiteL2CoordinateIsometry μ (hu.toLp u) =
      WithLp.toLp 2 (fun i ↦ (hu.eval_piLp i).toLp (fun x ↦ u x i)) := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae μ (hu.toLp u) i,
    hu.coeFn_toLp, (hu.eval_piLp i).coeFn_toLp] with x hx hy hz
  exact hx.trans ((congrArg (fun z : EuclideanSpace ℂ I ↦ z i) hy).trans hz.symm)

/-- Coordinatewise literal kernel identities give the vector identity without
changing representatives or measure (`app:ch_regular_base:thm:actual-calculus`). -/
theorem finiteL2CoordinateIsometry_ae_iff (f : Lp (EuclideanSpace ℂ I) 2 μ)
    (u : X → EuclideanSpace ℂ I) :
    f =ᵐ[μ] u ↔ ∀ i, finiteL2CoordinateIsometry μ f i =ᵐ[μ] fun x ↦ u x i := by
  constructor
  · intro h i
    filter_upwards [finiteL2Coordinates_apply_ae μ f i, h] with x hx hy
    exact hx.trans (congrArg (fun z : EuclideanSpace ℂ I ↦ z i) hy)
  · intro h
    have hc := ae_all_iff.mpr (fun i ↦ finiteL2Coordinates_apply_ae μ f i)
    have hu := ae_all_iff.mpr h
    filter_upwards [hc, hu] with x hx hy
    apply PiLp.ext
    intro i
    exact (hx i).symm.trans (hy i)

end JanetCartan.Pseudodifferential
