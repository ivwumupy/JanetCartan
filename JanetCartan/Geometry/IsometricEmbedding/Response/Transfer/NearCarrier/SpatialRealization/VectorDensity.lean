module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.ScalarDensity
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Coordinates

/-!
# Simultaneous finite-fiber approximation

The all-data extension of `app:ch_response:eq:direct-envelope-profile` uses
compact smooth tests converging with all first derivatives in the actual
Euclidean finite-fiber L² space. The scalar density theorem supplies these
approximants coordinate by coordinate, including zero-dimensional fibers.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter LineDeriv
open scoped ContDiff SchwartzMap Topology
namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral Pseudodifferential AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Coordinate projection of the classical test derivative, for the density
step in `app:ch_response:eq:direct-envelope-profile`. -/
theorem graphTestPartialDeriv_coordinate (u : graphTestSpace n r) (i : Fin n)
    (a : Fin r) (x : E) :
    ((graphTestPartialDeriv i u).val x) a =
      euclideanCoordinateDerivList [i] (fun y ↦ u.val y a) x := by
  let P := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin r ↦ ℂ) a)
  have h := P.hasFDerivAt.comp x ((u.property.1.differentiable (by simp) x).hasFDerivAt)
  exact (congrArg (fun D : E →L[ℝ] ℂ ↦ D (EuclideanSpace.single i 1)) h.fderiv).symm

/-- Actual compact smooth vector tests approximate an L² datum and every
first L² derivative simultaneously. This proves the density premise needed by
the literal spatial transfer, `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_graphTest_coordinateDerivatives_tendsto
    (u : H) (du : Fin n → H)
    (hdu : ∀ i, lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (u : 𝓢'(E, V)) =
      (du i : 𝓢'(E, V))) :
    ∃ g : ℕ → graphTestSpace n r,
      Tendsto (fun k ↦ graphTestToLp (g k)) atTop (𝓝 u) ∧
      ∀ i, Tendsto (fun k ↦ graphTestToLp (graphTestPartialDeriv i (g k)))
        atTop (𝓝 (du i)) := by
  let Q := finiteL2CoordinateIsometry (I := Fin r) (volume : Measure E)
  choose g hg hc hlim using fun a : Fin r ↦
    exists_compactSmooth_coordinateDerivatives_tendsto (Q u a) (fun i ↦ Q (du i) a)
      (fun i ↦ graphL2_coordinate_derivative (hdu i) a)
  let v : ℕ → E → V := fun k x ↦ WithLp.toLp 2 (fun a ↦ g a k x)
  have hv (k) : ContDiff ℝ ∞ (v k) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.contDiff.comp
      (contDiff_pi.mpr (fun a ↦ hg a k))
  have hs (k) : HasCompactSupport (v k) := by
    let K := ⋃ a, tsupport (g a k)
    have hK : IsCompact K := isCompact_iUnion (fun a ↦ hc a k)
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    apply hx
    apply PiLp.ext
    intro a
    change g a k x = 0
    exact image_eq_zero_of_notMem_tsupport (fun ha ↦ hn (mem_iUnion.mpr ⟨a, ha⟩))
  let t : ℕ → graphTestSpace n r := fun k ↦ ⟨v k, hv k, hs k⟩
  have hbase (k) : Q (graphTestToLp (t k)) = WithLp.toLp 2 (fun a ↦
      ((hg a k).continuous.memLp_of_hasCompactSupport (hc a k)).toLp (g a k)) := by
    exact finiteL2CoordinateIsometry_toLp volume (t k).val (graphTest_memLp (t k))
  have hderiv (k) (i : Fin n) : Q (graphTestToLp (graphTestPartialDeriv i (t k))) =
      WithLp.toLp 2 (fun a ↦
        (((contDiff_euclideanCoordinateDerivList (hg a k) [i]).continuous.memLp_of_hasCompactSupport
          (hasCompactSupport_euclideanCoordinateDerivList (hc a k) [i])).toLp
            (euclideanCoordinateDerivList [i] (g a k)))) := by
    rw [show Q = finiteL2CoordinateIsometry volume from rfl,
      graphTestToLp, LinearMap.coe_mk, AddHom.coe_mk, finiteL2CoordinateIsometry_toLp]
    apply PiLp.ext
    intro a
    apply Lp.ext
    filter_upwards [(graphTest_memLp (graphTestPartialDeriv i (t k))).eval_piLp a |>.coeFn_toLp,
      ((contDiff_euclideanCoordinateDerivList (hg a k) [i]).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList (hc a k) [i])).coeFn_toLp] with x hx hy
    exact hx.trans ((graphTestPartialDeriv_coordinate (t k) i a x).trans hy.symm)
  refine ⟨t, ?_, fun i ↦ ?_⟩
  · have h := (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (fun a ↦ (hlim a).1))
    have he : Tendsto (fun k ↦ Q (graphTestToLp (t k))) atTop (𝓝 (Q u)) := by
      simpa only [hbase, Function.comp_def, WithLp.toLp_ofLp] using h
    simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using
      (Q.symm.continuous.tendsto (Q u)).comp he
  · have h := (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (fun a ↦ (hlim a).2 i))
    have he : Tendsto (fun k ↦ Q (graphTestToLp (graphTestPartialDeriv i (t k))))
        atTop (𝓝 (Q (du i))) := by
      simpa only [hderiv, Function.comp_def, WithLp.toLp_ofLp] using h
    simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using
      (Q.symm.continuous.tendsto (Q (du i))).comp he

end JanetCartan.ResponseTransfer.SpatialRealization
