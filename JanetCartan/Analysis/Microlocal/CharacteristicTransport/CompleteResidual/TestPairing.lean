module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Reality

/-!
# Linear test functionals on the actual vector L² space

The finite-sector assembly of `app:ch_regular_base:eq:energy-complete-residual`
uses these functionals to add and conjugate tested equations. Integrability
comes from L² and compact smooth tests. No derivative of an L² representative
is used. The consuming declaration is `physicalPairedSectorSum_test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.CharacteristicTransport.CompleteResidual
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => EuclideanSpace ℂ (Fin q)
local notation "C2" => Lp H 2 (volume : Measure E)

private theorem integrable_coordinate_pairing (ψ : E → ℝ) (hψ : MemLp ψ 2 volume)
    (u : C2) (i : Fin q) : Integrable (fun x ↦ ψ x • u x i) := by
  let L : H →L[ℝ] ℂ := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).restrictScalars ℝ
  exact memLp_one_iff_integrable.mp (hψ.smul (L.comp_memLp' (Lp.memLp u)))

/-- L² pairing against one real scalar test and one vector coordinate.
It is complex linear, as needed to sum the complete residual equations
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def testCoordinatePairing (ψ : E → ℝ) (hψ : MemLp ψ 2 volume) (i : Fin q) :
    C2 →ₗ[ℂ] ℂ where
  toFun u := ∫ x, ψ x • u x i
  map_add' u v := by
    calc
      _ = ∫ x, ψ x • u x i + ψ x • v x i := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add u v] with x hx
        simp only [hx, Pi.add_apply, PiLp.add_apply, smul_add]
      _ = _ := integral_add (integrable_coordinate_pairing ψ hψ u i)
        (integrable_coordinate_pairing ψ hψ v i)
  map_smul' z u := by
    calc
      _ = ∫ x, z • (ψ x • u x i) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul z u] with x hx
        simp only [hx, Pi.smul_apply, PiLp.smul_apply]
        exact smul_comm _ _ _
      _ = _ := integral_smul z _

/-- The actual physical test action is a complex linear functional on L².
The coefficients and their derivatives are multiplied by compact tests;
the zeroth-order term is retained
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def physicalTestActionLp
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q) :
    C2 →ₗ[ℂ] ℂ :=
  -(∑ a, ∑ j, testCoordinatePairing
    (fun x ↦ partialDeriv (fun y ↦ φ y * A y a i j) x a)
    ((((hφ.mul (hA a i j)).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport (hc.mul_right.fderiv_apply ℝ (EuclideanSpace.single a 1))) j) +
    ∑ j, testCoordinatePairing (fun x ↦ φ x * B x i j)
      ((hφ.mul (hB i j)).continuous.memLp_of_hasCompactSupport hc.mul_right) j

/-- The functional evaluates to the previously proved formal test action
on exactly the same L² representative
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalTestActionLp_apply
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q) (u : C2) :
    physicalTestActionLp A B hA hB φ hφ hc i u =
      physicalTestAction A B (fun x ↦ (u x).ofLp) φ i := by
  simp [physicalTestActionLp, testCoordinatePairing, physicalTestAction]

/-- Real tests commute with the actual a.e. L² conjugation
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem testCoordinatePairing_star (ψ : E → ℝ) (hψ : MemLp ψ 2 volume)
    (i : Fin q) (u : C2) :
    testCoordinatePairing ψ hψ i (star u) = star (testCoordinatePairing ψ hψ i u) := by
  change (∫ x, ψ x • (star u) x i) = star (∫ x, ψ x • u x i)
  change (∫ x, ψ x • (star u) x i) = (starRingEnd ℂ) (∫ x, ψ x • u x i)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with x hx
  simp only [hx, Pi.star_apply]
  change ψ x • star (u x i) = star (ψ x • u x i)
  simp

/-- The full first-order test action commutes with conjugation on L²,
including the zeroth-order coefficient
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalTestActionLp_star
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q) (u : C2) :
    physicalTestActionLp A B hA hB φ hφ hc i (star u) =
      star (physicalTestActionLp A B hA hB φ hφ hc i u) := by
  simp only [physicalTestActionLp, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, testCoordinatePairing_star, star_add, star_neg, star_sum]

/-- Compact test pairings are continuous in the actual L² topology. This
is the density step from smooth source tests to all L² sources in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem testCoordinatePairing_continuous (ψ : E → ℝ) (hψ : MemLp ψ 2 volume)
    (i : Fin q) : Continuous (testCoordinatePairing ψ hψ i) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let L : H →L[ℝ] ℂ := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).restrictScalars ℝ
  have hid : Filter.Tendsto (fun v : C2 ↦ v) (nhds u) (nhds u) := Filter.tendsto_id
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun v : C2 ↦ (v : E → H)) (fun v ↦ Lp.memLp v) u (Lp.memLp u)).mp
    (by simpa only [Lp.toLp_coeFn] using hid)
  exact Mollification.tendsto_integral_smul_of_tendsto_eLpNorm_two hψ
    (fun v ↦ L.comp_memLp' (Lp.memLp v)) (L.comp_memLp' (Lp.memLp u))
    (Mollification.tendsto_eLpNorm_compCLM_sub L (fun v ↦ Lp.memLp v) (Lp.memLp u) ht)

/-- The full physical test functional is continuous on L²; its coefficient
derivatives are controlled on the compact test support, including for
unbounded measurement domains (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalTestActionLp_continuous
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q) :
    Continuous (physicalTestActionLp A B hA hB φ hφ hc i) := by
  change Continuous (fun u ↦ physicalTestActionLp A B hA hB φ hφ hc i u)
  simp only [physicalTestActionLp, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.sum_apply]
  apply Continuous.add
  · apply Continuous.neg
    apply continuous_finsetSum
    intro a _
    apply continuous_finsetSum
    intro j _
    exact testCoordinatePairing_continuous _ _ _
  · apply continuous_finsetSum
    intro j _
    exact testCoordinatePairing_continuous _ _ _

end JanetCartan.CharacteristicTransport.CompleteResidual
