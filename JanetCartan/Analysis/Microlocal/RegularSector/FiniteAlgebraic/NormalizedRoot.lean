module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.Selection

/-!
# An actual smooth root domain for the supported algebraic inverse

The coefficient root is smooth on the retained normalized-frequency buffer.
Substitute the ORIGINAL coefficient field there, obtaining both smoothness
and its characteristic equation. The supported conic inverse evaluates this
root only at normalized covectors. Consumers: `contDiff_conicAlgebraicSymbol`
and `conicBminus_identity` in `app:ch_regular_base:eq:complement-symbol`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AmplitudeBounds FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

/-- The normalized root's physical/frequency product domain. It uses the
original selected radii and does not claim smoothness of a homogeneous
extension at zero (`complement-symbol`). -/
def normalizedRootDomain (c : LocalChart Ω x RQ A₀ ξ M) : Set Z :=
  {w | rootPhysicalPosition (coordinateSplit c.index) w ∈ Ω ∧
    w.2.2 ∈ ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius)}

/-- The retained normalized root domain is open (`complement-inverse`). -/
theorem isOpen_normalizedRootDomain (c : LocalChart Ω x RQ A₀ ξ M) (hΩ : IsOpen Ω) :
    IsOpen (normalizedRootDomain c) :=
  (hΩ.preimage ((coordinateSplit c.index).symm.continuous.comp
    (continuous_fst.prodMk continuous_snd.fst))).inter
    (isOpen_ball.preimage continuous_snd.snd)

/-- Substitute the same original coefficient field into the retained joint
root. Its smoothness and characteristic equation follow from `RootBuffer`,
which is constructed before finite selection; no root or inverse equation
is added as an analytic premise (`complement-symbol`). -/
theorem fieldRoot_smooth_and_characteristic_on_normalizedRootDomain
    (c : LocalChart Ω x RQ A₀ ξ M) (hΩ : IsOpen Ω)
    (hc : RootBuffer c.index c.row c.col A₀ ξ c.root c.coefficientRadius c.rootRadius
      c.minorGap c.transportGap)
    (Q : E → Coeff) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hQr : MapsTo Q Ω (closedBall A₀ c.coefficientRadius)) :
    ContDiffOn ℝ ∞ (fieldRoot (coordinateSplit c.index) Q c.root) (normalizedRootDomain c) ∧
    ∀ w ∈ normalizedRootDomain c,
      (rootPencil (coordinateSplit c.index) Q
        (fieldRoot (coordinateSplit c.index) Q c.root) w).det = 0 := by
  have hphysical : ContDiff ℝ ∞ (rootPhysicalPosition (coordinateSplit c.index)) :=
    (coordinateSplit c.index).symm.contDiff.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hparam (w : Z) (hw : w ∈ normalizedRootDomain c) :
      (Q (rootPhysicalPosition (coordinateSplit c.index) w), w.2.2) ∈
        closedBall A₀ c.coefficientRadius ×ˢ
          closedBall (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius) :=
    ⟨hQr hw.1, ball_subset_closedBall hw.2⟩
  constructor
  · intro w hw
    apply ContDiffAt.contDiffWithinAt
    exact ((hc.2 _ (hparam w hw)).1).comp w
      (((hQ.contDiffAt (hΩ.mem_nhds hw.1)).comp w hphysical.contDiffAt).prodMk
        contDiffAt_snd.snd)
  · intro w hw
    exact (hc.2 _ (hparam w hw)).2.1

end JanetCartan.RegularSector.FiniteAlgebraic
