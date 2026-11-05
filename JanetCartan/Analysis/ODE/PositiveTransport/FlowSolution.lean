module

public import JanetCartan.Analysis.ODE.PositiveTransport.JointRegularity
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Positive smooth transport along a supplied flow

This assembles the scalar part of `app:ch_waves:thm:leading` and
`app:ch_background:prop:bg-positive`. The flow and its inverse chart are
geometric inputs. The solution, its regularity, and its positivity are proved
from the exponential-integral formula, rather than assumed as an interface.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan

variable {P X : Type*}

/-- `app:ch_waves:thm:leading`: uniqueness in physical coordinates follows
from uniqueness on each characteristic and the right inverse chart identity. -/
theorem transportFromFootpoint_unique {c : ℝ × P → ℝ} {u : ℝ × X → ℝ}
    {r : P → ℝ} {Y : ℝ × X → P} {Φ : ℝ × P → X}
    {I : Set ℝ} {U : Set P} {D : Set (ℝ × X)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I)
    (hc : ∀ p ∈ U, ContinuousOn (fun t ↦ c (t, p)) I) (ht₀ : t₀ ∈ I)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ U))
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2)
    (hu : ∀ p ∈ U, ∀ t ∈ I, HasDerivAt (fun s ↦ u (s, Φ (s, p)))
      (-c (t, p) * u (t, Φ (t, p))) t)
    (hu₀ : ∀ p ∈ U, u (t₀, Φ (t₀, p)) = r p) :
    EqOn u (transportFromFootpoint c t₀ r Y) D := by
  have he := characteristicTransport_unique (u := fun q ↦ u (q.1, Φ q))
    hI hIc hc ht₀ hu hu₀
  intro q hq
  simpa only [transportFromFootpoint, hΦY q hq, Prod.eta] using he (hYU hq)

/-- `app:ch_waves:thm:leading`: the physical solution operator is linear
in the prescribed initial function; the flow and footpoint chart stay fixed. -/
def transportFromFootpointLinearMap (c : ℝ × P → ℝ) (t₀ : ℝ) (Y : ℝ × X → P) :
    (P → ℝ) →ₗ[ℝ] (ℝ × X → ℝ) where
  toFun r := transportFromFootpoint c t₀ r Y
  map_add' r q := funext fun w ↦ scalarTransport_add _ t₀ (r (Y w)) (q (Y w)) w.1
  map_smul' k r := funext fun w ↦ scalarTransport_smul _ t₀ k (r (Y w)) w.1

section SmoothFlow

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `app:ch_waves:thm:leading`: the scalar equation in physical coordinates,
written as the derivative in the space-time direction `(1, v)`. The supplied
flow has velocity `v` at this point; smoothness of the constructed amplitude
is discharged using joint interval-integral regularity. -/
theorem fderiv_transportFromFootpoint_along_flow
    {c : ℝ × P → ℝ} {r : P → ℝ} {Y : ℝ × X → P} {Φ : ℝ × P → X}
    {I : Set ℝ} {U : Set P} {D : Set (ℝ × X)} {t₀ t : ℝ} {p : P} {v : X}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U) (hD : IsOpen D)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (hr : ContDiffOn ℝ ∞ r U)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) (hp : p ∈ U)
    (hY : ContDiffOn ℝ ∞ Y D) (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ U))
    (hYΦ : ∀ s ∈ I, Y (s, Φ (s, p)) = p) (hq : (t, Φ (t, p)) ∈ D)
    (hΦ : HasDerivAt (fun s ↦ Φ (s, p)) v t) :
    fderiv ℝ (transportFromFootpoint c t₀ r Y) (t, Φ (t, p)) (1, v) =
      -c (t, p) * transportFromFootpoint c t₀ r Y (t, Φ (t, p)) := by
  have hα := (contDiffOn_transportFromFootpoint hI hIc hU hc hr ht₀ hY hYU).contDiffAt
    (hD.mem_nhds hq)
  have hc_time : ContinuousOn (fun s ↦ c (s, p)) I :=
    hc.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hs ↦ ⟨hs, hp⟩)
  have hd : HasDerivAt (fun s ↦ transportFromFootpoint c t₀ r Y (s, Φ (s, p)))
      (fderiv ℝ (transportFromFootpoint c t₀ r Y) (t, Φ (t, p)) (1, v)) t :=
    HasFDerivAt.comp_hasDerivAt t (l := transportFromFootpoint c t₀ r Y)
      (l' := fderiv ℝ (transportFromFootpoint c t₀ r Y) (t, Φ (t, p)))
      (hα.differentiableAt (by simp)).hasFDerivAt
      ((hasDerivAt_id t).prodMk hΦ)
  exact hd.unique
    (hasDerivAt_transportFromFootpoint_along_flow hI hIc p hc_time ht₀ ht r hYΦ)

/-- `app:ch_waves:thm:leading` and `app:ch_background:prop:bg-positive`:
existence, positivity, joint smoothness, and uniqueness of scalar transport
along a given smooth flow with a smooth inverse footpoint chart. The label
space may contain both initial spatial and carrier variables. Uniqueness is
on the stated physical domain, not for arbitrary extensions outside it. -/
theorem exists_positive_smooth_transport_along_flow
    {c : ℝ × X → ℝ} {r : P → ℝ} {Y : ℝ × X → P} {Φ : ℝ × P → X}
    {I : Set ℝ} {U : Set P} {D V : Set (ℝ × X)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c V) (hΦ : ContDiffOn ℝ ∞ Φ (I ×ˢ U))
    (hV : MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ U) V)
    (hr : ContDiffOn ℝ ∞ r U) (hrpos : ∀ p ∈ U, 0 < r p) (ht₀ : t₀ ∈ I)
    (hY : ContDiffOn ℝ ∞ Y D) (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ U))
    (hYΦ : ∀ p ∈ U, ∀ t ∈ I, Y (t, Φ (t, p)) = p)
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2) :
    ∃ u : ℝ × X → ℝ,
      u = transportFromFootpoint (flowTransportCoefficient c Φ) t₀ r Y ∧
      ContDiffOn ℝ ∞ u D ∧
      (∀ p ∈ U, u (t₀, Φ (t₀, p)) = r p) ∧
      (∀ p ∈ U, ∀ t ∈ I, HasDerivAt (fun s ↦ u (s, Φ (s, p)))
        (-c (t, Φ (t, p)) * u (t, Φ (t, p))) t) ∧
      (∀ q ∈ D, 0 < u q) ∧
      (∀ w : ℝ × X → ℝ,
        (∀ p ∈ U, w (t₀, Φ (t₀, p)) = r p) →
        (∀ p ∈ U, ∀ t ∈ I, HasDerivAt (fun s ↦ w (s, Φ (s, p)))
          (-c (t, Φ (t, p)) * w (t, Φ (t, p))) t) → EqOn w u D) := by
  have hc_flow := contDiffOn_flowTransportCoefficient hc hΦ hV
  have hc_time (p : P) (hp : p ∈ U) :
      ContinuousOn (fun s ↦ flowTransportCoefficient c Φ (s, p)) I :=
    hc_flow.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hs ↦ ⟨hs, hp⟩)
  refine ⟨transportFromFootpoint (flowTransportCoefficient c Φ) t₀ r Y, rfl,
    contDiffOn_transportFromFootpoint hI hIc hU hc_flow hr ht₀ hY hYU, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [transportFromFootpoint_along_flow _ _ _ (hYΦ p hp t₀ ht₀)]
    exact characteristicTransport_initial _ _ _ _
  · intro p hp t ht
    exact hasDerivAt_transportFromFootpoint_along_flow hI hIc p
      (hc_time p hp) ht₀ ht r (hYΦ p hp)
  · intro q hq
    exact transportFromFootpoint_pos _ _ _ _ _ (hrpos (Y q) (hYU hq).2)
  · intro w hw₀ hw
    exact transportFromFootpoint_unique hI hIc hc_time ht₀ hYU hΦY hw hw₀

end SmoothFlow

end JanetCartan
