module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.FlowAmplitude.Coordinates
public import JanetCartan.Analysis.ODE.PositiveTransport.FlowSolution

/-!
# Positive null amplitudes from a supplied characteristic flow

For `app:ch_waves:thm:leading`, construct the scalar by the published
exponential-integral formula and multiply the actual fixed adjugate column.
The reduced operator includes its Christoffel terms. Joint smoothness and
compact positive lower bounds include the carrier variables.

This is a conditional deduction: the characteristic covector, symmetric frame,
nonzero fixed minor and time root, smooth actual zero-order coefficient, adapted
linear coordinates, flow, and inverse footpoint chart must be supplied by the
geometric producers. No scalar or vector transport solution is an input. The
compact bounds here do not assert the manuscript's uniform tame estimates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.FlowAmplitude

variable {n N : ℕ} {X Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- The supplied characteristic flow gives the positive null amplitude in
`app:ch_waves:thm:leading`. The velocity hypothesis is an ODE for the *normalized
actual principal field*, with zero carrier velocity. The time-coordinate identity
makes the chain rule agree with Euclidean partial derivatives. The initial flow
is the identity, so the initial value is on the prescribed section itself.

Consumers `jc-null-transport` and `jc-leading-wave` must instantiate all geometric
and analytic hypotheses before claiming the original existence theorem. -/
theorem exists_positive_null_amplitude_of_flow
    (g : Geometry n N Z) (e : Euclidean n ≃L[ℝ] (ℝ × X))
    (he : ∀ v : Euclidean n, (e v).1 = v g.time)
    {I : Set ℝ} {U : Set (X × Z)} {D : Set (ℝ × (X × Z))} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U) (hD : IsOpen D)
    (ht₀ : t₀ ∈ I)
    (hQ : ∀ i j a, ContDiffOn ℝ ∞ (fun w ↦ g.frame w.2 w.1 i j a)
      (coordinates e ⁻¹' D))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (fun w ↦ g.covector w.2 w.1 a)
      (coordinates e ⁻¹' D))
    (hQsym : ∀ w ∈ coordinates e ⁻¹' D, ∀ i, (g.frame w.2 w.1 i).IsSymm)
    (hchar : ∀ w ∈ coordinates e ⁻¹' D, (g.symbol w).det = 0)
    (hminor : ∀ w ∈ coordinates e ⁻¹' D, (g.symbol w).adjugate g.row g.col ≠ 0)
    (hroot : ∀ w ∈ coordinates e ⁻¹' D,
      partialDeriv (reducedDeterminant (g.frame w.2 w.1))
        (g.covector w.2 w.1) g.time ≠ 0)
    (hc : ContDiffOn ℝ ∞ g.coefficient (coordinates e ⁻¹' D))
    {r : X × Z → ℝ} (hr : ContDiffOn ℝ ∞ r U) (hrpos : ∀ p ∈ U, 0 < r p)
    {Φ : ℝ × (X × Z) → X × Z} {Y : ℝ × (X × Z) → X × Z}
    (hΦ : ContDiffOn ℝ ∞ Φ (I ×ˢ U))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ U) D)
    (hΦ₀ : ∀ p ∈ U, Φ (t₀, p) = p)
    (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ U))
    (hYΦ : ∀ p ∈ U, ∀ t ∈ I, Y (t, Φ (t, p)) = p)
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2)
    (hvelocity : ∀ p ∈ U, ∀ t ∈ I,
      HasDerivAt (fun s ↦ Φ (s, p))
        ((e (g.direction ((coordinates e).symm (t, Φ (t, p))))).2, 0) t) :
    ∃ α : Euclidean n × Z → ℝ,
      α = (fun w ↦ transportFromFootpoint
        (flowTransportCoefficient (fun q ↦ g.coefficient ((coordinates e).symm q)) Φ)
        t₀ r Y (coordinates e w)) ∧
      ContDiffOn ℝ ∞ α (coordinates e ⁻¹' D) ∧
      ContDiffOn ℝ ∞ (fun w ↦ α w • g.kernel w) (coordinates e ⁻¹' D) ∧
      (∀ p ∈ U, α (e.symm (t₀, p.1), p.2) = r p) ∧
      (∀ w ∈ coordinates e ⁻¹' D, 0 < α w) ∧
      (∀ K : Set (Euclidean n × Z), IsCompact K → K ⊆ coordinates e ⁻¹' D →
        ∃ m > 0, ∀ w ∈ K, m ≤ α w) ∧
      (∀ w ∈ coordinates e ⁻¹' D,
        (∑ a, g.direction w a * partialDeriv (fun x ↦ α (x, w.2)) w.1 a) +
          g.coefficient w * α w = 0) ∧
      (∀ w ∈ coordinates e ⁻¹' D,
        g.symbol w *ᵥ (fun j ↦ (α w • g.kernel w) j) = 0) ∧
      (∀ w ∈ coordinates e ⁻¹' D,
        g.dual w ⬝ᵥ reducedOperator (g.immersion w.2) (g.frame w.2)
          (fun x ↦ α (x, w.2) • g.kernel (x, w.2)) w.1 = 0) ∧
      (∀ w ∈ coordinates e ⁻¹' D,
        g.kernel w ≠ 0 ∧ g.dual w ≠ 0 ∧ g.dual w ᵥ* g.symbol w = 0) := by
  let C := coordinates (Z := Z) e
  let c : ℝ × (X × Z) → ℝ := fun q ↦ g.coefficient (C.symm q)
  have hc' : ContDiffOn ℝ ∞ c D :=
    hc.comp C.symm.contDiff.contDiffOn (fun q hq ↦ by simpa [C] using hq)
  have hc_flow := contDiffOn_flowTransportCoefficient hc' hΦ hΦD
  obtain ⟨u, hu_eq, hu, hu₀, _, hu_pos, _⟩ :=
    exists_positive_smooth_transport_along_flow hI hIc hU hc' hΦ hΦD
      hr hrpos ht₀ hY hYU hYΦ hΦY
  subst u
  let u := transportFromFootpoint (flowTransportCoefficient c Φ) t₀ r Y
  let α : Euclidean n × Z → ℝ := fun w ↦ u (C w)
  have hα : ContDiffOn ℝ ∞ α (C ⁻¹' D) :=
    hu.comp C.contDiff.contDiffOn (fun _ hw ↦ hw)
  have hk := g.contDiffOn_kernel hQ hξ
  have hΩ : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
  have ht (w) (hw : w ∈ C ⁻¹' D) : g.timeCoefficient w ≠ 0 :=
    g.timeCoefficient_ne_zero (hQsym w hw) (hchar w hw) (hminor w hw) (hroot w hw)
  have hpde (w) (hw : w ∈ C ⁻¹' D) :
      (∑ a, g.direction w a * partialDeriv (fun x ↦ α (x, w.2)) w.1 a) +
        g.coefficient w * α w = 0 := by
    let q := C w
    have hq : q ∈ D := hw
    have hlabel := hYU hq
    have hpoint : (q.1, Φ (q.1, Y q)) = q := by rw [hΦY q hq]
    have hd := fderiv_transportFromFootpoint_along_flow
      hI hIc hU hD hc_flow hr ht₀ hlabel.1 hlabel.2 hY hYU
      (hYΦ (Y q) hlabel.2) (hpoint.symm ▸ hq)
      (hvelocity (Y q) hlabel.2 q.1 hlabel.1)
    rw [hpoint] at hd
    have hcw : C.symm q = w := C.symm_apply_apply w
    have hcf : flowTransportCoefficient c Φ (q.1, Y q) = g.coefficient w := by
      change c (q.1, Φ (q.1, Y q)) = _
      rw [hpoint]
      exact congrArg g.coefficient hcw
    rw [hcw, hcf] at hd
    have he_time : (e (g.direction w)).1 = 1 :=
      (he _).trans (g.direction_time (ht w hw))
    have hchain := directional_derivative_coordinates e
      ((hu.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)) (g.direction w)
    change (∑ a, g.direction w a * partialDeriv (fun x ↦ α (x, w.2)) w.1 a) = _
      at hchain
    rw [he_time] at hchain
    rw [hchain]
    change fderiv ℝ u q (1, (e (g.direction w)).2, 0) + g.coefficient w * u q = 0
    rw [hd]
    ring
  refine ⟨α, rfl, hα, hα.smul hk, ?_, ?_, ?_, hpde, ?_, ?_, ?_⟩
  · intro p hp
    have hi := hu₀ p hp
    rw [hΦ₀ p hp] at hi
    simpa [α, C, coordinates_apply] using hi
  · intro w hw
    exact hu_pos (C w) hw
  · intro K hK hKD
    obtain ⟨m, hm, hb⟩ := exists_pos_le_transportFromFootpoint_on_compact
      hI hIc hU hc_flow hr ht₀ hrpos hY hYU
      (hK.image C.continuous) (by rintro _ ⟨w, hw, rfl⟩; exact hKD hw)
    exact ⟨m, hm, fun w hw ↦ hb (C w) (mem_image_of_mem C hw)⟩
  · intro w hw
    change g.symbol w *ᵥ (α w • rightNullvector (g.symbol w) g.col) = 0
    rw [Matrix.mulVec_smul, mulVec_rightNullvector (hchar w hw), smul_zero]
  · intro w hw
    have hαx : DifferentiableAt ℝ (fun x ↦ α (x, w.2)) w.1 :=
      ((hα.contDiffAt (hΩ.mem_nhds hw)).comp w.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hkx : ∀ j, DifferentiableAt ℝ (fun x ↦ g.kernel (x, w.2) j) w.1 := by
      intro j
      exact ((contDiffAt_piLp 2).1
        ((hk.contDiffAt (hΩ.mem_nhds hw)).comp w.1
          (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
    apply (scalar_reduction_normalized_iff (g.immersion w.2) (g.frame w.2)
      (hQsym w hw) hαx hkx (g.dual w) g.time (ht w hw)).2
    exact hpde w hw
  · intro w hw
    refine ⟨?_, leftNullvector_ne_zero (hminor w hw),
      leftNullvector_vecMul (hchar w hw) g.row⟩
    intro hkzero
    apply rightNullvector_ne_zero (hminor w hw)
    exact congrArg (fun v : Euclidean n ↦ fun j ↦ v j) hkzero

end JanetCartan.NullTransport.FlowAmplitude
