module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Coordinates
public import JanetCartan.Analysis.ODE.PositiveTransport.FlowSolution

/-!
# Positive amplitude in the retained adapted coordinates

The actual section normal need not be a coordinate vector. This specialization
of the characteristic formula uses that normal and the literal projected-frame
coefficients. `ActualAmplitude.LocalConstruction` supplies the flow and all
coefficient hypotheses from the primitive geometry (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace

namespace JanetCartan.NullTransport
open ActualCarriers FrozenMenu CurrentFullPhase ActualFlow FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The actual exponential-integral formula for the prescribed scalar on the
retained adapted section (`app:ch_waves:thm:leading`). -/
def carrierScalarAmplitude (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (w : Euclidean n × Euclidean 3) : ℝ :=
  transportFromFootpoint
    (flowTransportCoefficient (fun q ↦ carrierTransportPotential T Q F row col
      ((coordinates (adaptedCoordinates T.data.adapted)).symm q)) Φ)
    0 r Y (coordinates (adaptedCoordinates T.data.adapted) w)

/-- The characteristic formula solves the literal null transport equation in
the actual adapted coordinates. This deduction is instantiated with the
constructed flow in `exists_projected_local_positive_amplitude`; no scalar PDE
or transport solution is an input (`app:ch_waves:thm:leading`). -/
theorem carrierScalarAmplitude_spec (F : Euclidean n → Euclidean N) (row col : Fin n)
    {I : Set ℝ} {L : Set (Euclidean (n - 1) × Euclidean 3)}
    {D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hI : IsOpen I) (hIc : OrdConnected I) (hL : IsOpen L) (hD : IsOpen D)
    (h0 : (0 : ℝ) ∈ I)
    (hk : ContDiffOn ℝ ∞ (carrierNullvector T Q col)
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D))
    (hc : ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col)
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D))
    (hQsym : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      ∀ i, (Q.1 w.1 i).IsSymm)
    (hden : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      carrierAdaptedDenominator T Q row col w ≠ 0)
    (hnull : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
        (fun j ↦ carrierNullvector T Q col w j) = 0)
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ r L) (hrpos : ∀ p ∈ L, 0 < r p)
    {Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    (hΦ : ContDiffOn ℝ ∞ Φ (I ×ˢ L))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D)
    (hΦ₀ : ∀ p ∈ L, Φ (0, p) = p)
    (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L))
    (hYΦ : ∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p)
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2)
    (hvelocity : ∀ p ∈ L, ∀ t ∈ I,
      HasDerivAt (fun s ↦ Φ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
          ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p))))).2, 0) t) :
    let α := carrierScalarAmplitude T Q F row col Φ Y r
    let Ω := coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D
    ContDiffOn ℝ ∞ α Ω ∧
      ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) Ω ∧
      (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r p) ∧
      (∀ w ∈ Ω, 0 < α w) ∧
      (∀ K : Set (Euclidean n × Euclidean 3), IsCompact K → K ⊆ Ω →
        ∃ m > 0, ∀ w ∈ K, m ≤ α w) ∧
      (∀ w ∈ Ω,
        fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
          carrierTransportPotential T Q F row col w * α w = 0) ∧
      (∀ w ∈ Ω,
        reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
          (fun j ↦ (α w • carrierNullvector T Q col w) j) = 0) ∧
      (∀ w ∈ Ω, carrierConullvector T Q row w ⬝ᵥ reducedOperator F Q.1
        (fun x ↦ α (x, w.2) • carrierNullvector T Q col (x, w.2)) w.1 = 0) := by
  let e := adaptedCoordinates T.data.adapted
  let C := coordinates (Z := Euclidean 3) e
  let c := fun q ↦ carrierTransportPotential T Q F row col (C.symm q)
  have hc' : ContDiffOn ℝ ∞ c D :=
    hc.comp C.symm.contDiff.contDiffOn (fun q hq ↦ by
      change C (C.symm q) ∈ D
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq)
  have hcflow := contDiffOn_flowTransportCoefficient hc' hΦ hΦD
  obtain ⟨u, rfl, hu, hu₀, _, hu_pos, _⟩ :=
    exists_positive_smooth_transport_along_flow hI hIc hL hc' hΦ hΦD
      hr hrpos h0 hY hYU hYΦ hΦY
  let u := transportFromFootpoint (flowTransportCoefficient c Φ) 0 r Y
  let α := carrierScalarAmplitude T Q F row col Φ Y r
  have hα : ContDiffOn ℝ ∞ α (C ⁻¹' D) :=
    hu.comp C.contDiff.contDiffOn (fun _ hw ↦ hw)
  have hΩ : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
  have hpde (w) (hw : w ∈ C ⁻¹' D) :
      fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
        carrierTransportPotential T Q F row col w * α w = 0 := by
    let q := C w
    have hq : q ∈ D := hw
    have hlabel := hYU hq
    have hpoint : (q.1, Φ (q.1, Y q)) = q := by rw [hΦY q hq]
    have hd := fderiv_transportFromFootpoint_along_flow hI hIc hL hD hcflow hr h0
      hlabel.1 hlabel.2 hY hYU (hYΦ (Y q) hlabel.2) (hpoint.symm ▸ hq)
      (hvelocity (Y q) hlabel.2 q.1 hlabel.1)
    rw [hpoint] at hd
    have hcw : C.symm q = w := C.symm_apply_apply w
    have hcf : flowTransportCoefficient c Φ (q.1, Y q) =
        carrierTransportPotential T Q F row col w := by
      change c (q.1, Φ (q.1, Y q)) = _
      rw [hpoint]
      exact congrArg (carrierTransportPotential T Q F row col) hcw
    rw [hcw, hcf] at hd
    have ht : (e (carrierTransportDirection T Q row col w)).1 = 1 := by
      simpa [e] using carrierTransportDirection_normal T Q row col w (hden w hw)
    have hchain := directional_derivative_coordinates e
      ((hu.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp))
      (carrierTransportDirection T Q row col w)
    have hs : (∑ a, carrierTransportDirection T Q row col w a *
        partialDeriv (fun x ↦ α (x, w.2)) w.1 a) =
        fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) := by
      simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply, partialDeriv, smul_eq_mul] using
        congrArg (fderiv ℝ (fun x ↦ α (x, w.2)) w.1)
          ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (carrierTransportDirection T Q row col w))
    change (∑ a, carrierTransportDirection T Q row col w a *
      partialDeriv (fun x ↦ α (x, w.2)) w.1 a) = _ at hchain
    rw [hs, ht] at hchain
    rw [hchain]
    change fderiv ℝ u q (1, (e (carrierTransportDirection T Q row col w)).2, 0) +
      carrierTransportPotential T Q F row col w * u q = 0
    rw [hd]
    ring
  refine ⟨hα, hα.smul hk, ?_, fun w hw ↦ hu_pos (C w) hw, ?_, hpde, ?_, ?_⟩
  · intro p hp
    have hi := hu₀ p hp
    rw [hΦ₀ p hp] at hi
    have he : e.symm (0, p.1) = T.data.adapted.embedding p.1 := by simp [e]
    rw [← he]
    change u (C (e.symm (0, p.1), p.2)) = r p
    simpa only [C, coordinates_apply, ContinuousLinearEquiv.apply_symm_apply] using hi
  · intro K hK hKD
    obtain ⟨m, hm, hb⟩ := exists_pos_le_transportFromFootpoint_on_compact
      hI hIc hL hcflow hr h0 hrpos hY hYU
      (hK.image C.continuous) (by rintro _ ⟨w, hw, rfl⟩; exact hKD hw)
    exact ⟨m, hm, fun w hw ↦ hb (C w) (mem_image_of_mem C hw)⟩
  · intro w hw
    change reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
      (α w • (fun j ↦ carrierNullvector T Q col w j)) = 0
    rw [Matrix.mulVec_smul, hnull w hw, smul_zero]
  · intro w hw
    have hαx : DifferentiableAt ℝ (fun x ↦ α (x, w.2)) w.1 :=
      ((hα.contDiffAt (hΩ.mem_nhds hw)).comp w.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hkx : ∀ j, DifferentiableAt ℝ (fun x ↦ carrierNullvector T Q col (x, w.2) j) w.1 := by
      intro j
      exact ((contDiffAt_piLp 2).1
        ((hk.contDiffAt (hΩ.mem_nhds hw)).comp w.1
          (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
    exact (carrier_scalar_reduction_iff T Q F row col (hQsym w hw) hαx hkx (hden w hw)).2
      (hpde w hw)

end JanetCartan.NullTransport
