module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.InitialData
public import JanetCartan.Analysis.ODE.PositiveTransport.FlowSolution

/-!
# Positive amplitude in the retained adapted coordinates

The actual section normal need not be a coordinate vector. This specialization
of the characteristic formula uses that normal and the literal projected-frame
coefficients. `Transport.Construction` constructs the flow from the named
coefficient hypotheses (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace

namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The characteristic formula solves the literal null transport equation in
the actual adapted coordinates. This deduction is instantiated with the
constructed flow in `FullModulation.exists_positive_amplitude`; no scalar PDE
or transport solution is an input (`app:ch_waves:thm:leading`). -/
theorem scalarAmplitude_spec (F : Euclidean n → Euclidean N) (row col : Fin n)
    {I : Set ℝ} {L : Set (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))}
    {D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))))}
    (hI : IsOpen I) (hIc : OrdConnected I) (hL : IsOpen L) (hD : IsOpen D)
    (h0 : (0 : ℝ) ∈ I)
    (hk : ContDiffOn ℝ ∞ (nullvector T Q col)
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D))
    (hc : ContDiffOn ℝ ∞ (transportPotential T Q F row col)
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D))
    (hQsym : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      ∀ i, (Q.1 w.1 i).IsSymm)
    (hden : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      adaptedDenominator T Q row col w ≠ 0)
    (hphase : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      (w.1, w.2.2) ∈ phaseDomain T)
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ r (initialProjection '' L))
    (hrpos : ∀ p ∈ initialProjection '' L, 0 < r p)
    {Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) → Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))}
    (hΦ : ContDiffOn ℝ ∞ Φ (I ×ˢ L))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D)
    (hΦ₀ : ∀ p ∈ L, Φ (0, p) = p)
    (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L))
    (hYΦ : ∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p)
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2)
    (hvelocity : ∀ p ∈ L, ∀ t ∈ I,
      HasDerivAt (fun s ↦ Φ (s, p))
        ((adaptedCoordinates T.data.adapted (transportDirection T Q row col
          ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p))))).2, 0) t) :
    let α := scalarAmplitude T Q F row col Φ Y r
    let Ω := coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D
    ContDiffOn ℝ ∞ α Ω ∧
      ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) Ω ∧
      (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
      (∀ w ∈ Ω, 0 < α w) ∧
      (∀ K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))), IsCompact K → K ⊆ Ω →
        ∃ m > 0, ∀ w ∈ K, m ≤ α w) ∧
      (∀ w ∈ Ω,
        fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
          transportPotential T Q F row col w * α w = 0) ∧
      (∀ w ∈ Ω,
        reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
          (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
      (∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
        (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) := by
  have hr : ContDiffOn ℝ ∞ (initialScalar r) L :=
    contDiffOn_initialScalar hr (mapsTo_image _ _)
  have hrpos : ∀ p ∈ L, 0 < initialScalar r p :=
    fun p hp ↦ hrpos _ (mem_image_of_mem initialProjection hp)
  have hnull (w) (hw : w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D) :=
    (nullvector_relations T Q row col (hphase w hw)).1
  let e := adaptedCoordinates T.data.adapted
  let C := coordinates (Z := (Euclidean 3 × Euclidean (n - 1))) e
  let c := fun q ↦ transportPotential T Q F row col (C.symm q)
  have hc' : ContDiffOn ℝ ∞ c D :=
    hc.comp C.symm.contDiff.contDiffOn (fun q hq ↦ by
      change C (C.symm q) ∈ D
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq)
  have hcflow := contDiffOn_flowTransportCoefficient hc' hΦ hΦD
  obtain ⟨u, rfl, hu, hu₀, _, hu_pos, _⟩ :=
    exists_positive_smooth_transport_along_flow hI hIc hL hc' hΦ hΦD
      hr hrpos h0 hY hYU hYΦ hΦY
  let u := transportFromFootpoint (flowTransportCoefficient c Φ) 0 (initialScalar r) Y
  let α := scalarAmplitude T Q F row col Φ Y r
  have hα : ContDiffOn ℝ ∞ α (C ⁻¹' D) :=
    hu.comp C.contDiff.contDiffOn (fun _ hw ↦ hw)
  have hΩ : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
  have hpde (w) (hw : w ∈ C ⁻¹' D) :
      fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
        transportPotential T Q F row col w * α w = 0 := by
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
        transportPotential T Q F row col w := by
      change c (q.1, Φ (q.1, Y q)) = _
      rw [hpoint]
      exact congrArg (transportPotential T Q F row col) hcw
    rw [hcw, hcf] at hd
    have ht : (e (transportDirection T Q row col w)).1 = 1 := by
      simpa [e] using transportDirection_normal T Q row col w (hden w hw)
    have hchain := directional_derivative_coordinates e
      ((hu.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp))
      (transportDirection T Q row col w)
    have hs : (∑ a, transportDirection T Q row col w a *
        partialDeriv (fun x ↦ α (x, w.2)) w.1 a) =
        fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) := by
      simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply, partialDeriv, smul_eq_mul] using
        congrArg (fderiv ℝ (fun x ↦ α (x, w.2)) w.1)
          ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (transportDirection T Q row col w))
    change (∑ a, transportDirection T Q row col w a *
      partialDeriv (fun x ↦ α (x, w.2)) w.1 a) = _ at hchain
    rw [hs, ht] at hchain
    rw [hchain]
    change fderiv ℝ u q (1, (e (transportDirection T Q row col w)).2, 0) +
      transportPotential T Q F row col w * u q = 0
    rw [hd]
    ring
  refine ⟨hα, hα.smul hk, ?_, fun w hw ↦ hu_pos (C w) hw, ?_, hpde, ?_, ?_⟩
  · intro p hp
    have hi := hu₀ p hp
    rw [hΦ₀ p hp] at hi
    have he : e.symm (0, p.1) = T.data.adapted.embedding p.1 := by simp [e]
    rw [← he]
    change u (C (e.symm (0, p.1), p.2)) = r (p.1, p.2.1)
    simpa only [C, coordinates_apply, ContinuousLinearEquiv.apply_symm_apply, u, initialScalar] using hi
  · intro K hK hKD
    obtain ⟨m, hm, hb⟩ := exists_pos_le_transportFromFootpoint_on_compact
      hI hIc hL hcflow hr h0 hrpos hY hYU
      (hK.image C.continuous) (by rintro _ ⟨w, hw, rfl⟩; exact hKD hw)
    exact ⟨m, hm, fun w hw ↦ hb (C w) (mem_image_of_mem C hw)⟩
  · intro w hw
    change reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
      (α w • (fun j ↦ nullvector T Q col w j)) = 0
    rw [Matrix.mulVec_smul, hnull w hw, smul_zero]
  · intro w hw
    have hαx : DifferentiableAt ℝ (fun x ↦ α (x, w.2)) w.1 :=
      ((hα.contDiffAt (hΩ.mem_nhds hw)).comp w.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hkx : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1 := by
      intro j
      exact ((contDiffAt_piLp 2).1
        ((hk.contDiffAt (hΩ.mem_nhds hw)).comp w.1
          (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
    exact (scalar_reduction_iff T Q F row col (hQsym w hw) hαx hkx (hden w hw)).2
      (hpde w hw)

end JanetCartan.LeadingWave.FullModulation
