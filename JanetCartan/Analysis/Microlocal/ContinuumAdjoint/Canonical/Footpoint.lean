module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Footpoint.Conservation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.LocalConstruction

/-!
# The canonical Hamilton footpoint is the actual null-flow footpoint

This deduction uses the SAME `Φ,Y` returned by
`NullTransport.exists_projected_local_positive_amplitude`. Its inputs are
precisely that producer's forward/inverse maps, initial condition, carrier
identities, ODE, domain inclusion and nullvector/denominator properties.
The spatial Hamilton conservation law is proved in `Footpoint.Conservation`.
The existing physical and carrier buffers imply all Hamilton target and
initial-section containments, on the complete tube `D`.

For the producer's projected frame, symmetry follows from
`projectedStress_mem_stressSpace`, as recorded below. The parent adjoint task
retains finite-family selection, extensions, cutoffs and quantitative estimates.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_waves:thm:leading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude Footpoint ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Symmetry needed by the determinant/transport identity is supplied by the
actual projected stress producer from its original immersion data. This is
not an extra analytic hypothesis on the flow (`app:ch_waves:thm:leading`). -/
theorem projected_frame_symmetry {N : ℕ} (F : Euclidean n → Euclidean N)
    (hF : ContDiffOn ℝ ∞ F U) (hrank : HasFullNormalRankOn F U)
    (hQF : Q.1 = projectedStress F) : ∀ x ∈ U, ∀ i, (Q.1 x i).IsSymm := by
  intro x hx i
  rw [hQF]
  exact (ProjectedStressFrame.projectedStress_mem_stressSpace
    ((hF.contDiffAt (hU.mem_nhds hx)).of_le (by simp)) (hrank x hx) i).1

section Flow
variable (row col : Fin n) {c C₁ : ℝ} (hP : P.IsValid c C₁)
    {K : Set (Euclidean n)} (hKU : K ⊆ U)
    (hsymm : ∀ x ∈ U, ∀ i, (Q.1 x i).IsSymm)
    {τ : ℝ} (hτ : 0 < τ)
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    {D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (hgeom : (coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D ⊆
      (ball 0 T.physicalRadius ∩ interior K) ×ˢ parameterInterior (3 * P.radius / 2))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ L) D)
    (hYD : MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ L))
    (hinit : ∀ p ∈ L, Φ (0, p) = p)
    (hinv : ∀ q ∈ D, Φ (q.1, Y q) = q.2)
    (hcarrier : ∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, (Φ (t, p)).2 = p.2)
    (hYcarrier : ∀ q ∈ D, (Y q).2 = q.2.2)
    (hode : ∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, HasDerivAt (fun s ↦ Φ (s, p))
      ((adaptedCoordinates T.data.adapted
        (carrierTransportDirection T Q row col
          ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p))))).2, 0) t)
    (hnull : ∀ w ∈ (coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D,
      carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
      carrierConullvector T Q row w ᵥ*
        reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
      carrierAdaptedDenominator T Q row col w ≠ 0)

include hP hKU hsymm hτ hgeom hΦD hYD hinit hinv hcarrier hYcarrier hode hnull in
/-- Both components of the SAME inverse flow equal the Hamilton phase
footpoint and original carrier label everywhere on the complete supported
tube. All hypotheses after the fixed data are direct outputs of
`exists_projected_local_positive_amplitude`; frame symmetry is discharged by
`projected_frame_symmetry` (`app:ch_background:prop:bg-adjoint`). -/
theorem odeInitialPoint_eq_transportPosition {x : Euclidean n} {z : CarrierParameter}
    (hw : coordinates (adaptedCoordinates T.data.adapted)
      (x, CanonicalCarrier.parameter z) ∈ D) :
    odeInitialPoint T Y (z, x) =
      (CanonicalCarrier.transportPosition T Q (x, z), CanonicalCarrier.parameter z) := by
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let q := C (x, CanonicalCarrier.parameter z)
  let p := Y q
  let γ : ℝ → Euclidean n := fun t ↦ (C.symm (t, Φ (t, p))).1
  have hp : p ∈ L := (hYD hw).2
  have ht : q.1 ∈ Ioo (-τ) τ := (hYD hw).1
  have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨neg_neg_of_pos hτ, hτ⟩
  have hpz : p.2 = CanonicalCarrier.parameter z := hYcarrier q hw
  have hpath (t : ℝ) (ht : t ∈ Ioo (-τ) τ) :
      C.symm (t, Φ (t, p)) = (γ t, CanonicalCarrier.parameter z) := by
    refine Prod.ext ?_ ?_
    · rfl
    · exact (hcarrier p hp t ht).trans hpz
  have hmem (t : ℝ) (ht : t ∈ Ioo (-τ) τ) :
      (γ t, CanonicalCarrier.parameter z) ∈ C ⁻¹' D := by
    rw [← hpath t ht]
    change C (C.symm (t, Φ (t, p))) ∈ D
    rw [C.apply_symm_apply]
    exact hΦD (show (t, p) ∈ Ioo (-τ) τ ×ˢ L from ⟨ht, hp⟩)
  have htarget (t : ℝ) (ht : t ∈ Ioo (-τ) τ) :
      (γ t, (0, T.reference.spatialPatch (CanonicalCarrier.parameter z))) ∈
        (T.currentChart Q).target :=
    nullTransport_mem_hamiltonTarget T Q hP (hgeom (hmem t ht)).1.1 (hgeom (hmem t ht)).2
  have hγ (t : ℝ) (ht : t ∈ Ioo (-τ) τ) :
      HasDerivAt γ (carrierTransportDirection T Q row col (γ t, CanonicalCarrier.parameter z)) t := by
    have hd := (hnull _ (hmem t ht)).2.2.2
    rw [← hpath t ht] at hd
    have hh := hasDerivAt_physical_nullCharacteristic T Q row col Φ p t (hode p hp t ht) hd
    rw [hpath t ht] at hh
    exact hh
  have hconst (t : ℝ) (ht : t ∈ Ioo (-τ) τ) :
      HasDerivAt (fun s ↦ CanonicalCarrier.transportPosition T Q (γ s, z)) 0 t := by
    have hh := ((hasFDerivAt_transportPosition T Q (htarget t ht)).differentiableAt.hasFDerivAt).comp_hasDerivAt
      t (hγ t ht)
    rw [fderiv_transportPosition_carrierTransportDirection T Q row col (htarget t ht)
      (hsymm _ (hKU (interior_subset (hgeom (hmem t ht)).1.2)))
      (hnull _ (hmem t ht)).1 (hnull _ (hmem t ht)).2.1] at hh
    exact hh
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-τ) τ).isPreconnected
    (fun t ht ↦ (hconst t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hconst t ht).deriv) ht h0
  have hγt : γ q.1 = x := by
    change (C.symm (q.1, Φ (q.1, Y q))).1 = x
    rw [hinv q hw]
    exact congrArg Prod.fst (C.symm_apply_apply (x, CanonicalCarrier.parameter z))
  have hγ0 : γ 0 = T.data.adapted.embedding p.1 := by
    simp [γ, hinit p hp, C]
  have hsection : CanonicalCarrier.transportPosition T Q (γ 0, z) = p.1 := by
    rw [hγ0]
    apply transportPosition_on_initialSection T Q
    · rw [← hγ0]
      exact (hgeom (hmem 0 h0)).1.1
    · exact fun i ↦ ((hgeom (hmem 0 h0)).2 i).le.trans (by linarith [hP.1])
  rw [hγt, hsection] at he
  exact Prod.ext he.symm hpz

include hP hKU hsymm hτ hgeom hΦD hYD hinit hinv hcarrier hYcarrier hode hnull in
/-- The actual local normal is the prescribed initial scalar at `d_ζ S`,
times its literal exponential flow factor and actual canonical normal.
This is the formula consumed by `Assembly.ScalarTransport`; it is deduced
from the constructed ODE and Hamilton equations, not a scalar-composition
hypothesis (`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`). -/
theorem normalField_eq_initialScalar_transportPosition {N : ℕ}
    (F : Euclidean n → Euclidean N)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {x : Euclidean n} {z : CarrierParameter}
    (hw : coordinates (adaptedCoordinates T.data.adapted)
      (x, CanonicalCarrier.parameter z) ∈ D) :
    CanonicalCarrier.normalField T Q F row col Φ Y initial x z =
      (initialScalar initial (z, CanonicalCarrier.transportPosition T Q (x, z)) *
        flowFactor T Q F row col Φ Y (z, x)) • geometricNormal T Q F col (z, x) := by
  rw [normalField_eq_initial_flow,
    odeInitialPoint_eq_transportPosition T Q row col hP hKU hsymm hτ Φ Y
      hgeom hΦD hYD hinit hinv hcarrier hYcarrier hode hnull hw]
  rfl

end Flow
end JanetCartan.ContinuumAdjoint.Canonical
