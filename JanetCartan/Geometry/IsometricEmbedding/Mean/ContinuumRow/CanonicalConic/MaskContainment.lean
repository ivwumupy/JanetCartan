module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SymbolGeometry

/-!
# Actual mask and phase containment

The carrier mask uses the smaller physical radius, while its angular width
comes from the frozen annular chart. Its closed support has room inside the
same conic geometry. The literal normal density vanishes off that input
cone, for every radial regularization and both physical positions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}

/-- The actual smaller mask fits the supported cone and the physical `6a`
buffer at every point of the original output chart. This connects the smooth
mask constructor to the actual inverse domain (`app:ch_background:defn:bg-row`). -/
theorem angularMask_mem_symbolInputDomain (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a)
    (har : a ≤ r) {x y : Euclidean n}
    (hx : x ∈ closedBall 0 (4 * a)) (hy : y ∈ closedBall 0 (4 * a))
    {z : CarrierParameter} {η : Euclidean (n - 1)} (hη : η ≠ 0)
    (hm : angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
      z (‖η‖⁻¹ • η) ≠ 0) :
    ((x, y), z, η) ∈ symbolInputDomain z₀ ηb r (6 * a) := by
  obtain ⟨hs, hv, hθ⟩ := angularMask_nonzero z₀ (NormedSpace.normalize ηb)
    ha (angularWidth_spec hηb hr).1 hm
  refine ⟨⟨ball_subset_ball (by linarith) hv,
    (closedBall_subset_ball (by linarith : 4 * a < 6 * a)) hx,
    (closedBall_subset_ball (by linarith : 4 * a < 6 * a)) hy⟩, ?_⟩
  exact ⟨ball_subset_ball (by linarith) hs, hη,
    ball_subset_ball (by linarith [(angularWidth_spec hηb hr).1]) hθ⟩

/-- The closed angular/carrier support also lies strictly inside the same
input cone. This supplies the buffer needed for subsequent zero extension
of the literal density (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem angularMask_tsupport_mem_symbolInputDomain (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a)
    (har : a ≤ r) {x y : Euclidean n}
    (hx : x ∈ closedBall 0 (4 * a)) (hy : y ∈ closedBall 0 (4 * a))
    {z : CarrierParameter} {η : Euclidean (n - 1)} (hη : η ≠ 0)
    (hm : (z, NormedSpace.normalize η) ∈ tsupport
      (Function.uncurry (angularMask z₀ (NormedSpace.normalize ηb) ha
        (angularWidth_spec hηb hr).1))) :
    ((x, y), z, η) ∈ symbolInputDomain z₀ ηb r (6 * a) := by
  obtain ⟨⟨hs, hv⟩, hθ⟩ := angularMask_tsupport z₀ (NormedSpace.normalize ηb)
    ha (angularWidth_spec hηb hr).1 hm
  refine ⟨⟨closedBall_subset_ball (by linarith) hv,
    closedBall_subset_ball (by linarith) hx,
    closedBall_subset_ball (by linarith) hy⟩, ?_⟩
  exact ⟨closedBall_subset_ball (by linarith) hs, hη,
    closedBall_subset_ball (by linarith [(angularWidth_spec hηb hr).1]) hθ⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The physical phase difference agrees with the original averaged gradient
on every point of the actual input chart. Its regularity and parameter
containment are proved from the retained Hamilton family (`bg-Psi`). -/
theorem phase_identity_on_symbolInputDomain {c C : ℝ} (hP : P.IsValid c C)
    (hr : 0 < r) (haR : a < T.family.radius) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {p : InputVariables n} (hp : p ∈ symbolInputDomain z₀ ηb r a) :
    inner ℝ (transportPosition T Q (p.1.1, p.2.1)) p.2.2 -
        inner ℝ (transportPosition T Q (p.1.2, p.2.1)) p.2.2 =
      inner ℝ (p.1.1 - p.1.2) (transportAveragedGradient (transportPosition T Q) p) := by
  apply transportPosition_sub_eq_inner_averagedGradient T Q hP
    (ball_subset_ball haR.le hp.1.2.1) (ball_subset_ball haR.le hp.1.2.2)
  exact hcarrier ⟨(ball_subset_closedBall.trans (closedBall_subset_closedBall har)) hp.1.1,
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hp.2.1⟩

/-- Support of the SAME canonical two-position density, for any frequency
mask. Zero covectors vanish through the literal `|η|` factor; all other
nonzero densities lie in the smaller conic chart. This is the support premise
of `TransportKernel.ChartInputs` (`bg-full-complex-amplitude`). -/
theorem normalDensityEntry_zero_outside_symbolInputDomain
    {N : ℕ} (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : a ≤ r)
    (hcell : 4 * a < 1 / 2) (high : ℝ → ℝ) (m : CarrierVariable n → ℝ)
    (x y : Torus n)
    (hx : x ∈ (data T Q F row col Φ Y initial ha hcell
      (angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1) high).outputChart)
    (hy : y ∈ (data T Q F row col Φ Y initial ha hcell
      (angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1) high).outputChart)
    (u : CarrierVariable n)
    (hu : ((AmplitudeBound.centeredTorusRepresentative x,
      AmplitudeBound.centeredTorusRepresentative y), u) ∉ symbolInputDomain z₀ ηb r (6 * a))
    (i j : Fin n) :
    TransportKernel.normalDensityEntry (data T Q F row col Φ Y initial ha hcell
      (angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1) high)
      m x y u i j = 0 := by
  by_cases hη : u.2 = 0
  · simp [TransportKernel.normalDensityEntry, hη]
  have hm : angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
      u.1 (‖u.2‖⁻¹ • u.2) = 0 := by
    by_contra hm
    exact hu (angularMask_mem_symbolInputDomain hηb hr ha har hx hy hη hm)
  simp only [TransportKernel.normalDensityEntry, data, hm, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_mul]

end JanetCartan.ContinuumRow.CanonicalConic
