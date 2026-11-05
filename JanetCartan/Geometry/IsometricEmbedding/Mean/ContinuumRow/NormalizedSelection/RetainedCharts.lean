module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.KernelMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.DensityMultipliers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.SourceMatching

/-!
# Literal normalized actions of the original retained charts

Apply the proved source-flow uniqueness theorem to the supplied seed and
contracted charts. Their common output cylinder, minor, scalar and inverse
are retained. The resulting kernel equality identifies both integral actions
without selecting another bounded operator. Arbitrary initial multipliers
remain at the original inverse ODE label, with their square in the kernel.

Consumers: the normalized finite row and its original density class, for
`app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-Nsigma`,
`app:ch_background:prop:bg-normalized` and `new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier
open ContinuumNormal.FrozenModel ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedLeading
open NullTransport ActualFlow FlowAmplitude HamiltonPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- An arbitrary prescribed initial multiplier contributes its square at
the literal inverse ODE label to the carrier kernel. There is no change of
carrier measure or Hamilton position (`app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-mixed-input`). -/
theorem carrierKernel_initial_mul
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial weight : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (x : Torus n) (u : CarrierVariable n) :
    carrierKernel (data T Q F row col Φ Y (fun p ↦ initial p * weight p)
      hr hcell angular high) x u =
      (weight (densityFootpoint T Y (AmplitudeBound.centeredTorusRepresentative x, u.1)) ^ 2 : ℂ) •
        carrierKernel (data T Q F row col Φ Y initial hr hcell angular high) x u := by
  by_cases hx : x ∈ PeriodicLocalL2.torusChart (closedBall (0 : Euclidean n) (4 * r))
  · simp only [carrierKernel, data, hx, indicator_of_mem, carrierPhase, carrierAmplitude,
      NormalizedCarrierProfiles.normalField_initial_mul, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    rw [show ∀ a b c d e w : ℝ, a * b * c * d * (w * e) =
      w * (a * b * c * d * e) by intros; ring]
    rw [mul_smul, map_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), reducedCovector]
    rw [smul_comm, RCLike.ofReal_pow]
    rfl
  · simp [carrierKernel, data, hx]

/-- The seed and contracted charts supplied by the original leading
construction have exactly the normalized carrier kernel, test integral and
adjoint integral on the full supported chart. The scalar identity is proved
from their ODEs, rather than assumed. The final identity keeps every original
initial multiplier at the actual contracted inverse label, including
`sqrt (1 + v)` in the original positive density class
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem retained_chart_normalized_kernel_and_integrals
    {c C : ℝ} (hP : P.IsValid c C)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {z₀ : Euclidean 3} {ρ Rc B τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), z₀) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc)
      (closedBall ((0 : Euclidean n), z₀) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (hsupport : ∀ (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1)),
      FixedCutoffs.periodic hr hcell 1 x ≠ 0 → angular z η ≠ 0 →
      densityCoordinates T (AmplitudeBound.centeredTorusRepresentative x, z) ∈
        Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 32))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (cσ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col (sourceDilation F σ)) :
    let d := data T cσ.Q (sourceDilation F σ) row col cσ.forward cσ.inverse
      (fun _ ↦ σ) hr hcell angular high
    let e := normalizedCarrierData T c₀.Q F row col c₀.forward c₀.inverse
      (fun _ ↦ 1) hr hcell angular high σ
    carrierKernel d = carrierKernel e ∧
    carrierTestIntegral d = carrierTestIntegral e ∧
    carrierAdjointIntegral d = carrierAdjointIntegral e ∧
    ∀ (weight : Euclidean (n - 1) × Euclidean 3 → ℝ) (x : Torus n) (u : CarrierVariable n),
      carrierKernel (data T cσ.Q (sourceDilation F σ) row col cσ.forward cσ.inverse
        (fun p ↦ σ * weight p) hr hcell angular high) x u =
        (weight (densityFootpoint T cσ.inverse
          (AmplitudeBound.centeredTorusRepresentative x, u.1)) ^ 2 : ℂ) • carrierKernel e x u := by
  intro d e
  have hpatch' : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) :=
    fun p hp ↦ ⟨(hpatch hp).1, fun i ↦ ((hpatch hp).2 i).le⟩
  obtain ⟨_, _, hscalar, _, _⟩ := retained_charts_source_dilation T hΩ hKΩ hpatch'
    hRc hτ hτR hbuffer hF hrank hphysical c₀ htrans hflat hσ hσ1 cσ
  let Cc := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hW : Cc ⁻¹' cσ.D ⊆ ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius) := by
    intro w hw
    apply hpatch
    have h := cσ.domain_coefficients hw
    change Cc.symm (Cc w) ∈ Ω at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  have hkernel : carrierKernel d = carrierKernel e :=
    carrierKernel_eq_normalized_of_scalar_transport T c₀.Q cσ.Q hF hrank hphysical
      c₀.frame_eq htrans hσ hσ1 cσ.frame_eq row col c₀.forward c₀.inverse cσ.forward cσ.inverse
      (fun _ ↦ 1) (fun _ ↦ σ) hP hr hcell angular high hW
      (fun x z η hx hz ↦ cσ.small_subset (hsupport x z η hx hz)) hscalar
  refine ⟨hkernel, ?_, ?_, ?_⟩
  · funext v x
    simp only [carrierTestIntegral, hkernel]
  · funext w u
    simp only [carrierAdjointIntegral, hkernel]
  · intro weight x u
    exact (carrierKernel_initial_mul T cσ.Q (sourceDilation F σ) row col
      cσ.forward cσ.inverse (fun _ ↦ σ) weight hr hcell angular high x u).trans
        (congrArg (fun k ↦ (weight (densityFootpoint T cσ.inverse
          (AmplitudeBound.centeredTorusRepresentative x, u.1)) ^ 2 : ℂ) • k)
          (congrFun (congrFun hkernel x) u))

end JanetCartan.ContinuumRow.NormalizedSelection
