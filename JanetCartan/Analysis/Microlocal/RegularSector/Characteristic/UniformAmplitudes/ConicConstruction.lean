module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.SupportedAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.SourceMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.BufferedBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.SupportedEndpoint

/-!
# Actual uniform supported conic amplitudes

Choose the source and auxiliary time masks before the coefficient field, on
the common source radius of the existing root/flow construction. Its literal
three matrices are extended by zero and then continued on the same radial
section. Their shell budgets follow from the original coefficient bounds,
with reserve ten in `Q` and nine in `B`, independent of shell and output order.
No root, flow, inverse, transport, amplitude or supported symbol estimate is
an input. A fixed smooth angular mask is supplied by the finite-cover owner.

Consumer: `EvolutionIntegral`'s actual primitive amplitude budgets for
`app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
The actual local null/correction equations are retained from the SAME
uniform root and flow and instantiate the supported cancellation producer.
One globally smooth auxiliary phase has the exact diagonal, agrees with the
Hamilton phase on the supported solver and residual, and gives the literal
upper leading endpoint. The complete integrated physical solver remains
separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open ActualCarriers AmplitudeBounds RootFamily ConicAmplitude ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
open EvolutionIntegral.SymbolBudgets hiding TwoTimePoint
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- Retain the SAME root, flow and inverse evolution through supported conic
continuation. The common time and root/geometry constants precede the masks,
angular cutoff, coefficient fields and requested jet orders. Entire inverse
segments retain their actual ODE, range and clock identities; the initial
condition and original compact root/flow/inverse budgets are also exported.
All literal supported matrices, the smooth phase `G`, cancellation, endpoint,
mask supports and original amplitude budgets are unchanged.

Consumers: `ResponseTransfer.RetainedFactors.exists_retained_conic_critical_geometry`
and `CompatibleResponse.elapsedModulatedPhase_critical_value`, for
`app:ch_response:eq:response-exact-phase`, `app:ch_response:eq:direct-envelope-profile`
and `paper-v2.tex`, `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_uniform_supported_conic_pencilAmplitudes_with_retained_evolution
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) (ξ : E) (r c : Fin (d + 1))
    (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0)
    (hm : (pencil A₀ ξ).adjugate r c ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ i : Fin (d + 1),
      let e := coordinateSplit i
      let z : Z := ((e x).1, ((e x).2, (e ξ).2))
      ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
        (H : (Fin (d + 1) → Mat) × Euclidean d → ℝ),
        ∃ ε > (0 : ℝ), ∃ L > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
        ∃ ρ > (0 : ℝ), ∃ ρo > ρ, ∃ src > (0 : ℝ), src < a ∧
        ρ ≤ b ∧ src ≤ ρ / 4 ∧
        ∃ μ > (0 : ℝ), ∃ ν > (0 : ℝ),
        ∃ phaseCost : ℕ → ℝ, (∀ m, 0 < phaseCost m) ∧
        ∃ rootCost : ℕ → ℝ, (∀ m, 0 < rootCost m) ∧
        ∃ evolutionTime > (0 : ℝ),
        2 * a ≤ L / 4 ∧ 2 * a ≤ evolutionTime / 4 ∧
        closedBall (z.1, z) (2 * a) ⊆ twoTimeDomain z (L / 2) evolutionTime ∧
        ℓ z.2.2 = 1 ∧
        AlgebraicChart.RootBuffer i r c A₀ ξ H ε L μ ν ∧
        a < L ∧ MapsTo (rootPhysicalPosition e) (closedBall z L) (closedBall x RQ) ∧
        ∃ (σ : Z → ℝ) (κ : ℝ → ℝ),
          ContDiff ℝ ∞ σ ∧ ContDiff ℝ ∞ κ ∧
          (∀ w, σ w ∈ Icc (0 : ℝ) 1) ∧ (∀ t, κ t ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport σ ∧ HasCompactSupport κ ∧
          tsupport σ ⊆ ball z (src / 2) ∧ tsupport κ ⊆ ball z.1 (src / 2) ∧
          closedBall z (src / 4) ⊆ interior {w | σ w = 1} ∧
          closedBall z.1 (src / 4) ⊆ interior {t | κ t = 1} ∧
        ∀ angular : Euclidean d → ℝ, ContDiff ℝ ∞ angular →
          (∀ η ∈ tsupport angular, 0 < ℓ η) →
          ∀ ra > (0 : ℝ), ∀ rb : ℝ,
          ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
          ∀ Q : E → Fin (d + 1) → Mat,
            ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
            cNorm (closedBall x RQ) 10 Q ≤ M →
            let h := fieldRoot e Q H
            let U := fieldDomain e Ω ℓ z.2.2 ε
            ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph T T,
              ODE.IsSmoothFlowOn (rootHamiltonField h) z L (L / 2) evolutionTime Φ ∧
              C.source ⊆ twoTimeDomain z (L / 2) evolutionTime ∧
              ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z (L / 2) evolutionTime) ∧
              ContDiffOn ℝ ∞ (twoTimeProjection Φ) (twoTimeDomain z (L / 2) evolutionTime) ∧
              ContDiffOn ℝ ∞ C C.source ∧
              (∀ q ∈ twoTimeDomain z (L / 2) evolutionTime,
                HasDerivAt (fun t ↦ twoTimeState Φ (t, q.2))
                  (rootHamiltonField h (twoTimeState Φ q)) q.1) ∧
              (∀ q ∈ twoTimeDomain z (L / 2) evolutionTime, ∀ u ∈ uIcc q.2.1 q.1,
                (u, q.2) ∈ twoTimeDomain z (L / 2) evolutionTime ∧
                  twoTimeState Φ (u, q.2) ∈ closedBall z L ∧
                  (twoTimeState Φ (u, q.2)).1 = u) ∧
              (∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
                (u, (C.symm q).2) ∈ twoTimeDomain z (L / 2) evolutionTime ∧
                  HasDerivAt (fun t ↦ twoTimeState Φ (t, (C.symm q).2))
                    (rootHamiltonField h (twoTimeState Φ (u, (C.symm q).2))) u ∧
                  twoTimeState Φ (u, (C.symm q).2) ∈ closedBall z L ∧
                  (twoTimeState Φ (u, (C.symm q).2)).1 = u) ∧
              (∀ m, cNorm (closedBall z L) m h ≤
                rootCost m * (1 + cNorm (closedBall x RQ) m Q)) ∧
              (∀ (R₀ : ℕ) (M₀ : ℝ), cNorm (closedBall x RQ) R₀ Q ≤ M₀ →
                ∀ j ≤ R₀, cNorm (closedBall z L) j h ≤ rootCost R₀ * (1 + M₀)) ∧
              (∀ (cost : ℕ → ℝ) (R₀ : ℕ) (scale : ℝ), 1 ≤ scale →
                (∀ m, cNorm (closedBall x RQ) m Q ≤ cost m * scale ^ (m - R₀)) →
                ∀ m, cNorm (closedBall z L) m h ≤
                  (rootCost m * (1 + cost m)) * scale ^ (m - R₀)) ∧
              (∀ m, cNorm (closedBall z (L / 4) ×ˢ
                  Icc (-evolutionTime / 4) (evolutionTime / 4)) m Φ +
                (cNorm (closedBall (z.1, z) a) m (twoTimeState Φ) +
                  cNorm (closedBall (z.1, z) a) m (twoTimeProjection Φ)) +
                (cNorm (closedBall (z.1, z) b) m C.symm +
                  cNorm (closedBall (z.1, z) b) m (twoTimePhase C)) ≤
                    phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
              (∀ w ∈ ball z a, Φ (w, 0) = w) ∧
              ContDiffOn ℝ ∞ h U ∧
              (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
              closedBall z L ⊆ U ∧
              (∀ w ∈ closedBall z L, (rootPencil e Q h w).det = 0 ∧
                μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
                ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
              (C : T → T) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) a ∧
              ContDiffOn ℝ ∞ C.symm C.target ∧ closedBall (z.1, z) b ⊆ C.target ∧
              ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
              (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
              (∀ q ∈ C.target,
                (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
                (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
              (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ U ∧
                (twoTimeState Φ (C.symm q)).1 = q.1) ∧
              (∀ w ∈ ball z a, (w.1, w) ∈ C.target ∧
                C.symm (w.1, w) = (w.1, w) ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
              (∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
              (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
                phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
              ball (z.1, z) ρo ⊆ C.target ∧
              MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2)) ∧
              ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω → cNorm (closedBall x RQ) 9 B ≤ M →
                let V := C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
                  (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))
                let Fs := fun j ↦ bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
                let W₀ := curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0))
                let W₁ := curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
                ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
                  (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
                  (∀ p ∈ tsupport (collared ℓ 0 angular (Fs 0)) ∪
                    tsupport (collared ℓ 1 angular (Fs 1)), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
                    collared ℓ 1 angular (Fs 2) p ≠ 0 → G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ y : E, κ =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
                    WKB.firstOrderApply
                      (fun x a ↦ ((coefficient i Q x a).map Complex.ofReal).mulVecLin)
                      (fun x ↦ ((zeroth i B x).map Complex.ofReal).mulVecLin)
                      (fun x ↦ Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
                        (fun k ↦ (W₀ + W₁) (x 0) s (spatialPart x) η k j)) y =
                      Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
                        (fun k ↦ twoTimePhysicalApply (fun x a ↦ (coefficient i Q x a).map Complex.ofReal)
                          (fun x ↦ (zeroth i B x).map Complex.ofReal) W₁
                            (y 0) s (spatialPart y) η k j)) ∧
                  (∀ y : E, κ (y 0) = 1 → ∀ η,
                    (coefficient i Q y 0).map Complex.ofReal * W₀ (y 0) (y 0) (spatialPart y) η =
                      conicSourceSymbol ℓ (FiniteMasks.conicMask angular) σ y η •
                        projector i Q h r c y ((ℓ η)⁻¹ • η)) ∧
                (∀ q : T, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d + 1),
                  (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
                    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                      (fun y k ↦ collared ℓ 1 angular (Fs 1)
                        (physicalSlice e q.2.1 q.2.2.2 y) k j)
                      (e.symm (q.1, q.2.2.1))) ∧
                ∀ j : Fin 3,
                  let f := pencilAmplitudeFamily i Q B h Φ C r c σ j
                  let F := bufferedMatrix V κ f
                  let o := if j = 0 then 0 else 1
                  let W := collared ℓ o angular F
                  ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ V ∧
                  tsupport F ⊆ closedBall (z.1, z) (ρ / 2) ∧ ContDiff ℝ ∞ W ∧
                  tsupport W ⊆ ConicPhase.domain ℓ V ∧
                  (∀ q : T, q.2.1 ≤ z.1 - src → W q = 0) ∧
                  (∀ q ∈ V, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → F =ᶠ[𝓝 q] f) ∧
                  ∀ m,
                    BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ∧
                    twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ≤
                      D m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
                        cNorm (closedBall x RQ) (m + 9) B) := by
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost,
    rootCost, hrootCost, evolutionTime, hevolutionTime, haR, haT, htimeDomain,
    hℓ, halgebraic, haL, hrootPhys, hlocal⟩ :=
    exists_uniform_pencilAmplitudes_with_retained_evolution hΩ x hRQ hKΩ A₀ ξ r c hξ hp hreg hm hM
  let e := coordinateSplit i
  let z : Z := ((e x).1, ((e x).2, (e ξ).2))
  obtain ⟨σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, _⟩ :=
    exists_common_characteristic_source_masks z hsrc
  obtain ⟨D₀, hD₀, hfields⟩ := hlocal (cNorm (closedBall z L) 9 σ) (cNorm_nonneg _ _ _)
  refine ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost,
    rootCost, hrootCost, evolutionTime, hevolutionTime, haR, haT, htimeDomain,
    hℓ, halgebraic, haL, hrootPhys,
    σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, ?_⟩
  intro angular hang hapos ra hra rb
  let K := ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb
  let J := closedBall (z.1, z) ρ
  let timeCost := fun m : ℕ ↦ 1 + (m + 1 : ℝ) * 2 ^ m *
    cNorm J m (fun p : T ↦ (κ p.1 : ℂ))
  let radialCost := fun m ↦ collarBoundConstant angular K m *
    (symbolBoundConstant (n := d + 1) ℓ 0 K m + symbolBoundConstant (n := d + 1) ℓ 1 K m)
  let maskCost := fun m ↦ 1 + cNorm (closedBall z L) (m + 9) σ
  have htime m : 0 < timeCost m := by
    have := cNorm_nonneg J m (fun p : T ↦ (κ p.1 : ℂ))
    dsimp [timeCost]; positivity
  have hradial m : 0 < radialCost m := mul_pos (collarBoundConstant_pos _ _ _)
    (add_pos (symbolBoundConstant_pos _ _ _ _) (symbolBoundConstant_pos _ _ _ _))
  have hmask m : 0 < maskCost m := by
    have := cNorm_nonneg (closedBall z L) (m + 9) σ
    dsimp [maskCost]; positivity
  refine ⟨fun m ↦ radialCost m * timeCost m * D₀ m * maskCost m,
    fun m ↦ mul_pos (mul_pos (mul_pos (hradial m) (htime m)) (hD₀ m)) (hmask m), ?_⟩
  intro Q hQ hQrange hQM h U
  obtain ⟨Φ, C, hΦ, hsourceD, hstateSmooth, hprojectionSmooth, hforwardSmooth,
    hderiv, hsegment, hinverseEvolution, hrootnorm, hrootlow, hgraded, hbudget,
    hh, hhom, hrootU, hgaps, hC, hsource, hCs, hbuffer,
    hphase, hdiff, hcoords, hstate, hdiag, hmixed, hphaseB, htarget, hflow, hinit, hkernel, hmat⟩ :=
    hfields Q hQ hQrange hQM
  refine ⟨Φ, C, hΦ, hsourceD, hstateSmooth, hprojectionSmooth, hforwardSmooth,
    hderiv, hsegment, hinverseEvolution, hrootnorm, hrootlow, hgraded, hbudget, hinit,
    hh, hhom, hrootU, hgaps, hC, hsource, hCs, hbuffer,
    hphase, hdiff, hcoords, hstate, hdiag, hmixed, hphaseB, htarget, hflow, ?_⟩
  intro B hB hBM V Fs W₀ W₁
  obtain ⟨hW₀, hW₁, hPW₁, hWbudget⟩ := hmat B σ hB hσ hBM le_rfl
  have hf j : ContDiffOn ℝ ∞ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
      (ball (z.1, z) ρo) := by
    fin_cases j
    · exact hW₀
    · exact hW₁
    · exact hPW₁
  have hfb j m : cNorm J m (pencilAmplitudeFamily i Q B h Φ C r c σ j) ≤
      D₀ m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
        cNorm (closedBall x RQ) (m + 9) B + cNorm (closedBall z L) (m + 9) σ) := by
    fin_cases j
    · exact (hWbudget m).1
    · exact (hWbudget m).2.1
    · exact (hWbudget m).2.2
  have hbuffered := buffered_pencilAmplitudeFamily_of_uniform_outputs i Q B h Φ C hC r c z
    hsrc hsrca hρ hρo hsource hflow hκ hcκ hsκ hcσ hsσ hf
  let I := ball z.1 (src / 2)
  let Jsource := ball z.2 (src / 2)
  have hsmall : I ×ˢ Jsource ⊆ ball z a := by
    intro w hw
    apply ball_subset_ball (show src / 2 ≤ a by linarith only [hsrca, hsrc])
    simpa only [I, Jsource, mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hw
  have hbox : I ×ˢ (I ×ˢ Jsource) ⊆ C.source := by
    rw [hsource]
    intro q hq
    apply ball_subset_ball (show src / 2 ≤ a by linarith only [hsrca, hsrc])
    simpa only [I, Jsource, mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hq
  have hσbox : tsupport σ ⊆ I ×ˢ Jsource := by
    intro w hw
    simpa only [I, Jsource, mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hsσ hw
  have hdiagonal w (hw : w ∈ I ×ˢ Jsource) : (w.1, w) ∈ C.target ∧
      twoTimeState Φ (C.symm (w.1, w)) = w ∧
        twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ := by
    obtain ⟨hwt, hwi, hwp⟩ := hdiag w (hsmall hw)
    refine ⟨hwt, ?_, hwp⟩
    simp only [hwi, twoTimeState, sub_self, hinit w (hsmall hw)]
  have hω : tsupport (FiniteMasks.conicMask angular) ⊆ {η | 0 < ℓ η} :=
    FiniteMasks.conicMask_tsupport_subset_cone angular hapos (fun η hη t ht ↦ by
      change 0 < ℓ (t • η)
      simpa only [map_smul, smul_eq_mul] using mul_pos ht hη)
  obtain ⟨hcols, hend, hcanc⟩ := hkernel B σ hB hσ
  obtain ⟨_, _, G, hG, hGdiag, hGerm, hcancel⟩ := exists_smooth_supported_conic_cancellation
    ℓ i Q B h Φ C hC r c σ isOpen_ball isOpen_ball hbox κ hκ hcκ hsκ hcσ hσbox
    (FiniteMasks.conicMask angular) (FiniteMasks.contDiff_conicMask hang) hω hphase hdiff
    (fun q hq ↦ (hstate q hq).2) hdiagonal hcols
    (fun q hq j ↦ (hcanc q hq j).1) (fun q hq j ↦ (hcanc q hq j).2.2)
  have hF₀ : Fs 0 = fun p : T ↦ bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    congr 1
  have hF₁ : Fs 1 = fun p : T ↦ bufferedAmplitude V κ (correction i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    congr 1
  have hphysical (q : T) (hk : κ =ᶠ[𝓝 q.1] (fun _ ↦ 1)) (j : Fin (d + 1)) :
      (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ collared ℓ 1 angular (Fs 1)
            (physicalSlice e q.2.1 q.2.2.2 y) k j) (e.symm (q.1, q.2.2.1)) := by
    have hV : IsOpen V := C.symm.continuousOn.isOpen_inter_preimage
      C.open_target (isOpen_ball.prod (isOpen_ball.prod isOpen_ball))
    have hVU : V ⊆ ball (z.1, z) ρo :=
      (transported_small_box_subset C z hsrc.le hflow).trans
        (closedBall_subset_ball (by linarith : ρ / 2 < ρo))
    exact collared_buffered_correction_residual_eq_physicalApply ℓ angular i Q B h Φ C r c σ κ
      hV isOpen_ball hVU hW₁ (hbuffered 1).1 (hbuffered 1).2.2.1 (hbuffered 2).2.2.1 q hk j
  refine ⟨G, hG, hGdiag, ?_, ?_, ?_, ?_, hphysical, ?_⟩
  · simpa only [collared_eq_supportedConicMatrix, hF₀, hF₁] using hGerm
  · intro p hκp hp
    have hs : p ∈ tsupport (collared ℓ 1 angular (Fs 1)) := by
      by_contra hn
      apply hp
      ext k j
      have hz := firstOrderApply_physicalSlice_eq_zero_of_notMem_tsupport
        i Q B (collared ℓ 1 angular (Fs 1)) p hn j
      have he := (hphysical p hκp j).trans hz
      exact congrFun he k
    apply hGerm p
    right
    simpa only [collared_eq_supportedConicMatrix, hF₁] using hs
  · simpa only [W₀, W₁, collared_eq_supportedConicMatrix, hF₀, hF₁] using hcancel
  · intro y hκy η
    simpa only [W₀, collared_eq_supportedConicMatrix, hF₀] using
      supported_leading_endpoint ℓ i Q B h Φ C hC r c σ I Jsource hbox
        (fun w hw ↦ hinit w (hsmall hw)) hσbox κ (FiniteMasks.conicMask angular) hend y hκy η
  intro j f F o W
  obtain ⟨hF, hcF, hsF, hsJ, hlower, hFnorm, hagree⟩ := hbuffered j
  refine ⟨hF, hcF, hsF, hsJ, contDiff_collared ℓ o hang hapos hF,
    tsupport_collared_subset_domain ℓ o angular hapos F hsF,
    collared_lower_buffer ℓ o angular (z.1 - src) hlower, hagree, ?_⟩
  intro m
  have hnorms := ConicPhase.bufferedJetSet_normalizes ℓ (z := z) (half_pos hρ).le hra (b := rb)
  have hnorm : MapsTo (ConicPhase.normalize ℓ ∘ evolutionToCharacteristicPoint) K J := by
    intro p hp
    have ht := hnorms.2 hp
    change ConicPhase.normalize ℓ (evolutionToCharacteristicPoint p) ∈
      closedBall (z.1, z) (2 * (ρ / 2)) at ht
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at ht
    exact ht
  have hKU : evolutionToCharacteristicPoint '' K ⊆ ConicPhase.domain ℓ univ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hnorms.1 p hp, mem_univ _⟩
  have hK := ConicPhase.isCompact_bufferedJetSet ℓ z (ρ / 2) ra rb
  refine ⟨(twoTimeOrderSeminorm_curry_collared_le ℓ o hang hK isOpen_univ hKU hF.contDiffOn m).1, ?_⟩
  have hconic := twoTimeOrderSeminorm_curry_collared_le_local ℓ o hang hK
    (isCompact_closedBall _ _) isOpen_univ (subset_univ J) hnorms.1 hnorm hF.contDiffOn m
  have hrad : collarBoundConstant angular K m * symbolBoundConstant (n := d + 1) ℓ o K m ≤
      radialCost m := by
    apply mul_le_mul_of_nonneg_left _ (collarBoundConstant_pos _ _ _).le
    dsimp [o]
    split_ifs
    · exact le_add_of_nonneg_right (symbolBoundConstant_pos _ _ _ _).le
    · exact le_add_of_nonneg_left (symbolBoundConstant_pos _ _ _ _).le
  have hFbound : cNorm J m F ≤ timeCost m * cNorm J m f :=
    (hFnorm m).trans (mul_le_mul_of_nonneg_right (by dsimp [timeCost]; linarith)
      (cNorm_nonneg _ _ _))
  have hhigh : 1 + cNorm (closedBall x RQ) (m + 10) Q +
      cNorm (closedBall x RQ) (m + 9) B + cNorm (closedBall z L) (m + 9) σ ≤
      maskCost m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
        cNorm (closedBall x RQ) (m + 9) B) := by
    have hq0 := cNorm_nonneg (closedBall x RQ) (m + 10) Q
    have hb0 := cNorm_nonneg (closedBall x RQ) (m + 9) B
    have hs0 := cNorm_nonneg (closedBall z L) (m + 9) σ
    dsimp [maskCost]
    nlinarith only [mul_nonneg hq0 hs0, mul_nonneg hb0 hs0]
  calc
    _ ≤ radialCost m * cNorm J m F := hconic.trans
      (mul_le_mul_of_nonneg_right hrad (cNorm_nonneg _ _ _))
    _ ≤ radialCost m * (timeCost m * (D₀ m *
        (maskCost m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
          cNorm (closedBall x RQ) (m + 9) B)))) := by
      apply mul_le_mul_of_nonneg_left _ (hradial m).le
      apply hFbound.trans
      apply mul_le_mul_of_nonneg_left _ (htime m).le
      exact (hfb j m).trans (mul_le_mul_of_nonneg_left hhigh (hD₀ m).le)
    _ = _ := by ring

/-- The algebraic-data endpoint is the projection of the same construction
retaining evolution, with its original public signature
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_uniform_supported_conic_pencilAmplitudes_with_algebraic_data
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) (ξ : E) (r c : Fin (d + 1))
    (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0)
    (hm : (pencil A₀ ξ).adjugate r c ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ i : Fin (d + 1),
      let e := coordinateSplit i
      let z : Z := ((e x).1, ((e x).2, (e ξ).2))
      ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
        (H : (Fin (d + 1) → Mat) × Euclidean d → ℝ),
        ∃ ε > (0 : ℝ), ∃ L > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
        ∃ ρ > (0 : ℝ), ∃ ρo > ρ, ∃ src > (0 : ℝ), src < a ∧
        ρ ≤ b ∧ src ≤ ρ / 4 ∧
        ∃ μ > (0 : ℝ), ∃ ν > (0 : ℝ),
        ∃ phaseCost : ℕ → ℝ, (∀ m, 0 < phaseCost m) ∧ ℓ z.2.2 = 1 ∧
        AlgebraicChart.RootBuffer i r c A₀ ξ H ε L μ ν ∧
        a < L ∧ MapsTo (rootPhysicalPosition e) (closedBall z L) (closedBall x RQ) ∧
        ∃ (σ : Z → ℝ) (κ : ℝ → ℝ),
          ContDiff ℝ ∞ σ ∧ ContDiff ℝ ∞ κ ∧
          (∀ w, σ w ∈ Icc (0 : ℝ) 1) ∧ (∀ t, κ t ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport σ ∧ HasCompactSupport κ ∧
          tsupport σ ⊆ ball z (src / 2) ∧ tsupport κ ⊆ ball z.1 (src / 2) ∧
          closedBall z (src / 4) ⊆ interior {w | σ w = 1} ∧
          closedBall z.1 (src / 4) ⊆ interior {t | κ t = 1} ∧
        ∀ angular : Euclidean d → ℝ, ContDiff ℝ ∞ angular →
          (∀ η ∈ tsupport angular, 0 < ℓ η) →
          ∀ ra > (0 : ℝ), ∀ rb : ℝ,
          ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
          ∀ Q : E → Fin (d + 1) → Mat,
            ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
            cNorm (closedBall x RQ) 10 Q ≤ M →
            let h := fieldRoot e Q H
            let U := fieldDomain e Ω ℓ z.2.2 ε
            ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph T T,
              ContDiffOn ℝ ∞ h U ∧
              (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
              closedBall z L ⊆ U ∧
              (∀ w ∈ closedBall z L, (rootPencil e Q h w).det = 0 ∧
                μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
                ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
              (C : T → T) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) a ∧
              ContDiffOn ℝ ∞ C.symm C.target ∧ closedBall (z.1, z) b ⊆ C.target ∧
              ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
              (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
              (∀ q ∈ C.target,
                (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
                (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
              (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ U ∧
                (twoTimeState Φ (C.symm q)).1 = q.1) ∧
              (∀ w ∈ ball z a, (w.1, w) ∈ C.target ∧
                C.symm (w.1, w) = (w.1, w) ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
              (∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
              (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
                phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
              ball (z.1, z) ρo ⊆ C.target ∧
              MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2)) ∧
              ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω → cNorm (closedBall x RQ) 9 B ≤ M →
                let V := C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
                  (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))
                let Fs := fun j ↦ bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
                let W₀ := curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0))
                let W₁ := curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
                ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
                  (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
                  (∀ p ∈ tsupport (collared ℓ 0 angular (Fs 0)) ∪
                    tsupport (collared ℓ 1 angular (Fs 1)), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
                    collared ℓ 1 angular (Fs 2) p ≠ 0 → G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ y : E, κ =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
                    WKB.firstOrderApply
                      (fun x a ↦ ((coefficient i Q x a).map Complex.ofReal).mulVecLin)
                      (fun x ↦ ((zeroth i B x).map Complex.ofReal).mulVecLin)
                      (fun x ↦ Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
                        (fun k ↦ (W₀ + W₁) (x 0) s (spatialPart x) η k j)) y =
                      Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
                        (fun k ↦ twoTimePhysicalApply (fun x a ↦ (coefficient i Q x a).map Complex.ofReal)
                          (fun x ↦ (zeroth i B x).map Complex.ofReal) W₁
                            (y 0) s (spatialPart y) η k j)) ∧
                  (∀ y : E, κ (y 0) = 1 → ∀ η,
                    (coefficient i Q y 0).map Complex.ofReal * W₀ (y 0) (y 0) (spatialPart y) η =
                      conicSourceSymbol ℓ (FiniteMasks.conicMask angular) σ y η •
                        projector i Q h r c y ((ℓ η)⁻¹ • η)) ∧
                (∀ q : T, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d + 1),
                  (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
                    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                      (fun y k ↦ collared ℓ 1 angular (Fs 1)
                        (physicalSlice e q.2.1 q.2.2.2 y) k j)
                      (e.symm (q.1, q.2.2.1))) ∧
                ∀ j : Fin 3,
                  let f := pencilAmplitudeFamily i Q B h Φ C r c σ j
                  let F := bufferedMatrix V κ f
                  let o := if j = 0 then 0 else 1
                  let W := collared ℓ o angular F
                  ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ V ∧
                  tsupport F ⊆ closedBall (z.1, z) (ρ / 2) ∧ ContDiff ℝ ∞ W ∧
                  tsupport W ⊆ ConicPhase.domain ℓ V ∧
                  (∀ q : T, q.2.1 ≤ z.1 - src → W q = 0) ∧
                  (∀ q ∈ V, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → F =ᶠ[𝓝 q] f) ∧
                  ∀ m,
                    BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ∧
                    twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ≤
                      D m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
                        cNorm (closedBall x RQ) (m + 9) B) := by
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost,
    rootCost, hrootCost, evolutionTime, hevolutionTime, haR, haT, htimeDomain,
    hℓ, halgebraic, haL, hrootPhys, hrest⟩ :=
    exists_uniform_supported_conic_pencilAmplitudes_with_retained_evolution hΩ x hRQ hKΩ A₀ ξ r c hξ hp hreg hm hM
  refine ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost,
    hℓ, halgebraic, haL, hrootPhys, ?_⟩
  obtain ⟨σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hfields⟩ := hrest
  refine ⟨σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, ?_⟩
  intro angular hang hapos ra hra rb
  obtain ⟨D, hD, hfields⟩ := hfields angular hang hapos ra hra rb
  refine ⟨D, hD, ?_⟩
  intro Q hQ hQrange hQM
  obtain ⟨Φ, C, _, _, _, _, _, _, _, _, _, _, _, _, _, hdata⟩ := hfields Q hQ hQrange hQM
  exact ⟨Φ, C, hdata⟩

/-- The original retarded-radius endpoint is a corollary of the same construction
retaining joint coefficient data (`app:ch_regular_base:eq:complement-inverse`). -/
theorem exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) (ξ : E) (r c : Fin (d + 1))
    (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0)
    (hm : (pencil A₀ ξ).adjugate r c ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ i : Fin (d + 1),
      let e := coordinateSplit i
      let z : Z := ((e x).1, ((e x).2, (e ξ).2))
      ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
        (H : (Fin (d + 1) → Mat) × Euclidean d → ℝ),
        ∃ ε > (0 : ℝ), ∃ L > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
        ∃ ρ > (0 : ℝ), ∃ ρo > ρ, ∃ src > (0 : ℝ), src < a ∧
        ρ ≤ b ∧ src ≤ ρ / 4 ∧
        ∃ μ > (0 : ℝ), ∃ ν > (0 : ℝ),
        ∃ phaseCost : ℕ → ℝ, (∀ m, 0 < phaseCost m) ∧ ℓ z.2.2 = 1 ∧
        ∃ (σ : Z → ℝ) (κ : ℝ → ℝ),
          ContDiff ℝ ∞ σ ∧ ContDiff ℝ ∞ κ ∧
          (∀ w, σ w ∈ Icc (0 : ℝ) 1) ∧ (∀ t, κ t ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport σ ∧ HasCompactSupport κ ∧
          tsupport σ ⊆ ball z (src / 2) ∧ tsupport κ ⊆ ball z.1 (src / 2) ∧
          closedBall z (src / 4) ⊆ interior {w | σ w = 1} ∧
          closedBall z.1 (src / 4) ⊆ interior {t | κ t = 1} ∧
        ∀ angular : Euclidean d → ℝ, ContDiff ℝ ∞ angular →
          (∀ η ∈ tsupport angular, 0 < ℓ η) →
          ∀ ra > (0 : ℝ), ∀ rb : ℝ,
          ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
          ∀ Q : E → Fin (d + 1) → Mat,
            ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
            cNorm (closedBall x RQ) 10 Q ≤ M →
            let h := fieldRoot e Q H
            let U := fieldDomain e Ω ℓ z.2.2 ε
            ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph T T,
              ContDiffOn ℝ ∞ h U ∧
              (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
              closedBall z L ⊆ U ∧
              (∀ w ∈ closedBall z L, (rootPencil e Q h w).det = 0 ∧
                μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
                ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
              (C : T → T) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) a ∧
              ContDiffOn ℝ ∞ C.symm C.target ∧ closedBall (z.1, z) b ⊆ C.target ∧
              ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
              (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
              (∀ q ∈ C.target,
                (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
                (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
              (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ U ∧
                (twoTimeState Φ (C.symm q)).1 = q.1) ∧
              (∀ w ∈ ball z a, (w.1, w) ∈ C.target ∧
                C.symm (w.1, w) = (w.1, w) ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
              (∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
              (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
                phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
              ball (z.1, z) ρo ⊆ C.target ∧
              MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2)) ∧
              ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω → cNorm (closedBall x RQ) 9 B ≤ M →
                let V := C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
                  (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))
                let Fs := fun j ↦ bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
                let W₀ := curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0))
                let W₁ := curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
                ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
                  (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
                  (∀ p ∈ tsupport (collared ℓ 0 angular (Fs 0)) ∪
                    tsupport (collared ℓ 1 angular (Fs 1)), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
                    collared ℓ 1 angular (Fs 2) p ≠ 0 → G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ y : E, κ =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
                    WKB.firstOrderApply
                      (fun x a ↦ ((coefficient i Q x a).map Complex.ofReal).mulVecLin)
                      (fun x ↦ ((zeroth i B x).map Complex.ofReal).mulVecLin)
                      (fun x ↦ Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
                        (fun k ↦ (W₀ + W₁) (x 0) s (spatialPart x) η k j)) y =
                      Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
                        (fun k ↦ twoTimePhysicalApply (fun x a ↦ (coefficient i Q x a).map Complex.ofReal)
                          (fun x ↦ (zeroth i B x).map Complex.ofReal) W₁
                            (y 0) s (spatialPart y) η k j)) ∧
                  (∀ y : E, κ (y 0) = 1 → ∀ η,
                    (coefficient i Q y 0).map Complex.ofReal * W₀ (y 0) (y 0) (spatialPart y) η =
                      conicSourceSymbol ℓ (FiniteMasks.conicMask angular) σ y η •
                        projector i Q h r c y ((ℓ η)⁻¹ • η)) ∧
                (∀ q : T, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d + 1),
                  (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
                    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                      (fun y k ↦ collared ℓ 1 angular (Fs 1)
                        (physicalSlice e q.2.1 q.2.2.2 y) k j)
                      (e.symm (q.1, q.2.2.1))) ∧
                ∀ j : Fin 3,
                  let f := pencilAmplitudeFamily i Q B h Φ C r c σ j
                  let F := bufferedMatrix V κ f
                  let o := if j = 0 then 0 else 1
                  let W := collared ℓ o angular F
                  ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ V ∧
                  tsupport F ⊆ closedBall (z.1, z) (ρ / 2) ∧ ContDiff ℝ ∞ W ∧
                  tsupport W ⊆ ConicPhase.domain ℓ V ∧
                  (∀ q : T, q.2.1 ≤ z.1 - src → W q = 0) ∧
                  (∀ q ∈ V, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → F =ᶠ[𝓝 q] f) ∧
                  ∀ m,
                    BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ∧
                    twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ≤
                      D m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
                        cNorm (closedBall x RQ) (m + 9) B) := by
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost, hℓ,
    _, _, _, hrest⟩ :=
    exists_uniform_supported_conic_pencilAmplitudes_with_algebraic_data hΩ x hRQ hKΩ A₀ ξ r c hξ hp hreg hm hM
  exact ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost, hℓ, hrest⟩

/-- Construct the SAME uniform chart, fixed compact masks and supported
conic `W₀,W₁,PW₁` from the original coefficients. The normalized symbol
orders are exactly zero, minus one, minus one. All constants and masks
precede `Q`, and the chart precedes `B`; the only high norms in the estimate
are one additive original coefficient budget. The same witnesses also
produce global supported cancellation and the exact leading endpoint.
Source:
`app:ch_regular_base:lem:characteristic-kernel` and `retarded-kernel`. -/
theorem exists_uniform_supported_conic_pencilAmplitudes
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) (ξ : E) (r c : Fin (d + 1))
    (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0)
    (hm : (pencil A₀ ξ).adjugate r c ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ i : Fin (d + 1),
      let e := coordinateSplit i
      let z : Z := ((e x).1, ((e x).2, (e ξ).2))
      ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
        (H : (Fin (d + 1) → Mat) × Euclidean d → ℝ),
        ∃ ε > (0 : ℝ), ∃ L > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
        ∃ ρ > (0 : ℝ), ∃ ρo > ρ, ∃ src > (0 : ℝ), src < a ∧
        ∃ μ > (0 : ℝ), ∃ ν > (0 : ℝ),
        ∃ phaseCost : ℕ → ℝ, (∀ m, 0 < phaseCost m) ∧ ℓ z.2.2 = 1 ∧
        ∃ (σ : Z → ℝ) (κ : ℝ → ℝ),
          ContDiff ℝ ∞ σ ∧ ContDiff ℝ ∞ κ ∧
          (∀ w, σ w ∈ Icc (0 : ℝ) 1) ∧ (∀ t, κ t ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport σ ∧ HasCompactSupport κ ∧
          tsupport σ ⊆ ball z (src / 2) ∧ tsupport κ ⊆ ball z.1 (src / 2) ∧
          closedBall z (src / 4) ⊆ interior {w | σ w = 1} ∧
          closedBall z.1 (src / 4) ⊆ interior {t | κ t = 1} ∧
        ∀ angular : Euclidean d → ℝ, ContDiff ℝ ∞ angular →
          (∀ η ∈ tsupport angular, 0 < ℓ η) →
          ∀ ra > (0 : ℝ), ∀ rb : ℝ,
          ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
          ∀ Q : E → Fin (d + 1) → Mat,
            ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
            cNorm (closedBall x RQ) 10 Q ≤ M →
            let h := fieldRoot e Q H
            let U := fieldDomain e Ω ℓ z.2.2 ε
            ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph T T,
              ContDiffOn ℝ ∞ h U ∧
              (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
              closedBall z L ⊆ U ∧
              (∀ w ∈ closedBall z L, (rootPencil e Q h w).det = 0 ∧
                μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
                ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
              (C : T → T) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) a ∧
              ContDiffOn ℝ ∞ C.symm C.target ∧ closedBall (z.1, z) b ⊆ C.target ∧
              ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
              (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
              (∀ q ∈ C.target,
                (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
                (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
              (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ U ∧
                (twoTimeState Φ (C.symm q)).1 = q.1) ∧
              (∀ w ∈ ball z a, (w.1, w) ∈ C.target ∧
                C.symm (w.1, w) = (w.1, w) ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
              (∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
              (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
                phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
              ball (z.1, z) ρo ⊆ C.target ∧
              MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2)) ∧
              ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω → cNorm (closedBall x RQ) 9 B ≤ M →
                let V := C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
                  (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))
                let Fs := fun j ↦ bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
                let W₀ := curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0))
                let W₁ := curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
                ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
                  (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
                  (∀ p ∈ tsupport (collared ℓ 0 angular (Fs 0)) ∪
                    tsupport (collared ℓ 1 angular (Fs 1)), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
                    collared ℓ 1 angular (Fs 2) p ≠ 0 → G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
                  (∀ y : E, κ =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
                    WKB.firstOrderApply
                      (fun x a ↦ ((coefficient i Q x a).map Complex.ofReal).mulVecLin)
                      (fun x ↦ ((zeroth i B x).map Complex.ofReal).mulVecLin)
                      (fun x ↦ Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
                        (fun k ↦ (W₀ + W₁) (x 0) s (spatialPart x) η k j)) y =
                      Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
                        (fun k ↦ twoTimePhysicalApply (fun x a ↦ (coefficient i Q x a).map Complex.ofReal)
                          (fun x ↦ (zeroth i B x).map Complex.ofReal) W₁
                            (y 0) s (spatialPart y) η k j)) ∧
                  (∀ y : E, κ (y 0) = 1 → ∀ η,
                    (coefficient i Q y 0).map Complex.ofReal * W₀ (y 0) (y 0) (spatialPart y) η =
                      conicSourceSymbol ℓ (FiniteMasks.conicMask angular) σ y η •
                        projector i Q h r c y ((ℓ η)⁻¹ • η)) ∧
                (∀ q : T, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d + 1),
                  (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
                    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                      (fun y k ↦ collared ℓ 1 angular (Fs 1)
                        (physicalSlice e q.2.1 q.2.2.2 y) k j)
                      (e.symm (q.1, q.2.2.1))) ∧
                ∀ j : Fin 3,
                  let f := pencilAmplitudeFamily i Q B h Φ C r c σ j
                  let F := bufferedMatrix V κ f
                  let o := if j = 0 then 0 else 1
                  let W := collared ℓ o angular F
                  ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ V ∧
                  tsupport F ⊆ closedBall (z.1, z) (ρ / 2) ∧ ContDiff ℝ ∞ W ∧
                  tsupport W ⊆ ConicPhase.domain ℓ V ∧
                  (∀ q : T, q.2.1 ≤ z.1 - src → W q = 0) ∧
                  (∀ q ∈ V, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → F =ᶠ[𝓝 q] f) ∧
                  ∀ m,
                    BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ∧
                    twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                      (curryCharacteristicMatrix W) ≤
                      D m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
                        cNorm (closedBall x RQ) (m + 9) B) := by
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, _, _, hrest⟩ :=
    exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii hΩ x hRQ hKΩ A₀ ξ r c hξ hp hreg hm hM
  exact ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hrest⟩

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
