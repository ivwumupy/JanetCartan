module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ProtectionCertificates.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.Buffers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.RootGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.KernelIdentities

/-!
# Literal characteristic amplitudes from the original coefficient family

Apply the uniform root/flow producer and the primitive amplitude producer to
one and the same chart. All root, flow, inverse, image and gap hypotheses of
the latter are discharged. The only varying analytic inputs are the original
physical coefficients and the fixed source mask. The reserve is ten in `Q`
(nine for the amplitudes and one for the Hamilton geometry).

Consumer: conic continuation and the actual `W₀,W₁,PW₁` symbol budgets of
`EvolutionIntegral`, for `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
This is the local family construction, not the integrated sector theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open ActualCarriers AmplitudeBounds RootFamily UniformGeometry
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- Retain the global normalized speed and state bounds for the finite protection
export (`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`).
Retain the actual evolution witnesses through the literal amplitude construction.
The positive common time, root constants and original radius comparisons precede
all masks and coefficient fields. On the SAME `h`, `Φ` and `C`, retain the
smooth flow, initial condition, entire inverse time segments and original compact
jet bounds (reserve zero for the root, one for the flow and inverse).

Consumers: the conic constructor below, then
`ResponseTransfer.RetainedFactors.exists_retained_conic_critical_geometry` and
`CompatibleResponse.elapsedModulatedPhase_critical_value`. Sources:
`app:ch_response:eq:response-exact-phase`, `app:ch_response:eq:direct-envelope-profile`
and `paper-v2.tex`, `app:ch_regular_base:lem:retarded-kernel`.
Every algebraic, amplitude, cancellation and retarded-radius conclusion is retained. -/
theorem exists_uniform_pencilAmplitudes_with_protection_certificates
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
        ∃ evolutionTime > (0 : ℝ), ∃ speedGap > (0 : ℝ), ∃ rootSize > (0 : ℝ),
        2 * a ≤ L / 4 ∧ 2 * a ≤ evolutionTime / 4 ∧
        closedBall (z.1, z) (2 * a) ⊆ twoTimeDomain z (L / 2) evolutionTime ∧
        ℓ z.2.2 = 1 ∧
        AlgebraicChart.RootBuffer i r c A₀ ξ H ε L μ ν ∧
        a < L ∧ MapsTo (rootPhysicalPosition e) (closedBall z L) (closedBall x RQ) ∧
        (∀ w ∈ closedBall z L,
          w ∈ fieldDomain e Ω ℓ z.2.2 ε ∧
          rootPhysicalPosition e w ∈ closedBall x RQ ∧
          w.2.2 ∈ closedBall z.2.2 ε ∧ (1 / 2 : ℝ) ≤ ℓ w.2.2) ∧
        ∀ Mmask ≥ (0 : ℝ), ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
          ∀ Q : E → Fin (d + 1) → Mat,
            ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
            cNorm (closedBall x RQ) 10 Q ≤ M →
            let h := fieldRoot e Q H
            let U := fieldDomain e Ω ℓ z.2.2 ε
            ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph TP TP,
              RootProtectionBounds Q e h U ℓ speedGap rootSize ∧
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
              ContDiffOn ℝ ∞ h U ∧
              (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
              closedBall z L ⊆ U ∧
              (∀ w ∈ closedBall z L, (rootPencil e Q h w).det = 0 ∧
                μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
                ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
              (C : TP → TP) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) a ∧
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
              (∀ w ∈ ball z a, Φ (w, 0) = w) ∧
              (∀ (B : E → Mat) (mask : Z → ℝ),
                ContDiffOn ℝ ∞ B Ω → ContDiff ℝ ∞ mask →
                let I := ball z.1 (src / 2)
                let J := ball z.2 (src / 2)
                let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ J))
                (∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c mask j) V ∧
                  ContDiffOn ℝ ∞ (pencilCorrectionColumn e Q B h Φ C r c mask j) V) ∧
                (∀ w ∈ I ×ˢ J, ∀ j, pencilLeadingColumn e Q B h Φ C r c mask j (w.1, w) =
                  (mask w * minorLeftNullvector (rootPencil e Q h w)
                    (rootTimeCoefficient e Q w) r c j) • minorRightNullvector (rootPencil e Q h w) r c) ∧
                ∀ q ∈ V, ∀ j,
                  rootPencil e Q h (twoTimeState Φ (C.symm q)) *ᵥ
                    pencilLeadingColumn e Q B h Φ C r c mask j q = 0 ∧
                  pencilChartLeft e Q h Φ C r c q ⬝ᵥ
                    adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c mask j) q = 0 ∧
                  rootPencil e Q h (twoTimeState Φ (C.symm q)) *ᵥ
                    pencilCorrectionColumn e Q B h Φ C r c mask j q =
                    adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c mask j) q) ∧
              ∀ (B : E → Mat) (mask : Z → ℝ),
                ContDiffOn ℝ ∞ B Ω → ContDiff ℝ ∞ mask →
                cNorm (closedBall x RQ) 9 B ≤ M → cNorm (closedBall z L) 9 mask ≤ Mmask →
                let W₀ := pencilLeadingComplexMatrix e Q B h Φ C r c mask
                let W₁ := pencilCorrectionComplexMatrix e Q B h Φ C r c mask
                let PW₁ := pencilCorrectionResidualComplexMatrix e Q B h Φ C r c mask
                ContDiffOn ℝ ∞ W₀ (ball (z.1, z) ρo) ∧
                ContDiffOn ℝ ∞ W₁ (ball (z.1, z) ρo) ∧
                ContDiffOn ℝ ∞ PW₁ (ball (z.1, z) ρo) ∧
                ∀ m,
                  let high := 1 + cNorm (closedBall x RQ) (m + 10) Q +
                    cNorm (closedBall x RQ) (m + 9) B + cNorm (closedBall z L) (m + 9) mask
                  cNorm (closedBall (z.1, z) ρ) m W₀ ≤ D m * high ∧
                  cNorm (closedBall (z.1, z) ρ) m W₁ ≤ D m * high ∧
                  cNorm (closedBall (z.1, z) ρ) m PW₁ ≤ D m * high := by
  obtain ⟨i, hgeo⟩ := AlgebraicChart.exists_uniform_fieldRoot_twoTimeHamiltonPhase_with_algebraic_data
    hΩ x hRQ hKΩ A₀ ξ r c hξ hp hreg hm hM
  obtain ⟨ℓ, Uroot, Vroot, H, hgeo⟩ := hgeo
  obtain ⟨ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ, hgeo⟩ := hgeo
  obtain ⟨r₀, hr₀, A, hA, T, hT, a, ha, β, hβ, J, hJ, hgeo⟩ := hgeo
  obtain ⟨haR, haT, hβη, htime, hi, hℓ, hUr, hVr, hbase, hH,
    hrootbuffer, hband, hU, hcentre, hstate, halgebraic, hfields⟩ := hgeo
  let e := coordinateSplit i
  let z : Z := ((e x).1, ((e x).2, (e ξ).2))
  let L := 3 * r₀
  let F := min (3 * r₀ / 4) (T / 4) / 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hFr : F < 3 * r₀ / 4 := by
    have hf := min_le_left (3 * r₀ / 4) (T / 4)
    dsimp [F]; linarith only [hf, hr₀]
  have hFT : F < T / 4 := by
    have hf := min_le_right (3 * r₀ / 4) (T / 4)
    dsimp [F]; linarith only [hf, hT]
  let K := 1 + J 1 * (1 + M) + 2 * (1 + 2 * (A 3 * (1 + M)))
  have hK : 1 ≤ K := by
    have hj := mul_nonneg (hJ 1).le (show 0 ≤ 1 + M by linarith only [hM])
    have har := mul_nonneg (hA 3).le (show 0 ≤ 1 + M by linarith only [hM])
    dsimp [K]
    linarith only [hj, har]
  obtain ⟨S, hS, R, hR, σ, hσ, τ, hτ, ρ, hρ, ρo, hρo,
    hσR, hτS, hρoS, hRa, hRF, hSb, hbuffers⟩ :=
    exists_common_amplitude_chart_buffers z ha (lt_min (by positivity : 0 < 2 * β) ha) hF hK
  obtain ⟨src, hsrc, hsrca, hsrchalf, hflowout⟩ :=
    exists_common_amplitude_flowout_radius_le_half z ha (half_pos hρ) hK
  have hSa : 2 * S ≤ a := hSb.trans (min_le_right _ _)
  have hSβ : 2 * S ≤ 2 * β := hSb.trans (min_le_left _ _)
  have hρβ : ρ ≤ 2 * β := by linarith only [hρo, hρoS, hSβ, hS]
  have hsrcρ : src ≤ ρ / 4 := by linarith only [hsrchalf]
  have haL : a < L := by dsimp [L]; linarith only [haR, hr₀]
  have hSL : S ≤ L := by linarith only [hSa, haL, hS]
  have hrootPhys : MapsTo (rootPhysicalPosition e) (closedBall z L) (closedBall x RQ) :=
    fun w hw ↦ (hstate w hw).2.1
  have hphysicalPhys : MapsTo (PhysicalAction.physicalPosition e)
      (closedBall (z.1, z) S) (closedBall x RQ) :=
    physicalPosition_mapsTo_of_rootPhysicalPosition e z hL.le hSL hrootPhys
  have hμ' : 0 < (1 / 2 : ℝ) ^ d * μ := mul_pos (by positivity) hμ
  have hν' : 0 < (1 / 2 : ℝ) ^ (2 * d) * ν := mul_pos (by positivity) hν
  refine ⟨i, ℓ, H, ε, hε, L, hL, a, ha, 2 * β, by positivity,
    ρ, hρ, ρo, hρo, src, hsrc, hsrca, hρβ, hsrcρ, (1 / 2 : ℝ) ^ d * μ, hμ',
    (1 / 2 : ℝ) ^ (2 * d) * ν, hν', J, hJ, A, hA, T, hT, κ, hκ, G, hG, haR, haT, htime, hℓ, halgebraic, haL, hrootPhys, hstate, ?_⟩
  intro Mmask hMmask
  let Mprim := 1 + M + Mmask + A 9 * (1 + M) + 2 * J 9 * (1 + M)
  have hMprim : 0 ≤ Mprim := by
    have ha9 := hA 9
    have hj9 := hJ 9
    dsimp [Mprim]
    positivity
  obtain ⟨D, hD, hlocal⟩ := exists_pencilPrimitiveAmplitudes_cNorm_bounds e z.1 z.2 z.2 x
    hρ hσ hτ hρo hσR hτS hρoS (hRa.trans haL) hRF hRQ hMprim r c hμ' hν'
    hrootPhys hphysicalPhys
  let Cbudget := fun m ↦ 1 + A (m + 9) + 2 * J (m + 9)
  have hCb m : 0 < Cbudget m := by
    have ham := hA (m + 9)
    have hjm := hJ (m + 9)
    dsimp [Cbudget]
    positivity
  refine ⟨fun m ↦ D m * Cbudget m, fun m ↦ mul_pos (hD m) (hCb m), ?_⟩
  intro Q hQ hQrange hQM h U
  have hQM3 : cNorm (closedBall x RQ) 3 Q ≤ M :=
    (cNorm_mono_order (by omega : 3 ≤ 10)).trans hQM
  obtain ⟨hh, hhom, hrootnorm, hrootlow, hgraded, hgaps, hroot, hflow⟩ :=
    hfields Q hQ hQrange hQM3
  obtain ⟨Φ, C, hflow⟩ := hflow
  obtain ⟨hΦ, hs, hproj, hC, hsource, hsourceD, hCs, hCis, hbuffer, hflow⟩ := hflow
  obtain ⟨hderiv, hsegment, hcoords, hinverseSegment, hdiag, hphase, hdiff,
    hgap, hlip, hmixed, hbudget⟩ := hflow
  have hcentreDiag := hdiag z (mem_ball_self ha)
  have hCicentre : C.symm (z.1, z) = (z.1, z) := hcentreDiag.2.2.2.2.1
  have hQlow (k : ℕ) (hk : k ≤ 10) : cNorm (closedBall x RQ) k Q ≤ M :=
    (cNorm_mono_order hk).trans hQM
  have hprojnorm (m : ℕ) : cNorm (closedBall (z.1, z) a) m (twoTimeProjection Φ) ≤
      J m * (1 + cNorm (closedBall x RQ) (m + 1) Q) := by
    have hb := hbudget m
    have h₁ := cNorm_nonneg (closedBall z (3 * r₀ / 4) ×ˢ Icc (-T / 4) (T / 4)) m Φ
    have h₂ := cNorm_nonneg (closedBall (z.1, z) a) m (twoTimeState Φ)
    have h₃ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) m C.symm
    have h₄ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) m (twoTimePhase C)
    linarith only [hb, h₁, h₂, h₃, h₄]
  have hforward (q : TP) (hq : q ∈ ball (z.1, z) a) :
      ‖C q - (z.1, z)‖ ≤ K * ‖q - (z.1, z)‖ := by
    rw [hC]
    apply (projection_displacement_le_cNorm z ha (isOpen_twoTimeDomain _ _ _)
      ((closedBall_subset_closedBall (by linarith only [ha] : a ≤ 2 * a)).trans htime)
      hproj hcentreDiag.2.2.2.1 (hprojnorm 1) (ball_subset_closedBall hq)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hqm := hQlow 2 (by omega)
    have hj := hJ 1
    have ha3 := hA 3
    dsimp [K]
    nlinarith only [hqm, hj, ha3, hM, mul_nonneg ha3.le (by positivity : 0 ≤ 1 + M)]
  have hinverse (q : TP) (hq : q ∈ C.target) :
      ‖C.symm q - (z.1, z)‖ ≤ K * ‖q - (z.1, z)‖ := by
    have hh := hlip q hq (z.1, z) hcentreDiag.2.1
    rw [hCicentre] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    dsimp [K]
    have := mul_nonneg (hJ 1).le (by positivity : 0 ≤ 1 + M)
    linarith only [this]
  obtain ⟨hforwardK, hforwardOpen, hinverseK, hinverseOpen, htargetS,
    hflowK, hflowOpen⟩ := hbuffers C hsource
      ((closedBall_subset_closedBall (min_le_left _ _)).trans hbuffer) hforward hinverse
  let V := ball (z.1, z) (2 * S)
  let W := ball z ((3 * r₀) / 2) ×ˢ Ioo (-T) T
  have hV : IsOpen V := isOpen_ball
  have hW : IsOpen W := isOpen_ball.prod isOpen_Ioo
  have hCV : V ⊆ C.target := ball_subset_closedBall.trans htargetS
  have hKC : closedBall (z.1, z) S ⊆ V := closedBall_subset_ball (by linarith only [hS])
  have hFU : closedBall (z, (0 : ℝ)) F ⊆ W := by
    intro q hq
    have h : ‖q.1 - z‖ ≤ F ∧ ‖q.2‖ ≤ F := by
      simpa only [mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
        Prod.snd_sub, sub_zero, max_le_iff] using hq
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]; linarith only [h.1, hFr, hr₀]
    · have := abs_le.mp (show |q.2| ≤ F from h.2)
      constructor <;> linarith only [this.1, this.2, hFT, hT]
  have hFK : closedBall (z, (0 : ℝ)) F ⊆
      closedBall z ((3 * r₀) / 4) ×ˢ Icc (-T / 4) (T / 4) := by
    intro q hq
    have h : ‖q.1 - z‖ ≤ F ∧ ‖q.2‖ ≤ F := by
      simpa only [mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
        Prod.snd_sub, sub_zero, max_le_iff] using hq
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]; linarith only [h.1, hFr, hr₀]
    · have := abs_le.mp (show |q.2| ≤ F from h.2)
      constructor <;> linarith only [this.1, this.2, hFT, hT]
  have hrectW : closedBall z ((3 * r₀) / 4) ×ˢ Icc (-T / 4) (T / 4) ⊆ W := by
    intro q hq
    exact ⟨(closedBall_subset_ball (by linarith only [hr₀] : 3 * r₀ / 4 < 3 * r₀ / 2)) hq.1,
      ⟨by linarith only [hq.2.1, hT], by linarith only [hq.2.2, hT]⟩⟩
  have hflowV : MapsTo (twoTimeFlowInput ∘ C.symm) V W :=
    fun q hq ↦ hFU (ball_subset_closedBall (hflowOpen hq))
  have hrootU : closedBall z L ⊆ U := fun w hw ↦ (hstate w hw).1
  have hstateK : MapsTo (fun q ↦ twoTimeState Φ (C.symm q))
      (closedBall (z.1, z) S) (closedBall z L) := by
    intro q hq
    have hf := hFU (hflowK hq)
    exact hΦ.range _ (ball_subset_closedBall hf.1) _ (Ioo_subset_Icc_self hf.2)
  have hstateV : MapsTo (fun q ↦ twoTimeState Φ (C.symm q)) V U := by
    intro q hq
    have hf := hflowV hq
    exact hrootU (hΦ.range _ (ball_subset_closedBall hf.1) _ (Ioo_subset_Icc_self hf.2))
  have hphysicalV : MapsTo (PhysicalAction.physicalPosition e) V Ω := by
    intro q hq
    have hqC := hCV hq
    have hi := hinverseSegment q hqC q.1 (right_mem_uIcc ..)
    have hc := hcoords q hqC
    have hzU := hstateV hq
    have ht : (twoTimeState Φ (C.symm q)).1 = q.1 := by
      have he : (q.1, (C.symm q).2) = C.symm q := by rw [← hc.1]
      simpa only [he] using hi.2.2
    change e.symm (q.1, q.2.2.1) ∈ Ω
    change 0 < ℓ (twoTimeState Φ (C.symm q)).2.2 ∧
      e.symm ((twoTimeState Φ (C.symm q)).1, (twoTimeState Φ (C.symm q)).2.1) ∈ Ω ∧ _ at hzU
    simpa only [ht, hc.2.2.2] using hzU.2.1
  have hflowNorm (m : ℕ) : cNorm (closedBall (z, (0 : ℝ)) F) m Φ ≤
      J m * (1 + cNorm (closedBall x RQ) (m + 1) Q) := by
    apply (cNorm_restrict_of_smooth hFK ((isCompact_closedBall _ _).prod isCompact_Icc)
      hW hrectW hΦ.smooth m).trans
    have hb := hbudget m
    have h₁ := cNorm_nonneg (closedBall (z.1, z) a) m (twoTimeState Φ)
    have h₂ := cNorm_nonneg (closedBall (z.1, z) a) m (twoTimeProjection Φ)
    have h₃ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) m C.symm
    have h₄ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) m (twoTimePhase C)
    linarith only [hb, h₁, h₂, h₃, h₄]
  have hinverseNorm (m : ℕ) : cNorm (closedBall (z.1, z) S) m C.symm ≤
      J m * (1 + cNorm (closedBall x RQ) (m + 1) Q) := by
    apply (cNorm_restrict_of_smooth
      (closedBall_subset_closedBall (by linarith only [hSβ, hS] : S ≤ 2 * β))
      (isCompact_closedBall _ _) C.open_target hbuffer hCis m).trans
    have hb := hbudget m
    have h₁ := cNorm_nonneg (closedBall z (3 * r₀ / 4) ×ˢ Icc (-T / 4) (T / 4)) m Φ
    have h₂ := cNorm_nonneg (closedBall (z.1, z) a) m (twoTimeState Φ)
    have h₃ := cNorm_nonneg (closedBall (z.1, z) a) m (twoTimeProjection Φ)
    have h₄ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) m (twoTimePhase C)
    linarith only [hb, h₁, h₂, h₃, h₄]
  have htarget : ball (z.1, z) ρo ⊆ C.target :=
    (ball_subset_ball (by linarith only [hρoS, hS] : ρo ≤ 2 * S)).trans hCV
  have hphaseNorm (m : ℕ) : cNorm (closedBall (z.1, z) (2 * β)) m (twoTimePhase C) ≤
      J m * (1 + cNorm (closedBall x RQ) (m + 1) Q) := by
    have hb := hbudget m
    have h₁ := cNorm_nonneg (closedBall z (3 * r₀ / 4) ×ˢ Icc (-T / 4) (T / 4)) m Φ
    have h₂ := cNorm_nonneg (closedBall (z.1, z) a) m (twoTimeState Φ)
    have h₃ := cNorm_nonneg (closedBall (z.1, z) a) m (twoTimeProjection Φ)
    have h₄ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) m C.symm
    linarith only [hb, h₁, h₂, h₃, h₄]
  have hstateTarget (q : TP) (hq : q ∈ C.target) :
      twoTimeState Φ (C.symm q) ∈ U ∧ (twoTimeState Φ (C.symm q)).1 = q.1 := by
    have hi := hinverseSegment q hq q.1 (right_mem_uIcc ..)
    have he : (q.1, (C.symm q).2) = C.symm q := by rw [← (hcoords q hq).1]
    have hrange : twoTimeState Φ (C.symm q) ∈ closedBall z L := by
      simpa only [he] using hi.2.1
    exact ⟨hrootU hrange, by simpa only [he] using hi.2.2⟩
  have hinverseEvolution (q : TP) (hq : q ∈ C.target) (u : ℝ)
      (hu : u ∈ uIcc q.2.1 q.1) :
      (u, (C.symm q).2) ∈ twoTimeDomain z (L / 2) T ∧
        HasDerivAt (fun t ↦ twoTimeState Φ (t, (C.symm q).2))
          (rootHamiltonField h (twoTimeState Φ (u, (C.symm q).2))) u ∧
        twoTimeState Φ (u, (C.symm q).2) ∈ closedBall z L ∧
        (twoTimeState Φ (u, (C.symm q).2)).1 = u := by
    obtain ⟨hdom, hrange, hclock⟩ := hinverseSegment q hq u hu
    exact ⟨hdom, hderiv _ hdom, hrange, hclock⟩
  have hprotection : RootProtectionBounds Q e h U ℓ κ G := by
    intro w hw
    obtain ⟨hmomentum, hdet, _, _, hspeed, _, hsize, _⟩ := hroot w hw
    refine ⟨hmomentum, hdet, ?_, hspeed, hsize⟩
    rw [rootPencil_time_derivative]
    exact (mul_ne_zero_iff.mp (abs_pos.mp (hκ.trans_le hspeed))).2
  refine ⟨Φ, C, hprotection, hΦ, hsourceD, hs, hproj, hCs, hderiv, hsegment,
    hinverseEvolution, hrootnorm, hrootlow, hgraded, hbudget,
    hh, hhom, hrootU, hgaps, hC, hsource, hCis, hbuffer,
    hphase, hdiff, hcoords, hstateTarget,
    (fun w hw ↦ ⟨(hdiag w hw).2.1, (hdiag w hw).2.2.2.2.1, (hdiag w hw).2.2.2.2.2⟩),
    hmixed, hphaseNorm, htarget, hflowout C hforward, ?_, ?_, ?_⟩
  · intro w hw
    simpa only [twoTimeState, sub_self] using (hdiag w hw).2.2.1
  · intro B mask hB hmask I J Vsmall
    have hsmall : I ×ˢ J ⊆ ball z a := by
      intro w hw
      apply ball_subset_ball (show src / 2 ≤ a by linarith only [hsrca, hsrc])
      simpa only [I, J, mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hw
    have hbox : I ×ˢ (I ×ˢ J) ⊆ C.source := by
      rw [hsource]
      intro q hq
      apply ball_subset_ball (show src / 2 ≤ a by linarith only [hsrca, hsrc])
      simpa only [I, J, mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hq
    have hdet (w : Z) (hw : w ∈ U) : (rootPencil e Q h w).det = 0 := (hroot w hw).2.1
    have hder (w : Z) (hw : w ∈ U) : fderiv ℝ Matrix.det (rootPencil e Q h w)
        (rootTimeCoefficient e Q w) ≠ 0 := by
      obtain ⟨_, _, _, _, hd, _⟩ := hroot w hw
      rw [rootPencil_time_derivative]
      exact (mul_ne_zero_iff.mp (abs_pos.mp (hκ.trans_le hd))).2
    have hminor w (hw : w ∈ U) : (rootPencil e Q h w).adjugate r c ≠ 0 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hmrad, _⟩ := hroot w hw
      apply abs_pos.mp
      exact (mul_pos (pow_pos hw.1 d) hμ).trans_le hmrad
    have hst : ContDiffOn ℝ ∞ (fun q ↦ twoTimeState Φ (C.symm q)) C.target :=
      hs.comp hCis (fun q hq ↦ hsourceD (C.map_target hq))
    have hsmallD : I ×ˢ J ⊆ U := hsmall.trans (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall haL.le).trans hrootU))
    exact pencilColumns_of_retained_rootFlow e hQ hB hU hh (fun _ hw ↦ hw.2.1)
      r c hdet hder hminor hC hCs hCis hst hstateTarget isOpen_ball
      (convex_ball z.1 (src / 2)).ordConnected isOpen_ball hbox hsmallD
      (fun w hw ↦ by simpa only [twoTimeState, sub_self] using (hdiag w (hsmall hw)).2.2.1)
      (fun q hq ↦ by
        have hqD := hsourceD (hbox hq)
        exact hΦ.hasDerivAt (ball_subset_closedBall hqD.1) hqD.2)
      (mem_ball_self (half_pos hsrc)) mask hmask
  intro B mask hB hmask hBM hmM W₀ W₁ PW₁
  have hQM9 := hQlow 9 (by omega)
  have hhn9 := (hrootnorm 9).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hQM9) (hA 9).le)
  have hfn9 := (hflowNorm 9).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hQM) (hJ 9).le)
  have hin9 := (hinverseNorm 9).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hQM) (hJ 9).le)
  have hAr9 := mul_nonneg (hA 9).le (show 0 ≤ 1 + M by linarith only [hM])
  have hJr9 := mul_nonneg (hJ 9).le (show 0 ≤ 1 + M by linarith only [hM])
  have hMbase : M ≤ Mprim := by dsimp [Mprim]; linarith only [hM, hMmask, hAr9, hJr9]
  have hMmaskbase : Mmask ≤ Mprim := by dsimp [Mprim]; linarith only [hM, hMmask, hAr9, hJr9]
  have hMroot : A 9 * (1 + M) ≤ Mprim := by dsimp [Mprim]; linarith only [hM, hMmask, hAr9, hJr9]
  have hMflow : J 9 * (1 + M) ≤ Mprim := by dsimp [Mprim]; linarith only [hM, hMmask, hAr9, hJr9]
  obtain ⟨_hdatum, _hpot, _hrow, hcols, hb⟩ :=
    hlocal Ω U V W hΩ hU hV hW hKΩ hrootU hKC hFU
      (fun _ hw ↦ hw.2.1) hphysicalV Q B h mask Φ C hQ hB hh hmask.contDiffOn
      hΦ.smooth (hCis.mono hCV) hC hflowV hflowK hstateV hstateK
      hforwardK hforwardOpen hinverseK hinverseOpen htarget
      (hQM9.trans hMbase) (hBM.trans hMbase) (hhn9.trans hMroot)
      (hmM.trans hMmaskbase) (hfn9.trans hMflow) (hin9.trans hMflow) hgaps
  refine ⟨contDiffOn_complexColumnMatrix (fun j ↦ (hcols j).1),
    (contDiffOn_complexColumnMatrix (fun j ↦ (hcols j).2.1)).const_smul Complex.I,
    (contDiffOn_complexColumnMatrix (fun j ↦ (hcols j).2.2)).const_smul Complex.I, ?_⟩
  intro m high
  have hnorm : pencilPrimitiveNorm (closedBall x RQ) (closedBall z L)
      (closedBall (z, 0) F) (closedBall (z.1, z) S) Q B h mask Φ C.symm (m + 9) ≤
      Cbudget m * high := by
    have hq : cNorm (closedBall x RQ) (m + 9) Q ≤ cNorm (closedBall x RQ) (m + 10) Q :=
      cNorm_mono_order (by omega)
    have hh' := hrootnorm (m + 9)
    have hf' : cNorm (closedBall (z, 0) F) (m + 9) Φ ≤
        J (m + 9) * (1 + cNorm (closedBall x RQ) (m + 10) Q) := hflowNorm (m + 9)
    have hi' : cNorm (closedBall (z.1, z) S) (m + 9) C.symm ≤
        J (m + 9) * (1 + cNorm (closedBall x RQ) (m + 10) Q) := hinverseNorm (m + 9)
    have ha' := hA (m + 9)
    have hj' := hJ (m + 9)
    have hb0 := cNorm_nonneg (closedBall x RQ) (m + 9) B
    have hm0 := cNorm_nonneg (closedBall z L) (m + 9) mask
    have hq0 := cNorm_nonneg (closedBall x RQ) (m + 10) Q
    have hroot' : cNorm (closedBall z L) (m + 9) h ≤
        A (m + 9) * (1 + cNorm (closedBall x RQ) (m + 10) Q) :=
      hh'.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hq) ha'.le)
    change 1 + cNorm (closedBall x RQ) (m + 9) Q +
        cNorm (closedBall x RQ) (m + 9) B + cNorm (closedBall z L) (m + 9) h +
        cNorm (closedBall z L) (m + 9) mask + cNorm (closedBall (z, 0) F) (m + 9) Φ +
        cNorm (closedBall (z.1, z) S) (m + 9) C.symm ≤
      (1 + A (m + 9) + 2 * J (m + 9)) *
        (1 + cNorm (closedBall x RQ) (m + 10) Q +
          cNorm (closedBall x RQ) (m + 9) B + cNorm (closedBall z L) (m + 9) mask)
    nlinarith only [hq, hf', hi', hroot', hq0, hb0, hm0, mul_nonneg ha'.le hb0, mul_nonneg ha'.le hm0,
      mul_nonneg hj'.le hb0, mul_nonneg hj'.le hm0]
  have hbound := mul_le_mul_of_nonneg_left hnorm (hD m).le
  constructor
  · exact (hb m).2.2.2.2.1.trans (by simpa only [mul_assoc] using hbound)
  constructor
  · exact (hb m).2.2.2.2.2.1.trans (by simpa only [mul_assoc] using hbound)
  · exact (hb m).2.2.2.2.2.2.trans (by simpa only [mul_assoc] using hbound)

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
