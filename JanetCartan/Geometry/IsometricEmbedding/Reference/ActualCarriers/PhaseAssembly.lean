module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Comparison

/-!
# Finite carrier phases on common physical buffers

Steps 1–2 of `app:ch_seed:prop:seed-actual-menu`, conditional on the precise
per-patch full Hamilton inputs in `PhaseAssembly/Inputs`. The finite minima and
maximum are chosen before the current symbol and perturbation size. The carrier
phases are constructed by the literal zero-energy restriction, with the same
section data and sign; no family of already constructed carriers is assumed.

The owners of `jc-actual-carriers` and `jc-compatible-phase-geometry` must supply
`CarrierPhaseReference` from adapted frozen patches, `CarrierFullPhaseInput` from
the uniform Hamilton construction, and the projected-current symbol identity.
Signed pairs, rank/minor persistence, incidence roots, detectors and all-order
tame production remain the responsibilities of their respective owners. There
is no change of initial-data measure in this construction.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Topology
namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu

/-- The output of finite phase assembly on `B_in = ball 0 r` and
`B_out = ball 0 (2*r)`, smooth on the larger `ball 0 (3*r)`.
This is an output predicate, never a construction hypothesis
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
structure IsAssembledCarrierPhase {n : ℕ} {P : Patch n}
    (R : CarrierPhaseReference P) {H : HomogeneousSymbol (Euclidean n)} {bound : ℝ}
    (F : CarrierFullPhaseInput R H bound) (Q : Euclidean n → Fin n → MetricTensor n)
    (Θ : Euclidean n → Euclidean 3 → ℝ) (r K ε : ℝ) : Prop where
  restriction : Θ = carrierPhase F.chart R.spatialPatch
  smooth : ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦ Θ q.1 q.2)
    (ball (0 : Euclidean n) (3 * r) ×ˢ parameterInterior (2 * P.radius))
  gradient_smooth : ContDiffOn ℝ ∞
    (fun q : Euclidean n × Euclidean 3 ↦ gradient (fun y ↦ Θ y q.2) q.1)
    (ball (0 : Euclidean n) (3 * r) ×ˢ parameterInterior (2 * P.radius))
  section_value : ∀ u, R.sectionEmbedding u ∈ closedBall (0 : Euclidean n) (2 * r) →
    ∀ z ∈ parameterCube P.radius, Θ (R.sectionEmbedding u) z = ⟪u, R.spatialPatch z⟫_ℝ
  characteristic : ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
    ∀ z ∈ parameterCube P.radius, determinant (Q x) (gradient (fun y ↦ Θ y z) x) = 0
  gradient_comparison : ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
    ∀ z ∈ parameterCube P.radius, ‖gradient (fun y ↦ Θ y z) x - P.toFun z‖ ≤ K * ε
  parameter_comparison : ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
    ∀ z ∈ parameterCube P.radius,
      ‖fderiv ℝ (fun w ↦ gradient (fun y ↦ Θ y w) x) z - fderiv ℝ P.toFun z‖ ≤ K * ε
  parameter_lipschitz : ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
    ∀ z ∈ parameterCube P.radius, ∀ w ∈ parameterCube P.radius,
      ‖gradient (fun y ↦ Θ y z) x - gradient (fun y ↦ Θ y w) x‖ ≤ 2 * K * ‖z - w‖

/-- Assemble the actual finite frozen menu, including duplicate patches and the
possible empty patch family, on one common physical buffer. The constants are
chosen before `ε`, the current symbols and their Hamilton constructions.

The conditional analytic inputs are exactly the reference full charts, the
per-patch thresholds and full momentum comparison constants, the supplied current
full charts below those thresholds, and the identification of their symbols with
`|ξ|^(1-n) p_F`. In particular this theorem does not produce uniform Hamilton
estimates or assert the unconditional actual-menu proposition.
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2.) -/
theorem exists_finite_carrierPhase_assembly {n : ℕ} (D : CoverData n)
    {c C : ℝ} (hD : D.IsValid c C)
    (R : (a : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      CarrierPhaseReference (D.patches a.1 a.2))
    (threshold coefficient : ((b : Fin D.chartCount) × Fin (D.patchCount b)) → ℝ)
    (hthreshold : ∀ a, 0 < threshold a) (hcoefficient : ∀ a, 0 ≤ coefficient a) :
    ∃ r δ K : ℝ, 0 < r ∧ 3 * r < 1 ∧ 0 < δ ∧ 0 < K ∧ δ ≤ 1 ∧
      (∀ a, 3 * r < (R a).radius ∧ δ ≤ threshold a) ∧
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ δ →
      ∀ (H : ((b : Fin D.chartCount) × Fin (D.patchCount b)) → HomogeneousSymbol (Euclidean n))
        (Q : Euclidean n → Fin n → MetricTensor n),
      (∀ a, ∀ q ∈ (H a).domain,
        (H a).h q = ‖q.2‖ ^ (1 - (n : ℤ)) * determinant (Q q.1) q.2) →
      (∀ a, ∀ q ∈ (H a).domain, q.2 ≠ 0) →
      (∀ a, ε ≤ threshold a → Nonempty (CarrierFullPhaseInput (R a) (H a) (coefficient a * ε))) →
      ∃ (F : ∀ a, CarrierFullPhaseInput (R a) (H a) (coefficient a * ε))
        (Θ : ((b : Fin D.chartCount) × Fin (D.patchCount b)) → Euclidean n → Euclidean 3 → ℝ),
        ∀ a, IsAssembledCarrierPhase (R a) (F a) Q (Θ a) r K ε := by
  classical
  let I := (b : Fin D.chartCount) × Fin (D.patchCount b)
  have hP (a : I) := (hD.2.2.2.2.1 a.1 a.2).1
  choose L hL hderiv using fun a : I ↦ (R a).exists_patch_derivative_bound (hP a)
  obtain ⟨r, δ, K, hr, hr1, hδ, hK, hcommon⟩ := exists_common_phase_buffers
    (fun a ↦ (R a).radius) threshold
    (fun a ↦ max (max (coefficient a) (coefficient a * L a)) (L a))
    (fun a ↦ (R a).radius_pos) hthreshold
  refine ⟨r, min δ 1, K, hr, hr1, lt_min hδ (by norm_num), hK, min_le_right _ _,
    fun a ↦ ⟨(hcommon a).1, (min_le_left _ _).trans (hcommon a).2.1⟩, ?_⟩
  intro ε hε hεδ H Q hsymbol hnonzero hproduce
  have hε1 : ε ≤ 1 := hεδ.trans (min_le_right _ _)
  let F : ∀ a : I, CarrierFullPhaseInput (R a) (H a) (coefficient a * ε) :=
    fun a ↦ Classical.choice (hproduce a (hεδ.trans ((min_le_left _ _).trans (hcommon a).2.1)))
  refine ⟨F, fun a ↦ carrierPhase (F a).chart (R a).spatialPatch, ?_⟩
  intro a
  have hradius : 2 * r < (R a).radius := lt_trans (by linarith) (hcommon a).1
  have hphysical : closedBall (0 : Euclidean n) (2 * r) ⊆ ball 0 (R a).radius :=
    closedBall_subset_ball hradius
  have hparam := parameterCube_subset_doubledInterior (hP a).1
  have hA : coefficient a ≤ K :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (hcommon a).2.2)
  have hAL : coefficient a * L a ≤ K :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (hcommon a).2.2)
  have hLK : L a ≤ K := (le_max_right _ _).trans (hcommon a).2.2
  have htarget (x : Euclidean n) (hx : x ∈ ball 0 (R a).radius)
      (z : Euclidean 3) (hz : z ∈ parameterInterior (2 * (D.patches a.1 a.2).radius)) :
      (x, (0, (R a).spatialPatch z)) ∈ (F a).chart.target := by
    rw [(F a).target_eq]
    exact (R a).target_contains x hx z hz
  have hcomparison (x : Euclidean n) (hx : x ∈ closedBall 0 (2 * r))
      (z : Euclidean 3) (hz : z ∈ parameterCube (D.patches a.1 a.2).radius) :
      ‖gradient (fun y ↦ carrierPhase (F a).chart (R a).spatialPatch y z) x -
        (D.patches a.1 a.2).toFun z‖ ≤ K * ε ∧
      ‖fderiv ℝ (fun w ↦ gradient (fun y ↦ carrierPhase (F a).chart (R a).spatialPatch y w) x) z -
        fderiv ℝ (D.patches a.1 a.2).toFun z‖ ≤ K * ε := by
    have hc := (F a).carrier_comparison (mul_nonneg (hcoefficient a) hε)
      (hP a) (hphysical hx) hz
    refine ⟨hc.1.trans (mul_le_mul_of_nonneg_right hA hε), hc.2.trans ?_⟩
    calc
      _ ≤ (coefficient a * ε) * L a :=
        mul_le_mul_of_nonneg_left (hderiv a z hz).1 (mul_nonneg (hcoefficient a) hε)
      _ = (coefficient a * L a) * ε := by ring
      _ ≤ K * ε := mul_le_mul_of_nonneg_right hAL hε
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx z hz ↦ (hcomparison x hx z hz).1,
    fun x hx z hz ↦ (hcomparison x hx z hz).2, ?_⟩
  · exact contDiffOn_carrierPhase (F a).chart (F a).coordinates_smooth
      ((R a).spatialPatch_smooth (hP a))
      (fun x hx z hz ↦ htarget x (ball_subset_ball (hcommon a).1.le hx) z hz)
  · exact contDiffOn_carrierGradient (F a).chart (F a).momentum_smooth
      (F a).coordinates_smooth ((R a).spatialPatch_smooth (hP a))
      (fun x hx z hz ↦ htarget x (ball_subset_ball (hcommon a).1.le hx) z hz)
  · intro u hu z hz
    exact (F a).carrier_section (hphysical hu) (hparam hz)
  · intro x hx z hz
    exact carrierPhase_determinant_eq_zero (F a).chart (R a).spatialPatch Q
      (hsymbol a) (hnonzero a) (htarget x (hphysical hx) z (hparam hz))
  · intro x hx z hz w hw
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := parameterCube _)
      (fun v hv ↦ ?_) (fun v hv ↦ ?_) (convex_parameterCube _) hw hz
    · have hd := (((R a).spatialPatch_smooth (hP a)).contDiffAt
        ((isOpen_parameterInterior _).mem_nhds (hparam hv))).differentiableAt (by simp)
      exact (hasFDerivAt_carrierGradient_parameter (F a).chart (F a).momentum_smooth
        (F a).coordinates_smooth hd (htarget x (hphysical hx) v (hparam hv))).differentiableAt
    · have hh := (hcomparison x hx v hv).2
      have hb := (hderiv a v hv).2.trans hLK
      have hn := norm_le_norm_sub_add
        (fderiv ℝ (fun w ↦ gradient
          (fun y ↦ carrierPhase (F a).chart (R a).spatialPatch y w) x) v)
        (fderiv ℝ (D.patches a.1 a.2).toFun v)
      nlinarith [mul_le_mul_of_nonneg_left hε1 hK.le]

end JanetCartan.ActualCarriers
