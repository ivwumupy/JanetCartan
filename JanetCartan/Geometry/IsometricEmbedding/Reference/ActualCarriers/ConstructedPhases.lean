module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly
public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Bounds

/-!
# Constructed carrier phases on one fixed physical buffer

This instantiates the Hamilton producer in Steps 1–2 of
`app:ch_seed:prop:seed-actual-menu`. The phase is always the restriction of the
same quantitative chart; its full-phase tame bounds remain available. A positive
comparison tolerance is chosen first, then an actual positive frame threshold.
No linear modulus in the frame distance is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu CurrentFullPhase

/-- Assemble a supplied, already constructed chart, preserving its identity.
This pointwise form of finite phase assembly is used to retain the quantitative
family's sharp bounds (`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem CarrierFullPhaseInput.isAssembled {n : ℕ} {P : Patch n}
    {c C : ℝ} (hP : P.IsValid c C) {R : CarrierPhaseReference P}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q U)
    {ε r K : ℝ} (I : CarrierFullPhaseInput R (normalizedHomogeneousSymbol hU Q hQ) ε)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : 0 < r) (hradius : 3 * r < R.radius)
    (hK : 1 ≤ K)
    (hderiv : ∀ z ∈ parameterCube P.radius,
      ‖fderiv ℝ R.spatialPatch z‖ ≤ K ∧ ‖fderiv ℝ P.toFun z‖ ≤ K) :
    IsAssembledCarrierPhase R I Q (carrierPhase I.chart R.spatialPatch) r K ε := by
  have hphysical : closedBall (0 : Euclidean n) (2 * r) ⊆ ball 0 R.radius :=
    closedBall_subset_ball (by linarith)
  have hparam := parameterCube_subset_doubledInterior hP.1
  have htarget (x : Euclidean n) (hx : x ∈ ball 0 R.radius)
      (z : Euclidean 3) (hz : z ∈ parameterInterior (2 * P.radius)) :
      (x, (0, R.spatialPatch z)) ∈ I.chart.target := by
    rw [I.target_eq]
    exact R.target_contains x hx z hz
  have hcomparison (x : Euclidean n) (hx : x ∈ closedBall 0 (2 * r))
      (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
      ‖gradient (fun y ↦ carrierPhase I.chart R.spatialPatch y z) x - P.toFun z‖ ≤ K * ε ∧
      ‖fderiv ℝ (fun w ↦ gradient (fun y ↦ carrierPhase I.chart R.spatialPatch y w) x) z -
        fderiv ℝ P.toFun z‖ ≤ K * ε := by
    have hc := I.carrier_comparison hε hP (hphysical hx) hz
    exact ⟨hc.1.trans (by nlinarith), hc.2.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hderiv z hz).1 hε)⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx z hz ↦ (hcomparison x hx z hz).1,
    fun x hx z hz ↦ (hcomparison x hx z hz).2, ?_⟩
  · exact contDiffOn_carrierPhase I.chart I.coordinates_smooth (R.spatialPatch_smooth hP)
      (fun x hx z hz ↦ htarget x (ball_subset_ball hradius.le hx) z hz)
  · exact contDiffOn_carrierGradient I.chart I.momentum_smooth I.coordinates_smooth
      (R.spatialPatch_smooth hP)
      (fun x hx z hz ↦ htarget x (ball_subset_ball hradius.le hx) z hz)
  · intro u hu z hz
    exact I.carrier_section (hphysical hu) (hparam hz)
  · intro x hx z hz
    exact carrierPhase_normalizedSymbol_determinant_eq_zero hU Q hQ I.chart R.spatialPatch
      (htarget x (hphysical hx) z (hparam hz))
  · intro x hx z hz w hw
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := parameterCube _)
      (fun v hv ↦ ?_) (fun v hv ↦ ?_) (convex_parameterCube _) hw hz
    · have hd := ((R.spatialPatch_smooth hP).contDiffAt
        ((isOpen_parameterInterior _).mem_nhds (hparam hv))).differentiableAt (by simp)
      exact (hasFDerivAt_carrierGradient_parameter I.chart I.momentum_smooth
        I.coordinates_smooth hd (htarget x (hphysical hx) v (hparam hv))).differentiableAt
    · have hh := (hcomparison x hx v hv).2
      have hb := (hderiv v hv).2
      have hn := norm_le_norm_sub_add
        (fderiv ℝ (fun w ↦ gradient (fun y ↦ carrierPhase I.chart R.spatialPatch y w) x) v)
        (fderiv ℝ P.toFun v)
      nlinarith

/-- The assembled phase satisfies the actual projected chord lower bound;
the error retains the length of arbitrarily short chords
(`app:ch_seed:eq:seed-actual-chord`). -/
theorem IsAssembledCarrierPhase.projected_chord {n : ℕ} {P : Patch n}
    {c C : ℝ} (hP : P.IsValid c C) {R : CarrierPhaseReference P}
    {H : HomogeneousSymbol (Euclidean n)} {bound : ℝ} {I : CarrierFullPhaseInput R H bound}
    {Q : Euclidean n → Fin n → MetricTensor n} {Θ : Euclidean n → Euclidean 3 → ℝ}
    {r K ε : ℝ} (h : IsAssembledCarrierPhase R I Q Θ r K ε) (hr : 0 < r)
    {x : Euclidean n} (hx : x ∈ closedBall 0 (2 * r))
    {z w : Euclidean 3} (hz : z ∈ parameterCube P.radius)
    (hw : w ∈ parameterCube P.radius) {L : Submodule ℝ (Euclidean n)}
    (hL : L ∈ cubeBadSubspaces n) :
    (c - K * ε) * ‖z - w‖ ≤
      ‖Lᗮ.orthogonalProjectionOnto
        (gradient (fun y ↦ Θ y z) x - gradient (fun y ↦ Θ y w) x)‖ := by
  have hp := parameterCube_subset_doubledInterior hP.1
  have hx' : x ∈ ball (0 : Euclidean n) (3 * r) :=
    closedBall_subset_ball (by linarith : 2 * r < 3 * r) hx
  have hg (v : Euclidean 3) (hv : v ∈ parameterCube P.radius) :
      DifferentiableAt ℝ (fun w ↦ gradient (fun y ↦ Θ y w) x) v := by
    have hopen : IsOpen (ball (0 : Euclidean n) (3 * r) ×ˢ
        parameterInterior (2 * P.radius)) := isOpen_ball.prod (isOpen_parameterInterior _)
    have hjoint : ContDiffAt ℝ ∞
        (fun q : Euclidean n × Euclidean 3 ↦ gradient (fun y ↦ Θ y q.2) q.1) (x, v) :=
      h.gradient_smooth.contDiffAt (hopen.mem_nhds ⟨hx', hp hv⟩)
    have hpair : ContDiffAt ℝ ∞ (fun w : Euclidean 3 ↦ (x, w)) v :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (hjoint.comp v hpair).differentiableAt (by simp)
  exact (SignedPairs.projected_chord_stability (convex_parameterCube P.radius)
    Lᗮ.orthogonalProjectionOnto (fun v ↦ Lᗮ.norm_orthogonalProjectionOnto_apply_le v)
    (f := P.toFun) (g := fun w ↦ gradient (fun y ↦ Θ y w) x)
    (f' := fderiv ℝ P.toFun)
    (g' := fderiv ℝ (fun w ↦ gradient (fun y ↦ Θ y w) x))
    (fun v hv ↦ ((hP.2.2.2.1.contDiffAt
      ((isOpen_parameterInterior _).mem_nhds (hp hv))).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (fun v hv ↦ (hg v hv).hasFDerivAt.hasFDerivWithinAt)
    (fun v hv ↦ h.parameter_comparison x hx v hv)
    (fun v hv u hu ↦ (hP.2.2.2.2.2 v hv u hu).1 L hL)
    (fun v hv u hu ↦ (hP.2.2.2.2.2 v hv u hu).2.1) hz hw).1

namespace CurrentFullPhase.PatchQuantitativeFamily
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The literal carrier attached to the already selected current full chart
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
def carrier (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) : Euclidean n → Euclidean 3 → ℝ :=
  carrierPhase (T.currentChart Q) T.reference.spatialPatch

/-- The literal physical gradient of the constructed carrier. This definition
is shared by signed-pair, incidence and tame estimates
(`app:ch_seed:prop:seed-actual-menu`, Steps 2–3). -/
def carrierGradient (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x : Euclidean n) (z : Euclidean 3) : Euclidean n :=
  gradient (fun y ↦ T.carrier Q y z) x

end CurrentFullPhase.PatchQuantitativeFamily

private theorem carrierPhase_eq_of_chart_heq {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)}
    {Φ Ψ : HamiltonFlow H (Euclidean (n - 1))}
    (A : ProjectionChart Φ) (B : ProjectionChart Ψ)
    (hflow : Φ = Ψ) (hchart : HEq A B) (ζ : Euclidean 3 → Euclidean (n - 1)) :
    carrierPhase A ζ = carrierPhase B ζ := by
  subst Ψ
  cases eq_of_heq hchart
  rfl

/-- Construct all carrier phases from primitive smooth-frame closeness on one
fixed compact construction ball. Every input to phase assembly is discharged.
The exact chart identities preserve the full-phase continuity and sharp tame
bounds of the producer. The fixed physical buffer and upper constants precede
the comparison tolerance and the frame. The projected lower chord bound is
uniform and includes arbitrarily short chords
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2).

This proves the phase and chord part, not yet the signed angular, incidence-root
or detection conclusions of the full proposition. -/
theorem exists_constructed_carrier_phases {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {b : ℝ} (hb : 0 < b)
    (hBU : closedBall (0 : Euclidean n) b ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain, q.1 ∈ ball (0 : Euclidean n) b) ∧
        ∃ r K εmax : ℝ, 0 < r ∧ 3 * r < min b 1 ∧ 1 ≤ K ∧ 0 < εmax ∧
          εmax ≤ 1 ∧ K * εmax ≤ c / 2 ∧
          (∀ i, 3 * r < (T i).reference.radius) ∧
          ∀ ε, 0 < ε → ε ≤ εmax → ∃ δ > (0 : ℝ),
          ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
            (∀ j, cNorm (closedBall (0 : Euclidean n) b) 6
              (fun x ↦ Q x j - cubeStress n j) < δ) →
            ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
                (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) <
                  (T i).family.threshold,
              ∀ i, ∃ I : CarrierFullPhaseInput (T i).reference
                  (normalizedHomogeneousSymbol hU Q hQ) ε,
                I.flow = (T i).family.flow ⟨Q, hQ, hlow i⟩ ∧
                HEq I.chart ((T i).currentChart ⟨Q, hQ, hlow i⟩) ∧
                IsAssembledCarrierPhase (T i).reference I Q
                  ((T i).carrier ⟨Q, hQ, hlow i⟩) r K ε ∧
                (∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
                  ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
                  ∀ w ∈ parameterCube (D.patches i.1 i.2).radius,
                  ∀ L ∈ cubeBadSubspaces n,
                    (c / 2) * ‖z - w‖ ≤ ‖Lᗮ.orthogonalProjectionOnto
                      ((T i).carrierGradient ⟨Q, hQ, hlow i⟩ x z -
                        (T i).carrierGradient ⟨Q, hQ, hlow i⟩ x w)‖) := by
  classical
  obtain ⟨D, c, C, hD, T, hphysical, hproduce⟩ :=
    exists_finite_current_fullPhaseInputs hn hU hb (ball_subset_closedBall.trans hBU)
  let J := (j : Fin D.chartCount) × Fin (D.patchCount j)
  have hP (i : J) := (hD.2.2.2.2.1 i.1 i.2).1
  choose L hL hderiv using fun i : J ↦ (T i).reference.exists_patch_derivative_bound (hP i)
  obtain ⟨r, _d, K₀, hr, hr1, _hd, hK₀, hcommon⟩ := exists_common_phase_buffers
    (fun i : J ↦ (T i).reference.radius) (fun _ ↦ (1 : ℝ)) L
    (fun i ↦ (T i).reference.radius_pos) (fun _ ↦ zero_lt_one)
  let r' := min r (b / 4)
  let K := max 1 K₀
  let εmax := min 1 (c / (2 * K))
  have hr' : 0 < r' := lt_min hr (by positivity)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hemax : 0 < εmax := lt_min zero_lt_one (div_pos hD.1 (by positivity))
  have hemax1 : εmax ≤ 1 := min_le_left _ _
  have hemaxc : K * εmax ≤ c / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp
      (show εmax ≤ c / (2 * K) from min_le_right _ _)
    nlinarith
  have hradius (i : J) : 3 * r' < (T i).reference.radius :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 3)).trans_lt
      (hcommon i).1
  refine ⟨D, c, C, hD, T, hphysical, r', K, εmax, hr', ?_, hK, hemax,
    hemax1, hemaxc, hradius, ?_⟩
  · have h₁ : r' ≤ r := min_le_left _ _
    have h₂ : r' ≤ b / 4 := min_le_right _ _
    exact lt_min (by linarith) (by linarith)
  intro ε hε he
  obtain ⟨δ, hδ, hinputs⟩ := hproduce ε hε
  refine ⟨δ, hδ, fun Q hQ hclose ↦ ?_⟩
  have hlocal (i : J) (j : Fin n) :
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (fun x ↦ Q x j - cubeStress n j) < δ := by
    apply lt_of_le_of_lt _ (hclose j)
    apply cNorm_mono_set_of_contDiffAt
      ((frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
        ball_subset_closedBall) (isCompact_closedBall _ _)
    intro x hx
    exact (((contDiffOn_pi.mp hQ j).contDiffAt (hU.mem_nhds (hBU hx))).sub
      contDiffAt_const).of_le (by simp)
  choose hlow I hflow hchart using hinputs Q hQ hlocal
  refine ⟨hlow, fun i ↦ ⟨I i, hflow i, hchart i, ?_⟩⟩
  have hidentity : carrierPhase (I i).chart (T i).reference.spatialPatch =
      (T i).carrier ⟨Q, hQ, hlow i⟩ := by
    exact carrierPhase_eq_of_chart_heq _ _ (hflow i) (hchart i) _
  have hass := (I i).isAssembled (hP i) hU hQ hε.le (he.trans hemax1) hr' (hradius i) hK
    (fun z hz ↦ ⟨((hderiv i z hz).1.trans (hcommon i).2.2).trans (le_max_right _ _),
      ((hderiv i z hz).2.trans (hcommon i).2.2).trans (le_max_right _ _)⟩)
  rw [hidentity] at hass
  refine ⟨hass, ?_⟩
  intro x hx z hz w hw A hA
  have hch := hass.projected_chord (hP i) hr' hx hz hw hA
  apply le_trans _ hch
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hh := (mul_le_mul_of_nonneg_left he hKpos.le).trans hemaxc
  linarith

end JanetCartan.ActualCarriers
