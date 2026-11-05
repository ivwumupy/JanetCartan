module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.LocalJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.Fourier

/-!
# Sobolev envelopes of the literal primary strain

This is the conditional deduction required by
`app:ch_response:eq:response-graded-source` and
`app:ch_response:cor:current-atoms`. Local joint grades imply the actual
Lebesgue Fourier Sobolev bounds, including all prescribed carrier derivatives
of the SAME output-cutoff extension. Constants precede the amplitude, its
size and scale, the carrier, and the unit directions. The scale is `A*L^p`,
with no extra derivative or reserve loss.

The parent construction must instantiate the local grades using
`RawPrimary.exists_fullPrimaryStrain_grade_on_retained_workingBall` on its
retained family, with reserve `14+(rpar+2) ≤ RF,Rr`. The results here do not
assert that this actual-data instantiation or the negative-norm assembly has
been performed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponsePrimarySources
open ResponseSourceExtension ResponseTransfer.SourceNegative

variable {n : ℕ} {core chart : Set (Euclidean n)}
local notation "E" => Euclidean n
local notation "P" => Euclidean 3 × Euclidean (n - 1)
local notation "Tensor" => Matrix (Fin n) (Fin n) ℂ

/-- The literal cutoff extension satisfies the Fourier envelope profile from
local spatial grades (`app:ch_response:eq:response-graded-source`). This
specialized deduction constructs membership as well as the numerical bound. -/
theorem exists_primary_zeroExtend_sobolev_constants
    (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ C : ℕ → ℝ, (∀ p, 0 ≤ C p) ∧
      ∀ (f : E → Tensor) (A L : ℝ), 0 ≤ A → 1 ≤ L → ContDiffOn ℝ ∞ f chart →
      (∀ x ∈ chart, ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ B j * A * L ^ j) →
      ∃ hf : MemLp (χ.zeroExtend (fun x : chart ↦ f x)) 2 volume,
        SobolevEnvelopeBounds (χ.zeroExtend (fun x : chart ↦ f x)) hf A L C := by
  obtain ⟨J, hJ, hjet⟩ := exists_primary_zeroExtend_jet_constants (F := Tensor) χ hchart B hB
  obtain ⟨C, hC, hsob⟩ := exists_primary_tensor_sobolev_constants χ.compact J hJ
  refine ⟨C, hC, ?_⟩
  intro f A L hA hL hf hb
  have hs := χ.contDiff_zeroExtend_restrict hchart hf
  have hm : MemLp (χ.zeroExtend (fun x : chart ↦ f x)) 2 volume :=
    hs.continuous.memLp_of_hasCompactSupport (χ.hasCompactSupport_zeroExtend _)
  exact ⟨hm, hsob _ hm A L hA hL hs (χ.tsupport_zeroExtend_subset _)
    (hjet f A L hA hL hf hb)⟩

/-- Carrier differentiation commutes with the SAME literal output extension.
The identity is global in space, including outside the validity chart
(`app:ch_response:cor:current-atoms`). -/
theorem primary_zeroExtend_carrier_derivative_eq
    (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set P} (hV : IsOpen V) {a : E × P → Tensor}
    (ha : ContDiffOn ℝ ∞ a (chart ×ˢ V)) (k : ℕ) (v : Fin k → P)
    {c : P} (hc : c ∈ V) :
    (fun x ↦ iteratedFDeriv ℝ k
      (fun d ↦ χ.zeroExtend (fun y : chart ↦ a (y, d)) x) c v) =
      χ.zeroExtend (fun x : chart ↦ iteratedFDeriv ℝ k (fun d ↦ a (x, d)) c v) := by
  have hext (d : P) := χ.zeroExtend_restrict (fun x ↦ a (x, d))
  have hextk := χ.zeroExtend_restrict (fun x ↦ iteratedFDeriv ℝ k (fun d ↦ a (x, d)) c v)
  rw [hextk]
  simp_rw [hext]
  funext x
  by_cases hx : χ.toFun x = 0
  · simp [hx]
  · have hxc : x ∈ chart := χ.support_chart (subset_tsupport _ hx)
    have hs : ContDiffAt ℝ ∞ (fun d ↦ a (x, d)) c :=
      (ha.contDiffAt ((hchart.prod hV).mem_nhds ⟨hxc, hc⟩)).comp c
        (contDiffAt_const.prodMk contDiffAt_id)
    let M : Tensor →L[ℝ] Tensor := χ.toFun x • ContinuousLinearMap.id ℝ Tensor
    have he := M.iteratedFDeriv_comp_left hs (i := k) (by simp)
    exact congrArg (fun t ↦ t v) he

/-- Exact local joint grades imply Fourier envelopes for the original slice
and every prescribed unit-direction carrier derivative. The `k`-th profile
uses `B(j,k)` and has the SAME `A*L^p` power. Consumer:
`app:ch_response:cor:current-atoms`; the retained grade producer and its
actual-data instantiation remain obligations of the parent. -/
theorem exists_primary_joint_sobolev_constants
    (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set P} (hV : IsOpen V) (B : ℕ → ℕ → ℝ)
    (hB : ∀ j k, 0 ≤ B j k) (rpar : ℕ) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k p, 0 ≤ C k p) ∧
      ∀ (a : E × P → Tensor) (A L : ℝ), 0 ≤ A → 1 ≤ L →
      ContDiffOn ℝ ∞ a (chart ×ˢ V) →
      (∀ x ∈ chart, ∀ c ∈ V, ∀ j k, k ≤ rpar →
        ‖iteratedFDeriv ℝ (j + k) a (x, c)‖ ≤ B j k * A * L ^ j) →
      (∀ c ∈ V, ∃ hf : MemLp (χ.zeroExtend (fun x : chart ↦ a (x, c))) 2 volume,
        SobolevEnvelopeBounds (χ.zeroExtend (fun x : chart ↦ a (x, c))) hf A L (C 0)) ∧
      ∀ k ≤ rpar, ∀ v : Fin k → P, (∀ i, ‖v i‖ ≤ 1) → ∀ c ∈ V,
        ∃ hf : MemLp (fun x ↦ iteratedFDeriv ℝ k
          (fun d ↦ χ.zeroExtend (fun y : chart ↦ a (y, d)) x) c v) 2 volume,
        SobolevEnvelopeBounds (fun x ↦ iteratedFDeriv ℝ k
          (fun d ↦ χ.zeroExtend (fun y : chart ↦ a (y, d)) x) c v) hf A L (C k) := by
  choose C hC hsob using fun k ↦ exists_primary_zeroExtend_sobolev_constants
    χ hchart (fun j ↦ B j k) (fun j ↦ hB j k)
  refine ⟨C, hC, ?_⟩
  intro a A L hA hL ha hb
  constructor
  · intro c hc
    apply hsob 0 (fun x ↦ a (x, c)) A L hA hL
      (ha.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ ⟨hx, hc⟩))
    intro x hx j
    exact (norm_iteratedFDeriv_primary_spatialSlice_le hchart hV ha hx hc j).trans
      (by simpa only [Nat.add_zero] using hb x hx c hc j 0 (Nat.zero_le _))
  · intro k hk v hv c hc
    rw [primary_zeroExtend_carrier_derivative_eq χ hchart hV ha k v hc]
    have hj := primary_carrier_derivative_spatial_bounds hchart hV ha k v hv hc
    exact hsob k _ A L hA hL hj.1
      (fun x hx j ↦ (hj.2 x hx j).trans (hb x hx c hc j k hk))

open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- Specialize the no-loss Fourier deduction to the already defined
`fullStrainEnvelope`, with its smoothness supplied by the retained leading
outputs. The joint-grade hypothesis is exactly the output to be instantiated
from `RawPrimary.exists_fullPrimaryStrain_grade_on_retained_workingBall`.
This proves the conditional Sobolev step in
`app:ch_response:cor:current-atoms`, including derivatives of the SAME envelope;
the parent retains actual grade instantiation and negative-norm assembly. -/
theorem exists_fullStrainEnvelope_sobolev_constants
    (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set P} (hV : IsOpen V) (B : ℕ → ℕ → ℝ)
    (hB : ∀ j k, 0 ≤ B j k) (rpar : ℕ) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k p, 0 ≤ C k p) ∧
      ∀ {N : ℕ} {patch : Patch n} {U : Set E} {hU : IsOpen U}
        (T : PatchQuantitativeFamily patch U hU)
        (Q : {Q : E → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (Metric.closedBall (0 : E) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F₀ : E → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × P) → Euclidean (n - 1) × P)
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ A L : ℝ),
        0 ≤ A → 1 ≤ L →
        (∀ w ∈ chart ×ˢ V, w.1 ∈ U) →
        (∀ w ∈ chart ×ˢ V, (w.1, w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F₀ U → IsImmersionOn F₀ U → HasFullNormalRankOn F₀ U →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F₀ row col Φ Y r) (chart ×ˢ V) →
        (∀ w ∈ chart ×ˢ V, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ x ∈ chart, ∀ c ∈ V, ∀ j k, k ≤ rpar →
          ‖iteratedFDeriv ℝ (j + k)
            (fullPrimaryStrainAmplitude T Q F₀ row col Φ Y r τ) (x, c)‖ ≤
              B j k * A * L ^ j) →
        (∀ c ∈ V, ∃ hf : MemLp (fullStrainEnvelope T Q F₀ row col Φ Y r χ τ c) 2 volume,
          SobolevEnvelopeBounds (fullStrainEnvelope T Q F₀ row col Φ Y r χ τ c)
            hf A L (C 0)) ∧
        ∀ k ≤ rpar, ∀ v : Fin k → P, (∀ i, ‖v i‖ ≤ 1) → ∀ c ∈ V,
          ∃ hf : MemLp (fun x ↦ iteratedFDeriv ℝ k
            (fun d ↦ fullStrainEnvelope T Q F₀ row col Φ Y r χ τ d x) c v) 2 volume,
          SobolevEnvelopeBounds (fun x ↦ iteratedFDeriv ℝ k
            (fun d ↦ fullStrainEnvelope T Q F₀ row col Φ Y r χ τ d x) c v) hf A L (C k) := by
  obtain ⟨C, hC, hsob⟩ := exists_primary_joint_sobolev_constants χ hchart hV B hB rpar
  refine ⟨C, hC, ?_⟩
  intro N patch U hU T Q F₀ row col Φ Y r τ A L hA hL hspace hphase hF hi hrank hα hn hb
  exact hsob (fullPrimaryStrainAmplitude T Q F₀ row col Φ Y r τ) A L hA hL
    (contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F₀ row col Φ Y r τ
      (hchart.prod hV) hspace hphase hF hi hrank hα hn) hb

end JanetCartan.ResponsePrimarySources
