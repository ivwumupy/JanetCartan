module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.TransverseBuffers
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.GraphPhaseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.InverseGraphs
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.OuterInverse

/-!
# Sharp bounds for the actual transverse-chart inverse

The SAME current Hamilton phase supplies all primitive estimates in
`app:ch_seed:prop:seed-phase-charts`. Only the inverse geometry already
constructed by `exists_actual_buffered_inverses_below` is an input here.
There is no assumed forward, phase, or inverse high-norm estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ActualComparison
open InverseEstimates

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (n - 1)
local notation "X" => E

/-- Close all primitive inputs of the transverse inverse/epsilon estimate for the
literal current phase, also bounding the forward map and its epsilon derivative.
The inverse is estimated on the entire closure of its fixed target. A radius cap and frame threshold are fixed before the
inverse chart and current frame. The only remaining premises are the already
proved buffered inverse and its normalized gap; the parent construction
instantiates them on the SAME charts (`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_transverse_inverse_phase_bounds {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius) (ηb : E) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (r s e b c : ℝ) (V L : Set E),
        0 < s → 0 < e → s ≤ r → 2 * r ≤ ρ → e ≤ ρ →
        0 < b → IsCompact (closure V) →
        ∀ Q,
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q.1 - fun _ ↦ cubeStress n) < δ →
          BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (transverseParameterSet z₀ s (2 * e))
            (closedBall ηb r) (ball ηb (2 * r)) (closedBall ηb (2 * r)) V L b c
            (ContinuousLinearEquiv.refl ℝ E) →
          ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
            (transverseParameterSet z₀ s (2 * e) ×ˢ ball ηb (2 * r)) →
          (∀ p ∈ transverseParameterSet z₀ s (2 * e), ∀ u ∈ closedBall ηb (2 * r),
            ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) u -
              ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) →
          let f := fun q ↦ transverseChartFamily (current T Q) (spatialCarrier T)
            (transverseParameterReindex q.1) q.2
          let BF := closedBall (((0 : ℝ), ((spectatorCenter z₀, (0 : ℝ), z₀ 0), (0 : E), (0 : E))), ηb) ρ
          let g := fun q ↦ phaseChartInverse
            (transverseChartFamily (current T Q) (spatialCarrier T)) (ball ηb (2 * r))
            ((transverseParameterReindex (n := n)) q.1) q.2
          ∀ m, (cNorm BF m f + cNorm BF m
            (fun q ↦ deriv (fun ε ↦ f ((ε,q.1.2),q.2)) q.1.1)) + (cNorm (transversePrimitiveBox z₀ (s / 2) e ×ˢ closure V) m g +
            cNorm (transversePrimitiveBox z₀ (s / 2) e ×ˢ closure V) m
              (fun q ↦ deriv (fun ε ↦ g ((ε,q.1.2),q.2)) q.1.1)) ≤
            A m * (1 + cNorm (closedBall (0, covectorCenter T) T.family.radius)
              (m + 3) (current T Q)) := by
  obtain ⟨e₀, he₀, σ, hσ, ρ, hρ, hb, ha, hp, hd, hmap, hseg, hcoord,
    hproj, hz, hv, hshift, hphys, hS⟩ := exists_transverse_primitive_buffers T hP hz₀ ηb
  let p₀ := ((spectatorCenter z₀, (0 : ℝ), z₀ 0), ηb)
  let z := fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ spatialCarrier T (p.1.1,p.1.2.2)
  let v := fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ p.2
  let KF := closedBall ((p₀,(0 : X)),z p₀) σ
  let JF := closedBall p₀ ρ
  obtain ⟨δ, hδ, N, hN, M, hM, _, _, hzM, hvM, hlow⟩ :=
    exists_primitive_low_bounds T ∅ KF ∅ JF (by simp [MapsTo]) hproj
  have hI : (0 : ℝ) ∈ Ioo (-e₀) e₀ := ⟨by linarith, he₀⟩
  have hunit : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  choose B hB hbound using fun m ↦ exists_carrierQuotient_inverse_epsilon_oneHigh_on_graph
    ((p₀,(0 : ℝ)),(0 : X)) ((p₀,(0 : X)),z p₀)
    ((p₀,(0 : ℝ)),((0 : X),(0 : X)))
    (((0 : ℝ),(p₀.1,(0 : X),(0 : X))),p₀.2)
    hρ hσ hρ hρ (isOpen_transversePrimitiveDomain T ηb) isOpen_Ioo hI
    isOpen_ball isOpen_ball isOpen_ball isOpen_Ioo hunit isOpen_Ioo hunit
    ha hp hb hd hphys hseg hcoord
    (ContinuousLinearMap.id ℝ E) (ContinuousLinearEquiv.refl ℝ E) hM.le hN.le m
  let A := fun m : ℕ ↦ B m * (1 + ((m + 4 : ℝ) * 2 ^ (m + 3)) + cNorm JF (m + 3) z + cNorm JF (m + 3) v)
  refine ⟨ρ, hρ, δ, hδ, A, fun m ↦ by
    dsimp [A]; have := hB m; have := cNorm_nonneg JF (m + 3) z
    have := cNorm_nonneg JF (m + 3) v; positivity, ?_⟩
  intro r s e b c V L hs he hsr hrρ heρ hbpos hVc Q hQ hInv hforward hgap f BF g m
  have hext := bufferedInverse_outer_regular _ (isOpen_transverseParameterSet z₀ s (2 * e))
    isOpen_ball ball_subset_closedBall hbpos hforward hInv
  let J := ((transverseParameterReindex (n := n)) ⁻¹' transverseParameterSet (n := n) z₀ s (2 * e)) ×ˢ thickening (b / 2) (closure V)
  let K := transversePrimitiveBox (n := n) z₀ (s / 2) e ×ˢ closure V
  have hJ : IsOpen J := ((isOpen_transverseParameterSet z₀ s (2 * e)).preimage
    (transverseParameterReindex (n := n)).continuous).prod isOpen_thickening
  have hK : IsCompact K :=
    (isCompact_transversePrimitiveBox z₀ (s / 2) e).prod hVc
  have hKJ : K ⊆ J := by
    intro q hq
    refine ⟨?_, hext.1 hq.2⟩
    have hb : (transverseParameterReindex (n := n)) q.1 ∈ transverseParameterBox z₀ (s / 2) e := by
      have hq' : q.1 ∈ transversePrimitiveBox (n := n) z₀ (s / 2) e := hq.1
      rwa [transversePrimitiveBox_eq_preimage] at hq'
    change (transverseParameterReindex (n := n)) q.1 ∈ transverseParameterSet z₀ s (2 * e)
    simpa only [show 2 * (s / 2) = s by ring] using
      (transverseParameterBox_geometry z₀ (by positivity : 0 < s / 2) he).2.2.2 hb
  have hrange := transverse_inverseGraph_mem_ball hs he hsr hrρ heρ (self_subset_cthickening (closure V)) hInv
  have hi : ContDiff ℝ ∞ (fun q : (ℝ × ((Euclidean 2 × ℝ × ℝ) × E × E)) × E ↦
      ((transverseParameterReindex (n := n)) q.1, q.2)) :=
    ((transverseParameterReindex.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  have hg : ContDiffOn ℝ ∞ g J := hext.2.1.comp
    (f := fun q : (ℝ × ((Euclidean 2 × ℝ × ℝ) × E × E)) × E ↦
      ((transverseParameterReindex (n := n)) q.1, q.2)) hi.contDiffOn
    (fun _ hq ↦ hq)
  have hh := hbound m (fun p ξ ↦ current T Q (WithLp.toLp 2 (p.1.1.2.1,p.2),ξ)) z v g J K
    (hS Q) hz hv (hlow Q hQ).2 hzM hvM hshift hmap hJ hK hKJ hg hrange
    (by
      intro q hq
      have hqJ := hKJ hq
      have hu := (hext.2.2 _ hqJ.1 q.2 hqJ.2).1
      change ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T)
        ((transverseParameterReindex (n := n)) q.1)) (g q) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2
      exact (hgap _ hqJ.1 (g q) (ball_subset_closedBall hu)).trans (by norm_num))
    (fun q hq ↦ (hext.2.2 _ hq.1 q.2 hq.2).2)
  have hphase := cNorm_transversePhase_le T Q hproj (m + 3)
  have hhigh := cNorm_nonneg (closedBall (0,covectorCenter T) T.family.radius) (m + 3) (current T Q)
  have hz0 := cNorm_nonneg JF (m + 3) z
  have hv0 := cNorm_nonneg JF (m + 3) v
  apply hh.trans
  change B m * (1 + cNorm KF (m + 3) (fun q ↦ current T Q (WithLp.toLp 2 (q.1.1.1.2.1,q.1.2),q.2)) +
    cNorm JF (m + 3) z + cNorm JF (m + 3) v) ≤ _
  dsimp only [A]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hB m).le
  simp only [Nat.cast_add, Nat.cast_ofNat] at hphase
  have hcoef : 0 ≤ (m + 4 : ℝ) * 2 ^ (m + 3) := by positivity
  nlinarith [mul_nonneg hz0 hhigh, mul_nonneg hv0 hhigh]

end JanetCartan.FullPhaseCharts.ActualEstimates
