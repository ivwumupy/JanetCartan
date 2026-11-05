module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.IncidenceDomain

/-!
# Fixed compact ranges and low incidence budgets

The actual family's low continuity and primitive frame closeness imply all
range and `C¹` inputs of `exists_cNorm_incidence_root_le_reserve_six`. Only fixed
coordinate buffer containments occur as geometric hypotheses. The constants
and admissible threshold precede the current frame and all high orders.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ConstructedCarrierJets
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Fixed compact ranges and a joint low budget for the three literal
incidence fields, derived from primitive `C⁶` frame closeness and the same
family's low phase continuity (`app:ch_seed:prop:seed-actual-menu`, Step 3).
The output directly supplies the low inputs to the reserve-six root estimate;
there is no assumed dynamic range or low carrier bound. -/
theorem exists_incidence_low_budgets {c C : ℝ} (hP : P.IsValid c C)
    (a : (Euclidean n × Euclidean n) × ℝ) (ρ : ℝ) (z : Euclidean 3)
    {Kx : Set (Euclidean n)} {Kz : Set (Euclidean 3)}
    (hKx : IsCompact Kx) (hKz : IsCompact Kz)
    (hKxO : Kx ⊆ ball (0 : Euclidean n) T.physicalRadius)
    (hKzO : Kz ⊆ parameterInterior (2 * P.radius))
    (hKxframe : Kx ⊆ closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
    (hballU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hx : closedBall a.1.1 ρ ⊆ Kx)
    (hz : ∀ t ∈ Icc (a.2 - ρ) (a.2 + ρ), incidenceParameter z t ∈ Kz) :
    ∃ δ L : ℝ, ∃ TQ : Set (Fin n → MetricTensor n), ∃ Tξ Tk : Set (Euclidean n),
      0 < δ ∧ δ ≤ T.family.threshold ∧ 0 ≤ L ∧
      IsCompact TQ ∧ IsCompact Tξ ∧ IsCompact Tk ∧
      closedBall a ρ ⊆ T.incidenceDomain z ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        MapsTo (fun p ↦ Q.1 p.1.1) (closedBall a ρ) TQ ∧
        MapsTo (fun p ↦ T.carrierGradient Q p.1.1 (incidenceParameter z p.2))
          (closedBall a ρ) Tξ ∧
        MapsTo (fun p ↦ p.1.2) (closedBall a ρ) Tk ∧
        cNorm (closedBall a ρ) 1 (fun p ↦ Q.1 p.1.1) +
          cNorm (closedBall a ρ) 1
            (fun p ↦ T.carrierGradient Q p.1.1 (incidenceParameter z p.2)) +
          cNorm (closedBall a ρ) 1 (fun p ↦ p.1.2) ≤ L := by
  obtain ⟨A, B, D, hA, hB, hD, hframe, hgrad, hk⟩ :=
    exists_incidence_coordinate_budgets a ρ hKx hKz z hx hz
  obtain ⟨δ, Lξ, hδ, hLξ, hξ⟩ := T.exists_carrierGradient_low_bound
    hP (hKx.prod hKz) (Set.prod_mono hKxO hKzO)
  let MQ := A 1 * (1 + cNorm
    (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1
      (fun _ : Euclidean n ↦ cubeStress n))
  let Mξ := B 1 * Lξ
  have hbase := cNorm_nonneg
    (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1
      (fun _ : Euclidean n ↦ cubeStress n)
  have hMQ : 0 ≤ MQ := mul_nonneg (hA 1).le (by linarith)
  have hMξ : 0 ≤ Mξ := mul_nonneg (hB 1).le hLξ.le
  have hballW := T.closedBall_subset_incidenceDomain z (hKxframe.trans hballU)
    hKxO hKzO hx hz
  refine ⟨min T.family.threshold (min 1 δ), MQ + Mξ + D 1,
    closedBall 0 MQ, closedBall 0 Mξ, closedBall 0 (D 1),
    lt_min T.family.threshold_pos (lt_min zero_lt_one hδ), min_le_left _ _,
    by linarith [hD 1], isCompact_closedBall _ _, isCompact_closedBall _ _,
    isCompact_closedBall _ _, hballW, ?_⟩
  intro Q hQ
  have hQδ : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q.1 - fun _ ↦ cubeStress n) < δ :=
    hQ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hQ1 : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q.1 - fun _ ↦ cubeStress n) < 1 :=
    hQ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hframeAt : ∀ x ∈ Kx, ContDiffAt ℝ ∞ Q.1 x := fun x hx ↦
    Q.2.1.contDiffAt (hU.mem_nhds (hballU (hKxframe hx)))
  have hgradAt : ∀ q ∈ Kx ×ˢ Kz,
      ContDiffAt ℝ ∞ (fun q ↦ T.carrierGradient Q q.1 q.2) q := fun q hq ↦
    (T.carrierGradient_smooth hP Q).contDiffAt
      ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds ⟨hKxO hq.1, hKzO hq.2⟩)
  have hmono : cNorm Kx 1 Q.1 ≤
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1 Q.1 :=
    cNorm_mono_set_of_contDiffAt hKxframe (isCompact_closedBall _ _)
      (fun x hx ↦ (Q.2.1.contDiffAt (hU.mem_nhds (hballU hx))).of_le (by simp))
  have hbQ : cNorm (closedBall a ρ) 1 (fun p ↦ Q.1 p.1.1) ≤ MQ :=
    (hframe Q.1 hframeAt 1).trans (mul_le_mul_of_nonneg_left
      (hmono.trans (T.frame_low_bound hballU Q hQ1)) (hA 1).le)
  have hbξ : cNorm (closedBall a ρ) 1
      (fun p ↦ T.carrierGradient Q p.1.1 (incidenceParameter z p.2)) ≤ Mξ :=
    (hgrad _ hgradAt 1).trans (mul_le_mul_of_nonneg_left (hξ Q hQδ) (hB 1).le)
  have hs := T.incidence_fields_smooth hP z Q
  have norm_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : (Euclidean n × Euclidean n) × ℝ → E)
      (hf : ContDiffOn ℝ ∞ f (T.incidenceDomain z)) {M : ℝ}
      (hb : cNorm (closedBall a ρ) 1 f ≤ M) : MapsTo f (closedBall a ρ) (closedBall 0 M) := by
    intro p hp
    rw [mem_closedBall, dist_zero_right]
    have hn := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun q hq ↦ (hf.contDiffAt ((T.isOpen_incidenceDomain z).mem_nhds
        (hballW hq))).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hp (by omega : 0 ≤ 1)
    have hn' : ‖f p‖ ≤ cNorm (closedBall a ρ) 1 f := by
      simpa only [norm_iteratedFDeriv_zero] using hn
    exact hn'.trans hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact norm_bound (E := Fin n → MetricTensor n) (M := MQ)
      (fun p ↦ Q.1 p.1.1) hs.1 hbQ
  · exact norm_bound (E := Euclidean n) (M := Mξ)
      (fun p ↦ T.carrierGradient Q p.1.1 (incidenceParameter z p.2)) hs.2.1 hbξ
  · exact norm_bound (E := Euclidean n) (M := D 1) (fun p ↦ p.1.2) hs.2.2 (hk 1)
  · exact add_le_add (add_le_add hbQ hbξ) (hk 1)

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
