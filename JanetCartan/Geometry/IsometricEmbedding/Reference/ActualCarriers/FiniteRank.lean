module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierRank
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.RootQuantitative.Local

/-! # A common exact-rank threshold for the constructed finite carriers -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open FrozenMenu CurrentFullPhase

/-- Primitive componentwise frame closeness gives a common positive adjugate
gap and exact rank for every selected carrier, on the same physical buffer
(`app:ch_seed:prop:seed-actual-menu`, item 1). -/
theorem exists_constructed_carrier_rank_bound {n : ℕ} (hn : 2 ≤ n)
    {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {r : ℝ} (hr : 0 < r) (hradius : ∀ i, 3 * r < (T i).physicalRadius)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K) :
    ∃ δ a : ℝ, 0 < δ ∧ 0 < a ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
        (∀ j, cNorm K 6 (fun x ↦ Q x j - cubeStress n j) < δ) →
        ∀ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) <
            (T i).family.threshold,
        ∀ i, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
        ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
          a ≤ ‖(pencil (Q x) ((T i).carrierGradient ⟨Q, hQ, hlow i⟩ x z)).adjugate‖ ∧
          (pencil (Q x) ((T i).carrierGradient ⟨Q, hQ, hlow i⟩ x z)).rank = n - 1 := by
  classical
  let I := (j : Fin D.chartCount) × Fin (D.patchCount j)
  choose d a hd ha hb using fun i : I ↦
    (T i).exists_carrier_rank_threshold hn (hD.2.2.2.2.1 i.1 i.2).1 hK hKU (hball i)
  obtain ⟨d₀, hd₀, hd₀i⟩ := Pi.exists_forall_pos_add_lt hd
  obtain ⟨a₀, ha₀, ha₀i⟩ := Pi.exists_forall_pos_add_lt ha
  refine ⟨d₀ / 14, a₀, by positivity, ha₀, ?_⟩
  intro Q hQ hclose hlow i x hx z hz
  have hreg : ∀ y ∈ K, ContDiffAt ℝ 6 (Q - fun _ ↦ cubeStress n) y :=
    fun y hy ↦ ((hQ.contDiffAt (hU.mem_nhds (hKU hy))).sub contDiffAt_const).of_le (by simp)
  have hglobal : cNorm K 6 (Q - fun _ ↦ cubeStress n) < d₀ := by
    apply frame_cNorm_lt_of_componentwise hK hreg hd₀
    convert hclose using 1; norm_num
  have hxT : x ∈ ball (0 : Euclidean n) (T i).physicalRadius :=
    closedBall_subset_ball (by linarith [hradius i]) hx
  have hxK := hball i ((T i).physicalBall_subset_frameBall (hD.2.2.2.2.1 i.1 i.2).1 hxT)
  have hh := hb i ⟨Q, hQ, hlow i⟩ (hglobal.trans (by simpa using hd₀i i)) x hxT hxK z hz
  exact ⟨(show a₀ ≤ a i by simpa using (ha₀i i).le).trans hh.1, hh.2⟩

end JanetCartan.ActualCarriers
