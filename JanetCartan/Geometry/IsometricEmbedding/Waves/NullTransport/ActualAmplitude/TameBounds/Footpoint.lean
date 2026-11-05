module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Cylinder
public import JanetCartan.Analysis.ODE.PositiveTransport.Characteristics

/-!
# The exponential evaluated at the constructed footpoint

This is the second composition in the characteristic formula for
`app:ch_waves:eq:joint-tame`. The input is the coefficient along the forward
flow and the actual inverse footpoint map. The integral and exponential are
constructed, and no estimate for either is an assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame
open FullPhaseCharts.InverseEstimates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The flow factor after footpoint substitution has an additive one-high
estimate on the fixed coordinate image. Its only low inputs are `C¹` of the
coefficient and inverse map (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_factor_footpoint_bounds
    (e : (ℝ × E) ≃L[ℝ] ℝ × E) (a : ℝ × E) (p : E)
    {ρ τ σ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) (hσ : 0 < σ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (U V : Set (ℝ × E)), IsOpen U → IsOpen V →
      e '' closedBall a ρ ⊆ U → Icc (-τ) τ ×ˢ closedBall p σ ⊆ V →
      ∀ (Y : ℝ × E → E) (c : ℝ × E → ℝ),
      ContDiffOn ℝ ∞ Y U → ContDiffOn ℝ ∞ c V →
      MapsTo (fun q ↦ (q.1, Y q)) (e '' closedBall a ρ)
        (Icc (-τ) τ ×ˢ closedBall p σ) →
      cNorm (e '' closedBall a ρ) 1 Y ≤ M →
      cNorm (Icc (-τ) τ ×ˢ closedBall p σ) 1 c ≤ M →
      ∀ j, cNorm (e '' closedBall a ρ) j
          (fun q ↦ transportFactor (fun s ↦ c (s, Y q)) 0 q.1) ≤
        B j * (1 + cNorm (e '' closedBall a ρ) (j + 2) Y +
          cNorm (Icc (-τ) τ ×ˢ closedBall p σ) (j + 2) c) := by
  let K := e '' closedBall a ρ
  let J := Icc (-τ) τ ×ˢ closedBall p σ
  let d := timeDilation (E := E) (τ / σ) (div_pos hτ hσ).ne'
  have hd : d '' closedBall (0, p) σ = J := timeDilation_image_closedBall p hτ hσ
  let T := fun j ↦ cNorm K j (Prod.fst : ℝ × E → ℝ)
  have hT j : 0 ≤ T j := cNorm_nonneg _ _ _
  choose A hA hfactor using fun j ↦ exists_cNorm_transportFactor_le_cylinder p hτ hσ j M
  choose C hC hcomp using fun j ↦ exists_cNorm_comp_le_ballImage (G := ℝ)
    e d a (0, p) hρ hσ j (add_nonneg (hT 1) hM)
      (mul_nonneg (hA 1).le (by linarith : 0 ≤ 1 + M))
  let B := fun j ↦ C j * (1 + T (j + 2) + A (j + 2))
  have hB j : 0 < B j := mul_pos (hC j) (by linarith [hT (j + 2), hA (j + 2)])
  refine ⟨B, hB, ?_⟩
  intro U V hU hV hKU hJV Y c hY hc hm hYlow hclow j
  let Z := fun q : ℝ × E ↦ (q.1, Y q)
  let f := fun q : ℝ × E ↦ transportFactor (fun s ↦ c (s, q.2)) 0 q.1
  have hZ : ContDiffOn ℝ ∞ Z U := contDiffOn_fst.prodMk hY
  have hn (i) : cNorm K i Z ≤ T i + cNorm K i Y :=
    cNorm_prodMk_le_on K ((isCompact_closedBall a ρ).image e.continuous) i
      (fun _ _ ↦ contDiffAt_fst)
      (fun x hx ↦ (hY.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
  obtain ⟨W, hW, hJW, hf⟩ := exists_transportFactor_smooth_near_cylinder p hτ hσ hV hJV hc
  have hfhigh (i) : cNorm J i f ≤ A i * (1 + cNorm J i c) :=
    hfactor i V hV hJV c hc ((cNorm_mono_order (by omega : 0 ≤ 1)).trans hclow)
  have hflow : cNorm J 1 f ≤ A 1 * (1 + M) :=
    (hfhigh 1).trans (mul_le_mul_of_nonneg_left (by linarith) (hA 1).le)
  have hh := hcomp j U W hU hW hKU (hd ▸ hJW) Z f hZ hf
    (hd ▸ hm) ((hn 1).trans (add_le_add le_rfl hYlow)) (hd ▸ hflow)
  rw [hd] at hh
  apply hh.trans
  have hzi := hn (j + 2)
  have hfi := hfhigh (j + 2)
  have hi : 1 + cNorm K (j + 2) Z + cNorm J (j + 2) f ≤
      (1 + T (j + 2) + A (j + 2)) * (1 + cNorm K (j + 2) Y + cNorm J (j + 2) c) := by
    have hy0 := cNorm_nonneg K (j + 2) Y
    have hc0 := cNorm_nonneg J (j + 2) c
    nlinarith [hT (j + 2), hA (j + 2),
      mul_nonneg (hT (j + 2)) hy0, mul_nonneg (hT (j + 2)) hc0,
      mul_nonneg (hA (j + 2)).le hy0]
  exact (mul_le_mul_of_nonneg_left hi (hC j).le).trans_eq (by dsimp [B]; ring)

end JanetCartan.NullTransport.AmplitudeTame
