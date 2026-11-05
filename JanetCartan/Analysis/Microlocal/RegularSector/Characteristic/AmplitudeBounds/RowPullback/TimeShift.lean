module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.RowBounds

/-!
# Moving the common time center of the literal row

The bounds for `app:ch_regular_base:lem:characteristic-kernel` are transported
by a fixed simultaneous translation of both times. The oriented integral
identity holds without choosing an ordering of the endpoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback

variable {E F P X ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fixed translations preserve the actual joint norms, used to move the
common time center in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem cNorm_translate_ball (f : E → F) (a z : E) (r : ℝ) (m : ℕ) :
    cNorm (closedBall z r) m (fun x ↦ f (a + x)) =
      cNorm (closedBall (a + z) r) m f := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [iteratedFDeriv_comp_add_left]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨a + x, by simpa only [mem_closedBall, dist_add_left] using hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - a, ?_, by simp⟩
    simpa only [mem_closedBall, ← dist_add_left a (x - a) z, add_sub_cancel] using hx

/-- Smoothness on a translated open margin, for the fixed time translation
in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem contDiffOn_translate_ball {f : E → F} (a z : E) (r : ℝ)
    (hf : ContDiffOn ℝ ∞ f (ball (a + z) r)) :
    ContDiffOn ℝ ∞ (fun x ↦ f (a + x)) (ball z r) :=
  hf.comp (contDiffOn_const.add contDiffOn_id) (fun x hx ↦ by
    simpa only [mem_ball, dist_add_left] using hx)

variable [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [Fintype ι]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι] in
/-- Exact simultaneous time-translation formula for the signed row; it
includes `t < s` (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rowTransport_time_translate (t₀ : ℝ)
    (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ) (q : ℝ × (ℝ × P)) :
    rowTransport (fun z ↦ c ((t₀, (t₀, 0)) + z))
      (fun z ↦ r ((t₀, 0) + z)) q = rowTransport c r ((t₀, (t₀, 0)) + q) := by
  simp only [rowTransport, transportFactor, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  rw [intervalIntegral.integral_comp_add_left (fun u ↦ c (u, (t₀, 0) + q.2)) t₀]

/-- Characteristic row bounds on a ball centered at any fixed common time.
The constants precede the potential and datum; no row or integral estimate
is a premise (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_rowTransport_shifted_cNorm_bounds (t₀ : ℝ) (p : P) {σ R : ℝ}
    (hσ : 0 < σ) (hσR : σ < R) {M : ℝ} (hM : 0 ≤ M) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ),
      ContDiffOn ℝ ∞ c (ball (t₀, (t₀, p)) R) →
      ContDiffOn ℝ ∞ r (ball (t₀, p) R) →
      cNorm (closedBall (t₀, (t₀, p)) σ) 1 c ≤ M →
      cNorm (closedBall (t₀, p) σ) 1 r ≤ M →
      ∀ m, cNorm (closedBall (t₀, (t₀, p)) σ) m (rowTransport c r) ≤
        D m * (1 + cNorm (closedBall (t₀, (t₀, p)) σ) m c +
          cNorm (closedBall (t₀, p) σ) m r) := by
  obtain ⟨D, hD, hb⟩ := CharacteristicTransport.RowBounds.exists_rowTransport_cNorm_bounds
    (ι := ι) p hσ hσR hM
  refine ⟨D, hD, ?_⟩
  intro c r hc hr hcl hrl m
  have hn (f : ℝ × (ℝ × P) → ℝ) (j : ℕ) :=
    cNorm_translate_ball f (t₀, (t₀, 0)) (0, (0, p)) σ j
  have hrn (j : ℕ) := cNorm_translate_ball r (t₀, 0) (0, p) σ j
  have hcs := contDiffOn_translate_ball (t₀, (t₀, 0)) (0, (0, p)) R (by simpa using hc)
  have hrs := contDiffOn_translate_ball (t₀, 0) (0, p) R (by simpa using hr)
  have hh := hb _ _ hcs hrs (by simpa only [hn, Prod.mk_add_mk, add_zero, zero_add] using hcl)
    (by simpa only [hrn, Prod.mk_add_mk, add_zero, zero_add] using hrl) m
  simpa only [funext (rowTransport_time_translate t₀ c r), cNorm_translate_ball,
    Prod.mk_add_mk, add_zero, zero_add] using hh

/-- Physical row bounds after simultaneous time translation, retaining the
exact inverse-label image condition (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_physicalRowTransport_shifted_cNorm_bounds (t₀ : ℝ) (x : X) (p : P)
    {ρ σ Rx R : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hρRx : ρ < Rx) (hσR : σ < R)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ) (Y : ℝ × (ℝ × X) → P),
      ContDiffOn ℝ ∞ c (ball (t₀, (t₀, p)) R) →
      ContDiffOn ℝ ∞ r (ball (t₀, p) R) →
      ContDiffOn ℝ ∞ Y (ball (t₀, (t₀, x)) Rx) →
      MapsTo (fun q ↦ (q.1, (q.2.1, Y q)))
        (closedBall (t₀, (t₀, x)) ρ) (closedBall (t₀, (t₀, p)) σ) →
      cNorm (closedBall (t₀, (t₀, p)) σ) 1 c ≤ M →
      cNorm (closedBall (t₀, p) σ) 1 r ≤ M →
      cNorm (closedBall (t₀, (t₀, x)) ρ) 1 Y ≤ M →
      ∀ m, cNorm (closedBall (t₀, (t₀, x)) ρ) m (physicalRowTransport c r Y) ≤
        D m * (1 + cNorm (closedBall (t₀, (t₀, p)) σ) m c +
          cNorm (closedBall (t₀, p) σ) m r + cNorm (closedBall (t₀, (t₀, x)) ρ) m Y) := by
  obtain ⟨D, hD, hb⟩ := CharacteristicTransport.RowBounds.exists_physicalRowTransport_cNorm_bounds
    (ι := ι) x p hρ hσ hρRx hσR hM
  refine ⟨D, hD, ?_⟩
  intro c r Y hc hr hY hmap hcl hrl hYl m
  have hcs := contDiffOn_translate_ball (t₀, (t₀, 0)) (0, (0, p)) R (by simpa using hc)
  have hrs := contDiffOn_translate_ball (t₀, 0) (0, p) R (by simpa using hr)
  have hYs := contDiffOn_translate_ball (t₀, (t₀, 0)) (0, (0, x)) Rx (by simpa using hY)
  have hm : MapsTo (fun q : ℝ × (ℝ × X) ↦
      (q.1, (q.2.1, Y ((t₀, (t₀, 0)) + q))))
      (closedBall (0, (0, x)) ρ) (closedBall (0, (0, p)) σ) := by
    intro q hq
    have ht : (t₀, (t₀, 0)) + q ∈ closedBall (t₀, (t₀, x)) ρ := by
      simpa using (show (t₀, (t₀, 0)) + q ∈
        closedBall ((t₀, (t₀, 0)) + (0, (0, x))) ρ from by
          simpa only [mem_closedBall, dist_add_left] using hq)
    have hh := hmap ht
    simpa only [mem_closedBall, Prod.dist_eq, Real.dist_eq,
      Prod.fst_add, Prod.snd_add, add_sub_cancel_left, sub_zero] using hh
  have hh := hb _ _ _ hcs hrs hYs hm
    (by simpa only [cNorm_translate_ball, Prod.mk_add_mk, add_zero, zero_add] using hcl)
    (by simpa only [cNorm_translate_ball, Prod.mk_add_mk, add_zero, zero_add] using hrl)
    (by simpa only [cNorm_translate_ball, Prod.mk_add_mk, add_zero, zero_add] using hYl) m
  have he : physicalRowTransport (fun z ↦ c ((t₀, (t₀, 0)) + z))
      (fun z ↦ r ((t₀, 0) + z)) (fun z ↦ Y ((t₀, (t₀, 0)) + z)) =
      fun z ↦ physicalRowTransport c r Y ((t₀, (t₀, 0)) + z) := by
    funext q
    simpa only [physicalRowTransport, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, zero_add]
      using rowTransport_time_translate t₀ c r (q.1, (q.2.1, Y ((t₀, (t₀, 0)) + q)))
  simpa only [he, cNorm_translate_ball, Prod.mk_add_mk, add_zero, zero_add] using hh

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback
