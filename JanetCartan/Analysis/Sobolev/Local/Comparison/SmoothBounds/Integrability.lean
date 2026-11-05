module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.Cartesian
public import JanetCartan.Analysis.Extension.Ball

/-!
# Integrability of smooth vector jets

The local and global L² facts for the fixed extension in
`app:ch_regular_base:lem:ball-extension`, including zero dimensional domains.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every jet of a smooth compactly supported function is in L²
(`app:not:fourier`). -/
theorem memLp_iteratedFDeriv_of_contDiff_hasCompactSupport
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (j : ℕ) :
    MemLp (iteratedFDeriv ℝ j f) 2 volume :=
  (hf.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
    (hc.iteratedFDeriv j)

/-- The vector extension jets equal the intrinsic input jets on the open ball
(`app:ch_regular_base:lem:ball-extension`). No smoothness is needed for this identity. -/
theorem iteratedFDeriv_seeleyExtension_eq_on_ball
    (p : BallExtension.Parameters (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → F) (j : ℕ) :
    EqOn (iteratedFDeriv ℝ j (p.seeleyExtension f))
      (iteratedFDerivWithin ℝ j f (ball p.center p.radius)) (ball p.center p.radius) := by
  intro x hx
  rw [← iteratedFDerivWithin_of_isOpen j isOpen_ball hx]
  exact iteratedFDerivWithin_congr
    ((p.seeleyExtension_eq_on_closedBall f).mono ball_subset_closedBall) hx j

/-- All vector extension jets are in L², assuming only smoothness on the closed
input ball (`app:ch_regular_base:lem:ball-extension`). -/
theorem memLp_iteratedFDeriv_seeleyExtension [FiniteDimensional ℝ F]
    (p : BallExtension.Parameters (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (j : ℕ) :
    MemLp (iteratedFDeriv ℝ j (p.seeleyExtension f)) 2 volume :=
  memLp_iteratedFDeriv_of_contDiff_hasCompactSupport
    (p.contDiff_seeleyExtension hf) (p.hasCompactSupport_seeleyExtension f) j

/-- The intrinsic vector jets of a closed-ball smooth input are locally in L²
(`app:ch_regular_base:lem:ball-extension`). -/
theorem memLp_iteratedFDerivWithin_ball [FiniteDimensional ℝ F]
    (p : BallExtension.Parameters (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (j : ℕ) :
    MemLp (iteratedFDerivWithin ℝ j f (ball p.center p.radius)) 2
      (volume.restrict (ball p.center p.radius)) := by
  apply ((memLp_iteratedFDeriv_seeleyExtension p hf j).restrict _).ae_eq
  exact (ae_restrict_mem measurableSet_ball).mono
    (iteratedFDeriv_seeleyExtension_eq_on_ball p f j)

/-- The fixed vector extension itself belongs to L²
(`app:ch_regular_base:lem:ball-extension`). -/
theorem memLp_seeleyExtension [FiniteDimensional ℝ F]
    (p : BallExtension.Parameters (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    MemLp (p.seeleyExtension f) 2 volume :=
  (p.contDiff_seeleyExtension hf).continuous.memLp_of_hasCompactSupport
    (p.hasCompactSupport_seeleyExtension f)

/-- A closed-ball smooth vector representative is locally in L²
(`app:ch_regular_base:lem:ball-extension`). -/
theorem memLp_smooth_closedBall [FiniteDimensional ℝ F]
    (p : BallExtension.Parameters (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    MemLp f 2 (volume.restrict (ball p.center p.radius)) := by
  apply ((memLp_seeleyExtension p hf).restrict _).ae_eq
  exact (ae_restrict_mem measurableSet_ball).mono fun _ hx ↦
    p.seeleyExtension_eq_on_closedBall f (ball_subset_closedBall hx)

end JanetCartan.LocalSobolev
