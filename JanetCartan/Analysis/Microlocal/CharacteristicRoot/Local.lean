module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Local scalar characteristic roots

The implicit-function step of `app:ch_seed:prop:seed-actual-menu` and
`app:ch_response:thm:response-compatible-choice`. The parameter space may include
physical coordinates, transverse covectors and coefficient parameters. The scalar
root is constructed from the equation by Mathlib's implicit-function theorem.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

/-- The derivative in the distinguished scalar covector coordinate
(`app:ch_response:thm:response-compatible-choice`). -/
def scalarDerivative (f : P × ℝ → ℝ) (z : P × ℝ) : ℝ :=
  fderiv ℝ f z (0, 1)

omit [CompleteSpace P] in
/-- A nonzero scalar partial derivative is precisely the invertibility needed by
 the implicit-function construction in `app:ch_seed:prop:seed-actual-menu`. -/
theorem scalarPartial_isInvertible {f : P × ℝ → ℝ} {z : P × ℝ}
    (h : scalarDerivative f z ≠ 0) :
    (fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P ℝ).IsInvertible := by
  let L := fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P ℝ
  have hL (r : ℝ) : L r = r * scalarDerivative f z := by
    change fderiv ℝ f z (0, r) = _
    have he : ((0, r) : P × ℝ) = r • (0, 1) := by simp
    rw [he, map_smul]
    rfl
  change L.IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (scalarDerivative f z)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext
    intro r
    change L ((scalarDerivative f z)⁻¹ * r) = r
    rw [hL]
    simp [mul_comm, h]
  · apply ContinuousLinearMap.ext
    intro r
    change (scalarDerivative f z)⁻¹ * L r = r
    rw [hL]
    simp [mul_comm, h]

/-- The actual local root, constructed from the symbol, with all spectator
parameters retained (`app:ch_seed:prop:seed-actual-menu`). -/
def localRoot {f : P × ℝ → ℝ} {z : P × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (h : scalarDerivative f z ≠ 0) : P → ℝ :=
  hf.implicitFunction (by simp) (scalarPartial_isInvertible h)

/-- The constructed branch passes through the prescribed simple root.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem localRoot_base {f : P × ℝ → ℝ} {z : P × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (h : scalarDerivative f z ≠ 0) :
    localRoot hf h z.1 = z.2 :=
  hf.implicitFunction_apply_self _ _

/-- Joint smooth dependence at the base point, as used in
`app:ch_seed:prop:seed-actual-menu`. -/
theorem contDiffAt_localRoot {f : P × ℝ → ℝ} {z : P × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (h : scalarDerivative f z ≠ 0) :
    ContDiffAt ℝ ∞ (localRoot hf h) z.1 :=
  hf.contDiffAt_implicitFunction _ _

/-- The symbol vanishes on the constructed branch near the base point.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem localRoot_eventually_zero {f : P × ℝ → ℝ} {z : P × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (h : scalarDerivative f z ≠ 0) (hz : f z = 0) :
    ∀ᶠ q in 𝓝 z.1, f (q, localRoot hf h q) = 0 := by
  simpa only [hz, localRoot] using hf.eventually_apply_implicitFunction (by simp)
    (scalarPartial_isInvertible h)

/-- Local uniqueness among all scalar roots, not just among preselected branches.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem localRoot_eventually_unique {f : P × ℝ → ℝ} {z : P × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (h : scalarDerivative f z ≠ 0) (hz : f z = 0) :
    ∀ᶠ w in 𝓝 z, f w = 0 ↔ localRoot hf h w.1 = w.2 := by
  simpa only [hz, localRoot] using hf.eventually_apply_eq_iff_implicitFunction (by simp)
    (scalarPartial_isInvertible h)

/-- Any continuous solution germ through a simple root equals the constructed
branch. This transfers smoothness to a branch on one fixed open patch.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem localRoot_eventually_eq {f : P × ℝ → ℝ} {z : P × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (h : scalarDerivative f z ≠ 0) (hz : f z = 0)
    {g : P → ℝ} (hg : ContinuousAt g z.1) (hg₀ : g z.1 = z.2)
    (heq : ∀ᶠ q in 𝓝 z.1, f (q, g q) = 0) :
    g =ᶠ[𝓝 z.1] localRoot hf h := by
  have ht : Tendsto (fun q ↦ (q, g q)) (𝓝 z.1) (𝓝 z) := by
    simpa only [hg₀, id_eq, Prod.eta] using (continuousAt_id.prodMk hg).tendsto
  filter_upwards [ht.eventually (localRoot_eventually_unique hf h hz), heq] with q hq he
  exact (hq.mp he).symm

/-- Smoothness of a continuous solution follows from the equation and the simple
root condition (`app:ch_response:thm:response-compatible-choice`). -/
theorem contDiffAt_of_continuous_root {f : P × ℝ → ℝ} {g : P → ℝ} {q : P}
    (hf : ContDiffAt ℝ ∞ f (q, g q)) (h : scalarDerivative f (q, g q) ≠ 0)
    (hg : ContinuousAt g q) (heq : ∀ᶠ p in 𝓝 q, f (p, g p) = 0) :
    ContDiffAt ℝ ∞ g q :=
  (contDiffAt_localRoot hf h).congr_of_eventuallyEq
    (localRoot_eventually_eq hf h heq.self_of_nhds hg rfl heq)

end JanetCartan.CharacteristicRoot
