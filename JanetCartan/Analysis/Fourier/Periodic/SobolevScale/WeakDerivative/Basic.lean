module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Distributional coordinate derivatives on the unit torus

The weak derivatives used in the integer induction of
`app:ch_background:prop:bg-inverse` are defined by integration against every
smooth periodic field, with the real inner product. Smooth density gives
uniqueness; periodic integration by parts identifies classical derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The integral of a smooth coordinate derivative vanishes on the unit torus
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem integral_periodicCoordinateDeriv_eq_zero {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) (i : Fin n) :
    (∫ x, periodicCoordinateDeriv i f x) = 0 := by
  have h := congrArg Prod.fst (periodicFourierCoeff_coordinateDeriv hf i 0)
  simpa [periodicFourierCoeff, UnitAddTorus.mFourier_zero] using h

omit [FiniteDimensional ℝ F] in
/-- Real inner products of smooth periodic fields are smooth
(`app:ch_background:prop:bg-inverse`). -/
theorem IsSmoothPeriodic.inner {f g : Torus n → F}
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    IsSmoothPeriodic (fun x ↦ ⟪f x, g x⟫) :=
  ⟨hf.1.inner hg.1, hf.2.inner ℝ hg.2⟩

omit [FiniteDimensional ℝ F] in
/-- The coordinate product rule for the real pairing
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicCoordinateDeriv_inner {f g : Torus n → F}
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (i : Fin n) :
    periodicCoordinateDeriv i (fun x ↦ ⟪f x, g x⟫) =
      fun x ↦ ⟪periodicCoordinateDeriv i f x, g x⟫ +
        ⟪f x, periodicCoordinateDeriv i g x⟫ := by
  funext x
  have h := (hf.hasDerivAt_coordinate i x 0).inner ℝ (hg.hasDerivAt_coordinate i x 0)
  simpa [periodicCoordinateDeriv, add_comm] using h.deriv

omit [FiniteDimensional ℝ F] in
/-- Periodic integration by parts for the real Hilbert pairing
(`app:ch_background:prop:bg-inverse`). -/
theorem integral_periodicCoordinateDeriv_inner {f g : Torus n → F}
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (i : Fin n) :
    (∫ x, ⟪periodicCoordinateDeriv i f x, g x⟫) =
      -(∫ x, ⟪f x, periodicCoordinateDeriv i g x⟫) := by
  have h := integral_periodicCoordinateDeriv_eq_zero (hf.inner hg) i
  rw [periodicCoordinateDeriv_inner hf hg,
    integral_add (((hf.coordinateDeriv i).inner hg).1.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      ((hf.inner (hg.coordinateDeriv i)).1.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))] at h
  linarith

/-- The real L² pairing with a smooth representative is its actual integral
(`app:ch_background:prop:bg-inverse`). -/
theorem inner_periodicL2_ofSmooth (u : PeriodicL2 n F) (s : ℕ)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    ⟪u, PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s f hf)⟫ =
      ∫ x, ⟪u x, f x⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [PeriodicSobolevSpace.toL2_ofSmooth_ae s f hf] with x hx
  rw [hx]

/-- The weak pairing with a smooth field is integrable, so the distributional
identity uses genuine integrals (`app:ch_background:prop:bg-inverse`). -/
theorem integrable_inner_periodicL2_smooth (u : PeriodicL2 n F)
    {f : Torus n → F} (hf : IsSmoothPeriodic f) :
    Integrable (fun x ↦ ⟪u x, f x⟫) := by
  apply (L2.integrable_inner (𝕜 := ℝ) u
    (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 f hf))).congr
  filter_upwards [PeriodicSobolevSpace.toL2_ofSmooth_ae 0 f hf] with x hx
  rw [hx]

/-- An actual weak coordinate derivative of an L² class: the identity holds
against every smooth periodic F-valued test field, using the real inner product
(`app:ch_background:prop:bg-inverse`). -/
def HasPeriodicWeakDerivative (i : Fin n) (u v : PeriodicL2 n F) : Prop :=
  ∀ (φ : Torus n → F), IsSmoothPeriodic φ →
    (∫ x, ⟪v x, φ x⟫) = -(∫ x, ⟪u x, periodicCoordinateDeriv i φ x⟫)

/-- Equivalent formulation in terms of the continuous L² pairing. The test
class remains all smooth periodic fields (`app:ch_background:prop:bg-inverse`). -/
theorem hasPeriodicWeakDerivative_iff_inner (i : Fin n) (u v : PeriodicL2 n F) :
    HasPeriodicWeakDerivative i u v ↔
      ∀ (φ : Torus n → F) (hφ : IsSmoothPeriodic φ),
        ⟪v, PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 φ hφ)⟫ =
        -⟪u, PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0
          (periodicCoordinateDeriv i φ) (hφ.coordinateDeriv i))⟫ := by
  simp only [inner_periodicL2_ofSmooth]
  rfl

/-- Smooth density in L² makes the distributional derivative unique
(`app:ch_background:prop:bg-inverse`). -/
theorem HasPeriodicWeakDerivative.unique {i : Fin n} {u v w : PeriodicL2 n F}
    (hv : HasPeriodicWeakDerivative i u v) (hw : HasPeriodicWeakDerivative i u w) :
    v = w := by
  apply (PeriodicSobolevSpace.denseRange_toL2_ofSmooth (n := n) (F := F) 0).eq_of_inner_left ℝ
  intro φ
  simp only [inner_periodicL2_ofSmooth]
  exact (hv φ.1 φ.2).trans (hw φ.1 φ.2).symm

/-- A smooth representative's classical coordinate derivative is its weak
coordinate derivative (`app:ch_background:prop:bg-inverse`). -/
theorem IsSmoothPeriodic.hasPeriodicWeakDerivative {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (i : Fin n) (s t : ℕ) :
    HasPeriodicWeakDerivative i
      (PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s f hf))
      (PeriodicSobolevSpace.toL2 t (PeriodicSobolevSpace.ofSmooth t
        (periodicCoordinateDeriv i f) (hf.coordinateDeriv i))) := by
  intro φ hφ
  have hu := PeriodicSobolevSpace.toL2_ofSmooth_ae s f hf
  have hv := PeriodicSobolevSpace.toL2_ofSmooth_ae t _ (hf.coordinateDeriv i)
  calc
    _ = ∫ x, ⟪periodicCoordinateDeriv i f x, φ x⟫ := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = -(∫ x, ⟪f x, periodicCoordinateDeriv i φ x⟫) :=
      integral_periodicCoordinateDeriv_inner hf hφ i
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]

namespace HasPeriodicWeakDerivative

/-- Weak differentiation of zero (`app:ch_background:prop:bg-inverse`). -/
theorem zero (i : Fin n) : HasPeriodicWeakDerivative i (0 : PeriodicL2 n F) 0 := by
  rw [hasPeriodicWeakDerivative_iff_inner]
  intros
  simp

/-- Weak differentiation respects addition (`app:ch_background:prop:bg-inverse`). -/
theorem add {i : Fin n} {u v u' v' : PeriodicL2 n F}
    (h : HasPeriodicWeakDerivative i u v) (h' : HasPeriodicWeakDerivative i u' v') :
    HasPeriodicWeakDerivative i (u + u') (v + v') := by
  rw [hasPeriodicWeakDerivative_iff_inner] at h h' ⊢
  intro φ hφ
  simp only [inner_add_left, h φ hφ, h' φ hφ, neg_add]

/-- Weak differentiation respects real scalar multiplication
(`app:ch_background:prop:bg-inverse`). -/
theorem smul {i : Fin n} {u v : PeriodicL2 n F}
    (h : HasPeriodicWeakDerivative i u v) (c : ℝ) :
    HasPeriodicWeakDerivative i (c • u) (c • v) := by
  rw [hasPeriodicWeakDerivative_iff_inner] at h ⊢
  intro φ hφ
  simp only [real_inner_smul_left, h φ hφ, mul_neg]

/-- Weak differentiation respects negation (`app:ch_background:prop:bg-inverse`). -/
theorem neg {i : Fin n} {u v : PeriodicL2 n F}
    (h : HasPeriodicWeakDerivative i u v) : HasPeriodicWeakDerivative i (-u) (-v) := by
  simpa only [neg_one_smul] using h.smul (-1)

/-- Weak differentiation respects subtraction (`app:ch_background:prop:bg-inverse`). -/
theorem sub {i : Fin n} {u v u' v' : PeriodicL2 n F}
    (h : HasPeriodicWeakDerivative i u v) (h' : HasPeriodicWeakDerivative i u' v') :
    HasPeriodicWeakDerivative i (u - u') (v - v') := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

/-- The weak derivative graph is closed under simultaneous L² limits. This
passes integration by parts to Sobolev limits (`app:ch_background:prop:bg-inverse`). -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {i : Fin n}
    {u v : ι → PeriodicL2 n F} {u₀ v₀ : PeriodicL2 n F}
    (h : ∀ j, HasPeriodicWeakDerivative i (u j) (v j))
    (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀)) :
    HasPeriodicWeakDerivative i u₀ v₀ := by
  rw [hasPeriodicWeakDerivative_iff_inner]
  intro φ hφ
  have heq := fun j ↦ (hasPeriodicWeakDerivative_iff_inner i _ _).mp (h j) φ hφ
  exact tendsto_nhds_unique (hv.inner tendsto_const_nhds)
    (((hu.inner tendsto_const_nhds).neg).congr (fun j ↦ (heq j).symm))

end HasPeriodicWeakDerivative

/-- The distributional derivative graph is a closed linear subspace of L² × L²
(`app:ch_background:prop:bg-inverse`). -/
def periodicWeakDerivativeGraph (i : Fin n) : Submodule ℝ (PeriodicL2 n F × PeriodicL2 n F) where
  carrier := {p | HasPeriodicWeakDerivative i p.1 p.2}
  zero_mem' := HasPeriodicWeakDerivative.zero i
  add_mem' := fun h h' ↦ h.add h'
  smul_mem' := fun c _ h ↦ h.smul c

/-- Closedness of the distributional derivative graph
(`app:ch_background:prop:bg-inverse`). -/
theorem isClosed_periodicWeakDerivativeGraph (i : Fin n) :
    IsClosed (periodicWeakDerivativeGraph (F := F) i : Set (PeriodicL2 n F × PeriodicL2 n F)) := by
  change IsClosed {p : PeriodicL2 n F × PeriodicL2 n F | HasPeriodicWeakDerivative i p.1 p.2}
  simp only [hasPeriodicWeakDerivative_iff_inner, Set.ofPred_forall]
  exact isClosed_iInter fun φ ↦ isClosed_iInter fun hφ ↦
    isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_fst.inner continuous_const).neg

end JanetCartan
