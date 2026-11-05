module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Christoffel
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Variation
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Differential identities for ambient reconstruction

The reconstruction formula of `app:ch_waves:eq:reconstruction`, parametrized by
its pointwise normal-completion map. The product identity needs only linearity
of that map. The half-strain identity needs a smooth normal field and uses the
proved tangential and normal variation lemmas, not the unfinished combined
statement in `Normal.lean`. Identification of the completion map with the actual
smooth geometric inverse and construction of the carrier remain separate inputs.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set Matrix

namespace JanetCartan.LeadingWave

/-- Normal part of `app:ch_waves:eq:reconstruction`. The supplied linear map is
to be instantiated with `N_G Π_(K_Gᗮ)`. -/
def normalCorrection {n N : ℕ} (F : Euclidean n → Euclidean N)
    (L : Euclidean n → MetricTensor n →ₗ[ℝ] Euclidean N)
    (u : Euclidean n → Euclidean n) : Euclidean n → Euclidean N :=
  fun x ↦ L x (symmCovariantDeriv F u x)

/-- Ambient reconstruction from `app:ch_waves:eq:reconstruction`, with an explicit
normal-completion map. This definition does not assert the inverse identities. -/
def reconstruction {n N : ℕ} (F : Euclidean n → Euclidean N)
    (L : Euclidean n → MetricTensor n →ₗ[ℝ] Euclidean N)
    (u : Euclidean n → Euclidean n) : Euclidean n → Euclidean N :=
  tangentLift F u + normalCorrection F L u

/-- The principal normal amplitude in `app:ch_waves:eq:arbitrary-b-amplitudes`. -/
def principalNormal {n N : ℕ} (L : MetricTensor n →ₗ[ℝ] Euclidean N)
    (ξ b : Euclidean n) : Euclidean N := L (symmetricProduct ξ b)

/-- The reconstructed principal normal is linear in the scalar amplitude
(`app:ch_waves:thm:leading`). -/
theorem principalNormal_smul {n N : ℕ} (L : MetricTensor n →ₗ[ℝ] Euclidean N)
    (ξ b : Euclidean n) (a : ℝ) :
    principalNormal L ξ (a • b) = a • principalNormal L ξ b := by
  simp only [principalNormal, symmetricProduct_smul_right, map_smul]

/-- The principal tensor is quadratic in the scalar amplitude
(`app:ch_waves:thm:leading`). -/
theorem principalNormal_density_scaling {n N : ℕ}
    (L : MetricTensor n →ₗ[ℝ] Euclidean N) (ξ k : Euclidean n) (a : ℝ) :
    (principalMatrix (principalNormal L ξ (a • k)) ξ)ᵀ *
        principalMatrix (principalNormal L ξ (a • k)) ξ =
      a ^ 2 • ((principalMatrix (principalNormal L ξ k) ξ)ᵀ *
        principalMatrix (principalNormal L ξ k) ξ) := by
  rw [principalNormal_smul, principalMatrix_density_scaling]

/-- The covector `df` in the product rule for
`app:ch_waves:eq:exact-W-amplitude`. -/
def scalarDifferential {n : ℕ} (f : Euclidean n → ℝ) (x : Euclidean n) : Euclidean n :=
  WithLp.toLp 2 (fun i ↦ partialDeriv f x i)

/-- Covariant product rule underlying `app:ch_waves:eq:exact-W-amplitude`. -/
theorem symmCovariantDeriv_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    {f : Euclidean n → ℝ} {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) :
    symmCovariantDeriv F (fun y ↦ f y • u y) x =
      f x • symmCovariantDeriv F u x + symmetricProduct (scalarDifferential f x) (u x) := by
  have hc (j : Fin n) : DifferentiableAt ℝ (fun y ↦ u y j) x :=
    ((differentiableAt_piLp 2).mp hu) j
  have hd (i j : Fin n) :
      partialDeriv (fun y ↦ f y * u y j) x i =
        partialDeriv f x i * u x j + f x * partialDeriv (fun y ↦ u y j) x i := by
    change fderiv ℝ (fun y ↦ f y * u y j) x (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_mul hf (hc j)]
    simp only [_root_.add_apply, _root_.smul_apply,
      smul_eq_mul, partialDeriv]
    ring
  ext i j
  simp only [symmCovariantDeriv, hd, Matrix.add_apply, Matrix.smul_apply,
    PiLp.smul_apply, smul_eq_mul, symmetricProduct, scalarDifferential]
  have he : (∑ k, christoffel F x i j k * (f x * u x k)) =
      ∑ k, f x * (christoffel F x i j k * u x k) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, ← Finset.mul_sum]
  ring

/-- The tangential term is pointwise linear in the scalar amplitude, as used in
`app:ch_waves:eq:exact-W-amplitude`. -/
theorem tangentLift_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (f : Euclidean n → ℝ) (u : Euclidean n → Euclidean n) (x : Euclidean n) :
    tangentLift F (fun y ↦ f y • u y) x = f x • tangentLift F u x := by
  simp only [tangentLift, Finset.smul_sum, PiLp.smul_apply, smul_eq_mul, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- Exact real scalar product identity underlying
`app:ch_waves:eq:exact-W-amplitude`; no inverse identity is assumed. -/
theorem reconstruction_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (L : Euclidean n → MetricTensor n →ₗ[ℝ] Euclidean N)
    {f : Euclidean n → ℝ} {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) :
    reconstruction F L (fun y ↦ f y • u y) x =
      f x • reconstruction F L u x + principalNormal (L x) (scalarDifferential f x) (u x) := by
  simp only [reconstruction, Pi.add_apply, normalCorrection, tangentLift_smul,
    symmCovariantDeriv_smul F hf hu, map_add, map_smul, smul_add, principalNormal]
  abel

/-- The half-strain of a reconstruction with a smooth normal correction,
from `app:ch_waves:eq:exact-half-strain`. The remaining geometric step is to
identify the normal pairing with the complementary stress projection. -/
theorem reconstruction_half_strain {n N : ℕ}
    {F : Euclidean n → Euclidean N}
    {L : Euclidean n → MetricTensor n →ₗ[ℝ] Euclidean N}
    {u : Euclidean n → Euclidean n} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) (hw : ContDiffOn ℝ ∞ (normalCorrection F L u) s)
    (hn : ∀ x ∈ s, normalCorrection F L u x ∈ normalSpace F x) :
    EqOn (fun x ↦ (1 / 2 : ℝ) • linearizedMetric F (reconstruction F L u) x)
      (fun x ↦ symmCovariantDeriv F u x - normalPairing F (normalCorrection F L u) x) s := by
  intro x hx
  have ht := linearizedMetric_tangentLift hs hF hu himm hx
  have hn' := linearizedMetric_normal hs hF hw hn hx
  have htd := (((contDiffOn_tangentLift hs hF hu himm) x hx).contDiffAt
    (hs.mem_nhds hx)).differentiableAt (by simp)
  have hwd := ((hw x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have ha : linearizedMetric F (reconstruction F L u) x =
      linearizedMetric F (tangentLift F u) x +
        linearizedMetric F (normalCorrection F L u) x := by
    ext i j
    simp only [linearizedMetric, reconstruction, partialDeriv, fderiv_add htd hwd,
      _root_.add_apply, inner_add_left, inner_add_right, Matrix.add_apply]
    ring
  change (1 / 2 : ℝ) • linearizedMetric F (reconstruction F L u) x = _
  rw [ha, ht, hn']
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

end JanetCartan.LeadingWave
