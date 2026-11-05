module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.Analytic.Composition

/-!
# Finite compositions for the flat reference

The iteration in Proposition `app:ch_seed:prop:seed-analytic` starts from the
identity and applies maps into successively larger Euclidean spaces. This file
proves the general composition facts used by that construction. The hypotheses
on the individual maps must still be verified for the explicit circular bendings.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: a finite composition starting
from the identity, allowing the ambient dimension to change at each step. -/
def successiveComposition (d : ℕ → ℕ)
    (step : ∀ k, Euclidean (d k) → Euclidean (d (k + 1))) :
    (k : ℕ) → Euclidean (d 0) → Euclidean (d k)
  | 0 => id
  | k + 1 => step k ∘ successiveComposition d step k

variable {d : ℕ → ℕ}
  {step : ∀ k, Euclidean (d k) → Euclidean (d (k + 1))}

/-- Proposition `app:ch_seed:prop:seed-analytic`: composition preserves the
normalization of the value at the center. -/
theorem successiveComposition_zero (k : ℕ) (hzero : ∀ j < k, step j 0 = 0) :
    successiveComposition d step k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change step k (successiveComposition d step k 0) = 0
    rw [ih (fun j hj => hzero j (Nat.lt_succ_of_lt hj)), hzero k (Nat.lt_succ_self k)]

/-- Proposition `app:ch_seed:prop:seed-analytic`: a finite composition of
analytic bendings is analytic on the whole Euclidean domain. -/
theorem analyticOnNhd_successiveComposition (k : ℕ)
    (hanalytic : ∀ j < k, AnalyticOnNhd ℝ (step j) Set.univ) :
    AnalyticOnNhd ℝ (successiveComposition d step k) Set.univ := by
  induction k with
  | zero => exact analyticOnNhd_id
  | succ k ih =>
    exact (hanalytic k (Nat.lt_succ_self k)).comp
      (ih (fun j hj => hanalytic j (Nat.lt_succ_of_lt hj))) (Set.mapsTo_univ _ _)

/-- Proposition `app:ch_seed:prop:seed-analytic`: smoothness of the finite
composition, at any prescribed order. -/
theorem contDiff_successiveComposition (k : ℕ) {r : WithTop ℕ∞}
    (hsmooth : ∀ j < k, ContDiff ℝ r (step j)) :
    ContDiff ℝ r (successiveComposition d step k) := by
  induction k with
  | zero => exact contDiff_id
  | succ k ih =>
    exact (hsmooth k (Nat.lt_succ_self k)).comp
      (ih (fun j hj => hsmooth j (Nat.lt_succ_of_lt hj)))

/-- Proposition `app:ch_seed:prop:seed-analytic`: differentiability needed for
the chain rule in the bending iteration. -/
theorem differentiable_successiveComposition (k : ℕ)
    (hdiff : ∀ j < k, Differentiable ℝ (step j)) :
    Differentiable ℝ (successiveComposition d step k) := by
  induction k with
  | zero => exact differentiable_id
  | succ k ih =>
    exact (hdiff k (Nat.lt_succ_self k)).comp
      (ih (fun j hj => hdiff j (Nat.lt_succ_of_lt hj)))

/-- Proposition `app:ch_seed:prop:seed-analytic`: composing differentials that
preserve inner products again gives a differential preserving inner products. -/
theorem inner_fderiv_successiveComposition (k : ℕ)
    (hdiff : ∀ j < k, Differentiable ℝ (step j))
    (hinner : ∀ j < k, ∀ y u v,
      inner ℝ (fderiv ℝ (step j) y u) (fderiv ℝ (step j) y v) = inner ℝ u v)
    (x u v : Euclidean (d 0)) :
    inner ℝ (fderiv ℝ (successiveComposition d step k) x u)
      (fderiv ℝ (successiveComposition d step k) x v) = inner ℝ u v := by
  induction k with
  | zero => simp [successiveComposition]
  | succ k ih =>
    have hprev := differentiable_successiveComposition k
      (fun j hj => hdiff j (Nat.lt_succ_of_lt hj))
    change inner ℝ (fderiv ℝ (step k ∘ successiveComposition d step k) x u)
      (fderiv ℝ (step k ∘ successiveComposition d step k) x v) = inner ℝ u v
    rw [fderiv_comp x (hdiff k (Nat.lt_succ_self k) _) (hprev x)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hinner k (Nat.lt_succ_self k)]
    exact ih (fun j hj => hdiff j (Nat.lt_succ_of_lt hj))
      (fun j hj => hinner j (Nat.lt_succ_of_lt hj))

/-- Proposition `app:ch_seed:prop:seed-analytic`: the finite composition has
exactly the flat metric when each step has an isometric differential. -/
theorem inducedMetric_successiveComposition (k : ℕ)
    (hdiff : ∀ j < k, Differentiable ℝ (step j))
    (hinner : ∀ j < k, ∀ y u v,
      inner ℝ (fderiv ℝ (step j) y u) (fderiv ℝ (step j) y v) = inner ℝ u v)
    (x : Euclidean (d 0)) :
    inducedMetric (successiveComposition d step k) x = 1 := by
  ext i j
  change inner ℝ
    (fderiv ℝ (successiveComposition d step k) x (EuclideanSpace.single i 1))
    (fderiv ℝ (successiveComposition d step k) x (EuclideanSpace.single j 1)) = _
  rw [inner_fderiv_successiveComposition k hdiff hinner]
  simp [EuclideanSpace.inner_single_left, Matrix.one_apply]

/-- Proposition `app:ch_seed:prop:seed-analytic`: the flat finite composition is
an immersion everywhere, before restricting it to a local embedding. -/
theorem isImmersionOn_successiveComposition (k : ℕ)
    (hdiff : ∀ j < k, Differentiable ℝ (step j))
    (hinner : ∀ j < k, ∀ y u v,
      inner ℝ (fderiv ℝ (step j) y u) (fderiv ℝ (step j) y v) = inner ℝ u v) :
    IsImmersionOn (successiveComposition d step k) Set.univ := by
  intro x _
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  have h := inner_fderiv_successiveComposition k hdiff hinner x u u
  rw [hu, inner_zero_left] at h
  exact inner_self_eq_zero.mp h.symm

end JanetCartan.ReferenceConstruction
