module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationNonlinear
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationPositiveBounds

/-!
# The same linear atoms on smooth initial scalars

The estimates in `app:ch_mean_pairs:eq:mean-density-lipschitz` act on smooth
initial scalars, not arbitrary L² data. Restrict the original current map to
that domain and construct the linear transport map from the original positive
scalar, base matrix and footpoint. Its value at `r sqrt(1+v)` is proved to be
the existing transported matrix. No amplitude-realization identity is assumed.
-/

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow SmoothPeriodicFamily

/-- The singleton case of the existing smooth density domain, without a
carrier support restriction, for the initial scalars of the original atoms
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
abbrev PreparationScalar (n : ℕ) := smoothSupportedDensity n Unit (fun _ ↦ univ)

variable {n N : ℕ}

/-- Forget only the smoothness proof of an initial scalar
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def preparationScalarFunction : PreparationScalar n →ₗ[ℝ] (CarrierVariable n → ℝ) where
  toFun u := u.val ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Bundle an actual smooth initial scalar, retaining its values at every
carrier and initial point (`app:ch_mean_pairs:prop:mean-coarse`). -/
def preparationScalar (u : CarrierVariable n → ℝ) (hu : ContDiff ℝ ∞ u) :
    PreparationScalar n :=
  ⟨fun _ ↦ u, fun _ ↦ ⟨hu, by simp⟩⟩

/-- Restriction of the original linear atom extension to smooth scalars.
The resulting matrices are the shared smooth periodic families
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def preparationSmoothAtom
    (U : (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ))
    (hUc : ∀ u, ContDiff ℝ ∞ u → Continuous (U u))
    (hU : ∀ u, ContDiff ℝ ∞ u → ContDiff ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦ U u (torusQuotient p.1,p.2)))
    (z : CarrierParameter) :
    PreparationScalar n →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) where
  toFun u := ⟨fun x _ ↦ U (u.val ()) (x,z), fun _ ↦
    ⟨(hUc _ (u.property ()).1).comp (continuous_id.prodMk continuous_const),
      (hU _ (u.property ()).1).comp (contDiff_id.prodMk contDiff_const)⟩⟩
  map_add' u v := by apply Subtype.ext; funext x a; exact congrFun (map_add U _ _) (x,z)
  map_smul' c u := by apply Subtype.ext; funext x a; exact congrFun (map_smul U c _) (x,z)

/-- The literal linear transport extension, normalized by the SAME positive
base scalar. This divides by no sample weight and changes no phase or cutoff
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def preparationLinearTransport
    (r : CarrierVariable n → ℝ)
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ) :
    (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ) where
  toFun u p := (u (p.2,Y p) / r (p.2,Y p)) • T p
  map_add' u v := by funext p; simp [add_div, add_smul]
  map_smul' c u := by funext p; simp [mul_div_assoc, smul_smul]

/-- Joint regularity of this particular linear transport follows from
the original smooth positive scalar and smooth geometric extensions
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationLinearTransport_regular
    (r : CarrierVariable n → ℝ) (hr : ContDiff ℝ ∞ r) (hrpos : ∀ p, 0 < r p)
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : Continuous Y) (hTc : Continuous T)
    (hY : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ Y (torusQuotient p.1,p.2)))
    (hT : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ T (torusQuotient p.1,p.2)))
    (u : CarrierVariable n → ℝ) (hu : ContDiff ℝ ∞ u) :
    Continuous (preparationLinearTransport r Y T u) ∧
      ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
        preparationLinearTransport r Y T u (torusQuotient p.1,p.2)) := by
  exact ⟨((hu.continuous.comp (continuous_snd.prodMk hYc)).div
    (hr.continuous.comp (continuous_snd.prodMk hYc)) (fun _ ↦ (hrpos _).ne')).smul hTc,
    ((hu.comp (contDiff_snd.prodMk hY)).div
      (hr.comp (contDiff_snd.prodMk hY)) (fun _ ↦ (hrpos _).ne')).smul hT⟩

/-- The normalization cancels exactly at the prepared scalar, so the
estimated transport is the SAME matrix as the nonlinear preparation run
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationLinearTransport_prepared
    (r v : CarrierVariable n → ℝ) (hrpos : ∀ p, 0 < r p)
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ) :
    preparationLinearTransport r Y T (fun p ↦ positiveDensityAmplitude (r p) (v p)) =
      preparedTransportExtension Y T v := by
  funext p
  simp [preparationLinearTransport, preparedTransportExtension, positiveDensityAmplitude,
    mul_div_cancel_left₀ _ (hrpos _).ne']

end JanetCartan.CurrentMean
