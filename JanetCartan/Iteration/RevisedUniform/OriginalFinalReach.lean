module

public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistory
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalCompletionProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalCompletionBufferProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanErrorTransfer

/-!
# One dimension-only initial reach for every physical mean gate

The original prehistory threshold, normal-completion threshold, completed-mean
error threshold, physical base threshold, physical normal-buffer threshold and
full initialized-field threshold are all chosen before the metric scale,
history, target, smoothing order and finite Picard index.  This leaf only joins
the already-checked thresholds; it does not choose a new geometry or replace
any of the producers (`main:eq:displacement-budget`, `main:eq:mean-normal-field`,
`main:prop:mean`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] public noncomputable section
namespace JanetCartan.RevisedUniform.OriginalFinalReach

/-- The final initial reach is a finite maximum of the literal, dimension-only
thresholds.  Accuracy-dependent conditions such as `2*m ≤ R` are deliberately
not included here. -/
def initialReach (Tref Scomp Serror Sbase Sbuffer SfullW : ℝ) : ℝ :=
  max (max (max Tref Scomp) (max Serror Sbase)) (max Sbuffer SfullW)

theorem tref_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW : ℝ} :
    Tref ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  unfold initialReach
  exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem scomp_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW : ℝ} :
    Scomp ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  unfold initialReach
  exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem serror_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW : ℝ} :
    Serror ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  unfold initialReach
  exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem sbase_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW : ℝ} :
    Sbase ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  unfold initialReach
  exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem sbuffer_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW : ℝ} :
    Sbuffer ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  unfold initialReach
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem sfullW_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW : ℝ} :
    SfullW ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  unfold initialReach
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem two_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW : ℝ}
    (hTref : 2 ≤ Tref) (hScomp : 2 ≤ Scomp) (hSerror : 2 ≤ Serror)
    (hSbase : 2 ≤ Sbase) (hSbuffer : 2 ≤ Sbuffer) (hSfullW : 2 ≤ SfullW) :
    2 ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  unfold initialReach
  have h₁ : 2 ≤ max Tref Scomp := by
    by_cases h : Tref ≤ Scomp
    · exact hTref.trans h |>.trans (le_max_right _ _)
    · exact hScomp.trans (le_max_right _ _)
  have h₂ : 2 ≤ max Serror Sbase := by
    by_cases h : Serror ≤ Sbase
    · exact hSerror.trans h |>.trans (le_max_right _ _)
    · exact hSbase.trans (le_max_right _ _)
  have h₃ : 2 ≤ max (max Tref Scomp) (max Serror Sbase) :=
    h₁.trans (le_max_left _ _)
  have h₄ : 2 ≤ max Sbuffer SfullW := by
    by_cases h : Sbuffer ≤ SfullW
    · exact hSbuffer.trans h |>.trans (le_max_right _ _)
    · exact hSfullW.trans (le_max_right _ _)
  exact h₃.trans (le_max_left _ _)

theorem sourceAux_le_initialReach {Tref Scomp Serror Sbase Sbuffer SfullW aux : ℝ}
    (haux : aux ≤ Tref) :
    aux ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
  calc
    aux ≤ Tref := haux
    _ ≤ initialReach Tref Scomp Serror Sbase Sbuffer SfullW := by
      unfold initialReach
      exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem all_initial_gates {Tref Scomp Serror Sbase Sbuffer SfullW R₀ : ℝ}
    (hTref : 2 ≤ Tref) (hScomp : 2 ≤ Scomp) (hSerror : 2 ≤ Serror)
    (hSbase : 2 ≤ Sbase) (hSbuffer : 2 ≤ Sbuffer) (hSfullW : 2 ≤ SfullW)
    (hR : initialReach Tref Scomp Serror Sbase Sbuffer SfullW ≤ R₀) :
    2 ≤ R₀ ∧ Tref ≤ R₀ ∧ Scomp ≤ R₀ ∧ Serror ≤ R₀ ∧
      Sbase ≤ R₀ ∧ Sbuffer ≤ R₀ ∧ SfullW ≤ R₀ := by
  have h2 := (two_le_initialReach hTref hScomp hSerror hSbase hSbuffer hSfullW).trans hR
  exact ⟨h2, tref_le_initialReach.trans hR, scomp_le_initialReach.trans hR,
    serror_le_initialReach.trans hR, sbase_le_initialReach.trans hR,
    sbuffer_le_initialReach.trans hR, sfullW_le_initialReach.trans hR⟩

end JanetCartan.RevisedUniform.OriginalFinalReach
end

#print axioms JanetCartan.RevisedUniform.OriginalFinalReach.initialReach
#print axioms JanetCartan.RevisedUniform.OriginalFinalReach.all_initial_gates
