module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# The original one-radius corrected-comparison constants

The before-history constant uses the actual common measurement budget, the SAME
retained five-field tuple, original inner weight and detector, and the large
common cutoff selected by task26. The original full-response budget and shared
quadrature kernel are still explicit fixed inputs; the actual finite current
comparison is not asserted by this before-history cache alone.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000
open scoped Matrix.Norms.Frobenius

cache_original_corrected_comparison_budgets
