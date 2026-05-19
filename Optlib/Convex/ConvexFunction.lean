import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.MeanValue
import Optlib.Differential.Calculation
import Optlib.Differential.Lemmas

set_option linter.unusedVariables false

open InnerProductSpace

noncomputable section

section FirstOrderCondition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)} {x : E} {s : Set E}

theorem Convex_first_order_condition {s : Set E}
    (h : HasFDerivAt f (f' x) x) (hf : ConvexOn ℝ s f) (xs : x ∈ s) :
    ∀ y ∈ s, f x + f' x (y - x) ≤ f y := by
  sorry

theorem Convex_first_order_condition_inverse {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)}
    {s : Set E} (h : ∀ x ∈ s, HasFDerivAt f (f' x) x) (h₁: Convex ℝ s)
    (h₂ : ∀ (x : E), x ∈ s → ∀ (y : E), y ∈ s → f x + f' x (y - x) ≤ f y) : ConvexOn ℝ s f := by
  sorry

theorem Convex_first_order_condition_iff (h₁ : Convex ℝ s) (h : ∀ x ∈ s, HasFDerivAt f (f' x) x) :
    ConvexOn ℝ s f ↔ ∀ x ∈ s, ∀ y ∈ s, f x + f' x (y - x) ≤ f y := by
  sorry

theorem Convex_monotone_gradient (hfun: ConvexOn ℝ s f) (h : ∀ x ∈ s , HasFDerivAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, (f' x - f' y) (x - y) ≥ 0 := by
  sorry

end FirstOrderCondition

section FirstOrderCondition_Gradient

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {f' : E → E} {s : Set E} {x : E}

theorem Convex_first_order_condition' (h : HasGradientAt f (f' x) x) (hf : ConvexOn ℝ s f)
    (xs : x ∈ s) : ∀ (y : E), y ∈ s → f x + @inner ℝ E _ (f' x) (y - x) ≤ f y := by
  sorry

theorem Convex_first_order_condition_inverse' (h : ∀ x ∈ s , HasGradientAt f (f' x) x)
    (h₁ : Convex ℝ s)
    (h₂ : ∀ x : E, x ∈ s → ∀ y : E, y ∈ s → f x + @inner ℝ E _ (f' x) (y - x) ≤ f y) :
    ConvexOn ℝ s f := by
  sorry

theorem Convex_first_order_condition_iff' (h₁ : Convex ℝ s) (h : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ConvexOn ℝ s f ↔ ∀ x ∈ s, ∀ y ∈ s, f x + @inner ℝ E _ (f' x) (y - x) ≤ f y := by
  sorry

theorem Convex_monotone_gradient' (hfun: ConvexOn ℝ s f) (h : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, @inner ℝ E _ (f' x - f' y) (x - y) ≥ (0 : ℝ) := by
  sorry

theorem monotone_gradient_convex' (h₁ : Convex ℝ s) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x)
    (mono: ∀ x ∈ s, ∀ y ∈ s, @inner ℝ E _ (f' x - f' y) (x - y) ≥ (0 : ℝ)) : ConvexOn ℝ s f := by
  sorry

theorem monotone_gradient_iff_convex' (h₁ : Convex ℝ s) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x):
    ConvexOn ℝ s f ↔ ∀ x ∈ s, ∀ y ∈ s, @inner ℝ E _ (f' x - f' y) (x - y) ≥ (0 : ℝ) := by
  sorry

theorem monotone_gradient_convex {f' : E → (E →L[ℝ] ℝ)} (h₁ : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (mono : ∀ x ∈ s, ∀ y ∈ s, (f' x - f' y) (x - y) ≥ 0) : ConvexOn ℝ s f := by
  sorry

theorem montone_gradient_iff_convex {f' : E → (E →L[ℝ] ℝ)}
    (h₁ : Convex ℝ s) (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x):
    ConvexOn ℝ s f ↔  ∀ x ∈ s, ∀ y ∈ s, (f' x - f' y) (x - y) ≥ (0 : ℝ) := by
  sorry

end FirstOrderCondition_Gradient

section strict

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {f' : E → E} {s : Set E}

theorem monotone_gradient_strict_convex (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasGradientAt f (f' x) x)
    (mono: ∀ x ∈ s, ∀ y ∈ s, x ≠ y → @inner ℝ E _ (f' x - f' y) (x - y) > (0 : ℝ)) :
    StrictConvexOn ℝ s f := by
  sorry

theorem strict_convex_monotone_gradient (hf : ∀ x ∈ s, HasGradientAt f (f' x) x)
    (h₁ : StrictConvexOn ℝ s f ) :
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → @inner ℝ E _ (f' x - f' y) (x - y) > (0 : ℝ) := by
  sorry

theorem strict_convex_iff_monotone_gradient
    (hs: Convex ℝ s) (h : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → @inner ℝ E _ (f' x - f' y) (x - y) > (0 : ℝ))
    ↔ StrictConvexOn ℝ s f := by
  sorry

end strict
