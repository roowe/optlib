import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Optlib.Differential.Calculation
import Optlib.Convex.Farkas
import Optlib.Differential.Lemmas

open InnerProductSpace Set BigOperators
set_option linter.unusedVariables false

noncomputable section

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {τ σ : Finset ℕ}

structure Constrained_OptimizationProblem (E : Type _) (τ σ : Finset ℕ) where
  domain : Set E
  equality_constraints : (i : ℕ) → E → ℝ
  inequality_constraints : (j : ℕ) → E → ℝ
  eq_ine_not_intersect : τ ∩ σ = ∅
  objective : E → ℝ

namespace Constrained_OptimizationProblem

variable {p : Constrained_OptimizationProblem E τ σ} {x : E}

open Topology InnerProductSpace Set Filter

def FeasPoint (point : E) : Prop :=
  point ∈ p.domain ∧ (∀ i ∈ τ, p.equality_constraints i point = 0)
  ∧ (∀ j ∈ σ, p.inequality_constraints j point ≥ 0)

def FeasSet : Set E :=
  {point | p.FeasPoint point}

def Global_Minimum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsMinOn p.objective p.FeasSet point

def Global_Maximum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsMaxOn p.objective p.FeasSet point

def Local_Minimum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsLocalMinOn p.objective p.FeasSet point

def Local_Maximum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsLocalMaxOn p.objective p.FeasSet point

def Strict_Local_Minimum (point : E) : Prop :=
  (p.FeasPoint point) ∧ (∃ ε > 0, ∀ y, p.FeasPoint y → y ∈ Metric.ball point ε → y ≠ point
  → p.objective point > p.objective y)

def active_set (point : E) : Finset ℕ :=
  τ ∪ σ.filter fun i : ℕ ↦ p.inequality_constraints i point = (0 : ℝ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma equality_constraint_active_set (point : E) : τ ⊆ p.active_set point :=
  fun i itau ↦ Finset.mem_union_left _ itau

def linearized_feasible_directions (point : E) : Set E :=
  {v | (∀ i ∈ τ, ⟪gradient (p.equality_constraints i) point, v⟫_ℝ = (0 : ℝ))
    ∧ ∀ j ∈ σ ∩ (p.active_set point), ⟪gradient (p.inequality_constraints j) point, v⟫_ℝ ≥ (0 : ℝ)}

def LICQ (point : E) : Prop :=
  LinearIndependent ℝ (fun i : p.active_set point ↦
    if i.1 ∈ τ then gradient (p.equality_constraints i.1) point else gradient (p.inequality_constraints i.1) point)

def Lagrange_function :=
  fun (x : E) (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) ↦ (p.objective x)
    - (Finset.sum Finset.univ fun i ↦ (lambda1 i) * p.equality_constraints i x)
    - (Finset.sum Finset.univ fun j ↦ (lambda2 j) * p.inequality_constraints j x)

section linear

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsLinear (f : E → ℝ) : Prop := ∃ a, ∃ b, f = fun x ↦ (@inner ℝ E _ x a : ℝ) + b

lemma IsLinear_iff (f : E → ℝ) : IsLinear f ↔ ∃ a b, f = fun x ↦ (@inner ℝ E _ x a : ℝ) + b := by
  rfl

lemma IsLinear_iff' (f : E → ℝ) : IsLinear f ↔ ∃ a b, f = fun x ↦ (@inner ℝ E _ a x : ℝ) + b := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by ext x; simp [real_inner_comm]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by ext x; simp [real_inner_comm]⟩

end linear

def LinearCQ (point : E) : Prop :=
  (∀ i ∈ (p.active_set point ∩ τ), IsLinear (p.equality_constraints i)) ∧
  ∀ i ∈ (p.active_set point ∩ σ), IsLinear (p.inequality_constraints i)

end Constrained_OptimizationProblem

end
