/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He, Chenyi Li, Zichen Wang
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Basic


section

variable {E : Type*} [SeminormedAddCommGroup E]

variable {f : E → ℝ} {x : E} {s : Set E}

open Set

lemma EpigraphInterior_existence (hc : ContinuousOn f (interior s)) (hx : x ∈ interior s) :
    ∀ t > f x, (x, t) ∈ interior {p : E × ℝ| p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  sorry

lemma mem_epi_frontier : ∀ y ∈ interior s, (y, f y) ∈
    frontier {p : E × ℝ| p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  intro y ys
  constructor
  · exact subset_closure ⟨interior_subset ys, Eq.ge rfl⟩
  by_contra h
  simp only [mem_interior] at h
  obtain ⟨t, ⟨st, ⟨opent, ht⟩⟩⟩ := h
  simp only [Metric.isOpen_iff] at opent
  obtain ⟨ε, εpos, ballmem⟩ := opent (y, f y) ht
  have : (y, f y - ε / 2) ∈ t := by
    apply ballmem
    simp only [Metric.mem_ball, dist_eq_norm]
    calc
      ‖(y, f y - ε / 2) - (y, f y)‖ = ‖((0 : E), - (ε / 2))‖ := by
        apply congrArg norm (by simp only [Prod.mk_sub_mk, sub_self]; ring_nf)
      _ = ε / 2 := by simp [norm]; exact LT.lt.le (half_pos εpos)
      _ < ε := half_lt_self εpos
  obtain ⟨_, h2⟩ := st this
  simp at h2; linarith

lemma Continuous_epi_open {f₁ : E → ℝ} (hcon : ContinuousOn f₁ univ) :
    IsOpen {(x, y) : E × ℝ | y > f₁ x} := by
  sorry

end
noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {x : E} {s : Set E}

open Filter

/-- Subgradient of functions --/
def Banach_HasSubgradientAt (f : E → ℝ) (g : E →L[ℝ] ℝ) (x : E) : Prop :=
  ∀ y, f y ≥ f x + g (y - x)

def Banach_HasSubgradientWithinAt (f : E → ℝ) (g : E →L[ℝ] ℝ) (s : Set E) (x : E) : Prop :=
  ∀ y ∈ s, f y ≥ f x + g (y - x)

/-- Subderiv of functions --/
def Banach_SubderivAt (f : E → ℝ) (x : E) : Set (E →L[ℝ] ℝ) :=
  {g : E →L[ℝ] ℝ| Banach_HasSubgradientAt f g x}

def Banach_SubderivWithinAt (f : E → ℝ) (s : Set E) (x : E) : Set (E →L[ℝ] ℝ) :=
  {g : E →L[ℝ] ℝ| Banach_HasSubgradientWithinAt f g s x}

def Epi (f : E → ℝ) (s : Set E) : Set (E × ℝ) :=
  {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}

theorem Banach_SubderivWithinAt.Nonempty (hf : ConvexOn ℝ s f)
    (hc : ContinuousOn f (interior s)) (hx : x ∈ interior s) :
    Set.Nonempty (Banach_SubderivWithinAt f s x) := by
  sorry
