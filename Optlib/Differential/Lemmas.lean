/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Optlib.Differential.Calculation

/-!
# Lemmas

## Main results

This file contains the following parts of basic properties of continuous and differentiable lemmas
* the equivalent definition of continuous functions
* the equivalent definition of fderiv and gradient
* the deriv of composed function on a segment
* the gradient of special functions with inner product and norm
* the taylor expansion of a differentiable function locally
* the langrange interpolation of a differentiable function
-/
section continuous

variable {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {x y x' : E}

open Set InnerProductSpace Topology Filter
set_option linter.unusedVariables false
/-
  The epigraph of under-bounded lowersemicontinuous function is closed
-/
lemma bounded_lowersemicontinuous_to_epi_closed (f : E → ℝ) (hc : LowerSemicontinuousOn f univ)
    (underboundf : ∃ b : ℝ, ∀ x : E, b ≤ f x) :
    IsClosed {p : (E × ℝ) | f p.1 ≤ p.2} := by
  sorry

theorem ContinuousAt_Convergence (h : ContinuousAt f x) : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  rw [continuousAt_def] at h
  intro ε epos
  let A := Metric.ball (f x) ε
  specialize h A (Metric.ball_mem_nhds (f x) epos)
  rw [Metric.mem_nhds_iff] at h
  rcases h with ⟨δ, dpos, h⟩
  use (δ /2); constructor
  exact half_pos dpos
  intro x' x1le
  have H1: x' ∈ Metric.ball x δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub]
    apply lt_of_le_of_lt x1le
    exact half_lt_self dpos
  exact LT.lt.le (h H1)

theorem Convergence_ContinuousAt (h: ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
    ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε) :
  ContinuousAt f x := by
  rw [continuousAt_def]
  intro A amem
  rw [Metric.mem_nhds_iff] at amem
  rcases amem with ⟨ε, epos, bmem⟩
  specialize h (ε / 2) (half_pos epos)
  rcases h with ⟨δ , dpos, h⟩
  rw [Metric.mem_nhds_iff]
  use δ; constructor
  exact dpos
  rw [Set.subset_def]
  intro x' x1mem
  have : ‖x - x'‖ ≤ δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub] at x1mem
    exact LT.lt.le x1mem
  specialize h x' this
  have H1: f x' ∈  Metric.ball (f x) ε := by
    rw [Metric.ball, Set.mem_setOf, dist_eq_norm_sub]
    apply lt_of_le_of_lt h (half_lt_self epos)
  exact bmem H1

theorem ContinuousAt_iff_Convergence: ContinuousAt f x ↔ ∀ ε > (0 : ℝ),
    ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  constructor
  apply ContinuousAt_Convergence
  apply Convergence_ContinuousAt

lemma continuous (h : ContinuousAt f x) : ∀ ε > 0, ∃ δ > 0, ∀ (y : E), ‖y - x‖ < δ
    → ‖f y - f x‖ < ε := by
  rw [ContinuousAt_iff_Convergence] at h
  intro a ha; specialize h (a / 2) (by linarith); rcases h with ⟨δ, ⟨h₁, h₂⟩⟩
  use δ; constructor; assumption
  intro y hy;rw [norm_sub_rev] at hy; specialize h₂ y (by linarith); linarith

lemma continuous_positive_neighborhood (h : ContinuousAt f x) (hx : f x > 0) :
    ∃ ε > (0 : ℝ), ∀ (y : E), ‖y - x‖ < ε → f y > 0 := by
  obtain ⟨δ, hδ1, hδ2⟩ := continuous h (f x / 2) (half_pos hx)
  use δ; constructor; assumption
  intro y hy; specialize hδ2 y hy
  simp at hδ2;
  obtain hc := neg_lt_of_abs_lt hδ2
  linarith

lemma continuous_positive_direction [NormedSpace ℝ E] (h : ContinuousAt f x) (hx : f x > 0) (v : E) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Icc 0 ε, f (x + t • v) > 0 := by
  sorry

end continuous

section derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {l a : ℝ} {f' : E → (E →L[ℝ] ℝ)} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}

theorem deriv_function_comp_segment (x y : E) (h₁ : ∀ x₁ : E, HasFDerivAt f (f' x₁) x₁) :
    ∀ t₀ : ℝ , HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)))
    ((fun t : ℝ ↦ (f' (x + t • (y - x)) (y - x))) t₀) t₀ := by
  let h := fun t : ℝ ↦ x + t • (y - x)
  have h_deriv : ∀ t : ℝ,  HasDerivAt h (y - x) t := by
    intro t
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have : (fun z => h (t + z) - h t - z • (y - x)) = (fun z => 0) := by
      ext z; simp [h]
      rw [add_smul, add_comm, ← add_sub, sub_self, add_zero, sub_self]
    simp [this]
  have H₂: ∀ t₀ : ℝ , HasDerivAt (f ∘ h) (f' (x + t₀ • (y - x)) (y - x)) t₀ := by
    intro t₀
    apply HasFDerivAt.comp_hasDerivAt
    · apply h₁ (x + t₀ • (y - x))
    · apply h_deriv t₀
  intro t₀
  apply H₂ t₀

theorem HasFDeriv_Convergence (h: HasFDerivAt f (f' x) x) :
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
    → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  sorry

theorem Convergence_HasFDeriv (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
    ‖x - x'‖ ≤ δ → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖) :
      HasFDerivAt f (f' x) x := by
  sorry

theorem HasFDeriv_iff_Convergence_Point {f'x : (E →L[ℝ] ℝ)}:
  HasFDerivAt f (f'x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
     ‖x - x'‖ ≤ δ → ‖f x' - f x - (f'x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  · intro h
    apply HasFDeriv_Convergence
    exact h
  · apply Convergence_HasFDeriv

theorem HasFDeriv_iff_Convergence :
  HasFDerivAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
     ‖x - x'‖ ≤ δ → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasFDeriv_Convergence
  apply Convergence_HasFDeriv

end derivative

section gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open Topology InnerProductSpace Set Filter Tendsto

theorem HasGradient_Convergence (h : HasGradientAt f (f' x) x) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E, ‖x - x'‖ ≤ δ
    → ‖f x' - f x - @inner ℝ E _ (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  sorry

theorem Convergence_HasGradient (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
    ‖x - x'‖ ≤ δ → ‖f x' - f x - @inner ℝ E _ (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖) :
    HasGradientAt f (f' x) x := by
  sorry

theorem HasGradient_iff_Convergence_Point {f'x : E}:
      HasGradientAt f f'x x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
     ‖x - x'‖ ≤ δ → ‖f x' - f x - @inner ℝ E _ f'x (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  sorry

theorem HasGradient_iff_Convergence :
      HasGradientAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
      ‖x - x'‖ ≤ δ → ‖f x' - f x - @inner ℝ E _ (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  sorry

lemma gradient_norm_sq_eq_two_self (x : E) :
    HasGradientAt (fun x ↦ ‖x‖ ^ 2) ((2 : ℝ) • x) x := by
  sorry

lemma gradient_of_inner_const (x : E) (a : E):
    HasGradientAt (fun x ↦ (@inner ℝ E _ a x : ℝ)) a x := by
  sorry

lemma gradient_of_const_mul_norm (l : ℝ) (z : E) :
    HasGradientAt (fun (x : E) => l / 2 * ‖x‖ ^ 2) (l • z) z := by
  sorry

lemma gradient_of_sq : ∀ u : E, HasGradientAt (fun u ↦ ‖u - x‖ ^ 2 / 2) (u - x) u := by
  sorry

lemma sub_normsquare_gradient (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (m : ℝ):
    ∀ x ∈ s, HasGradientAt (fun x ↦ f x - m / 2 * ‖x‖ ^ 2) (f' x - m • x) x := by
  intro x xs
  apply HasGradientAt.sub
  . apply hf x xs
  . have u := HasGradientAt.const_smul (gradient_norm_sq_eq_two_self x) (m / 2)
    simp at u
    rw [smul_smul, div_mul_cancel_of_invertible] at u
    apply u

/-
If the function f is first-order continuously differentiable, then
the gradient of f is continuous.
-/
lemma gradient_continuous_of_contdiffat {x : E} (f : E → ℝ)
    (h : ContDiffAt ℝ 1 f x) : ContinuousAt (fun x ↦ gradient f x) x := by
  rw [contDiffAt_one_iff] at h
  rcases h with ⟨f', ⟨u, ⟨hu1, ⟨hu2, hu3⟩⟩⟩⟩
  have : Set.EqOn (fun y ↦ (LinearIsometryEquiv.symm (toDual ℝ E)) (f' y))
      (fun y ↦ gradient f y) u := by
    intro z hz; dsimp
    specialize hu3 z hz
    rw [hasFDerivAt_iff_hasGradientAt] at hu3
    have : HasGradientAt f (gradient f z) z :=
      DifferentiableAt.hasGradientAt hu3.differentiableAt
    exact HasGradientAt.unique hu3 this
  have hcon1 : ContinuousOn (fun y ↦ (LinearIsometryEquiv.symm (toDual ℝ E)) (f' y)) u :=
    Continuous.comp_continuousOn (LinearIsometryEquiv.continuous _) hu2
  rw [(continuousOn_congr this)] at hcon1
  apply ContinuousOn.continuousAt hcon1 hu1

lemma gradient_continuous_of_contdiffon {x : E} {ε : ℝ} (f : E → ℝ)
    (he : ε > 0) (hf : ContDiffOn ℝ 1 f (Metric.ball x ε)) :
    ContinuousAt (fun x ↦ gradient f x) x := by
  let s := Metric.ball x ε
  have h : ContDiffAt ℝ 1 f x := by
    apply ContDiffOn.contDiffAt hf
    rw [mem_nhds_iff]; use s
    exact ⟨Eq.subset rfl, ⟨Metric.isOpen_ball, Metric.mem_ball_self he⟩⟩
  exact gradient_continuous_of_contdiffat f h

end gradient

section expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open InnerProductSpace Set
/-
  For any function f : E → ℝ, where E is a InnerProduct space, and for any point x in E and vector p in E,
  if f has a gradient at every point in its domain, then there exists a real number t such that t is
  greater than 0 and less than 1, and f(x + p) is equal to f(x) plus the inner product of the gradient of
  f at (x + t * p) with p.
-/

lemma expansion (hf : ∀ x : E, HasGradientAt f (f' x) x) (x p : E) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + @inner ℝ E _ (f' (x + t • p)) p := by
  sorry

lemma general_expansion (x p : E) (hf : ∀ y ∈ Metric.closedBall x ‖p‖, HasGradientAt f (f' y) y) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + @inner ℝ E _ (f' (x + t • p)) p := by
  sorry

theorem lagrange (hs : Convex ℝ s) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, ∃ c : ℝ, c ∈ Set.Ioo 0 1 ∧
    @inner ℝ E _ (f' (x + c • (y - x))) (y - x) = f y - f x := by
  sorry

end expansion

section ProdLp

variable {E F : Type*}
variable [NormedAddCommGroup E]
variable [NormedAddCommGroup F]
variable {x : E} {y : F} {z : WithLp 2 (E × F)}

open Set Bornology Filter BigOperators Topology

lemma fst_norm_le_prod_L2 (z : WithLp 2 (E × F)) : ‖z.fst‖ ≤ ‖z‖ := by
  sorry

lemma snd_norm_le_prod_L2 (z : WithLp 2 (E × F)) : ‖z.snd‖ ≤ ‖z‖ := by
  sorry

lemma prod_norm_le_block_sum_L2 (z : WithLp 2 (E × F)) : ‖z‖ ≤ ‖z.fst‖ + ‖z.snd‖ := by
  sorry

lemma norm_prod_right_zero (x : E) :
    ‖((WithLp.equiv 2 (E × F)).symm (x, (0 : F)))‖ = ‖x‖ := by
  sorry

lemma norm_prod_left_zero (y : F):
    ‖((WithLp.equiv 2 (E × F)).symm ((0 : E), y))‖ = ‖y‖ := by
  sorry

end ProdLp

noncomputable section ProdLp_diff

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {x : E} {y : F} {z : WithLp 2 (E × F)}

instance instNormedSpaceProdL2 : NormedSpace ℝ (WithLp 2 (E × F)) :=
  inferInstance

lemma instIsBoundedLinearMapL2equiv :
    IsBoundedLinearMap ℝ ((WithLp.equiv 2 (E × F)).symm : E × F → WithLp 2 (E × F)) := by
  sorry

end ProdLp_diff
