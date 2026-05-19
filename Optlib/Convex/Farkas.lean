/-
Copyright (c) 2024 Shengyang Xu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu, Chenyi Li
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Optlib.Differential.Calculation
import Optlib.Convex.ClosedCone

/-!
# Farkas

## Main results

This file contains the proof of the Farkas lemma.
$p$ and $q \in \mathbb{N}$ Given sets of vectors $ \{a_i \in \mathbb{R}^n | i = 1, 2, \ldots, p\} $
and $ \{b_i \in \mathbb{R}^n | i = 1, 2, \ldots, q\} $,
and a vector $ c \in \mathbb{R}^n $, the following conditions are equivalent:

1. There does not exist a vector $ d \in \mathbb{R}^n $ such that:
   - $ d^T a_i = 0 $ for all $ i = 1, 2, \ldots, p $
   - $ d^T b_i \geq 0 $ for all $ i = 1, 2, \ldots, q $
   - $ d^T c < 0 $

2. The vector $ c $ can be expressed as a linear combination of the vectors
   $ a_i $ and $ b_i $ with coefficients $ \lambda_i $ and $ \mu_i $, respectively, where:
   - $ \lambda_i $ can be any real number for all $ i = 1, 2, \ldots, p $
   - $ \mu_i \geq 0 $ for all $ i = 1, 2, \ldots, q $
   - $ c = \sum_{i=1}^p \lambda_i a_i + \sum_{i=1}^q \mu_i b_i $

-/

variable {τ σ : Finset ℕ} {n : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin n)}
variable {b : ℕ → EuclideanSpace ℝ (Fin n)} {c : EuclideanSpace ℝ (Fin n)}


open Finset InnerProductSpace BigOperators

lemma polyhedra_iff_cone {σ : Finset ℕ} : ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    {z | ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ mu i • b i)} = cone σ b := by
  sorry

private lemma leq_tendsto_zero {a x : ℝ} (ha : a < 0) (h : ∀ t > 0, t * x > a) : 0 ≤ x := by
  by_contra h'; push_neg at h';
  have : 2 * a / x > 0 := by
    rw [← mul_div]; apply mul_pos; norm_num; apply div_pos_of_neg_of_neg ha h'
  specialize h (2 * a / x) this
  have : 2 * a / x * x = 2 * a := by
    ring_nf; simp; field_simp; rw [← mul_div, div_self (by linarith)]; linarith
  rw [this] at h; linarith

private lemma geq_tendsto_zero {a x : ℝ} (ha : a < 0) (h : ∀ t < 0, t * x > a) : 0 ≥ x := by
  by_contra h'; push_neg at h';
  have : 2 * a / x < 0 := by
    rw [← mul_div]; apply mul_neg_of_pos_of_neg; norm_num; apply div_neg_of_neg_of_pos ha h'
  specialize h (2 * a / x) this
  have : 2 * a / x * x = 2 * a := by ring_nf; simp; field_simp;
  rw [this] at h; linarith

private lemma decompose_pn : ∀ (lam : τ → ℝ), ∃ (lamp lamn : ℕ → ℝ),
    ∀ i : τ, (0 ≤ lamp i) ∧ (0 ≤ lamn i) ∧ (lam i = (lamp i) - (lamn i)) := by
  intro lam
  let lamp : ℕ → ℝ := fun j => if h : (j ∈ τ) then if _ : (0 ≤ lam ⟨j, h⟩) then lam ⟨j, h⟩ else 0 else 0
  let lamn : ℕ → ℝ := fun j => if h : (j ∈ τ) then if _ : (0 ≤ lam ⟨j, h⟩) then 0 else -lam ⟨j, h⟩ else 0
  use lamp; use lamn
  intro i
  by_cases hpos : 0 ≤ lam i
  · simp [lamp, lamn, hpos]
  · simp [lamp, lamn, hpos]; linarith

private lemma shift_sum (τ : Finset ℕ) (m : ℕ) (f : ℕ → EuclideanSpace ℝ (Fin n)) :
    (∑ i : τ, f i) = (∑ i : (Finset.image (fun x => x + m) τ), f (i - m)) := by
  sorry

private lemma shift_not_in (τ : Finset ℕ) (m : ℕ) (hm : ∀ i : τ, i < m): m ∉ τ := by
  sorry

private lemma mem_lt_m {m i : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : (i ∈ (τ ∪ σ)) → (i < m) := by
  intro iin; rw [hm]; apply Nat.lt_succ_of_le
  apply Finset.le_max' (τ ∪ σ) i iin

private lemma exist_of_mem_shift {x m : ℕ} {τ : Finset ℕ}:
    x ∈ (Finset.image (fun x => x + m) τ) → ∃ a : τ, x = a + m := by
  simp; intro a ain eq; use a; use ain; rw [← eq]

private lemma s_inter_t1_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : σ ∩ (Finset.image (fun x => x + m) τ) = ∅ := by
  sorry

private lemma s_inter_t2_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : σ ∩ (Finset.image (fun x => x + 2 * m) τ) = ∅ := by
  sorry

private lemma t1_inter_t2_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) :
    (Finset.image (fun x => x + m) τ) ∩ (Finset.image (fun x => x + 2 * m) τ) = ∅ := by
  sorry

lemma general_polyhedra_is_polyhedra_empty (τ σ : Finset ℕ) (he : ¬(τ ∪ σ).Nonempty) :
    ∀ (a : ℕ → EuclideanSpace ℝ (Fin n)), ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    ∃ μ c, {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)} =
    cone μ c := by
  sorry

lemma general_polyhedra_is_polyhedra_ne (τ σ : Finset ℕ) (he : (τ ∪ σ).Nonempty) :
    ∀ (a : ℕ → EuclideanSpace ℝ (Fin n)), ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    ∃ μ c, {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)} =
    cone μ c := by
  sorry

lemma general_polyhedra_is_polyhedra (τ σ : Finset ℕ) :
    ∀ (a : ℕ → EuclideanSpace ℝ (Fin n)), ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    ∃ μ c, {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)} =
    cone μ c := by
  by_cases trivial : (τ ∪ σ).Nonempty
  · exact general_polyhedra_is_polyhedra_ne τ σ trivial
  · exact general_polyhedra_is_polyhedra_empty τ σ trivial

lemma general_polyhedra_is_closed : IsClosed {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ),
    (∀ i, 0 ≤ mu i) ∧ z = Finset.sum univ (fun i ↦ lam i • a i) +
    Finset.sum univ (fun i ↦ mu i • b i)} := by
  rcases general_polyhedra_is_polyhedra τ σ a b with ⟨μ, c, h⟩
  rw [h]; exact closed_conic μ c

theorem Farkas :
  (∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ c =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)) ↔
    ¬ (∃ (z : EuclideanSpace ℝ (Fin n)), (∀ i ∈ τ, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (a i) z = (0 : ℝ))
    ∧ (∀ i ∈ σ, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b i) z ≥ (0 : ℝ))
    ∧ (@inner ℝ (EuclideanSpace ℝ (Fin n)) _ c z < (0 : ℝ))) := by
  sorry
