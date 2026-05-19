/-
Copyright (c) 2024 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Optlib.Function.L1Space

/-!
# Finite-Dimensional Convex Functions and Their Lipschitz Properties

Each convex function on an open convex subset of FiniteDimensional space
is Lipschitz continuous, so that continuous.

During proving , the real difficulty lies in “LocallyUpperBounded”.
Given a convex open set s in a finite dimensional spac , and f is convex on s ,
it wants us to find a convex open subset t of s ,which is
a neighborhood of x and f is upper bounded on t.
We use the interior of the convex hull t formed by the vectors which
the basis multiplied by the appropriate coefficient to make it a subset (int t) of s.

The remaining difficulty is to prove x ∈ int t which
is equivalent to proving that ∃ open set u ⊆ t.
The crucial point is that we use the ball in l₁ space as u.

## Main Results

* `Lipschitz_of_UpperBounded` :Let X be a normed space, x₀ ∈ X, r > 0.
Let f : B(x₀, r) → ℝ be a convex function.
If f(x) ≤ m on B(x₀, r) and ε ∈ (0, r),then f is  Lipschitz on B(x₀, r − ε).

* `LocallyLipschitzOn_of_UpperBounded`: Let X be a normed space, x₀ ∈ X, r > 0.
Let f : B(x₀, r) → ℝ  be a convex function.
If f is upper bounded on a open subset of s , then f is locally Lipschitz on s

* `LocallyUpperBounded` : Finite dimensional convex functions are locally upper bounded
on convex open sets. Let s is open convex set and f : s → ℝ be a convex function,
then there exist a convex open set in s and f is upperbounded on s.

* `FiniteDimensionalConvexFunctionsLocallyLipschitz` : Each convex function on an open convex
subset of FiniteDimensional space is locally Lipschitz

* `FiniteDimensionalConvexFunctionsContinous` : Each convex function on an open convex subset of FiniteDimensional space
is continuous

-/
open Set InnerProductSpace Topology Filter Metric Bornology Real FiniteDimensional

open scoped Pointwise

/-! ### Boundedness of convex function in a normed space -/

section Boundedness


variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {x₀ : X}{r : ℝ}{f : X → ℝ}

/--
Let X be a normed space, x₀ ∈ X, r > 0.Let f : B(x₀, r) → R be a convex function.
If f is upperbounded on B(x₀, r), then bounded on B(x₀, r).
-/
lemma Bounded_of_UpperBounded (hf : ConvexOn ℝ (ball x₀ r) f)
    (f_upperbounded: BddAbove (f '' (ball x₀ r))) : IsBounded (f '' (ball x₀ r)) := by
  sorry

/--
Let X be a normed space, x₀ ∈ X, r > 0.Let f : B(x₀, r) → R be a convex function.
If f is bounded on B(x₀, r) and ε ∈ (0, r), then f is Lipschitz on B(x₀, r − ε).
-/
lemma Lipschitz_of_Bounded [T0Space X](hf : ConvexOn ℝ (ball x₀ r) f)
    (f_bounded: IsBounded (f '' (ball x₀ r)))
    {ε : ℝ}(hε :0 < ε ∧ ε < r): ∃ K , LipschitzOnWith K f (ball x₀ (r - ε)) := by
  sorry

/--
Let X be a normed space, x₀ ∈ X, r > 0.Let f : B(x₀, r) → R be a convex function.
If f is upperbounded on B(x₀, r) and ε ∈ (0, r)
then f is Lipschitz on B(x₀, r − ε).
-/
theorem Lipschitz_of_UpperBounded [T0Space X](hf : ConvexOn ℝ (ball x₀ r) f)
    (f_upperbounded: BddAbove (f '' (ball x₀ r)))
    {ε : ℝ}(hε :0 < ε ∧ ε < r): ∃ K , LipschitzOnWith K f (ball x₀ (r - ε)) := by
  apply Lipschitz_of_Bounded hf _ hε
  apply Bounded_of_UpperBounded hf f_upperbounded

/--
If f is upper bounded on a open subset of s ,
then f is locally Lipschitz on s
-/
theorem LocallyLipschitzOn_of_UpperBounded [T0Space X]{s : Set X}(hs : IsOpen s)
    (f_upperbounded : BddAbove (f '' s)) (f_convex : ConvexOn ℝ s f):
    LocallyLipschitzOn s f := by
  dsimp [LocallyLipschitzOn]
  intro x hx
  rw[exists_comm]
  rw[Metric.isOpen_iff] at hs
  rcases hs x hx with ⟨r , hr⟩
  have : ball x (r / 2) ∈ 𝓝[s] x := by
    apply mem_nhdsWithin_of_mem_nhds
    apply ball_mem_nhds x
    linarith
  use ball x (r - r / 2)
  rw[exists_and_left]
  constructor
  · have eq_r : r - r / 2 = r / 2 := by linarith
    rw[eq_r]
    apply this
  · apply Lipschitz_of_UpperBounded
    apply ConvexOn.subset f_convex hr.2
    exact convex_ball x r
    apply BddAbove.mono _ f_upperbounded
    apply image_mono hr.2
    norm_num
    exact hr.1

end Boundedness

/-! ### Locally Boundedness of convex function in a finite dimensional space -/

section LocallyBoundedness

variable {α : Type*}
    [NormedAddCommGroup α] [InnerProductSpace ℝ α] [FiniteDimensional ℝ α]
    {f : α → ℝ}{s : Set α}
/--
Let X be a finite dimensional space.Let s is open convex set and f : s → R be a convex function.
Then ∃ open convex set t which contain x , and f is upperbounded on t.
-/
lemma LocallyUpperBounded (hs_convex : Convex ℝ s)(hs_isopen : IsOpen s)
    (hf : ConvexOn ℝ s f) : ∀ x ∈ s , ∃ t ∈ 𝓝[s] x ,Convex ℝ t ∧ IsOpen t ∧ BddAbove (f '' t) := by
  sorry

lemma LocallyLipschitz_of_LocallyUpperBounded (hs : IsOpen s)
    (h : ∀ x ∈ s , ∃ t ∈ 𝓝[s] x , Convex ℝ t ∧ IsOpen t ∧ BddAbove (f '' t))
    (hf : ConvexOn ℝ s f)
    : LocallyLipschitzOn s f := by
  dsimp [LocallyLipschitzOn]
  intro x hx
  rcases h x hx with ⟨t , ht⟩
  have t_isOpen := ht.2.2.1
  have isopen : IsOpen (t ∩ s) := IsOpen.inter t_isOpen hs
  have x_pos : x ∈ (t ∩ s) := by
    apply mem_inter _ hx
    rcases mem_nhdsWithin.1 ht.1 with ⟨u,hu⟩
    exact hu.2.2 (mem_inter hu.2.1 hx)
  rw[Metric.isOpen_iff] at isopen
  rcases isopen x x_pos with ⟨r , hr⟩
  rw[exists_comm]
  have : ball x (r / 2) ∈ 𝓝[s] x := by
    apply mem_nhdsWithin_of_mem_nhds
    apply ball_mem_nhds x
    linarith
  use ball x (r - r / 2)
  rw[exists_and_left]
  constructor
  · have eq_r : r - r / 2 = r / 2 := by linarith
    rw[eq_r];
    exact this
  · apply Lipschitz_of_UpperBounded
    have ball_s: ball x r ⊆ s := Set.Subset.trans hr.2 inter_subset_right
    apply ConvexOn.subset hf ball_s
    apply convex_ball x r
    apply BddAbove.mono _ ht.2.2.2
    have ball_t: ball x r ⊆ t := Set.Subset.trans hr.2 inter_subset_left
    apply image_mono ball_t
    norm_num
    exact hr.1

end LocallyBoundedness

/-! ### Continuity of convex function in a finite dimensional space -/

section Continuity

variable {α : Type*}{β : Type*}
    [NormedAddCommGroup α] [InnerProductSpace ℝ α] [FiniteDimensional ℝ α]
    {f : α → ℝ}{s : Set α}

/-
Each convex function on an open convex subset of FiniteDimensional space
is locally Lipschitz
-/
theorem FiniteDimensionalConvexFunctionsLocallyLipschitz
    (hs_convex : Convex ℝ s)(hs_isopen : IsOpen s)(hf : ConvexOn ℝ s f)
    : LocallyLipschitzOn s f :=by
  apply LocallyLipschitz_of_LocallyUpperBounded hs_isopen _ hf
  apply LocallyUpperBounded hs_convex hs_isopen hf

/-
Each convex function on an open convex subset of FiniteDimensional space
is continuous
-/
theorem FiniteDimensionalConvexFunctionsContinous
    (hs_convex : Convex ℝ s)(hs_isopen : IsOpen s)(hf : ConvexOn ℝ s f)
    : ContinuousOn f s := by
  apply LocallyLipschitzOn.continuousOn
  apply FiniteDimensionalConvexFunctionsLocallyLipschitz hs_convex hs_isopen hf

end Continuity
