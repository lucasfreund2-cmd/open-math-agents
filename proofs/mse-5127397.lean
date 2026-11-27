import OMAStatements.S_mse_5127397
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Counterexample to the proposed ultrametric characterization

Credit: @lucasfreund2-cmd
Source: Mathematics Stack Exchange question 5127397.
David Gao proposed the sum norm on two copies of a p-adic field in a comment
on 9 March 2026; the question author confirmed this counterexample on 15 March.
The proof below uses the 2-adic field, preserves ordinary partial-sum convergence,
and refutes the strong triangle inequality for the given norm.
-/

open Filter Topology

namespace MSE5127397Proof

open OMA.S_mse_5127397

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev CounterField := Padic 2
abbrev CounterSpace := WithLp 1 (CounterField × CounterField)

theorem terms_tendsto_zero_of_seriesConverges
    {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) (hu : SeriesConverges u) :
    Tendsto u atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := hu
  simpa only [Function.comp_apply, Finset.sum_range_succ,
    add_sub_cancel_left, sub_self] using
      (hs.comp (tendsto_add_atTop_nat 1)).sub hs

theorem counterSpace_not_ultrametric :
    ¬ ∀ x y : CounterSpace, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  intro h
  have bad := h
    (WithLp.toLp 1 ((1 : CounterField), 0))
    (WithLp.toLp 1 ((0 : CounterField), 1))
  norm_num [WithLp.prod_norm_eq_of_L1] at bad

theorem counterSpace_summable_iff_tendsto_zero (u : ℕ → CounterSpace) :
    Summable u ↔ Tendsto u atTop (𝓝 0) := by
  constructor
  · intro hu
    simpa only [Nat.cofinite_eq_atTop] using hu.tendsto_cofinite_zero
  · intro hu
    let e := WithLp.prodContinuousLinearEquiv 1 CounterField CounterField CounterField
    apply e.summable.mp
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop, map_zero, Function.comp_def] using
      (e.continuous.tendsto (0 : CounterSpace)).comp hu

theorem counterSpace_series_criterion (u : ℕ → CounterSpace) :
    SeriesConverges u ↔ Tendsto u atTop (𝓝 0) := by
  constructor
  · exact terms_tendsto_zero_of_seriesConverges u
  · intro hu
    exact ⟨∑' n, u n,
      ((counterSpace_summable_iff_tendsto_zero u).mpr hu).hasSum.tendsto_sum_nat⟩

theorem counterSpace_complete : CompleteSpace CounterSpace := inferInstance

end MSE5127397Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5127397.main) := by
  intro h
  exact MSE5127397Proof.counterSpace_not_ultrametric
    (h MSE5127397Proof.CounterField MSE5127397Proof.CounterSpace
      MSE5127397Proof.counterSpace_series_criterion).2

