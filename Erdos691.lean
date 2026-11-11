import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Data.Pi.Interval

/-!
Erdős 691 — the adaptive divisor-closed test criterion.
Private formalization, prepared at the user's request.

Main declarations
* Erdos691.Adaptive.erdos691
* Erdos691.Adaptive.fullSolution

The classical Davenport–Erdős finite-approximation dependency is adapted from
https://github.com/yuta0x89/ErdosProblems/blob/1aa94199fd3874e25b2126a0ff153e144e3e9c04/Erdos691.lean
The private source copy and adaptation diff are retained in evidence/.
The adaptive criterion, probability construction, and arithmetic bridges follow
the mathematical proposal with SHA256
381994afe79c3d63e31868e367bbc6f077d9a81491b5b95b843a02485870e16b.
-/

/-! Source module DavenportErdos -/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology
open Filter Set Asymptotics Real

/-!
# Erdős Problem 691

This file is an axiom-free integration of the formalization around Erdős problem 691.
It begins with a self-contained proof of the analytic input used in the main argument,
and later transports that result to the shifted Dirichlet conventions used for the final
finite-approximation theorem.

The first part, in namespace `Erdos691.DensityToDirichlet`, proves the following Hardy-style
Tauberian fact.

> If `B ⊆ ℕ` has natural density `δ`, then
> `μ s B → δ` as `s ↓ 1`, where
> `μ s B = (∑_{n∈B} n^{-s}) / ζ(s)`.

The key steps are:

1. encode `B` by a coefficient sequence `coeff B : ℕ → ℝ` with `coeff B 0 = 0`;
2. identify partial sums of `coeff B` with the counting function `countUpTo B`;
3. use Abel summation (`Mathlib/NumberTheory/AbelSummation`) with
   `f x = x^{-s}` and `c = coeff B`;
4. split the counting function into `δ x + err x`;
5. prove the error integral is `o ((s - 1)⁻¹)` by the epsilon-`T` argument from TeX;
6. use the mathlib theorem
   `tendsto_sub_mul_tsum_nat_rpow : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n, 1 / (n : ℝ)^s) (𝓝[>] 1) (𝓝 1)`
   for the denominator.

This part keeps all objects on `ℝ`; this avoids repeated coercions to `ℂ`.
-/

namespace Erdos691
namespace DensityToDirichlet

/-- Count elements of `B` in `[1,N]`.  We deliberately ignore `0`. -/
noncomputable def countUpTo (B : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun n => n ∈ B).card

/-- Density sequence, indexed by `N+1` so that the denominator never vanishes. -/
noncomputable def densSeq (B : Set ℕ) (N : ℕ) : ℝ :=
  (countUpTo B (N + 1) : ℝ) / (N + 1 : ℝ)

/-- `B` has natural density `δ`. -/
def HasNatDensity (B : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (densSeq B) atTop (𝓝 δ)

/-- Coefficient sequence for Abel summation.

It is the indicator of `B`, but forced to vanish at `0`, so that it is compatible with the
statements in `Mathlib.NumberTheory.AbelSummation`. -/
noncomputable def coeff (B : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if 0 < n ∧ n ∈ B then 1 else 0

/-- Counting function on real inputs, obtained by flooring. -/
noncomputable def countingFn (B : Set ℕ) (x : ℝ) : ℝ :=
  countUpTo B ⌊x⌋₊

/-- Error term `r(x) = B(x) - δx`. -/
noncomputable def err (B : Set ℕ) (δ : ℝ) (x : ℝ) : ℝ :=
  countingFn B x - δ * x

/-- Numerator of the Dirichlet density `μ_s(B)`.

The `n = 0` term is automatically zero because `coeff B 0 = 0`. -/
noncomputable def numerator (s : ℝ) (B : Set ℕ) : ℝ :=
  ∑' n : ℕ, coeff B n / (n : ℝ) ^ s

/-- Denominator of the Dirichlet density `μ_s(B)`.
This is the standard zeta-series, with the harmless `n = 0` term included. -/
noncomputable def zetaDenom (s : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (n : ℝ) ^ s

/-- Hardy's smoothed density attached to `B`. -/
noncomputable def mu (s : ℝ) (B : Set ℕ) : ℝ :=
  numerator s B / zetaDenom s

section EasyLemmas

lemma coeff_zero (B : Set ℕ) : coeff B 0 = 0 := by
  simp [coeff]

lemma coeff_nonneg (B : Set ℕ) (n : ℕ) : 0 ≤ coeff B n := by
  by_cases h : 0 < n ∧ n ∈ B
  · simp [coeff, h]
  · simp [coeff, h]

/-- Partial sums of `coeff B` recover the counting function of `B`. -/
lemma partialSum_coeff_eq_countUpTo (B : Set ℕ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, coeff B n) = countUpTo B N := by
  /-
  Expand `coeff`; only the terms with `1 ≤ n ≤ N` and `n ∈ B` survive, each contributing `1`.
  The result is exactly the cardinality of
  `((Finset.Icc 1 N).filter fun n => n ∈ B)`.
  -/
  classical
  have hfilter :
      (Finset.Icc 0 N).filter (fun n => 0 < n ∧ n ∈ B) =
        (Finset.Icc 1 N).filter (fun n => n ∈ B) := by
    ext n
    simp [Nat.succ_le_iff, and_left_comm, and_assoc]
  calc
    ∑ n ∈ Finset.Icc 0 N, coeff B n
        = ∑ n ∈ Finset.Icc 0 N, if 0 < n ∧ n ∈ B then (1 : ℝ) else 0 := by
            simp [coeff]
    _ = ∑ n ∈ (Finset.Icc 0 N).filter (fun n => 0 < n ∧ n ∈ B), (1 : ℝ) := by
          rw [← Finset.sum_filter]
    _ = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∈ B), (1 : ℝ) := by
          rw [hfilter]
    _ = countUpTo B N := by
          simp [countUpTo]

/-- Trivial upper bound for the counting function. -/
lemma countUpTo_le (B : Set ℕ) (N : ℕ) : countUpTo B N ≤ N := by
  /-
  The filtered finset is a subset of `Finset.Icc 1 N`, whose cardinality is `N`.
  -/
  classical
  rw [countUpTo]
  simpa using Finset.card_filter_le (Finset.Icc 1 N) (fun n => n ∈ B)

/-- Real-valued version of `partialSum_coeff_eq_countUpTo`. -/
lemma partialSum_coeff_eq_countingFn (B : Set ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, coeff B n) = countingFn B x := by
  simp [countingFn, partialSum_coeff_eq_countUpTo]

/-- A rough bound needed for the Abel-summation limit theorem. -/
lemma countingFn_le (B : Set ℕ) {x : ℝ} (hx : 0 ≤ x) : countingFn B x ≤ x := by
  /-
  Use `countUpTo_le B ⌊x⌋₊` and `Nat.floor_le hx`.
  -/
  unfold countingFn
  have hfloor : (countUpTo B ⌊x⌋₊ : ℝ) ≤ ⌊x⌋₊ := by
    exact_mod_cast (countUpTo_le B ⌊x⌋₊)
  exact hfloor.trans (Nat.floor_le hx)

end EasyLemmas

section DensityToErrorBounds

/-- Reformulation of natural density as an eventually-small relative error on the natural counting
function.  This is the discrete version of `B(x) = δx + o(x)`. -/
lemma eventually_abs_count_error_le
    {B : Set ℕ} {δ : ℝ} (hB : HasNatDensity B δ) :
    ∀ ε > 0, ∃ T : ℕ, ∀ n ≥ T,
      |(countUpTo B n : ℝ) - δ * n| ≤ ε * n := by
  intro ε hε
  rcases (Metric.tendsto_atTop.mp hB) ε hε with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn_nat : 0 < n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_nat
  have hsub : n - 1 + 1 = n := by omega
  have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    exact_mod_cast hsub
  have hdist : |((countUpTo B n : ℝ) / n) - δ| < ε := by
    have hN' : |densSeq B (n - 1) - δ| < ε := by
      simpa [Real.dist_eq] using hN (n - 1) (by omega)
    simpa [densSeq, Nat.cast_add, hcast, hsub] using hN'
  have hmul : |((((countUpTo B n : ℝ) / n) - δ) * n)| < ε * n := by
    have : |((countUpTo B n : ℝ) / n) - δ| * n < ε * n :=
      mul_lt_mul_of_pos_right hdist hn_pos
    simpa [abs_mul, abs_of_pos hn_pos] using this
  have hrewrite : (((countUpTo B n : ℝ) / n) - δ) * n = (countUpTo B n : ℝ) - δ * n := by
    field_simp [hn_pos.ne']
  exact le_of_lt (by simpa [hrewrite] using hmul)

/-- Continuous-input version of the previous lemma.

This is the place where the floor error is absorbed.  The statement is arranged so that the
subsequent integral estimate is literally the same epsilon-`T` argument as in the TeX proof. -/
lemma eventually_abs_err_le
    {B : Set ℕ} {δ : ℝ} (hB : HasNatDensity B δ) :
    ∀ ε > 0, ∃ T : ℕ, ∀ x : ℝ, (T : ℝ) ≤ x → |err B δ x| ≤ ε * x := by
  intro ε hε
  have hε2_pos : 0 < ε / 2 := by linarith
  have hε2_nonneg : 0 ≤ ε / 2 := le_of_lt hε2_pos
  rcases eventually_abs_count_error_le hB (ε / 2) hε2_pos with ⟨T0, hT0⟩
  let Tδ : ℕ := ⌈(2 * |δ|) / ε⌉₊
  refine ⟨max T0 Tδ, ?_⟩
  intro x hx
  have hT0max : (T0 : ℝ) ≤ (max T0 Tδ : ℕ) := by
    exact_mod_cast le_max_left T0 Tδ
  have hTδmax : (Tδ : ℝ) ≤ (max T0 Tδ : ℕ) := by
    exact_mod_cast le_max_right T0 Tδ
  have hxnonneg : 0 ≤ x := by
    exact le_trans (show (0 : ℝ) ≤ (max T0 Tδ : ℕ) by exact_mod_cast Nat.zero_le (max T0 Tδ)) hx
  have hT0x : (T0 : ℝ) ≤ x := hT0max.trans hx
  have hfloor_ge_T0 : T0 ≤ ⌊x⌋₊ := Nat.le_floor hT0x
  have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxnonneg
  have hcount :
      |(countUpTo B ⌊x⌋₊ : ℝ) - δ * (⌊x⌋₊ : ℝ)| ≤ (ε / 2) * (⌊x⌋₊ : ℝ) :=
    hT0 _ hfloor_ge_T0
  have hcount' :
      |(countUpTo B ⌊x⌋₊ : ℝ) - δ * (⌊x⌋₊ : ℝ)| ≤ (ε / 2) * x := by
    exact le_trans hcount (mul_le_mul_of_nonneg_left hfloor_le hε2_nonneg)
  have hfloor_abs : |((⌊x⌋₊ : ℝ) - x)| ≤ 1 := by
    rw [abs_sub_comm]
    have hnonneg : 0 ≤ x - (⌊x⌋₊ : ℝ) := sub_nonneg.mpr hfloor_le
    rw [abs_of_nonneg hnonneg]
    linarith [Nat.lt_floor_add_one x]
  have hδterm : |δ * ((⌊x⌋₊ : ℝ) - x)| ≤ |δ| := by
    calc
      |δ * ((⌊x⌋₊ : ℝ) - x)| = |δ| * |((⌊x⌋₊ : ℝ) - x)| := by rw [abs_mul]
      _ ≤ |δ| * 1 := mul_le_mul_of_nonneg_left hfloor_abs (abs_nonneg δ)
      _ = |δ| := by ring
  have hceil : ((2 * |δ|) / ε) ≤ (Tδ : ℝ) := by
    change ((2 * |δ|) / ε) ≤ (⌈(2 * |δ|) / ε⌉₊ : ℝ)
    exact Nat.le_ceil ((2 * |δ|) / ε)
  have hTδx : ((2 * |δ|) / ε) ≤ x := hceil.trans (hTδmax.trans hx)
  have hrewrite : (ε / 2) * ((2 * |δ|) / ε) = |δ| := by
    field_simp [ne_of_gt hε]
  have hδ_le : |δ| ≤ (ε / 2) * x := by
    rw [← hrewrite]
    exact mul_le_mul_of_nonneg_left hTδx hε2_nonneg
  have hδterm' : |δ * ((⌊x⌋₊ : ℝ) - x)| ≤ (ε / 2) * x := hδterm.trans hδ_le
  have herr_eq :
      err B δ x =
        ((countUpTo B ⌊x⌋₊ : ℝ) - δ * (⌊x⌋₊ : ℝ)) + δ * ((⌊x⌋₊ : ℝ) - x) := by
    simp [err, countingFn]
    ring
  calc
    |err B δ x| =
        |((countUpTo B ⌊x⌋₊ : ℝ) - δ * (⌊x⌋₊ : ℝ)) + δ * ((⌊x⌋₊ : ℝ) - x)| := by
          rw [herr_eq]
    _ ≤ |(countUpTo B ⌊x⌋₊ : ℝ) - δ * (⌊x⌋₊ : ℝ)| + |δ * ((⌊x⌋₊ : ℝ) - x)| :=
          abs_add_le _ _
    _ ≤ (ε / 2) * x + (ε / 2) * x := add_le_add hcount' hδterm'
    _ = ε * x := by ring

end DensityToErrorBounds

section AbelSummation

/-- The numerator is summable for every `s > 1`.

This can be proved either directly from `|coeff B n| ≤ 1` and `summable_one_div_nat_rpow`, or by
using `summable_mul_of_bigO_atTop'` from `AbelSummation`.  The direct proof is shorter. -/
lemma numerator_summable {B : Set ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => coeff B n / (n : ℝ) ^ s) := by
  /-
  Compare pointwise with `fun n => 1 / (n : ℝ)^s`, use `coeff_nonneg`, `|coeff B n| ≤ 1`, and
  `summable_one_div_nat_rpow.mpr hs`.
  -/
  refine Summable.of_nonneg_of_le ?_ ?_ (summable_one_div_nat_rpow.mpr hs)
  · intro n
    have hpow_nonneg : 0 ≤ (n : ℝ) ^ s := by
      exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) by exact_mod_cast (Nat.zero_le n)) _
    by_cases h : 0 < n ∧ n ∈ B
    · have hnonneg : 0 ≤ 1 / (n : ℝ) ^ s := one_div_nonneg.mpr hpow_nonneg
      simpa [coeff, h] using hnonneg
    · simp [coeff, h]
  · intro n
    have hpow_nonneg : 0 ≤ (n : ℝ) ^ s := by
      exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) by exact_mod_cast (Nat.zero_le n)) _
    by_cases h : 0 < n ∧ n ∈ B
    · simp [coeff, h]
    · have hnonneg : 0 ≤ 1 / (n : ℝ) ^ s := one_div_nonneg.mpr hpow_nonneg
      simpa [coeff, h] using hnonneg

/-- Abel summation formula specialized to the indicator sequence of `B`.

This is the Lean avatar of
`∑_{n∈B} n^{-s} = s ∫_1^∞ B(x) x^{-s-1} dx`.

Mathlib route:
`NumberTheory/AbelSummation.lean`, theorem
`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`, with
* `f x = x ^ (-s)`,
* `c = coeff B`,
* `l = 0`, because `x^{-s} * countUpTo B x = O(x^{1-s}) → 0`.

After obtaining the limit of the partial sums, identify it with the corresponding `tsum`
using `numerator_summable hs`.
-/
lemma numerator_eq_integral {B : Set ℕ} {s : ℝ} (hs : 1 < s) :
    numerator s B =
      s * ∫ x in Set.Ioi (1 : ℝ), countingFn B x * x ^ (-(s + 1 : ℝ)) := by
  classical
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, coeff B k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine isBigO_of_le _ fun n => ?_
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 n, coeff B k := by
      exact Finset.sum_nonneg fun k hk => coeff_nonneg B k
    have hsum_le : ∑ k ∈ Finset.Icc 1 n, coeff B k ≤ (n : ℝ) := by
      calc
        ∑ k ∈ Finset.Icc 1 n, coeff B k ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) := by
          exact Finset.sum_le_sum fun k hk => by
            by_cases h : 0 < k ∧ k ∈ B <;> simp [coeff, h]
        _ = (n : ℝ) := by
          simp
    have hrpow_nonneg : 0 ≤ (n : ℝ) ^ (1 : ℝ) :=
      Real.rpow_nonneg (show 0 ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n) _
    simpa [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg, abs_of_nonneg hrpow_nonneg,
      Real.rpow_natCast] using hsum_le
  have hL :
      LSeries (fun n ↦ (coeff B n : ℂ)) (s : ℂ) =
        (s : ℂ) *
          ∫ x in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (coeff B k : ℂ)) * x ^ (-((s : ℂ) + 1)) := by
    simpa using
      (LSeries_eq_mul_integral_of_nonneg (f := coeff B) (r := 1) (s := (s : ℂ))
        zero_le_one (by simpa using hs) hO (coeff_nonneg B))
  have hnum :
      (numerator s B : ℂ) = LSeries (fun n ↦ (coeff B n : ℂ)) (s : ℂ) := by
    rw [numerator, LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · subst hn
      simp [LSeries.term, coeff_zero]
    · rw [LSeries.term, if_neg hn]
      simp [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  apply Complex.ofReal_injective
  calc
    (numerator s B : ℂ) = LSeries (fun n ↦ (coeff B n : ℂ)) (s : ℂ) := hnum
    _ = (s : ℂ) *
          ∫ x in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (coeff B k : ℂ)) * x ^ (-((s : ℂ) + 1)) := hL
    _ = (s : ℂ) *
          ∫ x in Set.Ioi (1 : ℝ), ((countingFn B x * x ^ (-(s + 1 : ℝ)) : ℝ) : ℂ) := by
          have hInt :
              ∫ x in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (coeff B k : ℂ)) * x ^ (-((s : ℂ) + 1)) =
                ∫ x in Set.Ioi (1 : ℝ), ((countingFn B x * x ^ (-(s + 1 : ℝ)) : ℝ) : ℂ) := by
            apply MeasureTheory.integral_congr_ae
            exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 <|
              Eventually.of_forall fun x hx => by
                have hsumR : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, coeff B k = countingFn B x := by
                  unfold countingFn countUpTo
                  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
                  simp_rw [coeff]
                  rw [← Finset.sum_filter]
                  have hfilter :
                      (Finset.Icc 1 ⌊x⌋₊).filter (fun n => 0 < n ∧ n ∈ B) =
                        (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ B) := by
                    ext n
                    simp [Nat.succ_le_iff, and_left_comm, and_assoc]
                  simpa [hfilter]
                have hsum : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (coeff B k : ℂ) = (countingFn B x : ℂ) := by
                  simpa using congrArg (fun t : ℝ => (t : ℂ)) hsumR
                have hx_nonneg : 0 ≤ x := zero_le_one.trans hx.le
                have hpow :
                    ((x ^ (-(s + 1 : ℝ)) : ℝ) : ℂ) = (x : ℂ) ^ (-((s : ℂ) + 1)) := by
                  simpa using (Complex.ofReal_cpow hx_nonneg (-(s + 1 : ℝ)))
                calc
                  (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (coeff B k : ℂ)) * x ^ (-((s : ℂ) + 1))
                      = (countingFn B x : ℂ) * (x : ℂ) ^ (-((s : ℂ) + 1)) := by rw [hsum]
                  _ = ((countingFn B x * x ^ (-(s + 1 : ℝ)) : ℝ) : ℂ) := by
                        rw [← hpow, ← Complex.ofReal_mul]
          rw [hInt]
    _ = (s : ℂ) * ↑(∫ x in Set.Ioi (1 : ℝ), countingFn B x * x ^ (-(s + 1 : ℝ))) := by
          rw [integral_complex_ofReal]
    _ = ↑(s * ∫ x in Set.Ioi (1 : ℝ), countingFn B x * x ^ (-(s + 1 : ℝ))) := by
          exact (Complex.ofReal_mul s
            (∫ x in Set.Ioi (1 : ℝ), countingFn B x * x ^ (-(s + 1 : ℝ)))).symm

/-- Split the counting function into its main term `δx` and its error term. -/
lemma numerator_eq_mainTerm_add_errorIntegral
    {B : Set ℕ} {δ s : ℝ} (hs : 1 < s) :
    numerator s B =
      δ * (s / (s - 1))
        + s * ∫ x in Set.Ioi (1 : ℝ), err B δ x * x ^ (-(s + 1 : ℝ)) := by
  have hmeas_countingFn : Measurable (countingFn B) := by
    unfold countingFn
    exact ((Measurable.of_discrete :
      Measurable fun n : ℕ => (countUpTo B n : ℝ))).comp Nat.measurable_floor
  let f : ℝ → ℝ := fun x => countingFn B x * x ^ (-(s + 1 : ℝ))
  let g : ℝ → ℝ := fun x => (δ * x) * x ^ (-(s + 1 : ℝ))
  let h : ℝ → ℝ := fun x => err B δ x * x ^ (-(s + 1 : ℝ))
  have hpow {x : ℝ} (hx : 0 < x) : x * x ^ (-(s + 1 : ℝ)) = x ^ (-s) := by
    calc
      x * x ^ (-(s + 1 : ℝ)) = x ^ (1 : ℝ) * x ^ (-(s + 1 : ℝ)) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(s + 1 : ℝ))) := by
        rw [← Real.rpow_add hx]
      _ = x ^ (-s) := by
        congr 1
        ring
  have hcount_integrable : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    have hfs_ae :
        MeasureTheory.AEStronglyMeasurable f
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hcount :
          MeasureTheory.AEStronglyMeasurable (countingFn B)
            (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
        hmeas_countingFn.aestronglyMeasurable.mono_measure
          MeasureTheory.Measure.restrict_le_self
      have hrpow :
          MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ (-(s + 1 : ℝ)))
            (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
        exact (continuousOn_id.rpow_const fun x hx =>
          Or.inl (ne_of_gt (lt_trans zero_lt_one hx))).aestronglyMeasurable measurableSet_Ioi
      convert hcount.mul hrpow using 1 <;> rfl
    have hmajor : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))), ‖f x‖ ≤ x ^ (-s) := by
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 <|
        Eventually.of_forall fun x hx => by
        have hx1 : 1 < x := by simpa using hx
        have hx0 : 0 ≤ x := zero_le_one.trans hx1.le
        have hcount_nonneg : 0 ≤ countingFn B x := by
          unfold countingFn
          exact_mod_cast Nat.zero_le (countUpTo B ⌊x⌋₊)
        have hcount_le : countingFn B x ≤ x := countingFn_le B (zero_le_one.trans hx1.le)
        have hpow_nonneg : 0 ≤ x ^ (-(s + 1 : ℝ)) := Real.rpow_nonneg hx0 _
        calc
          ‖f x‖ = |countingFn B x * x ^ (-(s + 1 : ℝ))| := by simp [f, Real.norm_eq_abs]
          _ = countingFn B x * x ^ (-(s + 1 : ℝ)) := by
                rw [abs_of_nonneg (mul_nonneg hcount_nonneg hpow_nonneg)]
          _ ≤ x * x ^ (-(s + 1 : ℝ)) := mul_le_mul_of_nonneg_right hcount_le hpow_nonneg
          _ = x ^ (-s) := hpow (lt_trans zero_lt_one hx1)
    simpa [MeasureTheory.IntegrableOn] using
      MeasureTheory.Integrable.mono'
        (by simpa [MeasureTheory.IntegrableOn] using hmajor) hfs_ae hbound
  have hmain_base :
      MeasureTheory.IntegrableOn (fun x : ℝ => δ * x ^ (-s)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one).const_mul δ
  have hmain_integrable : MeasureTheory.IntegrableOn g (Set.Ioi (1 : ℝ)) := by
    refine hmain_base.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx1 : 1 < x := by simpa using hx
    calc
      δ * x ^ (-s) = δ * (x * x ^ (-(s + 1 : ℝ))) := by
        rw [← hpow (lt_trans zero_lt_one hx1)]
      _ = g x := by
        simp [g, mul_assoc, mul_left_comm, mul_comm]
  have hdiff :
      h =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))] fun x : ℝ => f x - g x := by
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 <|
      Eventually.of_forall fun x hx => by
      simp [f, g, h, err]
      ring
  have hcount_int :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, f] using hcount_integrable
  have hmain_int :
      MeasureTheory.Integrable g (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, g] using hmain_integrable
  have herr_integrable : MeasureTheory.IntegrableOn h (Set.Ioi (1 : ℝ)) := by
    have herr_int :
        MeasureTheory.Integrable h (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hcount_int.sub hmain_int).congr hdiff.symm
    simpa [MeasureTheory.IntegrableOn, h] using herr_int
  have herr_int :
      MeasureTheory.Integrable h (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, h] using herr_integrable
  have hsplit :
      ∫ x in Set.Ioi (1 : ℝ), f x =
        (∫ x in Set.Ioi (1 : ℝ), g x) + ∫ x in Set.Ioi (1 : ℝ), h x := by
    have hsum_eq :
        f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))] fun x : ℝ => g x + h x := by
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 <|
        Eventually.of_forall fun x hx => by
        simp [f, g, h, err]
        ring
    calc
      ∫ x in Set.Ioi (1 : ℝ), f x = ∫ x in Set.Ioi (1 : ℝ), (g x + h x) := by
        exact MeasureTheory.integral_congr_ae hsum_eq
      _ = (∫ x in Set.Ioi (1 : ℝ), g x) + ∫ x in Set.Ioi (1 : ℝ), h x := by
        rw [MeasureTheory.integral_add hmain_int herr_int]
  have hmain_eval : ∫ x in Set.Ioi (1 : ℝ), g x = δ / (s - 1) := by
    calc
      ∫ x in Set.Ioi (1 : ℝ), g x = ∫ x in Set.Ioi (1 : ℝ), δ * x ^ (-s) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        have hx1 : 1 < x := by simpa using hx
        calc
          g x = δ * (x * x ^ (-(s + 1 : ℝ))) := by
            simp [g, mul_assoc, mul_left_comm, mul_comm]
          _ = δ * x ^ (-s) := by rw [hpow (lt_trans zero_lt_one hx1)]
      _ = δ * ∫ x in Set.Ioi (1 : ℝ), x ^ (-s) := by
        rw [MeasureTheory.integral_const_mul]
      _ = δ / (s - 1) := by
        have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
        have hsne' : 1 - s ≠ 0 := by linarith
        rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one, Real.one_rpow]
        have haux : δ * (-1 / (1 - s)) = δ / (s - 1) := by
          field_simp [hsne, hsne']
          ring_nf
        convert haux using 1 <;> ring
  have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
  have hmul_main : s * (δ / (s - 1)) = δ * (s / (s - 1)) := by
    field_simp [hsne]
  calc
    numerator s B = s * ∫ x in Set.Ioi (1 : ℝ), f x := by
      rw [numerator_eq_integral hs]
    _ = s * ((∫ x in Set.Ioi (1 : ℝ), g x) + ∫ x in Set.Ioi (1 : ℝ), h x) := by
      rw [hsplit]
    _ = s * (∫ x in Set.Ioi (1 : ℝ), g x) + s * (∫ x in Set.Ioi (1 : ℝ), h x) := by
      rw [mul_add]
    _ = s * (δ / (s - 1)) + s * (∫ x in Set.Ioi (1 : ℝ), h x) := by
      rw [hmain_eval]
    _ = δ * (s / (s - 1)) + s * (∫ x in Set.Ioi (1 : ℝ), h x) := by
      rw [hmul_main]
    _ = δ * (s / (s - 1))
        + s * (∫ x in Set.Ioi (1 : ℝ), err B δ x * x ^ (-(s + 1 : ℝ))) := by
      rfl

end AbelSummation

section ErrorIntegral

/-- The error integral is negligible after multiplication by `s - 1`.
This is exactly the epsilon-`T` estimate from the TeX proof. -/
lemma tendsto_scaled_errorIntegral_zero
    {B : Set ℕ} {δ : ℝ} (hB : HasNatDensity B δ) :
    Tendsto
      (fun s : ℝ =>
        (s - 1) *
          (s * ∫ x in Set.Ioi (1 : ℝ), err B δ x * x ^ (-(s + 1 : ℝ))))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hmeas_countingFn : Measurable (countingFn B) := by
    unfold countingFn
    exact ((Measurable.of_discrete :
      Measurable fun n : ℕ => (countUpTo B n : ℝ))).comp Nat.measurable_floor
  have hmeas_err : Measurable (err B δ) := by
    unfold err
    exact hmeas_countingFn.sub (measurable_const.mul measurable_id)
  have herr_linear : ∀ {x : ℝ}, 0 ≤ x → |err B δ x| ≤ (1 + |δ|) * x := by
    intro x hx
    have hcount_nonneg : 0 ≤ countingFn B x := by
      unfold countingFn
      exact_mod_cast Nat.zero_le (countUpTo B ⌊x⌋₊)
    have hcount_le : countingFn B x ≤ x := countingFn_le B hx
    calc
      |err B δ x| = |countingFn B x - δ * x| := by rw [err]
      _ = |countingFn B x + -(δ * x)| := by ring_nf
      _ ≤ ‖countingFn B x‖ + ‖-(δ * x)‖ := by
            simpa [Real.norm_eq_abs] using norm_add_le (countingFn B x) (-(δ * x))
      _ = |countingFn B x| + |δ * x| := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
      _ = countingFn B x + |δ| * x := by
            rw [abs_of_nonneg hcount_nonneg, abs_mul, abs_of_nonneg hx]
      _ ≤ x + |δ| * x := by gcongr
      _ = (1 + |δ|) * x := by ring
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ε0 : ℝ := ε / 4
  have hε0_pos : 0 < ε0 := by
    dsimp [ε0]
    linarith
  have hε0_nonneg : 0 ≤ ε0 := le_of_lt hε0_pos
  rcases eventually_abs_err_le hB ε0 hε0_pos with ⟨N, hN⟩
  let Tnat : ℕ := max N 1
  let T : ℝ := Tnat
  have hTnat_ge_N : N ≤ Tnat := le_max_left N 1
  have hTnat_ge_one : 1 ≤ Tnat := le_max_right N 1
  have hT1 : (1 : ℝ) ≤ T := by
    dsimp [T]
    exact_mod_cast hTnat_ge_one
  have hTpos : (0 : ℝ) < T := zero_lt_one.trans_le hT1
  have hErr : ∀ x : ℝ, T ≤ x → |err B δ x| ≤ ε0 * x := by
    intro x hx
    refine hN x ?_
    exact (show (N : ℝ) ≤ T from by
      dsimp [T]
      exact_mod_cast hTnat_ge_N).trans hx
  let K : ℝ := ((1 + |δ|) * T) * MeasureTheory.volume.real (Set.Ioc (1 : ℝ) T)
  let A : ℝ := K + 1
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by positivity) MeasureTheory.measureReal_nonneg
  have hA_pos : 0 < A := by
    dsimp [A]
    linarith
  have hsmall : ∀ᶠ s in 𝓝[>] (1 : ℝ), |((s - 1) * s) * A| < ε / 2 := by
    have hcont : ContinuousAt (fun s : ℝ => ((s - 1) * s) * A) 1 := by
      fun_prop
    have htendsto : Tendsto (fun s : ℝ => ((s - 1) * s) * A) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto
    have hε2 : 0 < ε / 2 := by linarith
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp htendsto) (ε / 2) hε2
  have hlt2 : Set.Iio (2 : ℝ) ∈ 𝓝[>] (1 : ℝ) :=
    nhdsWithin_le_nhds <| Iio_mem_nhds (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hsmall, hlt2, self_mem_nhdsWithin] with s hsSmall hsLt2 hsGt1
  have hs : 1 < s := hsGt1
  have hs1_nonneg : 0 ≤ s - 1 := sub_nonneg.mpr hs.le
  have hs_nonneg : 0 ≤ s := le_trans (by norm_num) hs.le
  let fs : ℝ → ℝ := fun x => err B δ x * x ^ (-(s + 1 : ℝ))
  have hfs_ae_fin :
      MeasureTheory.AEStronglyMeasurable fs (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    have herr :
        MeasureTheory.AEStronglyMeasurable (err B δ)
          (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) :=
      hmeas_err.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
    have hrpow :
        MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ (-(s + 1 : ℝ)))
          (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
      exact (continuousOn_id.rpow_const fun x hx =>
        Or.inl (ne_of_gt (lt_trans zero_lt_one hx.1))).aestronglyMeasurable measurableSet_Ioc
    convert herr.mul hrpow using 1 <;> rfl
  have hfs_ae_tail :
      MeasureTheory.AEStronglyMeasurable fs (MeasureTheory.volume.restrict (Set.Ioi T)) := by
    have herr :
        MeasureTheory.AEStronglyMeasurable (err B δ) (MeasureTheory.volume.restrict (Set.Ioi T)) :=
      hmeas_err.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
    have hrpow :
        MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ (-(s + 1 : ℝ)))
          (MeasureTheory.volume.restrict (Set.Ioi T)) := by
      exact (continuousOn_id.rpow_const fun x hx =>
        Or.inl (ne_of_gt (lt_trans hTpos hx))).aestronglyMeasurable measurableSet_Ioi
    convert herr.mul hrpow using 1 <;> rfl
  have hpoint_fin : ∀ x ∈ Set.Ioc (1 : ℝ) T, ‖fs x‖ ≤ (1 + |δ|) * T := by
    intro x hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx.1.le
    have herrx : |err B δ x| ≤ (1 + |δ|) * x := herr_linear hx0
    have hpow_nonneg : 0 ≤ x ^ (-(s + 1 : ℝ)) := Real.rpow_nonneg hx0 _
    have hpow_le_one : x ^ (-(s + 1 : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos hx.1.le ?_
      linarith
    calc
      ‖fs x‖ = |err B δ x * x ^ (-(s + 1 : ℝ))| := by simp [fs, Real.norm_eq_abs]
      _ = |err B δ x| * x ^ (-(s + 1 : ℝ)) := by rw [abs_mul, abs_of_nonneg hpow_nonneg]
      _ ≤ ((1 + |δ|) * x) * 1 := by
            exact mul_le_mul herrx hpow_le_one hpow_nonneg (by positivity)
      _ = (1 + |δ|) * x := by ring
      _ ≤ (1 + |δ|) * T := by
            exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
  have hpoint_tail : ∀ x ∈ Set.Ioi T, ‖fs x‖ ≤ ε0 * x ^ (-s) := by
    intro x hx
    have hxT : T ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hTpos hxT
    have herrx : |err B δ x| ≤ ε0 * x := hErr x hxT
    have hpow_nonneg : 0 ≤ x ^ (-(s + 1 : ℝ)) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hpow : x * x ^ (-s - 1 : ℝ) = x ^ (-s) := by
      have hpow' : x ^ (-s) = x * x ^ (-s - 1 : ℝ) := by
        rw [Real.rpow_sub hxpos (-s) 1, Real.rpow_one, mul_div_cancel₀ _ hxpos.ne']
      exact hpow'.symm
    calc
      ‖fs x‖ = |err B δ x * x ^ (-(s + 1 : ℝ))| := by simp [fs, Real.norm_eq_abs]
      _ = |err B δ x| * x ^ (-(s + 1 : ℝ)) := by rw [abs_mul, abs_of_nonneg hpow_nonneg]
      _ ≤ (ε0 * x) * x ^ (-(s + 1 : ℝ)) := by
            exact mul_le_mul_of_nonneg_right herrx hpow_nonneg
      _ = (ε0 * x) * x ^ (-s - 1 : ℝ) := by
            congr 2
            ring
      _ = ε0 * (x * x ^ (-s - 1 : ℝ)) := by
            ring
      _ = ε0 * x ^ (-s) := by rw [hpow]
  have hfin_integrable : MeasureTheory.IntegrableOn fs (Set.Ioc (1 : ℝ) T) := by
    have hconst :
        MeasureTheory.Integrable (fun _ : ℝ => (1 + |δ|) * T)
          (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
      exact MeasureTheory.integrable_const _
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)), ‖fs x‖ ≤ (1 + |δ|) * T := by
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 <|
        Filter.Eventually.of_forall fun x hx => hpoint_fin x hx
    simpa [MeasureTheory.IntegrableOn] using MeasureTheory.Integrable.mono' hconst hfs_ae_fin hbound
  have htail_majorant_integrable :
      MeasureTheory.IntegrableOn (fun x : ℝ => ε0 * x ^ (-s)) (Set.Ioi T) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hTpos).const_mul _
  have htail_integrable : MeasureTheory.IntegrableOn fs (Set.Ioi T) := by
    have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi T)), ‖fs x‖ ≤ ε0 * x ^ (-s) := by
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 <|
        Filter.Eventually.of_forall fun x hx => hpoint_tail x hx
    simpa [MeasureTheory.IntegrableOn] using
      MeasureTheory.Integrable.mono'
        (by simpa [MeasureTheory.IntegrableOn] using htail_majorant_integrable) hfs_ae_tail hbound
  have hsplit :
      ∫ x in Set.Ioi (1 : ℝ), fs x =
        (∫ x in Set.Ioc (1 : ℝ) T, fs x) + ∫ x in Set.Ioi T, fs x := by
    have hsplit' :=
      (MeasureTheory.setIntegral_union
        (μ := MeasureTheory.volume) (f := fs)
        Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hfin_integrable htail_integrable)
    simpa [Set.Ioc_union_Ioi_eq_Ioi hT1] using hsplit'
  have hfin_bound : ‖∫ x in Set.Ioc (1 : ℝ) T, fs x‖ ≤ K := by
    dsimp [K]
    exact MeasureTheory.norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hpoint_fin
  have htail_norm_int : ‖∫ x in Set.Ioi T, fs x‖ ≤ ∫ x in Set.Ioi T, ε0 * x ^ (-s) := by
    exact
      (MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume.restrict (Set.Ioi T))
        (by simpa [MeasureTheory.IntegrableOn] using htail_majorant_integrable)
        (by
          exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 <|
            Filter.Eventually.of_forall fun x hx => hpoint_tail x hx))
  have htail_core :
      (s - 1) * ∫ (x : ℝ) in Set.Ioi T, ε0 * x ^ (-s) ≤ ε0 := by
    have hmono :
        ∫ (x : ℝ) in Set.Ioi T, x ^ (-s) ≤ ∫ (x : ℝ) in Set.Ioi (1 : ℝ), x ^ (-s) := by
      refine MeasureTheory.setIntegral_mono_set ?_ ?_ (Set.Ioi_subset_Ioi hT1).eventuallyLE
      · exact integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one
      · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr <|
          univ_mem' fun x hx => Real.rpow_nonneg (zero_le_one.trans hx.le) _
    calc
      _ = ((s - 1) * ε0) * ∫ (x : ℝ) in Set.Ioi T, x ^ (-s) := by
            rw [MeasureTheory.integral_const_mul]
            ring
      _ ≤ ((s - 1) * ε0) * ∫ (x : ℝ) in Set.Ioi (1 : ℝ), x ^ (-s) := by
            exact mul_le_mul_of_nonneg_left hmono (mul_nonneg hs1_nonneg hε0_nonneg)
      _ = ε0 * ((s - 1) * ∫ (x : ℝ) in Set.Ioi (1 : ℝ), x ^ (-s)) := by ring
      _ = ε0 := by
        have hsne : s - 1 ≠ 0 := by linarith
        have hneg : -(s - 1 : ℝ) = -s + 1 := by ring
        rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one, Real.one_rpow, ← hneg]
        field_simp [hsne]
  have htail_scaled : ‖(s - 1) * (s * ∫ x in Set.Ioi T, fs x)‖ ≤ s * ε0 := by
    calc
      ‖(s - 1) * (s * ∫ x in Set.Ioi T, fs x)‖
          = s * ((s - 1) * ‖∫ x in Set.Ioi T, fs x‖) := by
              rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg hs1_nonneg, abs_of_nonneg hs_nonneg]
              ring
      _ ≤ s * ((s - 1) * ∫ x in Set.Ioi T, ε0 * x ^ (-s)) := by
            gcongr
      _ ≤ s * ε0 := by
            gcongr
  have htail_scaled' : ‖(s - 1) * (s * ∫ x in Set.Ioi T, fs x)‖ ≤ ε / 2 := by
    refine le_trans htail_scaled ?_
    have hs2 : s ≤ 2 := le_of_lt hsLt2
    calc
      s * ε0 ≤ 2 * ε0 := by gcongr
      _ = ε / 2 := by
            dsimp [ε0]
            ring
  have hfin_scaled : ‖(s - 1) * (s * ∫ x in Set.Ioc (1 : ℝ) T, fs x)‖ < ε / 2 := by
    have hK_le_A : K ≤ A := by
      dsimp [A]
      linarith
    calc
      ‖(s - 1) * (s * ∫ x in Set.Ioc (1 : ℝ) T, fs x)‖
          = ((s - 1) * s) * ‖∫ x in Set.Ioc (1 : ℝ) T, fs x‖ := by
              rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg hs1_nonneg, abs_of_nonneg hs_nonneg]
              ring
      _ ≤ ((s - 1) * s) * K := by gcongr
      _ ≤ ((s - 1) * s) * A := by gcongr
      _ = |((s - 1) * s) * A| := by
            rw [abs_of_nonneg]
            exact mul_nonneg (mul_nonneg hs1_nonneg hs_nonneg) hA_pos.le
      _ < ε / 2 := hsSmall
  let Ifin : ℝ := ∫ x in Set.Ioc (1 : ℝ) T, fs x
  let Itail : ℝ := ∫ x in Set.Ioi T, fs x
  have hsplit_mul :
      s * ∫ x in Set.Ioi (1 : ℝ), fs x = s * Ifin + s * Itail := by
    have hsplit_paren : ∫ x in Set.Ioi (1 : ℝ), fs x = Ifin + Itail := by
      exact hsplit.trans (by simp [Ifin, Itail])
    calc
      s * ∫ x in Set.Ioi (1 : ℝ), fs x = s * (Ifin + Itail) := by rw [hsplit_paren]
      _ = s * Ifin + s * Itail := by ring
  have hsplit_outer :
      (s - 1) * (s * ∫ x in Set.Ioi (1 : ℝ), fs x) =
        (s - 1) * (s * Ifin) + (s - 1) * (s * Itail) := by
    rw [hsplit_mul, left_distrib]
  have hsplit_norm :
      ‖(s - 1) * (s * ∫ x in Set.Ioi (1 : ℝ), fs x)‖
        ≤ ‖(s - 1) * (s * ∫ x in Set.Ioc (1 : ℝ) T, fs x)‖
          + ‖(s - 1) * (s * ∫ x in Set.Ioi T, fs x)‖ := by
    rw [hsplit_outer]
    simpa [Ifin, Itail] using norm_add_le ((s - 1) * (s * Ifin)) ((s - 1) * (s * Itail))
  have hfinal :
      ‖(s - 1) * (s * ∫ x in Set.Ioi (1 : ℝ), fs x)‖ < ε := by
    have hsum_lt :
        ‖(s - 1) * (s * ∫ x in Set.Ioc (1 : ℝ) T, fs x)‖
          + ‖(s - 1) * (s * ∫ x in Set.Ioi T, fs x)‖ < ε := by
      linarith [hfin_scaled, htail_scaled']
    exact lt_of_le_of_lt hsplit_norm hsum_lt
  simpa [Real.dist_eq, Real.norm_eq_abs, fs] using hfinal

/-- The numerator has the expected residue `δ` at `s = 1`. -/
lemma tendsto_scaled_numerator
    {B : Set ℕ} {δ : ℝ} (hB : HasNatDensity B δ) :
    Tendsto (fun s : ℝ => (s - 1) * numerator s B) (𝓝[>] (1 : ℝ)) (𝓝 δ) := by
  /-
  Combine `numerator_eq_mainTerm_add_errorIntegral` with
  `tendsto_scaled_errorIntegral_zero hB`.

  The main term is
    `(s - 1) * (δ * s / (s - 1)) = δ * s`,
  which tends to `δ`.
  -/
  have hEq :
      (fun s : ℝ => (s - 1) * numerator s B) =ᶠ[𝓝[>] (1 : ℝ)]
        fun s : ℝ =>
          δ * s +
            (s - 1) *
              (s * ∫ x in Set.Ioi (1 : ℝ), err B δ x * x ^ (-(s + 1 : ℝ))) := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hs' : 1 < s := hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs')
    rw [numerator_eq_mainTerm_add_errorIntegral hs', mul_add]
    have hmain : (s - 1) * (δ * (s / (s - 1))) = δ * s := by
      field_simp [hs1]
    rw [hmain]
  apply Tendsto.congr' hEq.symm
  have h_id : Tendsto (fun s : ℝ => s) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hmain : Tendsto (fun s : ℝ => δ * s) (𝓝[>] (1 : ℝ)) (𝓝 (δ * 1)) := by
    exact Tendsto.const_mul δ h_id
  have hsum :=
    hmain.add (tendsto_scaled_errorIntegral_zero (B := B) (δ := δ) hB)
  simpa [one_mul] using hsum

end ErrorIntegral

section Denominator

/-- The denominator has residue `1` at `s = 1`.

This is already in mathlib, in exactly the real form needed here. -/
lemma tendsto_scaled_zetaDenom :
    Tendsto (fun s : ℝ => (s - 1) * zetaDenom s) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  simpa [zetaDenom] using tendsto_sub_mul_tsum_nat_rpow

end Denominator

/-- Auxiliary-namespace proof of **Lemma 5** (`lem:density-to-Dirichlet`) from the revised TeX note.

If `B` has natural density `δ`, then its smoothed Dirichlet density `μ s B` tends to `δ`
as `s ↓ 1`. -/
theorem tendsto_mu_of_hasNatDensity
    {B : Set ℕ} {δ : ℝ} (hB : HasNatDensity B δ) :
    Tendsto (fun s : ℝ => mu s B) (𝓝[>] (1 : ℝ)) (𝓝 δ) := by
  /-
  Let
    `N(s) := (s - 1) * numerator s B`,
    `D(s) := (s - 1) * zetaDenom s`.

  Then `N(s) → δ` by `tendsto_scaled_numerator hB` and `D(s) → 1` by
  `tendsto_scaled_zetaDenom`.
  Since `D(s)` is eventually nonzero (indeed eventually positive), we have

    `mu s B = N(s) / D(s)`

  eventually on `𝓝[>] 1`, and therefore `mu s B → δ / 1 = δ`.
  -/
  have hquot :
      Tendsto
        (fun s : ℝ => ((s - 1) * numerator s B) / ((s - 1) * zetaDenom s))
        (𝓝[>] (1 : ℝ)) (𝓝 (δ / 1)) :=
    (tendsto_scaled_numerator (B := B) (δ := δ) hB).div tendsto_scaled_zetaDenom one_ne_zero
  have hEq :
      (fun s : ℝ => mu s B) =ᶠ[𝓝[>] (1 : ℝ)]
        fun s : ℝ => ((s - 1) * numerator s B) / ((s - 1) * zetaDenom s) := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
    by_cases hz : zetaDenom s = 0
    · simp [mu, hz]
    · rw [mu]
      field_simp [hs1, hz]
  exact Tendsto.congr' hEq.symm <| by simpa using hquot

/-!
## Optional alternative endpoint

If one prefers the statement literally in the form
`μ_s(B) = (1 / ζ(s)) * ∑_{n∈B} n^{-s}`,
then the only additional work is a small compatibility lemma showing that `zetaDenom s`
coincides with the real zeta-series used by mathlib (or simply rewriting via
`tendsto_sub_mul_tsum_nat_rpow`, as we did above).
-/

end DensityToDirichlet
end Erdos691

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI ChatGPT
-/


set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators Classical
open Filter

noncomputable section

namespace Erdos691

/-!
# Main Finite-Approximation Argument

Let `A ⊆ ℕ` and let `Multiples A` be the set of positive integers divisible by some
element of `A`. The goal is to characterize when `Multiples A` has natural density `1`.

This part of the file works with the shifted Dirichlet conventions used in the final
statement. The Hardy-style Tauberian theorem from `Erdos691.DensityToDirichlet` is transported to
these conventions via compatibility lemmas, and the rest of the development proves the
finite-density infrastructure, the finite-stage precursor of Lemma 6, and the final criterion
`behrend_iff_R_tendsto_zero`.
-/

/-- Positive multiples of elements of `A`.  This matches the Erdős problem, which only
counts positive integers. -/
def Multiples (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∣ n}

/-- The truncation `A ∩ [1,N]`, packaged as a `Finset`. -/
def trunc (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => n ∈ A

/-- Counting function on `[1,N]`. -/
def countUpTo (S : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun n => n ∈ S).card

/-- Density sequence, indexed by `N`, but counting up to `N+1` to avoid dividing by `0`. -/
def densSeq (S : Set ℕ) (N : ℕ) : ℝ :=
  (countUpTo S (N + 1) : ℝ) / (N + 1 : ℝ)

/-- Natural density. -/
def HasNatDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (densSeq S) Filter.atTop (nhds δ)

/-- "Behrend sequence" in the terminology of the problem statement. -/
def IsBehrend (A : Set ℕ) : Prop :=
  HasNatDensity (Multiples A) 1

/-- Convenience predicate: all elements of the finite set are positive. -/
def PositiveFinset (F : Finset ℕ) : Prop :=
  ∀ ⦃a : ℕ⦄, a ∈ F → 0 < a

/-- The `n`-th Dirichlet weight used in the proof of **Theorem 1** (`thm:finite-approx`).
We index from `0`, but the weight corresponds to the positive integer `n+1`. -/
noncomputable def zetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (n + 1 : ℝ) s

/-- Real zeta-series, written as a `tsum` over `ℕ`. -/
noncomputable def zetaReal (s : ℝ) : ℝ :=
  ∑' n : ℕ, zetaTerm s n

/-- Dirichlet-weighted density used in **Lemma 5** / **Lemma 6** of the revised TeX note. -/
noncomputable def mu (s : ℝ) (S : Set ℕ) : ℝ :=
  (∑' n : ℕ, if n + 1 ∈ S then zetaTerm s n else 0) / zetaReal s

/-- Finite least common multiple.  By convention `lcm0 ∅ = 1`. -/
def lcm0 (F : Finset ℕ) : ℕ :=
  F.lcm id

/-- Inclusion-exclusion expression for the density of integers divisible by none of the
elements of `F`.  This is the `R_N`-type expression at finite level. -/
noncomputable def finiteAvoidDensity (F : Finset ℕ) : ℝ :=
  F.powerset.sum fun G => (-1 : ℝ) ^ G.card / (lcm0 G : ℝ)

/-- Density of the set of multiples generated by `F`. -/
noncomputable def finiteMultiplesDensity (F : Finset ℕ) : ℝ :=
  1 - finiteAvoidDensity F

/-- **Definition 7** (primitive part) in the revised self-contained TeX note.

Primitive kernel of `A`: keep only those positive elements that are minimal for
divisibility inside `A`. -/
def primitiveKernel (A : Set ℕ) : Set ℕ :=
  {a | a ∈ A ∧ 0 < a ∧ ∀ b, b ∈ A → 0 < b → b ∣ a → a ≤ b}

/-- `B_N = A^{prim} ∩ [1,N]` from **Corollary 2** / **Corollary 9** of the revised TeX note. -/
def primitiveTrunc (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  trunc (primitiveKernel A) N

/-- The explicit sieve remainder `R_N`. -/
noncomputable def R (A : Set ℕ) (N : ℕ) : ℝ :=
  finiteAvoidDensity (primitiveTrunc A N)

/-- Positive integers divisible by none of the elements of `F`.  This is the
finite avoidance set whose density is `finiteAvoidDensity F`. -/
def AvoidSet (F : Finset ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∀ a ∈ F, ¬ a ∣ n}

/-! ## Basic set-theoretic lemmas -/

lemma mem_trunc {A : Set ℕ} {N a : ℕ} :
    a ∈ trunc A N ↔ (1 ≤ a ∧ a ≤ N) ∧ a ∈ A := by
  simp [trunc]

lemma trunc_subset (A : Set ℕ) (N : ℕ) :
    (((trunc A N : Finset ℕ) : Set ℕ) ⊆ A) := by
  intro a ha
  have hmem : a ∈ trunc A N := ha
  exact ((mem_trunc (A := A) (N := N) (a := a)).1 hmem).2

lemma trunc_positive (A : Set ℕ) (N : ℕ) :
    PositiveFinset (trunc A N) := by
  intro a ha
  have hmem := (mem_trunc (A := A) (N := N) (a := a)).1 ha
  exact lt_of_lt_of_le Nat.zero_lt_one hmem.1.1

lemma primitiveTrunc_positive (A : Set ℕ) (N : ℕ) :
    PositiveFinset (primitiveTrunc A N) := by
  simpa [primitiveTrunc] using (trunc_positive (A := primitiveKernel A) N)

lemma primitiveKernel_subset (A : Set ℕ) :
    primitiveKernel A ⊆ A := by
  intro a ha
  exact ha.1

lemma Multiples_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    Multiples A ⊆ Multiples B := by
  intro n hn
  rcases hn with ⟨hnpos, a, haA, hapos, hadiv⟩
  exact ⟨hnpos, a, hAB haA, hapos, hadiv⟩

/-- The crucial localization lemma for the forward implication:
if `n ≤ N`, then membership of `n` in `Multiples A` depends only on `A ∩ [1,N]`. -/
lemma mem_Multiples_trunc_iff_of_le {A : Set ℕ} {n N : ℕ} (hnN : n ≤ N) :
    n ∈ Multiples A ↔ n ∈ Multiples (((trunc A N : Finset ℕ) : Set ℕ)) := by
  constructor
  · intro hn
    rcases hn with ⟨hnpos, a, haA, hapos, hadiv⟩
    have ha_le_n : a ≤ n := Nat.le_of_dvd hnpos hadiv
    have ha_le_N : a ≤ N := le_trans ha_le_n hnN
    have ha_trunc : a ∈ trunc A N := by
      refine (mem_trunc (A := A) (N := N) (a := a)).2 ?_
      exact ⟨⟨Nat.succ_le_of_lt hapos, ha_le_N⟩, haA⟩
    exact ⟨hnpos, a, ha_trunc, hapos, hadiv⟩
  · intro hn
    have hsubset : (((trunc A N : Finset ℕ) : Set ℕ) ⊆ A) := trunc_subset A N
    exact (Multiples_mono hsubset) hn

lemma finiteMultiplesDensity_eq_one_sub_R (A : Set ℕ) (N : ℕ) :
    finiteMultiplesDensity (primitiveTrunc A N) = 1 - R A N := by
  rfl

/-! ## Density-to-Dirichlet Compatibility Lemmas -/

lemma hasNatDensity_iff_densityToDirichletHasNatDensity {S : Set ℕ} {δ : ℝ} :
    HasNatDensity S δ ↔ Erdos691.DensityToDirichlet.HasNatDensity S δ := by
  rfl

lemma densityToDirichlet_numerator_eq {S : Set ℕ} {s : ℝ} (hs : 1 < s) :
    Erdos691.DensityToDirichlet.numerator s S =
      ∑' n : ℕ, if n + 1 ∈ S then zetaTerm s n else 0 := by
  have hsum :
      Summable (fun n : ℕ => Erdos691.DensityToDirichlet.coeff S n / (n : ℝ) ^ s) :=
    Erdos691.DensityToDirichlet.numerator_summable (B := S) hs
  calc
    Erdos691.DensityToDirichlet.numerator s S
        = Erdos691.DensityToDirichlet.coeff S 0 / ((0 : ℕ) : ℝ) ^ s
            + ∑' n : ℕ, Erdos691.DensityToDirichlet.coeff S (n + 1) / ((n + 1 : ℕ) : ℝ) ^ s := by
              rw [Erdos691.DensityToDirichlet.numerator, hsum.tsum_eq_zero_add]
    _ = ∑' n : ℕ, Erdos691.DensityToDirichlet.coeff S (n + 1) / ((n + 1 : ℕ) : ℝ) ^ s := by
          simp [Erdos691.DensityToDirichlet.coeff_zero]
    _ = ∑' n : ℕ, if n + 1 ∈ S then zetaTerm s n else 0 := by
          refine tsum_congr ?_
          intro n
          by_cases h : n + 1 ∈ S
          · simp [Erdos691.DensityToDirichlet.coeff, zetaTerm, h]
          · simp [Erdos691.DensityToDirichlet.coeff, zetaTerm, h]

lemma densityToDirichlet_zetaDenom_eq {s : ℝ} (hs : 1 < s) :
    Erdos691.DensityToDirichlet.zetaDenom s = zetaReal s := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s) :=
    summable_one_div_nat_rpow.mpr hs
  have hs0 : s ≠ 0 := by linarith
  calc
    Erdos691.DensityToDirichlet.zetaDenom s = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
      rfl
    _ = 1 / (0 : ℝ) ^ s + ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ s := by
      simpa using hsum.tsum_eq_zero_add
    _ = zetaReal s := by
      simp [zetaReal, zetaTerm, Real.zero_rpow hs0]

lemma mu_eq_densityToDirichlet_mu_of_gt_one {S : Set ℕ} {s : ℝ} (hs : 1 < s) :
    mu s S = Erdos691.DensityToDirichlet.mu s S := by
  rw [mu, Erdos691.DensityToDirichlet.mu, densityToDirichlet_numerator_eq (S := S) hs,
    densityToDirichlet_zetaDenom_eq hs]

/-- **Lemma 5** (`lem:density-to-Dirichlet`) in the revised self-contained TeX note.

If `S` has natural density `δ`, then the Dirichlet densities `mu s S` converge to `δ`
as `s ↓ 1`.  This is obtained by transporting the proof in `Erdos691.DensityToDirichlet`
to the shifted series conventions used in the present file. -/
theorem tendsto_mu_of_hasNatDensity
  {S : Set ℕ} {δ : ℝ} :
  HasNatDensity S δ →
    Tendsto (fun s : ℝ => mu s S)
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds δ) := by
  intro hS
  have hS' : Erdos691.DensityToDirichlet.HasNatDensity S δ :=
    (hasNatDensity_iff_densityToDirichletHasNatDensity (S := S) (δ := δ)).1 hS
  have hcompat :
      (fun s : ℝ => mu s S) =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))]
        fun s : ℝ => Erdos691.DensityToDirichlet.mu s S := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    exact mu_eq_densityToDirichlet_mu_of_gt_one (S := S) hs
  refine Tendsto.congr' hcompat.symm ?_
  simpa using Erdos691.DensityToDirichlet.tendsto_mu_of_hasNatDensity (B := S) (δ := δ) hS'

/-! ## Finite-stage density infrastructure -/


lemma mem_Multiples_finset_iff
    {F : Finset ℕ} (hFpos : PositiveFinset F) {n : ℕ} (hn : 0 < n) :
    n ∈ Multiples ((F : Set ℕ)) ↔ ∃ a ∈ F, a ∣ n := by
  constructor
  · rintro ⟨_, a, haF, _, hadiv⟩
    exact ⟨a, haF, hadiv⟩
  · rintro ⟨a, haF, hadiv⟩
    exact ⟨hn, a, haF, hFpos haF, hadiv⟩

lemma countUpTo_eq_nat_count_shift (S : Set ℕ) (M : ℕ) :
    countUpTo S M = Nat.count (fun n => n + 1 ∈ S) M := by
  classical
  unfold countUpTo
  rw [Nat.count_eq_card_filter_range]
  let e : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  have hmap :
      ((Finset.range M).filter fun n => n + 1 ∈ S).map e =
        (Finset.Icc 1 M).filter fun n => n ∈ S := by
    ext n
    simp [e, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨haM, haS⟩, rfl⟩
      exact ⟨⟨Nat.succ_le_succ (Nat.zero_le a), Nat.succ_le_of_lt haM⟩, by simpa using haS⟩
    · rintro ⟨⟨hn1, hnM⟩, hnS⟩
      refine ⟨n - 1, ?_, Nat.sub_add_cancel hn1⟩
      refine ⟨by omega, ?_⟩
      simpa [Nat.sub_add_cancel hn1] using hnS
  rw [← hmap, Finset.card_map]

lemma mem_AvoidSet_iff_not_mem_Multiples
    {F : Finset ℕ} (hFpos : PositiveFinset F) {n : ℕ} (hn : 0 < n) :
    n ∈ AvoidSet F ↔ n ∉ Multiples ((F : Set ℕ)) := by
  constructor
  · intro hnAvoid hmul
    rcases hnAvoid with ⟨_, hnodiv⟩
    rcases (mem_Multiples_finset_iff (F := F) hFpos (n := n) hn).1 hmul with
      ⟨a, haF, hadiv⟩
    exact hnodiv a haF hadiv
  · intro hnotmul
    refine ⟨hn, ?_⟩
    intro a haF hadiv
    exact hnotmul <|
      (mem_Multiples_finset_iff (F := F) hFpos (n := n) hn).2 ⟨a, haF, hadiv⟩

lemma countUpTo_avoidSet_add_countUpTo_multiples
    (F : Finset ℕ) (hFpos : PositiveFinset F) (N : ℕ) :
    countUpTo (AvoidSet F) N + countUpTo (Multiples ((F : Set ℕ))) N = N := by
  classical
  have hEq :
      ((Finset.Icc 1 N).filter fun n => n ∈ AvoidSet F) =
        (Finset.Icc 1 N).filter fun n => ¬ n ∈ Multiples ((F : Set ℕ)) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnAvoid⟩
      refine Finset.mem_filter.mpr ⟨hnIcc, ?_⟩
      have hnPos : 0 < n := by
        exact (Finset.mem_Icc.mp hnIcc).1
      exact (mem_AvoidSet_iff_not_mem_Multiples (F := F) hFpos
        (n := n) hnPos).1 hnAvoid
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnotmul⟩
      refine Finset.mem_filter.mpr ⟨hnIcc, ?_⟩
      have hnPos : 0 < n := by
        exact (Finset.mem_Icc.mp hnIcc).1
      exact (mem_AvoidSet_iff_not_mem_Multiples (F := F) hFpos
        (n := n) hnPos).2 hnotmul
  have hpart :
      ((Finset.Icc 1 N).filter fun n => n ∈ Multiples ((F : Set ℕ))).card +
        ((Finset.Icc 1 N).filter fun n => n ∈ AvoidSet F).card =
      (Finset.Icc 1 N).card := by
    calc
      ((Finset.Icc 1 N).filter fun n => n ∈ Multiples ((F : Set ℕ))).card +
          ((Finset.Icc 1 N).filter fun n => n ∈ AvoidSet F).card
          = ((Finset.Icc 1 N).filter fun n => n ∈ Multiples ((F : Set ℕ))).card +
              ((Finset.Icc 1 N).filter fun n => ¬ n ∈ Multiples ((F : Set ℕ))).card := by
                rw [hEq]
      _ = (Finset.Icc 1 N).card := by
            simpa using
              (Finset.card_filter_add_card_filter_not
                (s := Finset.Icc 1 N) (p := fun n => n ∈ Multiples ((F : Set ℕ))))
  calc
    countUpTo (AvoidSet F) N + countUpTo (Multiples ((F : Set ℕ))) N
        = ((Finset.Icc 1 N).filter fun n => n ∈ AvoidSet F).card +
            ((Finset.Icc 1 N).filter fun n => n ∈ Multiples ((F : Set ℕ))).card := by
              simp [countUpTo]
    _ = ((Finset.Icc 1 N).filter fun n => n ∈ Multiples ((F : Set ℕ))).card +
          ((Finset.Icc 1 N).filter fun n => n ∈ AvoidSet F).card := by
            rw [Nat.add_comm]
    _ = (Finset.Icc 1 N).card := hpart
    _ = N := by simp

lemma densSeq_avoidSet_eq_one_sub_densSeq_multiples
    (F : Finset ℕ) (hFpos : PositiveFinset F) (N : ℕ) :
    densSeq (AvoidSet F) N = 1 - densSeq (Multiples ((F : Set ℕ))) N := by
  have hcount_nat :
      countUpTo (AvoidSet F) (N + 1) + countUpTo (Multiples ((F : Set ℕ))) (N + 1) = N + 1 :=
    countUpTo_avoidSet_add_countUpTo_multiples F hFpos (N + 1)
  have hcount :
      (countUpTo (AvoidSet F) (N + 1) : ℝ) +
          (countUpTo (Multiples ((F : Set ℕ))) (N + 1) : ℝ) =
        (N + 1 : ℝ) := by
    exact_mod_cast hcount_nat
  have hcount' :
      (countUpTo (AvoidSet F) (N + 1) : ℝ) =
        (N + 1 : ℝ) - (countUpTo (Multiples ((F : Set ℕ))) (N + 1) : ℝ) := by
    linarith
  have hN0 : (N + 1 : ℝ) ≠ 0 := by positivity
  calc
    densSeq (AvoidSet F) N
        = ((N + 1 : ℝ) -
            (countUpTo (Multiples ((F : Set ℕ))) (N + 1) : ℝ)) / (N + 1 : ℝ) := by
            unfold densSeq
            rw [hcount']
    _ = (N + 1 : ℝ) / (N + 1 : ℝ) -
          (countUpTo (Multiples ((F : Set ℕ))) (N + 1) : ℝ) / (N + 1 : ℝ) := by
            rw [sub_div]
    _ = 1 - densSeq (Multiples ((F : Set ℕ))) N := by
          rw [div_self hN0]
          rfl

lemma card_univ_filter_subtype_eq_card_filter
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x : s => p x)).card = (s.filter p).card := by
  classical
  rw [Finset.univ_eq_attach, Finset.filter_attach, Finset.card_map, Finset.card_attach]

lemma mem_finsetInf
    {ι α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset ι} {f : ι → Finset α} {a : α} :
    a ∈ s.inf f ↔ ∀ i ∈ s, a ∈ f i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    simp [Finset.inf_insert, hi, ih, and_left_comm, and_assoc]

lemma lcm0_pos (F : Finset ℕ) (hFpos : PositiveFinset F) : 0 < lcm0 F := by
  have hne : lcm0 F ≠ 0 := by
    simpa [lcm0] using
      (Finset.lcm_ne_zero_iff (s := F) (f := id)).2
        (fun a ha => Nat.ne_of_gt (hFpos ha))
  exact Nat.pos_of_ne_zero hne


/-- For a positive finite set `F`, the natural density of `Multiples F` exists and is given by
the inclusion-exclusion expression `finiteMultiplesDensity F`.

Proof idea:
* put `L := lcm0 F`;
* divisibility by elements of `F` is periodic mod `L`;
* on one period, intersections are controlled by `lcm0 G`;
* inclusion-exclusion gives the exact block density. -/
theorem hasNatDensity_multiples_finset
  (F : Finset ℕ) (hFpos : PositiveFinset F) :
    HasNatDensity (Multiples ((F : Set ℕ))) (finiteMultiplesDensity F) := by
  classical
  set L : ℕ := lcm0 F with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact lcm0_pos F hFpos
  let p : ℕ → Prop := fun n => ∃ a ∈ F, a ∣ n + 1
  have hp_eq : (fun n : ℕ => n + 1 ∈ Multiples ((F : Set ℕ))) = p := by
    funext n
    apply propext
    simpa [p] using
      (mem_Multiples_finset_iff (F := F) hFpos (n := n + 1) (Nat.succ_pos n))
  have hp_periodic : Function.Periodic p L := by
    intro n
    apply propext
    constructor
    · rintro ⟨a, haF, hadiv⟩
      have haL : a ∣ L := by
        rw [hL, lcm0]
        exact Finset.dvd_lcm (f := id) haF
      have hsum : a ∣ L + (n + 1) := by
        simpa [add_assoc, add_left_comm, add_comm] using hadiv
      exact ⟨a, haF, (Nat.dvd_add_right haL).mp hsum⟩
    · rintro ⟨a, haF, hadiv⟩
      have haL : a ∣ L := by
        rw [hL, lcm0]
        exact Finset.dvd_lcm (f := id) haF
      have hsum : a ∣ L + (n + 1) := dvd_add haL hadiv
      exact ⟨a, haF, by simpa [add_assoc, add_left_comm, add_comm] using hsum⟩
  have hcount_eq : ∀ M : ℕ,
      countUpTo (Multiples ((F : Set ℕ))) M = Nat.count p M := by
    intro M
    simpa [hp_eq] using countUpTo_eq_nat_count_shift (S := Multiples ((F : Set ℕ))) M
  let c : ℕ := Nat.count p L
  have hcdef : c = Nat.count p L := rfl
  have hc_le : c ≤ L := by
    simpa [hcdef] using (Nat.count_le (p := p) (n := L))
  have hshift_fun : ∀ q : ℕ, (fun k : ℕ => p (q * L + k)) = p := by
    intro q
    funext k
    simpa [add_assoc, add_left_comm, add_comm, Nat.mul_comm] using (hp_periodic.nat_mul q k)
  have hcount_mul : ∀ q : ℕ, Nat.count p (q * L) = q * c := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        calc
          Nat.count p ((q + 1) * L)
              = Nat.count p (q * L + L) := by rw [Nat.succ_mul]
          _ = Nat.count p (q * L) + Nat.count (fun k ↦ p (q * L + k)) L := by
              rw [Nat.count_add (p := p)]
          _ = Nat.count p (q * L) + Nat.count p L := by
              simp [hshift_fun q]
          _ = Nat.count p (q * L) + c := by rw [← hcdef]
          _ = q * c + c := by rw [ih]
          _ = (q + 1) * c := by rw [Nat.succ_mul]
  have hcount_decomp : ∀ M : ℕ, Nat.count p M = (M / L) * c + Nat.count p (M % L) := by
    intro M
    calc
      Nat.count p M = Nat.count p (L * (M / L) + M % L) := by
        simpa [Nat.mul_comm] using congrArg (Nat.count p) (Nat.div_add_mod M L).symm
      _ = Nat.count p (L * (M / L)) + Nat.count (fun k ↦ p (L * (M / L) + k)) (M % L) := by
          rw [Nat.count_add (p := p)]
      _ = Nat.count p ((M / L) * L) + Nat.count p (M % L) := by
          rw [Nat.mul_comm L (M / L)]
          simp [hshift_fun (M / L)]
      _ = (M / L) * c + Nat.count p (M % L) := by rw [hcount_mul (M / L)]
  let T : ℕ → Finset ↥(Finset.range L) :=
    fun a => Finset.univ.filter fun n : ↥(Finset.range L) => a ∣ (n : ℕ) + 1
  let avoid : ℕ := Nat.count (fun n => ∀ a ∈ F, ¬ a ∣ n + 1) L
  have havoiddef : avoid = Nat.count (fun n => ∀ a ∈ F, ¬ a ∣ n + 1) L := rfl
  have havoid_card : (F.inf fun a ↦ (T a)ᶜ).card = avoid := by
    have hEq :
        F.inf (fun a ↦ (T a)ᶜ) =
          Finset.univ.filter
            (fun n : ↥(Finset.range L) => ∀ a ∈ F, ¬ a ∣ (n : ℕ) + 1) := by
      ext n
      simp [T, mem_finsetInf]
    rw [havoiddef]
    rw [hEq]
    rw [card_univ_filter_subtype_eq_card_filter
      (s := Finset.range L) (p := fun n => ∀ a ∈ F, ¬ a ∣ n + 1)]
    rw [Nat.count_eq_card_filter_range]
  have hcard_inter (G : Finset ℕ) : (G.inf T).card = L / lcm0 G := by
    have hEq :
        G.inf T =
          Finset.univ.filter
            (fun n : ↥(Finset.range L) => ∀ a ∈ G, a ∣ (n : ℕ) + 1) := by
      ext n
      simp [T, mem_finsetInf]
    have hfilter :
        (Finset.range L).filter (fun n => ∀ a ∈ G, a ∣ n + 1) =
          (Finset.range L).filter (fun n => lcm0 G ∣ n + 1) := by
      ext n
      simp [lcm0, Finset.lcm_dvd_iff]
    rw [hEq]
    rw [card_univ_filter_subtype_eq_card_filter
      (s := Finset.range L) (p := fun n => ∀ a ∈ G, a ∣ n + 1)]
    rw [hfilter, Nat.card_multiples]
  have havoid_card_int :
      (avoid : ℤ) = ((F.inf fun a ↦ (T a)ᶜ).card : ℤ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) havoid_card.symm
    simpa using hcast
  have havoid_int :
      (avoid : ℤ) =
        Finset.sum F.powerset (fun G => (-1 : ℤ) ^ G.card * ((L / lcm0 G : ℕ) : ℤ)) := by
    calc
      (avoid : ℤ) = ((F.inf fun a ↦ (T a)ᶜ).card : ℤ) := havoid_card_int
      _ =
          Finset.sum F.powerset
            (fun G => (-1 : ℤ) ^ G.card * ((G.inf T).card : ℤ)) := by
          simpa using (Finset.inclusion_exclusion_card_inf_compl F T)
      _ =
          Finset.sum F.powerset
            (fun G => (-1 : ℤ) ^ G.card * ((L / lcm0 G : ℕ) : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro G hG
          simp [hcard_inter G]
  have havoid_real :
      (avoid : ℝ) =
        Finset.sum F.powerset (fun G => (-1 : ℝ) ^ G.card * ((L / lcm0 G : ℕ) : ℝ)) := by
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) havoid_int
    calc
      (avoid : ℝ) =
          Finset.sum F.powerset
            (fun G => (((-1 : ℤ) ^ G.card * ((L / lcm0 G : ℕ) : ℤ)) : ℝ)) := by
          simpa using hcast
      _ = Finset.sum F.powerset (fun G => (-1 : ℝ) ^ G.card * ((L / lcm0 G : ℕ) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro G hG
          have hdivi : (↑L / ↑(lcm0 G) : ℤ) = ((L / lcm0 G : ℕ) : ℤ) := by
            exact (Int.natCast_div L (lcm0 G)).symm
          have hdivr : ((↑L / ↑(lcm0 G) : ℤ) : ℝ) = ((L / lcm0 G : ℕ) : ℝ) := by
            exact congrArg (fun z : ℤ => (z : ℝ)) hdivi
          change (↑(-1 : ℤ) : ℝ) ^ G.card * (((↑L / ↑(lcm0 G) : ℤ) : ℝ)) =
            (-1 : ℝ) ^ G.card * ((L / lcm0 G : ℕ) : ℝ)
          calc
            (↑(-1 : ℤ) : ℝ) ^ G.card * (((↑L / ↑(lcm0 G) : ℤ) : ℝ))
                = (↑(-1 : ℤ) : ℝ) ^ G.card * ((L / lcm0 G : ℕ) : ℝ) := by
                    exact congrArg (fun x : ℝ => (↑(-1 : ℤ) : ℝ) ^ G.card * x) hdivr
            _ = (-1 : ℝ) ^ G.card * ((L / lcm0 G : ℕ) : ℝ) := by
                norm_num
  have havoid_mul : (avoid : ℝ) = (L : ℝ) * finiteAvoidDensity F := by
    calc
      (avoid : ℝ) =
          Finset.sum F.powerset
            (fun G => (-1 : ℝ) ^ G.card * ((L / lcm0 G : ℕ) : ℝ)) := havoid_real
      _ =
          Finset.sum F.powerset
            (fun G => (L : ℝ) * (((-1 : ℝ) ^ G.card) / (lcm0 G : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro G hG
          have hGF : G ⊆ F := Finset.mem_powerset.mp hG
          have hdiv : lcm0 G ∣ L := by
            rw [hL, lcm0]
            apply Finset.lcm_dvd
            intro a ha
            exact Finset.dvd_lcm (f := id) (hGF ha)
          rw [Nat.cast_div_charZero (K := ℝ) hdiv]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ = (L : ℝ) * Finset.sum F.powerset (fun G => (-1 : ℝ) ^ G.card / (lcm0 G : ℝ)) := by
          rw [← Finset.mul_sum]
      _ = (L : ℝ) * finiteAvoidDensity F := by
          rw [finiteAvoidDensity]
  have hL0 : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hLpos)
  have havoid_div : (avoid : ℝ) / (L : ℝ) = finiteAvoidDensity F := by
    calc
      (avoid : ℝ) / (L : ℝ) = ((L : ℝ) * finiteAvoidDensity F) / (L : ℝ) := by rw [havoid_mul]
      _ = finiteAvoidDensity F := by
          field_simp [hL0]
  have hcount_add_avoid : c + avoid = L := by
    have hpred :
        (fun n : ℕ => ∀ a ∈ F, ¬ a ∣ n + 1) = fun n : ℕ => ¬ p n := by
      funext n
      simp [p]
    rw [hcdef, havoiddef]
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    simpa [hpred] using (Finset.card_filter_add_card_filter_not (s := Finset.range L) (p := p))
  let d0 : ℝ := (c : ℝ) / (L : ℝ)
  have hd0def : d0 = (c : ℝ) / (L : ℝ) := rfl
  have hd0_eq : d0 = finiteMultiplesDensity F := by
    have hsumR : (c : ℝ) + (avoid : ℝ) = (L : ℝ) := by
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcount_add_avoid
      simpa using hcast
    have hc_eq : (c : ℝ) = (L : ℝ) - (avoid : ℝ) := by
      linarith
    calc
      d0 = ((L : ℝ) - (avoid : ℝ)) / (L : ℝ) := by rw [hd0def, hc_eq]
      _ = 1 - (avoid : ℝ) / (L : ℝ) := by
          field_simp [hL0]
      _ = 1 - finiteAvoidDensity F := by rw [havoid_div]
      _ = finiteMultiplesDensity F := by simp [finiteMultiplesDensity]
  have hlim : HasNatDensity (Multiples ((F : Set ℕ))) d0 := by
    unfold HasNatDensity
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    have hzero :
        Tendsto (fun N : ℕ => (2 * L : ℝ) / (N + 1 : ℝ)) Filter.atTop (nhds 0) := by
      convert
        (tendsto_const_div_atTop_nhds_zero_nat (2 * L : ℝ)).comp (tendsto_add_atTop_nat 1) using 1
      ext N
      simp [Nat.cast_add, Nat.cast_one]
    rcases Metric.tendsto_atTop.1 hzero ε hε with ⟨N0, hN0⟩
    refine ⟨N0, ?_⟩
    intro N hN
    let q : ℕ := (N + 1) / L
    let r : ℕ := (N + 1) % L
    let rem : ℕ := Nat.count p r
    have hcountN : countUpTo (Multiples ((F : Set ℕ))) (N + 1) = q * c + rem := by
      dsimp [q, r, rem]
      rw [hcount_eq (N + 1), hcount_decomp (N + 1)]
    have hcountN' :
        (countUpTo (Multiples ((F : Set ℕ))) (N + 1) : ℝ) =
          (q : ℝ) * (c : ℝ) + (rem : ℝ) := by
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcountN
      simpa using hcast
    have hdecompR : (N + 1 : ℝ) = (q : ℝ) * (L : ℝ) + (r : ℝ) := by
      dsimp [q, r]
      have hcast :
          (L : ℝ) * (((N + 1) / L : ℕ) : ℝ) + (((N + 1) % L : ℕ) : ℝ) = (N + 1 : ℝ) := by
        exact_mod_cast (Nat.div_add_mod (N + 1) L)
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hcast.symm
    have hr_lt : r < L := by
      dsimp [r]
      exact Nat.mod_lt _ hLpos
    have hr_le : r ≤ L := hr_lt.le
    have hrem_le : rem ≤ L := by
      dsimp [rem]
      exact (Nat.count_le (p := p) (n := r)).trans hr_le
    have hNpos : 0 < (N + 1 : ℝ) := by positivity
    have hN0' : (N + 1 : ℝ) ≠ 0 := ne_of_gt hNpos
    let num : ℝ := (L : ℝ) * (rem : ℝ) - (c : ℝ) * (r : ℝ)
    have hdiff :
        densSeq (Multiples ((F : Set ℕ))) N - d0 =
          num / ((L : ℝ) * (N + 1 : ℝ)) := by
      rw [hd0def]
      unfold densSeq
      rw [hcountN']
      dsimp [num]
      field_simp [hL0, hN0']
      nlinarith [hdecompR]
    have hnum_bound : |num| ≤ (2 : ℝ) * L * L := by
      have hcR : (c : ℝ) ≤ L := by
        exact_mod_cast hc_le
      have hrR : (r : ℝ) ≤ L := by
        exact_mod_cast hr_le
      have hremR : (rem : ℝ) ≤ L := by
        exact_mod_cast hrem_le
      have htriangle :
          |num| ≤ |(L : ℝ) * (rem : ℝ) - 0| + |0 - (c : ℝ) * (r : ℝ)| := by
        dsimp [num]
        simpa using (_root_.abs_sub_le ((L : ℝ) * (rem : ℝ)) 0 ((c : ℝ) * (r : ℝ)))
      have hLnonneg : 0 ≤ (L : ℝ) := by positivity
      have hremnonneg : 0 ≤ (rem : ℝ) := by positivity
      have hcnonneg : 0 ≤ (c : ℝ) := by positivity
      have hrnonneg : 0 ≤ (r : ℝ) := by positivity
      have haux :
          (L : ℝ) * (rem : ℝ) + (c : ℝ) * (r : ℝ) ≤ (2 : ℝ) * L * L := by
        nlinarith [hcR, hrR, hremR, hLnonneg, hremnonneg, hcnonneg, hrnonneg]
      calc
        |num| ≤ |(L : ℝ) * (rem : ℝ) - 0| + |0 - (c : ℝ) * (r : ℝ)| := htriangle
        _ = (L : ℝ) * (rem : ℝ) + (c : ℝ) * (r : ℝ) := by
            rw [sub_zero, zero_sub, abs_neg,
              abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        _ ≤ (2 : ℝ) * L * L := haux
    have hden_pos : 0 < (L : ℝ) * (N + 1 : ℝ) := by positivity
    have hdist_bound :
        dist (densSeq (Multiples ((F : Set ℕ))) N) d0 ≤ (2 * L : ℝ) / (N + 1 : ℝ) := by
      rw [Real.dist_eq, hdiff, abs_div, abs_of_pos hden_pos]
      calc
        |num| / ((L : ℝ) * (N + 1 : ℝ)) ≤ ((2 : ℝ) * L * L) / ((L : ℝ) * (N + 1 : ℝ)) := by
            exact div_le_div_of_nonneg_right hnum_bound hden_pos.le
        _ = (2 * L : ℝ) / (N + 1 : ℝ) := by
            field_simp [hL0, hN0']
    have hsmall : (2 * L : ℝ) / (N + 1 : ℝ) < ε := by
      have hbound := hN0 N hN
      have hnonneg : 0 ≤ (2 * L : ℝ) / (N + 1 : ℝ) := by positivity
      have htwononneg : 0 ≤ (2 * L : ℝ) := by positivity
      have habs : (2 * L : ℝ) / |(N + 1 : ℝ)| < ε := by
        simpa [Real.dist_eq, sub_zero, abs_of_nonneg htwononneg, Nat.cast_add, Nat.cast_one]
          using hbound
      have hsmall' : (2 * L : ℝ) / (N + 1 : ℝ) < ε := by
        simpa [abs_of_pos hNpos] using habs
      exact hsmall'
    exact lt_of_le_of_lt hdist_bound hsmall
  simpa [hd0_eq] using hlim

/-- Finite avoidance-set version of the periodic-density computation.

This is the standalone theorem matching the sentence in the TeX corollary: the
inclusion-exclusion expression `finiteAvoidDensity F` is the natural density of
the positive integers divisible by none of the elements of `F`. -/
theorem hasNatDensity_avoidSet_finset
  (F : Finset ℕ) (hFpos : PositiveFinset F) :
    HasNatDensity (AvoidSet F) (finiteAvoidDensity F) := by
  have hmult :
      HasNatDensity (Multiples ((F : Set ℕ))) (finiteMultiplesDensity F) :=
    hasNatDensity_multiples_finset F hFpos
  have hsub :
      Tendsto (fun N : ℕ => 1 - densSeq (Multiples ((F : Set ℕ))) N)
        Filter.atTop (nhds (1 - finiteMultiplesDensity F)) := by
    simpa using (tendsto_const_nhds.sub hmult)
  have havoid :
      Tendsto (fun N : ℕ => densSeq (AvoidSet F) N)
        Filter.atTop (nhds (1 - finiteMultiplesDensity F)) := by
    convert hsub using 1
    ext N
    exact densSeq_avoidSet_eq_one_sub_densSeq_multiples F hFpos N
  have hδ : 1 - finiteMultiplesDensity F = finiteAvoidDensity F := by
    unfold finiteMultiplesDensity
    ring
  simpa [HasNatDensity, hδ] using havoid

/-! ## Finite-stage precursor of Lemma 6 via exponent space -/

/-!
# Finite-stage precursor of Lemma 6 via exponent space

This section contains the finite-dimensional product-geometric argument underlying the
finite-stage precursor of **Lemma 6** (`lem:divisibility-monotone`).

The strategy is:

* equip the exponent-vector space `ι → ℕ` with the product geometric law `nu q`;
* prove monotonicity of `nu q U` for upward-closed events under coordinatewise increase
  of the ratios;
* specialize to the event attached to multiples generated by a positive finite set;
* identify the exponent-space model with the original Dirichlet density `mu`.

The main technical ingredients are

* `geomAverage_mono_of_monotone`
* `nu_option_eq_geomAverage`
* `nu_mono_of_coordwise_le`

の 3 箇所です．
-/

/-- Coordinatewise upward-closed subset of a preorder. -/
def UpwardClosed {α : Type*} [Preorder α] (U : Set α) : Prop :=
  ∀ ⦃x y : α⦄, x ≤ y → x ∈ U → y ∈ U

section ProductGeometric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One-dimensional geometric weight with ratio `q`.

Later we use `q = p^{-s}` with `0 ≤ q < 1`.
-/
noncomputable def geomWeightOfRatio (q : ℝ) (k : ℕ) : ℝ :=
  (1 - q) * q ^ k

/-- Average of `f : ℕ → ℝ` against the geometric law of ratio `q`. -/
noncomputable def geomAverage (q : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, geomWeightOfRatio q k * f k

/-- Product weight on exponent vectors. -/
noncomputable def vecWeight (q : ι → ℝ) (v : ι → ℕ) : ℝ :=
  ∏ i, geomWeightOfRatio (q i) (v i)

/-- Product-geometric mass of an event in exponent space. -/
noncomputable def nu (q : ι → ℝ) (U : Set (ι → ℕ)) : ℝ :=
  by
    classical
    exact ∑' v : (ι → ℕ), if v ∈ U then vecWeight q v else 0

/-- `consVec k w` is the vector on `Option ι` obtained by putting `k` in the new coordinate. -/
def consVec {ι : Type*} (k : ℕ) (w : ι → ℕ) : Option ι → ℕ
  | none => k
  | some i => w i

/-- Section of an event at the new coordinate `k`. -/
def sectionAt {ι : Type*} (U : Set (Option ι → ℕ)) (k : ℕ) : Set (ι → ℕ) :=
  {w | consVec k w ∈ U}

/-- Explicit equivalence `(Option ι → ℕ) ≃ ℕ × (ι → ℕ)`.

This is useful for `tsum` reindexing in the option-step of the induction. -/
def optionVecEquivProd (ι : Type*) : (Option ι → ℕ) ≃ ℕ × (ι → ℕ) where
  toFun v := (v none, fun i => v (some i))
  invFun x := fun
    | none => x.1
    | some i => x.2 i
  left_inv v := by
    funext o
    cases o <;> rfl
  right_inv x := by
    cases x
    rfl

lemma section_upwardClosed {ι : Type*} {U : Set (Option ι → ℕ)}
    (hU : UpwardClosed U) (k : ℕ) :
    UpwardClosed (sectionAt U k) := by
  intro w z hwz hw
  exact hU (x := consVec k w) (y := consVec k z)
    (by
      intro i
      cases i with
      | none => exact le_rfl
      | some i => exact hwz i)
    (by simpa [sectionAt] using hw)

lemma section_mono {ι : Type*} {U : Set (Option ι → ℕ)}
    (hU : UpwardClosed U) :
    Monotone (sectionAt U) := by
  intro k l hkl w hw
  have hmem : consVec l w ∈ U := hU (x := consVec k w) (y := consVec l w)
    (by
      intro i
      cases i with
      | none => exact hkl
      | some i => exact le_rfl)
    (by simpa [sectionAt] using hw)
  simpa [sectionAt] using hmem

lemma geomWeight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    0 ≤ geomWeightOfRatio q k := by
  dsimp [geomWeightOfRatio]
  exact mul_nonneg (sub_nonneg.mpr hq1) (pow_nonneg hq0 _)

/-- Monotonicity in the function argument.  This is a tiny helper used in the induction step. -/
lemma geomAverage_mono_right {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {f g : ℕ → ℝ} (hfg : ∀ k, f k ≤ g k)
    (hf_bdd : ∀ k, 0 ≤ f k ∧ f k ≤ 1)
    (hg_bdd : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    geomAverage q f ≤ geomAverage q g := by
  have hs_weight : Summable (fun k : ℕ => geomWeightOfRatio q k) := by
    by_cases hq : q = 1
    · subst hq
      simp [geomWeightOfRatio]
    · have hq_lt : q < 1 := lt_of_le_of_ne hq1 hq
      simpa [geomWeightOfRatio] using
        Summable.mul_left (1 - q) (summable_geometric_of_lt_one hq0 hq_lt)
  have hs_f : Summable (fun k : ℕ => geomWeightOfRatio q k * f k) := by
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (geomWeight_nonneg hq0 hq1 k) (hf_bdd k).1)
      ?_ hs_weight
    intro k
    have hw : 0 ≤ geomWeightOfRatio q k := geomWeight_nonneg hq0 hq1 k
    nlinarith [(hf_bdd k).2]
  have hs_g : Summable (fun k : ℕ => geomWeightOfRatio q k * g k) := by
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (geomWeight_nonneg hq0 hq1 k) (hg_bdd k).1)
      ?_ hs_weight
    intro k
    have hw : 0 ≤ geomWeightOfRatio q k := geomWeight_nonneg hq0 hq1 k
    nlinarith [(hg_bdd k).2]
  unfold geomAverage
  exact hs_f.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (hfg k) (geomWeight_nonneg hq0 hq1 k))
    hs_g

omit [DecidableEq ι] in
lemma vecWeight_nonneg {q : ι → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (v : ι → ℕ) :
    0 ≤ vecWeight q v := by
  classical
  unfold vecWeight
  exact Finset.prod_nonneg fun i _ => geomWeight_nonneg (hq0 i) (hq1 i) (v i)

lemma summable_geomWeight {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (geomWeightOfRatio q) := by
  convert (summable_geometric_of_lt_one hq0 hq1).mul_left (1 - q) using 1 <;> rfl

lemma geomWeight_tsum_eq_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k : ℕ, geomWeightOfRatio q k = 1 := by
  simp_rw [geomWeightOfRatio]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  exact mul_inv_cancel₀ (sub_ne_zero.mpr hq1.ne')

lemma vecWeight_consVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Option ι → ℝ) (k : ℕ) (w : ι → ℕ) :
    vecWeight q (consVec k w) =
      geomWeightOfRatio (q none) k * vecWeight (fun i : ι => q (some i)) w := by
  unfold vecWeight consVec
  rw [Fintype.prod_option]

lemma summable_vecWeight (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1) :
    Summable (vecWeight q) := by
  classical
  let P : ∀ (α : Type _) [Fintype α], Prop := fun α _ =>
    ∀ [DecidableEq α] (q : α → ℝ),
      (∀ i, 0 ≤ q i ∧ q i < 1) → Summable (vecWeight q)
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β _ e h _ q hq
      letI : Fintype α := Fintype.ofEquiv β e.symm
      let eVec : (α → ℕ) ≃ (β → ℕ) := Equiv.piCongrLeft' (fun _ => ℕ) e
      have hq' : ∀ a : α, 0 ≤ q (e a) ∧ q (e a) < 1 := by
        intro a
        simpa using hq (e a)
      have hs := h (fun a => q (e a)) hq'
      rw [← eVec.summable_iff]
      convert hs using 1
      ext v
      unfold vecWeight
      simpa [eVec] using
        (Equiv.prod_comp e (fun b => geomWeightOfRatio (q b) (v (e.symm b)))).symm
    · intro _ q hq
      simpa using (Summable.of_finite (f := vecWeight q))
    · intro α _ h _ q hq
      let q' : α → ℝ := fun i => q (some i)
      have hqnone0 : 0 ≤ q none := (hq none).1
      have hqnone1 : q none < 1 := (hq none).2
      have hq' : ∀ i : α, 0 ≤ q' i ∧ q' i < 1 := by
        intro i
        simpa [q'] using hq (some i)
      have hvec := h q' hq'
      have hgeom : Summable (geomWeightOfRatio (q none)) := summable_geomWeight hqnone0 hqnone1
      have hpair : Summable (fun x : ℕ × (α → ℕ) =>
          geomWeightOfRatio (q none) x.1 * vecWeight q' x.2) := by
        exact hgeom.mul_of_nonneg hvec
          (fun k => geomWeight_nonneg hqnone0 hqnone1.le k)
          (fun w => vecWeight_nonneg (fun i => (hq' i).1) (fun i => (hq' i).2.le) w)
      rw [← (optionVecEquivProd α).symm.summable_iff]
      convert hpair using 1
      ext x
      rcases x with ⟨k, w⟩
      convert (vecWeight_consVec q k w) using 1 <;> rfl
  exact hP q hq

lemma tsum_vecWeight_eq_one (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1) :
    ∑' v : ι → ℕ, vecWeight q v = 1 := by
  classical
  let P : ∀ (α : Type _) [Fintype α], Prop := fun α _ =>
    ∀ [DecidableEq α] (q : α → ℝ),
      (∀ i, 0 ≤ q i ∧ q i < 1) → ∑' v : α → ℕ, vecWeight q v = 1
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β _ e h _ q hq
      letI : Fintype α := Fintype.ofEquiv β e.symm
      let eVec : (α → ℕ) ≃ (β → ℕ) := Equiv.piCongrLeft' (fun _ => ℕ) e
      have hq' : ∀ a : α, 0 ≤ q (e a) ∧ q (e a) < 1 := by
        intro a
        simpa using hq (e a)
      rw [← eVec.tsum_eq (fun v : β → ℕ => vecWeight q v)]
      have hrewrite : (fun c : α → ℕ => vecWeight q (eVec c)) =
          fun c => vecWeight (fun a => q (e a)) c := by
        funext v
        unfold vecWeight
        simpa [eVec] using
          (Equiv.prod_comp e (fun b => geomWeightOfRatio (q b) (v (e.symm b)))).symm
      rw [hrewrite, h (fun a => q (e a)) hq']
    · intro _ q hq
      rw [tsum_fintype]
      simp [vecWeight]
    · intro α _ h _ q hq
      let q' : α → ℝ := fun i => q (some i)
      have hqnone0 : 0 ≤ q none := (hq none).1
      have hqnone1 : q none < 1 := (hq none).2
      have hq' : ∀ i : α, 0 ≤ q' i ∧ q' i < 1 := by
        intro i
        simpa [q'] using hq (some i)
      have hvec : Summable (vecWeight q') := summable_vecWeight q' hq'
      have hgeom : Summable (geomWeightOfRatio (q none)) := summable_geomWeight hqnone0 hqnone1
      have hpair : Summable (fun x : ℕ × (α → ℕ) =>
          geomWeightOfRatio (q none) x.1 * vecWeight q' x.2) := by
        exact hgeom.mul_of_nonneg hvec
          (fun k => geomWeight_nonneg hqnone0 hqnone1.le k)
          (fun w => vecWeight_nonneg (fun i => (hq' i).1) (fun i => (hq' i).2.le) w)
      rw [← (optionVecEquivProd α).symm.tsum_eq (fun v : Option α → ℕ => vecWeight q v)]
      have hrewrite :
          (fun x : ℕ × (α → ℕ) => vecWeight q ((optionVecEquivProd α).symm x)) =
          fun x => geomWeightOfRatio (q none) x.1 * vecWeight q' x.2 := by
        funext x
        rcases x with ⟨k, w⟩
        convert (vecWeight_consVec q k w) using 1 <;> rfl
      rw [hrewrite, Summable.tsum_prod hpair]
      have hinner : ∀ k, ∑' w : α → ℕ,
          geomWeightOfRatio (q none) k * vecWeight q' w = geomWeightOfRatio (q none) k := by
        intro k
        simpa [h q' hq'] using hvec.tsum_mul_left (geomWeightOfRatio (q none) k)
      simp_rw [hinner]
      exact geomWeight_tsum_eq_one hqnone0 hqnone1
  exact hP q hq

lemma summable_nuSummand (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1) (U : Set (ι → ℕ)) :
    by
      classical
      exact Summable (fun v : ι → ℕ => if v ∈ U then vecWeight q v else 0) := by
  classical
  have hvec : Summable (vecWeight q) := summable_vecWeight q hq
  have hnonneg : ∀ v : ι → ℕ, 0 ≤ vecWeight q v :=
    fun v => vecWeight_nonneg (fun i => (hq i).1) (fun i => (hq i).2.le) v
  refine Summable.of_nonneg_of_le ?_ ?_ hvec
  · intro v
    by_cases hv : v ∈ U
    · simp [hv, hnonneg v]
    · simp [hv]
  · intro v
    by_cases hv : v ∈ U
    · simp [hv]
    · simp [hv, hnonneg v]


omit [DecidableEq ι] in
lemma nu_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (U : Set (ι → ℕ)) :
    0 ≤ nu q U := by
  unfold nu
  refine tsum_nonneg ?_
  intro v
  by_cases hv : v ∈ U
  · have hw : 0 ≤ vecWeight q v := by
      unfold vecWeight
      refine Finset.prod_nonneg ?_
      intro i hi
      exact geomWeight_nonneg (hq i).1 (hq i).2 (v i)
    simpa [hv] using hw
  · simp [hv]

/-- Monotonicity in the event argument. -/
lemma nu_mono_set (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    {U V : Set (ι → ℕ)} (hUV : U ⊆ V) :
    nu q U ≤ nu q V := by
  classical
  by_cases hlt : ∀ i, q i < 1
  · have hsU := summable_nuSummand q (fun i => ⟨hq0 i, hlt i⟩) U
    have hsV := summable_nuSummand q (fun i => ⟨hq0 i, hlt i⟩) V
    unfold nu
    refine hsU.tsum_le_tsum ?_ hsV
    intro v
    by_cases hU : v ∈ U
    · have hV : v ∈ V := hUV hU
      simp [hU, hV]
    · by_cases hV : v ∈ V
      · have hw : 0 ≤ vecWeight q v := vecWeight_nonneg hq0 hq1 v
        simp [hU, hV, hw]
      · simp [hU, hV]
  · obtain ⟨i, hi⟩ : ∃ i, q i = 1 := by
      rw [not_forall] at hlt
      rcases hlt with ⟨i, hi⟩
      exact ⟨i, le_antisymm (hq1 i) (le_of_not_gt hi)⟩
    have hzero : ∀ v : ι → ℕ, vecWeight q v = 0 := by
      intro v
      unfold vecWeight
      refine Finset.prod_eq_zero (i := i) ?_ ?_
      · exact Finset.mem_univ i
      · simp [geomWeightOfRatio, hi]
    have hUzero : nu q U = 0 := by
      unfold nu
      calc
        (∑' v : ι → ℕ, if v ∈ U then vecWeight q v else (0 : ℝ))
            = ∑' v : ι → ℕ, (0 : ℝ) := by
                refine tsum_congr ?_
                intro v
                by_cases hmem : v ∈ U
                · simp [hmem, hzero v]
                · simp [hmem]
        _ = 0 := tsum_zero
    have hVzero : nu q V = 0 := by
      unfold nu
      calc
        (∑' v : ι → ℕ, if v ∈ V then vecWeight q v else (0 : ℝ))
            = ∑' v : ι → ℕ, (0 : ℝ) := by
                refine tsum_congr ?_
                intro v
                by_cases hmem : v ∈ V
                · simp [hmem, hzero v]
                · simp [hmem]
        _ = 0 := tsum_zero
    rw [hUzero, hVzero]

/-- `nu q U ≤ 1`.  This is used only as a boundedness statement inside the induction.

A clean proof is:
1. first prove `nu q Set.univ = 1` by factorising the `tsum`,
2. then use `nu_mono_set`.
-/
lemma nu_le_one (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1) (U : Set (ι → ℕ)) :
    nu q U ≤ 1 := by
  have hq0 : ∀ i, 0 ≤ q i := fun i => (hq i).1
  have hq1 : ∀ i, q i ≤ 1 := fun i => (hq i).2.le
  calc
    nu q U ≤ nu q Set.univ :=
      nu_mono_set q hq0 hq1 (by intro v hv; simp)
    _ = 1 := by
      simpa [nu] using tsum_vecWeight_eq_one q hq

/-- The only genuinely one-dimensional analytic input.

For a monotone bounded function `f`, its expectation under the geometric law is monotone in the
ratio `q`.

Proof idea:
* first prove the Abel / tail-sum identity
  `geomAverage q f = f 0 + ∑' m, (f (m+1) - f m) * q^(m+1)`;
* then use that `f (m+1) - f m ≥ 0` and `q₂^(m+1) ≤ q₁^(m+1)` when `0 ≤ q₂ ≤ q₁ < 1`.
-/
theorem geomAverage_mono_of_monotone
    {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq21 : q₂ ≤ q₁) (hq1lt : q₁ < 1)
    {f : ℕ → ℝ}
    (hf_mono : Monotone f)
    (hf_bdd : ∀ n, 0 ≤ f n ∧ f n ≤ 1) :
    geomAverage q₂ f ≤ geomAverage q₁ f := by
  have htail :
      ∀ {q : ℝ}, 0 ≤ q → q < 1 →
        geomAverage q f = f 0 + ∑' n : ℕ, q ^ (n + 1) * (f (n + 1) - f n) := by
    intro q hq0 hq1
    let a : ℕ → ℝ := fun n => q ^ n * f n
    have ha : Summable a := by
      refine Summable.of_nonneg_of_le ?_ ?_ (summable_geometric_of_lt_one hq0 hq1)
      · intro n
        exact mul_nonneg (pow_nonneg hq0 n) (hf_bdd n).1
      · intro n
        have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
        simpa using mul_le_mul_of_nonneg_left (hf_bdd n).2 hpow
    have hb : Summable (fun n : ℕ => a (n + 1)) :=
      (_root_.summable_nat_add_iff 1).2 ha
    have hqa : Summable (fun n : ℕ => q * a n) := ha.mul_left q
    unfold geomAverage geomWeightOfRatio
    calc
      ∑' n : ℕ, ((1 - q) * q ^ n) * f n = ∑' n : ℕ, (a n - q * a n) := by
        refine tsum_congr ?_
        intro n
        dsimp [a]
        ring
      _ = (∑' n : ℕ, a n) - ∑' n : ℕ, q * a n := by
        rw [ha.tsum_sub hqa]
      _ = (a 0 + ∑' n : ℕ, a (n + 1)) - ∑' n : ℕ, q * a n := by
        rw [ha.tsum_eq_zero_add]
      _ = f 0 + ((∑' n : ℕ, a (n + 1)) - ∑' n : ℕ, q * a n) := by
        simp [a]
        ring
      _ = f 0 + ∑' n : ℕ, (a (n + 1) - q * a n) := by
        rw [← hb.tsum_sub hqa]
      _ = f 0 + ∑' n : ℕ, q ^ (n + 1) * (f (n + 1) - f n) := by
        congr 1
        refine tsum_congr ?_
        intro n
        dsimp [a]
        rw [pow_succ']
        ring
  have hq2lt : q₂ < 1 := lt_of_le_of_lt hq21 hq1lt
  let d : ℕ → ℝ := fun n => f (n + 1) - f n
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    intro n
    exact sub_nonneg.mpr (hf_mono (Nat.le_succ n))
  have hd_le_one : ∀ n, d n ≤ 1 := by
    intro n
    dsimp [d]
    nlinarith [(hf_bdd n).1, (hf_bdd (n + 1)).2]
  have hgeom₁ : Summable (fun n : ℕ => q₁ ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq₁ hq1lt)
  have hs₁ : Summable (fun n : ℕ => q₁ ^ (n + 1) * d n) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hgeom₁
    · intro n
      exact mul_nonneg (pow_nonneg hq₁ (n + 1)) (hd_nonneg n)
    · intro n
      have hpow : 0 ≤ q₁ ^ (n + 1) := pow_nonneg hq₁ (n + 1)
      simpa using mul_le_mul_of_nonneg_left (hd_le_one n) hpow
  have hs₂ : Summable (fun n : ℕ => q₂ ^ (n + 1) * d n) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hgeom₁
    · intro n
      exact mul_nonneg (pow_nonneg hq₂ (n + 1)) (hd_nonneg n)
    · intro n
      have hpow₂ : q₂ ^ (n + 1) ≤ q₁ ^ (n + 1) :=
        pow_le_pow_left₀ hq₂ hq21 (n + 1)
      have hpow₁_nonneg : 0 ≤ q₁ ^ (n + 1) := pow_nonneg hq₁ (n + 1)
      calc
        q₂ ^ (n + 1) * d n ≤ q₁ ^ (n + 1) * d n := by
          exact mul_le_mul_of_nonneg_right hpow₂ (hd_nonneg n)
        _ ≤ q₁ ^ (n + 1) * 1 := by
          exact mul_le_mul_of_nonneg_left (hd_le_one n) hpow₁_nonneg
        _ = q₁ ^ (n + 1) := by ring
  have hseries :
      ∑' n : ℕ, q₂ ^ (n + 1) * d n ≤ ∑' n : ℕ, q₁ ^ (n + 1) * d n := by
    refine hs₂.tsum_le_tsum ?_ hs₁
    intro n
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hq₂ hq21 (n + 1))
      (hd_nonneg n)
  rw [htail hq₂ hq2lt, htail hq₁ hq1lt]
  simpa [d] using add_le_add_left hseries (f 0)

/-- Option-step decomposition of the product measure.

This is the Fubini/reindexing step: separate the new coordinate `none` from the old coordinates.
`optionVecEquivProd` is exactly the equivalence needed to reindex the `tsum`.
-/
theorem nu_option_eq_geomAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Option ι → ℝ) (U : Set (Option ι → ℕ))
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1) :
    nu q U = geomAverage (q none) (fun k => nu (fun i : ι => q (some i)) (sectionAt U k)) := by
  classical
  let e : (Option ι → ℕ) ≃ ℕ × (ι → ℕ) := optionVecEquivProd ι
  let a : ℕ → ℝ := fun k => geomWeightOfRatio (q none) k
  let b : (ι → ℕ) → ℝ := fun w => vecWeight (fun i : ι => q (some i)) w
  let G : ℕ × (ι → ℕ) → ℝ := fun p => a p.1 * b p.2
  let F : ℕ × (ι → ℕ) → ℝ := fun p => if consVec p.1 p.2 ∈ U then G p else 0
  have ha : Summable a := by
    unfold a geomWeightOfRatio
    exact (summable_geometric_of_lt_one (hq none).1 (hq none).2).mul_left (1 - q none)
  have hb : Summable b := by
    simpa [b] using summable_vecWeight
      (q := fun i : ι => q (some i))
      (hq := fun i => by simpa using hq (some i))
  have hb_nonneg : ∀ w : ι → ℕ, 0 ≤ b w := by
    intro w
    unfold b vecWeight
    refine Finset.prod_nonneg ?_
    intro i hi
    exact geomWeight_nonneg (hq (some i)).1 (hq (some i)).2.le (w i)
  have hG_nonneg : ∀ p : ℕ × (ι → ℕ), 0 ≤ G p := by
    intro p
    exact mul_nonneg
      (geomWeight_nonneg (hq none).1 (hq none).2.le p.1)
      (hb_nonneg p.2)
  have hG : Summable G := by
    simpa [G] using ha.mul_of_nonneg hb
      (fun k => geomWeight_nonneg (hq none).1 (hq none).2.le k)
      hb_nonneg
  have hF_nonneg : ∀ p : ℕ × (ι → ℕ), 0 ≤ F p := by
    intro p
    by_cases hp : consVec p.1 p.2 ∈ U
    · simp [F, hp, hG_nonneg p]
    · simp [F, hp]
  have hF_le : ∀ p : ℕ × (ι → ℕ), F p ≤ G p := by
    intro p
    by_cases hp : consVec p.1 p.2 ∈ U
    · simp [F, hp]
    · simp [F, hp, hG_nonneg p]
  have hF : Summable F :=
    Summable.of_nonneg_of_le hF_nonneg hF_le hG
  have hleft : nu q U = ∑' p : ℕ × (ι → ℕ), F p := by
    unfold nu
    rw [← e.tsum_eq F]
    refine tsum_congr ?_
    intro v
    have hcons : consVec (v none) (fun i : ι => v (some i)) = v := by
      funext o
      cases o <;> rfl
    by_cases hv : v ∈ U
    · simp [F, G, a, b, e, optionVecEquivProd, hcons, hv, vecWeight, Fintype.prod_option]
    · simp [F, G, a, b, e, optionVecEquivProd, hcons, hv]
  calc
    nu q U = ∑' p : ℕ × (ι → ℕ), F p := hleft
    _ = ∑' k : ℕ, ∑' w : ι → ℕ, F (k, w) := by
      simpa using hF.tsum_prod' (fun k => hF.prod_factor k)
    _ = ∑' k : ℕ, a k * nu (fun i : ι => q (some i)) (sectionAt U k) := by
      refine tsum_congr ?_
      intro k
      calc
        ∑' w : ι → ℕ, F (k, w)
            = ∑' w : ι → ℕ, a k * (if w ∈ sectionAt U k then b w else 0) := by
                refine tsum_congr ?_
                intro w
                by_cases hw : consVec k w ∈ U
                · simp [F, G, a, b, sectionAt, hw]
                · simp [F, G, a, b, sectionAt, hw]
        _ = a k * ∑' w : ι → ℕ, if w ∈ sectionAt U k then b w else 0 := by
                rw [tsum_mul_left]
        _ = a k * nu (fun i : ι => q (some i)) (sectionAt U k) := by
                simp [nu, b]
    _ = geomAverage (q none) (fun k => nu (fun i : ι => q (some i)) (sectionAt U k)) := by
      simp [geomAverage, a]

/--
Finite-support stochastic domination for product geometric measures.

This is the finite-stage precursor of **Lemma 6** in the form that is actually needed later:
if an event is upward-closed, then its `nu`-mass is monotone under coordinatewise increase of the
ratios.

Proof idea:
* use `Fintype.induction_empty_option`;
* in the option-step, write `nu` as a geometric average of the sections (`nu_option_eq_geomAverage`);
* the inner `nu` is monotone by the induction hypothesis;
* the outer geometric average is monotone by `geomAverage_mono_of_monotone`, because the sections
  form an increasing family (`section_mono`) and `nu` is monotone in the event (`nu_mono_set`).
-/
theorem nu_mono_of_coordwise_le
    {U : Set (ι → ℕ)} (hU : UpwardClosed U)
    {q₁ q₂ : ι → ℝ}
    (hq_nonneg : ∀ i, 0 ≤ q₂ i ∧ q₂ i ≤ q₁ i)
    (hq_lt_one : ∀ i, q₁ i < 1) :
    nu q₂ U ≤ nu q₁ U := by
  classical
  have hP :
      ∀ [DecidableEq ι] (U : Set (ι → ℕ)) (q₁ q₂ : ι → ℝ),
        UpwardClosed U →
        (∀ i, 0 ≤ q₂ i ∧ q₂ i ≤ q₁ i) →
        (∀ i, q₁ i < 1) →
        nu q₂ U ≤ nu q₁ U := by
    refine Fintype.induction_empty_option
      (P := fun α _ =>
        ∀ [DecidableEq α] (U : Set (α → ℕ)) (q₁ q₂ : α → ℝ),
          UpwardClosed U →
          (∀ i, 0 ≤ q₂ i ∧ q₂ i ≤ q₁ i) →
          (∀ i, q₁ i < 1) →
          nu q₂ U ≤ nu q₁ U) ?_ ?_ ?_ ι
    · intro α β _ e h _ U q₁ q₂ hU hq_nonneg hq_lt_one
      letI : Fintype α := Fintype.ofEquiv β e.symm
      let eVec : (α → ℕ) ≃ (β → ℕ) := Equiv.piCongrLeft' (fun _ => ℕ) e
      let U' : Set (α → ℕ) := {v | eVec v ∈ U}
      have hU' : UpwardClosed U' := by
        intro v w hvw hv
        apply hU
        · intro b
          simpa [eVec] using hvw (e.symm b)
        · convert hv using 1 <;> rfl
      have hq_nonneg' : ∀ a : α, 0 ≤ q₂ (e a) ∧ q₂ (e a) ≤ q₁ (e a) := by
        intro a
        simpa using hq_nonneg (e a)
      have hq_lt_one' : ∀ a : α, q₁ (e a) < 1 := by
        intro a
        simpa using hq_lt_one (e a)
      have hnu_pull (q : β → ℝ) :
          nu q U = nu (fun a : α => q (e a)) U' := by
        unfold nu
        rw [← eVec.tsum_eq (fun v : β → ℕ => if v ∈ U then vecWeight q v else 0)]
        refine tsum_congr ?_
        intro v
        by_cases hv : eVec v ∈ U
        · simp [U', hv]
          unfold vecWeight
          simpa [eVec] using
            (Equiv.prod_comp e (fun b => geomWeightOfRatio (q b) (v (e.symm b)))).symm
        · simp [U', hv]
      have h' := h U' (fun a : α => q₁ (e a)) (fun a : α => q₂ (e a))
        hU' hq_nonneg' hq_lt_one'
      calc
        nu q₂ U = nu (fun a : α => q₂ (e a)) U' := hnu_pull q₂
        _ ≤ nu (fun a : α => q₁ (e a)) U' := h'
        _ = nu q₁ U := (hnu_pull q₁).symm
    · intro _ U q₁ q₂ hU hq_nonneg hq_lt_one
      let v0 : PEmpty → ℕ := fun x => nomatch x
      by_cases hv : v0 ∈ U
      · rw [nu, nu, tsum_fintype, tsum_fintype]
        simp [vecWeight]
      · rw [nu, nu, tsum_fintype, tsum_fintype]
        simp [vecWeight]
    · intro α _ h _ U q₁ q₂ hU hq_nonneg hq_lt_one
      let q₁' : α → ℝ := fun i => q₁ (some i)
      let q₂' : α → ℝ := fun i => q₂ (some i)
      have hq₁_all : ∀ i : Option α, 0 ≤ q₁ i ∧ q₁ i < 1 := by
        intro i
        exact ⟨le_trans (hq_nonneg i).1 (hq_nonneg i).2, hq_lt_one i⟩
      have hq₂_all : ∀ i : Option α, 0 ≤ q₂ i ∧ q₂ i < 1 := by
        intro i
        exact ⟨(hq_nonneg i).1, lt_of_le_of_lt (hq_nonneg i).2 (hq_lt_one i)⟩
      have hq₁' : ∀ i : α, 0 ≤ q₁' i ∧ q₁' i < 1 := by
        intro i
        simpa [q₁'] using hq₁_all (some i)
      have hq_nonneg' : ∀ i : α, 0 ≤ q₂' i ∧ q₂' i ≤ q₁' i := by
        intro i
        simpa [q₁', q₂'] using hq_nonneg (some i)
      have hq_lt_one' : ∀ i : α, q₁' i < 1 := by
        intro i
        simpa [q₁'] using hq_lt_one (some i)
      have hinner : ∀ k, nu q₂' (sectionAt U k) ≤ nu q₁' (sectionAt U k) := by
        intro k
        exact h (sectionAt U k) q₁' q₂' (section_upwardClosed hU k) hq_nonneg' hq_lt_one'
      have hmono : Monotone (fun k => nu q₁' (sectionAt U k)) := by
        intro k l hkl
        apply nu_mono_set q₁' (fun i => (hq₁' i).1) (fun i => (hq₁' i).2.le)
        exact (section_mono hU) hkl
      have hbdd : ∀ n, 0 ≤ nu q₁' (sectionAt U n) ∧ nu q₁' (sectionAt U n) ≤ 1 := by
        intro n
        constructor
        · exact nu_nonneg q₁' (fun i => ⟨(hq₁' i).1, (hq₁' i).2.le⟩) (sectionAt U n)
        · exact nu_le_one q₁' hq₁' (sectionAt U n)
      calc
        nu q₂ U = geomAverage (q₂ none) (fun k => nu q₂' (sectionAt U k)) := by
          simpa [q₂'] using (nu_option_eq_geomAverage (q := q₂) (U := U) (hq := hq₂_all))
        _ ≤ geomAverage (q₂ none) (fun k => nu q₁' (sectionAt U k)) := by
          apply geomAverage_mono_right (hq₂_all none).1 (hq₂_all none).2.le
          · intro k
            exact hinner k
          · intro n
            constructor
            · exact nu_nonneg q₂' (fun i => ⟨(hq_nonneg' i).1, (hq_nonneg' i).2.trans (hq_lt_one' i).le⟩)
                (sectionAt U n)
            · exact nu_le_one q₂'
                (fun i => ⟨(hq_nonneg' i).1, lt_of_le_of_lt (hq_nonneg' i).2 (hq_lt_one' i)⟩)
                (sectionAt U n)
          · exact hbdd
        _ ≤ geomAverage (q₁ none) (fun k => nu q₁' (sectionAt U k)) := by
          apply geomAverage_mono_of_monotone
            (hq₁ := (hq₁_all none).1)
            (hq₂ := (hq₂_all none).1)
            (hq21 := (hq_nonneg none).2)
            (hq1lt := (hq₁_all none).2)
          · exact hmono
          · exact hbdd
        _ = nu q₁ U := by
          simpa [q₁'] using (nu_option_eq_geomAverage (q := q₁) (U := U) (hq := hq₁_all)).symm
  exact hP U q₁ q₂ hU hq_nonneg hq_lt_one

end ProductGeometric

section MultipleEvent

/-- Finite set of primes appearing in the factorisations of elements of `F`. -/
noncomputable def supportPrimes (F : Finset ℕ) : Finset ℕ :=
  F.biUnion fun a => a.factorization.support

/-- Exponent vector of `a`, restricted to a chosen finite prime set `P`. -/
def expVec (P : Finset ℕ) (a : ℕ) : P.attach → ℕ :=
  fun p => a.factorization p.1

/-- Event on exponent vectors saying: some positive `a ∈ F` divides the represented integer.

This is the finite-dimensional replacement for the global set `M_F`.
-/
def multipleEvent (P F : Finset ℕ) : Set (P.attach → ℕ) :=
  {v | ∃ a ∈ F, 0 < a ∧ expVec P a ≤ v}

lemma multipleEvent_upwardClosed (P F : Finset ℕ) :
    UpwardClosed (multipleEvent P F) := by
  intro v w hvw hv
  rcases hv with ⟨a, haF, ha0, hva⟩
  exact ⟨a, haF, ha0, le_trans hva hvw⟩

/-- Every element of `supportPrimes F` is prime.

This is the only arithmetic fact about `supportPrimes` needed for the monotonicity in `s`.
-/
lemma prime_of_mem_supportPrimes {F : Finset ℕ} {p : ℕ}
    (hp : p ∈ supportPrimes F) : Nat.Prime p := by
  rcases Finset.mem_biUnion.mp hp with ⟨a, haF, hp'⟩
  exact Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp')

/-- `p^{-t} ≤ p^{-s}` on the range `1 < s ≤ t` for primes `p`.

This is a tiny real-analysis helper used in the final specialization theorem.
-/
lemma primeRatio_antitone {p : ℕ} (hp : Nat.Prime p)
    {s t : ℝ} (hst : s ≤ t) :
    0 ≤ (p : ℝ) ^ (-t) ∧ (p : ℝ) ^ (-t) ≤ (p : ℝ) ^ (-s) := by
  constructor
  · positivity
  · have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hp.one_lt.le
    have hneg : -t ≤ -s := by
      linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hp1 hneg

lemma primeRatio_lt_one {p : ℕ} (hp : Nat.Prime p) {s : ℝ} (hs : 1 < s) :
    (p : ℝ) ^ (-s) < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hneg : -s < 0 := by
    linarith
  simpa using Real.rpow_lt_rpow_of_exponent_lt hp1 hneg

/--
Finite-stage precursor of **Lemma 6**, in the exponent-space form that one actually proves.

Take `P = supportPrimes F`. Then the event `multipleEvent P F` is upward-closed, and the ratios are
`q_s(p) = p^{-s}`. Hence the generic theorem `nu_mono_of_coordwise_le` applies.
-/
theorem antitone_nu_multipleEvent
    (F : Finset ℕ) :
    AntitoneOn
      (fun s : ℝ =>
        nu
          (fun p : (supportPrimes F).attach => ((p.1 : ℝ) ^ (-s)))
          (multipleEvent (supportPrimes F) F))
      (Set.Ioi (1 : ℝ)) := by
  intro s hs t ht hst
  apply nu_mono_of_coordwise_le
  · exact multipleEvent_upwardClosed _ _
  · intro p
    have hp : Nat.Prime p.1 := prime_of_mem_supportPrimes (F := F) p.1.2
    simpa using primeRatio_antitone hp hst
  · intro p
    have hp : Nat.Prime p.1 := prime_of_mem_supportPrimes (F := F) p.1.2
    simpa using primeRatio_lt_one hp hs

/-- Standalone name for the finite exponent-space precursor of **Lemma 6**. -/
theorem finiteDivisibilityMonotonePrecursor
    (F : Finset ℕ) :
    AntitoneOn
      (fun s : ℝ =>
        nu
          (fun p : (supportPrimes F).attach => ((p.1 : ℝ) ^ (-s)))
          (multipleEvent (supportPrimes F) F))
      (Set.Ioi (1 : ℝ)) :=
  antitone_nu_multipleEvent F

end MultipleEvent

/-!
## How this plugs into the global proof

The next section proves the bridge theorem

```lean
mu s (Multiples (↑F : Set ℕ))
  = nu (fun p : (supportPrimes F).attach => ((p.1 : ℝ) ^ (-s)))
      (multipleEvent (supportPrimes F) F)
```

for `s > 1` and finite `F` of positive integers.

Combined with that bridge, `finiteDivisibilityMonotonePrecursor` yields the finite-stage
precursor of **Lemma 6** used later in this standalone file.
-/


/-! ## Bridge back from `nu` to the original `mu` -/

/-- Dirichlet weight on `ℕ`, extended by `0` at `0`. -/
noncomputable def dirichletWeight (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-s)

lemma dirichletWeight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ dirichletWeight s n := by
  by_cases hn : n = 0
  · simp [dirichletWeight, hn]
  · simp [dirichletWeight, hn, Real.rpow_nonneg (show 0 ≤ (n : ℝ) by positivity)]

lemma dirichletWeight_succ (s : ℝ) (n : ℕ) :
    dirichletWeight s (n + 1) = zetaTerm s n := by
  have hnonneg : 0 ≤ (n + 1 : ℝ) := by positivity
  simp [dirichletWeight, zetaTerm, Real.rpow_neg hnonneg, one_div]

lemma summable_dirichletWeight {s : ℝ} (hs : 1 < s) :
    Summable (dirichletWeight s) := by
  have hpowInv : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ s)⁻¹) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) 1).2
      (Real.summable_nat_rpow_inv.mpr hs)
  have htail : Summable (fun n : ℕ => dirichletWeight s (n + 1)) := by
    refine hpowInv.congr ?_
    intro n
    have hnonneg : 0 ≤ (n + 1 : ℝ) := by positivity
    simp [dirichletWeight, Real.rpow_neg hnonneg]
  exact (summable_nat_add_iff (f := dirichletWeight s) 1).1 htail

lemma tsum_dirichletWeight_eq_zetaReal {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, dirichletWeight s n = zetaReal s := by
  have hsum := summable_dirichletWeight hs
  have htail : ∑' n : ℕ, dirichletWeight s (n + 1) = zetaReal s := by
    calc
      ∑' n : ℕ, dirichletWeight s (n + 1) = ∑' n : ℕ, zetaTerm s n := by
        exact tsum_congr (dirichletWeight_succ s)
      _ = zetaReal s := by rfl
  calc
    ∑' n : ℕ, dirichletWeight s n = dirichletWeight s 0 + ∑' n : ℕ, dirichletWeight s (n + 1) := by
      simpa using hsum.tsum_eq_zero_add
    _ = zetaReal s := by
      simpa [dirichletWeight] using congrArg (fun t : ℝ => dirichletWeight s 0 + t) htail

lemma dirichletWeight_mul {s : ℝ} {l : ℕ} (hl : 0 < l) (m : ℕ) :
    dirichletWeight s (l * m) = (l : ℝ) ^ (-s) * dirichletWeight s m := by
  by_cases hm : m = 0
  · subst hm
    simp [dirichletWeight]
  · have hlnz : l ≠ 0 := Nat.ne_of_gt hl
    calc
      dirichletWeight s (l * m) = (((l : ℝ) * (m : ℝ)) ^ (-s)) := by
        simp [dirichletWeight, hlnz, hm]
      _ = (l : ℝ) ^ (-s) * (m : ℝ) ^ (-s) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (l : ℝ) ^ (-s) * dirichletWeight s m := by
        simp [dirichletWeight, hm]

/-- Multiplication by a positive integer identifies `ℕ` with its set of multiples. -/
def natEquivDvd (l : ℕ) (hl : 0 < l) : ℕ ≃ {n : ℕ // l ∣ n} where
  toFun m := ⟨l * m, dvd_mul_right l m⟩
  invFun n := n.1 / l
  left_inv m := by
    simp [Nat.mul_div_cancel_left _ hl]
  right_inv n := by
    apply Subtype.ext
    simp [Nat.mul_div_cancel' n.2]

lemma tsum_dirichletWeight_dvd {s : ℝ} {l : ℕ} (hl : 0 < l) :
    ∑' n : ℕ, (if l ∣ n then dirichletWeight s n else 0) =
      (l : ℝ) ^ (-s) * ∑' n : ℕ, dirichletWeight s n := by
  let e : ℕ ≃ {n : ℕ // l ∣ n} := natEquivDvd l hl
  calc
    ∑' n : ℕ, (if l ∣ n then dirichletWeight s n else 0)
        = ∑' n : ℕ, Set.indicator {n : ℕ | l ∣ n} (dirichletWeight s) n := by
            refine tsum_congr ?_
            intro n
            by_cases h : l ∣ n <;> simp [Set.indicator, h]
    _ = ∑' n : {n : ℕ // l ∣ n}, dirichletWeight s n := by
          symm
          exact tsum_subtype {n : ℕ | l ∣ n} (dirichletWeight s)
    _ = ∑' m : ℕ, dirichletWeight s (l * m) := by
          symm
          simpa [e, natEquivDvd] using
            e.tsum_eq (fun n : {n : ℕ // l ∣ n} => dirichletWeight s n)
    _ = ∑' m : ℕ, (l : ℝ) ^ (-s) * dirichletWeight s m := by
          refine tsum_congr ?_
          intro m
          simpa using dirichletWeight_mul (s := s) hl m
    _ = (l : ℝ) ^ (-s) * ∑' n : ℕ, dirichletWeight s n := by
          rw [tsum_mul_left]

/-- The common finite inclusion-exclusion expression for the Dirichlet mass of `Multiples F`. -/
noncomputable def finiteDirichletMultiples (F : Finset ℕ) (s : ℝ) : ℝ :=
  ∑ G ∈ F.powerset with G.Nonempty,
    (((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s)))

/-- Shifting every coordinate by a fixed exponent vector identifies all vectors with the
coordinatewise upper cone above it. -/
def vecShiftEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) :
    (ι → ℕ) ≃ {v : ι → ℕ // e ≤ v} where
  toFun w := ⟨fun i => e i + w i, by intro i; exact Nat.le_add_right _ _⟩
  invFun v := fun i => v.1 i - e i
  left_inv w := by
    funext i
    exact Nat.add_sub_cancel_left _ _
  right_inv v := by
    apply Subtype.ext
    funext i
    simpa [add_comm] using Nat.sub_add_cancel (v.2 i)

lemma geomWeight_shift (q : ℝ) (e k : ℕ) :
    geomWeightOfRatio q (e + k) = q ^ e * geomWeightOfRatio q k := by
  simp [geomWeightOfRatio, pow_add, mul_assoc, mul_left_comm, mul_comm]

lemma vecWeight_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (e w : ι → ℕ) :
    vecWeight q (fun i => e i + w i) = (∏ i, q i ^ e i) * vecWeight q w := by
  classical
  unfold vecWeight
  calc
    ∏ i, geomWeightOfRatio (q i) (e i + w i)
        = ∏ i, q i ^ e i * geomWeightOfRatio (q i) (w i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            simpa using geomWeight_shift (q i) (e i) (w i)
    _ = (∏ i, q i ^ e i) * ∏ i, geomWeightOfRatio (q i) (w i) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ i, q i ^ e i) * vecWeight q w := by
          rfl

lemma nu_Ici_eq_prod_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (e : ι → ℕ) (hq : ∀ i, 0 ≤ q i ∧ q i < 1) :
    nu q {v | e ≤ v} = ∏ i, q i ^ e i := by
  classical
  let E : (ι → ℕ) ≃ {v : ι → ℕ // e ≤ v} := vecShiftEquiv e
  calc
    nu q {v | e ≤ v} = ∑' v : {v : ι → ℕ // e ≤ v}, vecWeight q v := by
      unfold nu
      symm
      convert (tsum_subtype {v : ι → ℕ | e ≤ v} (vecWeight q)) using 1 <;> rfl
    _ = ∑' w : ι → ℕ, vecWeight q (E w) := by
      rw [← E.tsum_eq (fun v : {v : ι → ℕ // e ≤ v} => vecWeight q v)]
    _ = ∑' w : ι → ℕ, (∏ i, q i ^ e i) * vecWeight q w := by
      refine tsum_congr ?_
      intro w
      change vecWeight q (fun i => e i + w i) = (∏ i, q i ^ e i) * vecWeight q w
      simpa using vecWeight_shift q e w
    _ = (∏ i, q i ^ e i) * ∑' w : ι → ℕ, vecWeight q w := by
      rw [tsum_mul_left]
    _ = ∏ i, q i ^ e i := by
      rw [tsum_vecWeight_eq_one q hq, mul_one]

lemma mem_iInter_expVec_iff_lcm0_le (P G : Finset ℕ) (hGpos : PositiveFinset G)
    {v : P.attach → ℕ} :
    v ∈ ⋂ a ∈ G, {w : P.attach → ℕ | expVec P a ≤ w} ↔ expVec P (lcm0 G) ≤ v := by
  classical
  induction G using Finset.induction_on generalizing v with
  | empty =>
      simp [Pi.le_def, expVec, lcm0]
  | @insert a G ha ih =>
      have haPos : 0 < a := hGpos (by simp)
      have hGPos : PositiveFinset G := by
        intro b hb
        exact hGpos (by simp [hb])
      have hlcmGPos : 0 < lcm0 G := lcm0_pos G hGPos
      have hstep :
          expVec P (Nat.lcm a (lcm0 G)) ≤ v ↔ expVec P a ≤ v ∧ expVec P (lcm0 G) ≤ v := by
        rw [Pi.le_def, Pi.le_def, Pi.le_def]
        constructor
        · intro h
          constructor
          · intro p
            have hp := h p
            rw [expVec, Nat.factorization_lcm (Nat.ne_of_gt haPos) (Nat.ne_of_gt hlcmGPos),
              Finsupp.sup_apply] at hp
            exact (sup_le_iff.mp hp).1
          · intro p
            have hp := h p
            rw [expVec, Nat.factorization_lcm (Nat.ne_of_gt haPos) (Nat.ne_of_gt hlcmGPos),
              Finsupp.sup_apply] at hp
            exact (sup_le_iff.mp hp).2
        · rintro ⟨ha', hG'⟩ p
          rw [expVec, Nat.factorization_lcm (Nat.ne_of_gt haPos) (Nat.ne_of_gt hlcmGPos),
            Finsupp.sup_apply]
          exact sup_le (ha' p) (hG' p)
      have hlcm_insert : Nat.lcm a (lcm0 G) = lcm0 (insert a G) := by
        unfold lcm0
        rw [Finset.lcm_insert]
        change Nat.lcm a (G.lcm id) = Nat.lcm a (G.lcm id)
        rfl
      calc
        v ∈ ⋂ b ∈ insert a G, {w : P.attach → ℕ | expVec P b ≤ w}
            ↔ expVec P a ≤ v ∧ v ∈ ⋂ b ∈ G, {w : P.attach → ℕ | expVec P b ≤ w} := by
                simp
        _ ↔ expVec P a ≤ v ∧ expVec P (lcm0 G) ≤ v := by
              rw [ih hGPos]
        _ ↔ expVec P (Nat.lcm a (lcm0 G)) ≤ v := hstep.symm
        _ ↔ expVec P (lcm0 (insert a G)) ≤ v := by
              rw [hlcm_insert]

lemma factorizationSupport_lcm0_subset_supportPrimes
    {F G : Finset ℕ} (hFpos : PositiveFinset F) (hGF : G ⊆ F) :
    (lcm0 G).factorization.support ⊆ supportPrimes F := by
  classical
  let Q : Finset ℕ → Prop := fun G =>
    ∀ hGF : G ⊆ F, PositiveFinset G → (lcm0 G).factorization.support ⊆ supportPrimes F
  have hQ : Q G := by
    refine Finset.induction_on G ?_ ?_
    · intro hGF hPos
      simp [lcm0, supportPrimes]
    · intro a G ha ih hGF hPos
      intro p hp
      have haF : a ∈ F := hGF (by simp)
      have haPos : 0 < a := hPos (by simp)
      have hGPos : PositiveFinset G := by
        intro b hb
        exact hPos (by simp [hb])
      have hGF' : G ⊆ F := by
        intro b hb
        exact hGF (by simp [hb])
      have hlcmGPos : 0 < lcm0 G := lcm0_pos G hGPos
      have hpfac : (Nat.lcm a (lcm0 G)).factorization p ≠ 0 := by
        have : p ∈ (Nat.lcm a (lcm0 G)).factorization.support := by
          convert hp using 1 <;> simp only [lcm0, Finset.lcm_insert] <;> rfl
        exact Finsupp.mem_support_iff.mp this
      by_cases hap : a.factorization p = 0
      · have hpGfac : (lcm0 G).factorization p ≠ 0 := by
          simpa [Nat.factorization_lcm (Nat.ne_of_gt haPos) (Nat.ne_of_gt hlcmGPos),
            Finsupp.sup_apply, hap] using hpfac
        exact ih hGF' hGPos (Finsupp.mem_support_iff.mpr hpGfac)
      · exact Finset.mem_biUnion.mpr ⟨a, haF, Finsupp.mem_support_iff.mpr hap⟩
  exact hQ hGF (by
    intro a ha
    exact hFpos (hGF ha))

lemma finset_prod_rpow_natPow (s : Finset ℕ) (f : ℕ → ℕ) (r : ℝ) :
    Finset.prod s (fun p => (((p : ℝ) ^ f p) ^ r)) =
      (Finset.prod s (fun p => (p : ℝ) ^ f p)) ^ r := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha_nonneg : 0 ≤ (a : ℝ) ^ f a := by positivity
      have hs_nonneg : 0 ≤ Finset.prod s (fun p => (p : ℝ) ^ f p) := by
        refine Finset.prod_nonneg ?_
        intro p hp
        positivity
      calc
        Finset.prod (insert a s) (fun p => (((p : ℝ) ^ f p) ^ r))
            = (((a : ℝ) ^ f a) ^ r) * Finset.prod s (fun p => (((p : ℝ) ^ f p) ^ r)) := by
                rw [Finset.prod_insert ha]
        _ = (((a : ℝ) ^ f a) ^ r) * (Finset.prod s (fun p => (p : ℝ) ^ f p)) ^ r := by
              rw [ih]
        _ = (((a : ℝ) ^ f a) * Finset.prod s (fun p => (p : ℝ) ^ f p)) ^ r := by
              rw [(Real.mul_rpow ha_nonneg hs_nonneg).symm]
        _ = (Finset.prod (insert a s) (fun p => (p : ℝ) ^ f p)) ^ r := by
              rw [Finset.prod_insert ha]

lemma prod_supportPrimes_rpow_expVec_eq
    {F G : Finset ℕ} (hFpos : PositiveFinset F) (hGF : G ⊆ F) {s : ℝ} :
    Finset.prod (supportPrimes F)
      (fun p => ((p : ℝ) ^ (-s)) ^ (lcm0 G).factorization p) = (lcm0 G : ℝ) ^ (-s) := by
  classical
  have hGpos : PositiveFinset G := by
    intro a ha
    exact hFpos (hGF ha)
  have hlcm_ne : lcm0 G ≠ 0 := Nat.ne_of_gt (lcm0_pos G hGpos)
  have hsubset : (lcm0 G).factorization.support ⊆ supportPrimes F :=
    factorizationSupport_lcm0_subset_supportPrimes (F := F) (G := G) hFpos hGF
  have hprodCast :
      Finset.prod (lcm0 G).factorization.support
        (fun p => (p : ℝ) ^ (lcm0 G).factorization p) = (lcm0 G : ℝ) := by
    exact_mod_cast (Nat.factorization_prod_pow_eq_self hlcm_ne)
  calc
    Finset.prod (supportPrimes F)
        (fun p => ((p : ℝ) ^ (-s)) ^ (lcm0 G).factorization p)
        = Finset.prod (supportPrimes F)
            (fun p => ((p : ℝ) ^ (lcm0 G).factorization p) ^ (-s)) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          have hp0 : 0 ≤ (p : ℝ) := by positivity
          calc
            ((p : ℝ) ^ (-s)) ^ (lcm0 G).factorization p
                = (p : ℝ) ^ ((-s) * (lcm0 G).factorization p) := by
                    symm
                    exact Real.rpow_mul_natCast hp0 (-s) ((lcm0 G).factorization p)
            _ = (p : ℝ) ^ ((lcm0 G).factorization p * (-s)) := by
                    rw [mul_comm]
            _ = ((p : ℝ) ^ (lcm0 G).factorization p) ^ (-s) := by
                    simpa [mul_comm] using
                      (Real.rpow_natCast_mul hp0 ((lcm0 G).factorization p) (-s))
    _ = (Finset.prod (supportPrimes F)
          (fun p => (p : ℝ) ^ (lcm0 G).factorization p)) ^ (-s) := by
          simpa using (finset_prod_rpow_natPow (supportPrimes F)
            (fun p => (lcm0 G).factorization p) (-s))
    _ = (Finset.prod (lcm0 G).factorization.support
          (fun p => (p : ℝ) ^ (lcm0 G).factorization p)) ^ (-s) := by
          congr 1
          symm
          exact Finset.prod_subset hsubset (fun p hpP hpNot => by
            have hzero : (lcm0 G).factorization p = 0 := Finsupp.notMem_support_iff.mp hpNot
            simp [hzero])
    _ = (lcm0 G : ℝ) ^ (-s) := by
          rw [hprodCast]

lemma mu_multiples_finset_eq_finiteDirichlet
    (F : Finset ℕ) (hFpos : PositiveFinset F) {s : ℝ} (hs : 1 < s) :
    mu s (Multiples ((F : Set ℕ))) = finiteDirichletMultiples F s := by
  classical
  let w : ℕ → ℝ := dirichletWeight s
  let S : ℕ → Set ℕ := fun a => {n | a ∣ n}
  let U : Set ℕ := ⋃ a ∈ F, S a
  let A : Finset (Finset ℕ) := F.powerset.filter (·.Nonempty)
  let J : Finset ℕ → ℕ → ℝ := fun G n =>
    ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * Set.indicator (⋂ a ∈ G, S a) w n)
  have hpoint (n : ℕ) : Set.indicator U w n = Finset.sum A (fun G => J G n) := by
    simpa [A, J, U, zsmul_eq_mul] using
      (Finset.indicator_biUnion_eq_sum_powerset F S w n)
  have hJsum : ∀ G ∈ A, Summable (J G) := by
    intro G hG
    have hsumInter :
        Summable (fun n : ℕ => Set.indicator (⋂ a ∈ G, S a) w n) := by
      have hnonneg : ∀ n : ℕ, 0 ≤ Set.indicator (⋂ a ∈ G, S a) w n := by
        intro n
        by_cases hn : n ∈ ⋂ a ∈ G, S a
        · simpa [Set.indicator, hn, w] using dirichletWeight_nonneg s n
        · simp [Set.indicator, hn]
      have hle : ∀ n : ℕ, Set.indicator (⋂ a ∈ G, S a) w n ≤ w n := by
        intro n
        by_cases hn : n ∈ ⋂ a ∈ G, S a
        · simp [Set.indicator, hn]
        · simpa [Set.indicator, hn] using dirichletWeight_nonneg s n
      exact Summable.of_nonneg_of_le hnonneg hle (summable_dirichletWeight hs)
    simpa [J] using hsumInter.mul_left ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ))
  have hinner (G : Finset ℕ) (hG : G ∈ A) :
      ∑' n : ℕ, J G n =
        ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s)) * ∑' n : ℕ, w n := by
    have hGsubset : G ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1
    have hGpos : PositiveFinset G := by
      intro a ha
      exact hFpos (hGsubset ha)
    have hlcm : 0 < lcm0 G := lcm0_pos G hGpos
    calc
      ∑' n : ℕ, J G n =
          ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) *
            ∑' n : ℕ, Set.indicator (⋂ a ∈ G, S a) w n) := by
              change ∑' n : ℕ,
                  ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) *
                    Set.indicator (⋂ a ∈ G, S a) w n) = _
              simp [J]
              rw [tsum_mul_left]
      _ = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) *
            ∑' n : ℕ, if lcm0 G ∣ n then w n else 0) := by
              congr 1
              refine tsum_congr ?_
              intro n
              by_cases hdiv : lcm0 G ∣ n
              · have hmem : n ∈ ⋂ a ∈ G, S a := by
                  simpa [S, lcm0, Finset.lcm_dvd_iff] using hdiv
                simp [Set.indicator, hmem, hdiv]
              · have hmem : n ∉ ⋂ a ∈ G, S a := by
                  simpa [S, lcm0, Finset.lcm_dvd_iff] using hdiv
                simp [Set.indicator, hmem, hdiv]
      _ = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) *
            ((lcm0 G : ℝ) ^ (-s) * ∑' n : ℕ, w n)) := by
              rw [tsum_dirichletWeight_dvd hlcm]
      _ = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s)) * ∑' n : ℕ, w n := by
              ring
  have hnum :
      ∑' n : ℕ, Set.indicator U w n = finiteDirichletMultiples F s * ∑' n : ℕ, w n := by
    calc
      ∑' n : ℕ, Set.indicator U w n = ∑' n : ℕ, Finset.sum A (fun G => J G n) := by
        refine tsum_congr ?_
        intro n
        exact hpoint n
      _ = Finset.sum A (fun G => ∑' n : ℕ, J G n) := by
        rw [Summable.tsum_finsetSum hJsum]
      _ = Finset.sum A (fun G =>
            ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s)) * ∑' n : ℕ, w n) := by
          refine Finset.sum_congr rfl ?_
          intro G hG
          exact hinner G hG
      _ = (Finset.sum A (fun G =>
            ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s)))) * ∑' n : ℕ, w n := by
          rw [Finset.sum_mul]
      _ = finiteDirichletMultiples F s * ∑' n : ℕ, w n := by
          rfl
  have hmult : Set.indicator (Multiples ((F : Set ℕ))) w = Set.indicator U w := by
    funext n
    by_cases hn0 : n = 0
    · subst hn0
      by_cases hU0 : 0 ∈ U
      · simp [Set.indicator, hU0, w, dirichletWeight]
      · simp [Set.indicator, hU0, w, dirichletWeight]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hmem : n ∈ Multiples ((F : Set ℕ)) ↔ n ∈ U := by
        simp [U, S, mem_Multiples_finset_iff (F := F) hFpos hnpos]
      by_cases hU : n ∈ U
      · have hM : n ∈ Multiples ((F : Set ℕ)) := hmem.mpr hU
        simp [Set.indicator, hU, hM]
      · have hM : n ∉ Multiples ((F : Set ℕ)) := by
          intro hM
          exact hU (hmem.mp hM)
        simp [Set.indicator, hU, hM]
  have huSummable : Summable (fun n : ℕ => Set.indicator (Multiples ((F : Set ℕ))) w n) := by
    have hnonneg : ∀ n : ℕ, 0 ≤ Set.indicator (Multiples ((F : Set ℕ))) w n := by
      intro n
      by_cases hn : n ∈ Multiples ((F : Set ℕ))
      · simpa [Set.indicator, hn, w] using dirichletWeight_nonneg s n
      · simp [Set.indicator, hn]
    have hle : ∀ n : ℕ, Set.indicator (Multiples ((F : Set ℕ))) w n ≤ w n := by
      intro n
      by_cases hn : n ∈ Multiples ((F : Set ℕ))
      · simp [Set.indicator, hn]
      · simpa [Set.indicator, hn] using dirichletWeight_nonneg s n
    exact Summable.of_nonneg_of_le hnonneg hle (summable_dirichletWeight hs)
  have hshiftNum :
      (∑' n : ℕ, if n + 1 ∈ Multiples ((F : Set ℕ)) then zetaTerm s n else 0) =
        ∑' n : ℕ, Set.indicator (Multiples ((F : Set ℕ))) w n := by
    symm
    calc
      ∑' n : ℕ, Set.indicator (Multiples ((F : Set ℕ))) w n
          = Set.indicator (Multiples ((F : Set ℕ))) w 0 +
              ∑' n : ℕ, Set.indicator (Multiples ((F : Set ℕ))) w (n + 1) := by
              simpa using huSummable.tsum_eq_zero_add
      _ = ∑' n : ℕ, if n + 1 ∈ Multiples ((F : Set ℕ)) then zetaTerm s n else 0 := by
            have h0 : Set.indicator (Multiples ((F : Set ℕ))) w 0 = 0 := by
              simp [Set.indicator, w, dirichletWeight]
            rw [h0, zero_add]
            refine tsum_congr ?_
            intro n
            simpa [Set.indicator, w, dirichletWeight_succ,
              mem_Multiples_finset_iff (F := F) hFpos (Nat.succ_pos n)]
  have hmultTsum :
      ∑' n : ℕ, Set.indicator (Multiples ((F : Set ℕ))) w n = ∑' n : ℕ, Set.indicator U w n := by
    refine tsum_congr ?_
    intro n
    exact congrFun hmult n
  have hzeta_pos : 0 < zetaReal s := by
    rw [← tsum_dirichletWeight_eq_zetaReal hs]
    exact (summable_dirichletWeight hs).tsum_pos (fun n => dirichletWeight_nonneg s n) 1 (by
      simp [dirichletWeight])
  calc
    mu s (Multiples ((F : Set ℕ)))
        = (∑' n : ℕ, Set.indicator (Multiples ((F : Set ℕ))) w n) / zetaReal s := by
            unfold mu
            rw [hshiftNum]
    _ = (∑' n : ℕ, Set.indicator U w n) / zetaReal s := by
          rw [hmultTsum]
    _ = (finiteDirichletMultiples F s * ∑' n : ℕ, w n) / zetaReal s := by
          rw [hnum]
    _ = finiteDirichletMultiples F s := by
          rw [tsum_dirichletWeight_eq_zetaReal hs]
          simpa [mul_comm] using (mul_div_cancel_left₀ (finiteDirichletMultiples F s) hzeta_pos.ne')

lemma nu_multipleEvent_eq_finiteDirichlet
    (F : Finset ℕ) (hFpos : PositiveFinset F) {s : ℝ} (hs : 1 < s) :
    nu (fun p : (supportPrimes F).attach => ((p.1 : ℝ) ^ (-s))) (multipleEvent (supportPrimes F) F)
      = finiteDirichletMultiples F s := by
  classical
  let P : Finset ℕ := supportPrimes F
  let q : P.attach → ℝ := fun p => (p.1 : ℝ) ^ (-s)
  let EV : ℕ → Set (P.attach → ℕ) := fun a => {v | expVec P a ≤ v}
  let A : Finset (Finset ℕ) := F.powerset.filter (·.Nonempty)
  let J : Finset ℕ → (P.attach → ℕ) → ℝ := fun G v =>
    ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * Set.indicator (⋂ a ∈ G, EV a) (vecWeight q) v)
  have hq : ∀ p : P.attach, 0 ≤ q p ∧ q p < 1 := by
    intro p
    have hp : Nat.Prime p.1 := by
      simpa [P] using prime_of_mem_supportPrimes (F := F) p.1.2
    constructor
    · positivity
    · simpa [q] using primeRatio_lt_one hp hs
  have hmultEvent : multipleEvent P F = ⋃ a ∈ F, EV a := by
    ext v
    constructor
    · intro hv
      rcases hv with ⟨a, haF, _ha0, hva⟩
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨haF, by simpa [EV] using hva⟩⟩
    · intro hv
      rcases Set.mem_iUnion.1 hv with ⟨a, hv⟩
      rcases Set.mem_iUnion.1 hv with ⟨haF, hva⟩
      exact ⟨a, haF, hFpos haF, by simpa [EV] using hva⟩
  have hpoint : ∀ v : P.attach → ℕ,
      Set.indicator (multipleEvent P F) (vecWeight q) v = Finset.sum A (fun G => J G v) := by
    intro v
    simpa [A, J, hmultEvent, zsmul_eq_mul] using
      (Finset.indicator_biUnion_eq_sum_powerset F EV (vecWeight q) v)
  have hJsum : ∀ G ∈ A, Summable (J G) := by
    intro G hG
    have hsumInter : Summable (fun v : P.attach → ℕ => Set.indicator (⋂ a ∈ G, EV a) (vecWeight q) v) := by
      simpa [Set.indicator] using summable_nuSummand q hq (⋂ a ∈ G, EV a)
    simpa [J] using hsumInter.mul_left ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ))
  have hprodEq (G : Finset ℕ) (hGsubset : G ⊆ F) :
      (∏ p : P.attach, q p ^ expVec P (lcm0 G) p) = (lcm0 G : ℝ) ^ (-s) := by
    have hGpos : PositiveFinset G := by
      intro a ha
      exact hFpos (hGsubset ha)
    have hlcm_ne : lcm0 G ≠ 0 := Nat.ne_of_gt (lcm0_pos G hGpos)
    have hsubset : (lcm0 G).factorization.support ⊆ P := by
      simpa [P] using
        factorizationSupport_lcm0_subset_supportPrimes (F := F) (G := G) hFpos hGsubset
    have hprodCast :
        Finset.prod (lcm0 G).factorization.support (fun p => (p : ℝ) ^ (lcm0 G).factorization p) =
          (lcm0 G : ℝ) := by
      exact_mod_cast (Nat.factorization_prod_pow_eq_self hlcm_ne)
    calc
      (∏ p : P.attach, q p ^ expVec P (lcm0 G) p)
          = Finset.prod P.attach (fun p => q ⟨p, by simp⟩ ^ expVec P (lcm0 G) ⟨p, by simp⟩) := by
              rw [Finset.univ_eq_attach]
              simpa using
                (Finset.prod_attach P.attach (fun p => q ⟨p, by simp⟩ ^ expVec P (lcm0 G) ⟨p, by simp⟩))
      _ = Finset.prod P (fun p => ((p : ℝ) ^ (-s)) ^ (lcm0 G).factorization p) := by
            calc
              Finset.prod P.attach (fun p => q ⟨p, by simp⟩ ^ expVec P (lcm0 G) ⟨p, by simp⟩)
                  = Finset.prod P.attach (fun p => ((p.1 : ℝ) ^ (-s)) ^ (lcm0 G).factorization p.1) := by
                      refine Finset.prod_congr rfl ?_
                      intro p hp
                      simp [q, expVec]
              _ = Finset.prod P (fun p => ((p : ℝ) ^ (-s)) ^ (lcm0 G).factorization p) := by
                    simpa using
                      (Finset.prod_attach P (fun p : ℕ => ((p : ℝ) ^ (-s)) ^ (lcm0 G).factorization p))
      _ = Finset.prod P (fun p => (((p : ℝ) ^ (lcm0 G).factorization p) ^ (-s))) := by
            refine Finset.prod_congr rfl ?_
            intro p hp
            have hp0 : 0 ≤ (p : ℝ) := by positivity
            calc
              ((p : ℝ) ^ (-s)) ^ (lcm0 G).factorization p
                  = (p : ℝ) ^ ((-s) * (lcm0 G).factorization p) := by
                      symm
                      exact Real.rpow_mul_natCast hp0 (-s) ((lcm0 G).factorization p)
              _ = (p : ℝ) ^ ((lcm0 G).factorization p * (-s)) := by rw [mul_comm]
              _ = ((p : ℝ) ^ (lcm0 G).factorization p) ^ (-s) := by
                    exact Real.rpow_natCast_mul hp0 ((lcm0 G).factorization p) (-s)
      _ = (Finset.prod P (fun p => (p : ℝ) ^ (lcm0 G).factorization p)) ^ (-s) := by
            simpa using (finset_prod_rpow_natPow P (fun p => (lcm0 G).factorization p) (-s))
      _ = (Finset.prod (lcm0 G).factorization.support (fun p => (p : ℝ) ^ (lcm0 G).factorization p)) ^ (-s) := by
            congr 1
            symm
            exact Finset.prod_subset hsubset (fun p hpP hpNot => by
              have hzero : (lcm0 G).factorization p = 0 := Finsupp.notMem_support_iff.mp hpNot
              simp [hzero])
      _ = (lcm0 G : ℝ) ^ (-s) := by
            rw [hprodCast]
  have hinner (G : Finset ℕ) (hG : G ∈ A) :
      ∑' v : P.attach → ℕ, J G v = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s)) := by
    have hGsubset : G ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1
    have hGpos : PositiveFinset G := by
      intro a ha
      exact hFpos (hGsubset ha)
    calc
      ∑' v : P.attach → ℕ, J G v
          = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) *
              ∑' v : P.attach → ℕ, Set.indicator (⋂ a ∈ G, EV a) (vecWeight q) v) := by
                simp [J, tsum_mul_left]
      _ = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) *
            nu q {v | expVec P (lcm0 G) ≤ v}) := by
              congr 1
              unfold nu
              refine tsum_congr ?_
              intro v
              by_cases hle : expVec P (lcm0 G) ≤ v
              · have hmem : v ∈ ⋂ a ∈ G, EV a :=
                  (mem_iInter_expVec_iff_lcm0_le P G hGpos).2 hle
                simp [Set.indicator, EV, hle, hmem]
              · have hmem : v ∉ ⋂ a ∈ G, EV a := by
                  intro hv
                  exact hle ((mem_iInter_expVec_iff_lcm0_le P G hGpos).1 hv)
                simp [Set.indicator, EV, hle, hmem]
      _ = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * ∏ p : P.attach, q p ^ expVec P (lcm0 G) p) := by
              rw [nu_Ici_eq_prod_pow q (expVec P (lcm0 G)) hq]
      _ = ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s)) := by
              rw [hprodEq G hGsubset]
  have hmain : nu q (multipleEvent P F) = finiteDirichletMultiples F s := by
    calc
      nu q (multipleEvent P F)
          = ∑' v : P.attach → ℕ, Set.indicator (multipleEvent P F) (vecWeight q) v := by
              unfold nu
              refine tsum_congr ?_
              intro v
              by_cases hv : v ∈ multipleEvent P F
              · simp [Set.indicator, hv]
              · simp [Set.indicator, hv]
      _ = ∑' v : P.attach → ℕ, Finset.sum A (fun G => J G v) := by
            refine tsum_congr ?_
            intro v
            exact hpoint v
      _ = Finset.sum A (fun G => ∑' v : P.attach → ℕ, J G v) := by
            rw [Summable.tsum_finsetSum hJsum]
      _ = Finset.sum A (fun G => ((((-1 : ℤ) ^ (G.card + 1) : ℤ) : ℝ) * (lcm0 G : ℝ) ^ (-s))) := by
            refine Finset.sum_congr rfl ?_
            intro G hG
            exact hinner G hG
      _ = finiteDirichletMultiples F s := by
            rfl
  simpa [P, q] using hmain

/--
Bridge theorem between the finite-dimensional product-geometric model and the original
Dirichlet density `mu` for a finite set of multiples.

In the formalization below both sides are identified with the same finite
inclusion-exclusion expression `finiteDirichletMultiples F s`.
-/
theorem mu_multiples_finset_eq_nu
  (F : Finset ℕ) (hFpos : PositiveFinset F) {s : ℝ} (hs : 1 < s) :
    mu s (Multiples ((F : Set ℕ))) =
      nu
        (fun p : (supportPrimes F).attach => ((p.1 : ℝ) ^ (-s)))
        (multipleEvent (supportPrimes F) F) := by
  calc
    mu s (Multiples ((F : Set ℕ))) = finiteDirichletMultiples F s :=
      mu_multiples_finset_eq_finiteDirichlet F hFpos hs
    _ = nu
          (fun p : (supportPrimes F).attach => ((p.1 : ℝ) ^ (-s)))
          (multipleEvent (supportPrimes F) F) :=
      (nu_multipleEvent_eq_finiteDirichlet F hFpos hs).symm

/-- Finite-stage precursor of **Lemma 6** in the original `mu`-language. -/
theorem mu_multiples_finset_antitone
  (F : Finset ℕ) (hFpos : PositiveFinset F) :
    AntitoneOn (fun s : ℝ => mu s (Multiples ((F : Set ℕ)))) (Set.Ioi (1 : ℝ)) := by
  intro s hs t ht hst
  simpa [mu_multiples_finset_eq_nu (F := F) hFpos hs,
    mu_multiples_finset_eq_nu (F := F) hFpos ht] using
    (finiteDivisibilityMonotonePrecursor F hs ht hst)

/-- Finite-stage upper-bound consequence of the precursor of **Lemma 6**.

For a positive finite set `F`, the weighted density of `Multiples F` is bounded above by
its natural density.  This is the only direction needed in the forward implication. -/
theorem mu_multiples_finset_le_density
  (F : Finset ℕ) (hFpos : PositiveFinset F) {s : ℝ} (hs : 1 < s) :
  mu s (Multiples ((F : Set ℕ))) ≤ finiteMultiplesDensity F := by
  have hdens :
      HasNatDensity (Multiples ((F : Set ℕ))) (finiteMultiplesDensity F) :=
    hasNatDensity_multiples_finset F hFpos
  have hlim :
      Tendsto (fun r : ℝ => mu r (Multiples ((F : Set ℕ))))
        (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)))
        (nhds (finiteMultiplesDensity F)) :=
    tendsto_mu_of_hasNatDensity hdens
  have hmono := mu_multiples_finset_antitone F hFpos
  have hEv :
      ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        mu s (Multiples ((F : Set ℕ))) ≤ mu r (Multiples ((F : Set ℕ))) := by
    filter_upwards [show Set.Ioc (1 : ℝ) s ∈ nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)) from by
      simpa using (Ioc_mem_nhdsGT hs)] with r hr
    exact hmono hr.1 hs hr.2
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hEv

/-- Monotonicity of natural density under inclusion.

Compare the counting functions `countUpTo` pointwise and pass to the limit. -/
theorem natDensity_mono
  {S T : Set ℕ} {α β : ℝ}
  (hST : S ⊆ T)
  (hS : HasNatDensity S α)
  (hT : HasNatDensity T β) :
    α ≤ β := by
  refine le_of_tendsto_of_tendsto' hS hT fun N => ?_
  unfold densSeq countUpTo
  have hsubset :
      ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ S) ⊆
        ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ T) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnS⟩
    exact Finset.mem_filter.mpr ⟨hnIcc, hST hnS⟩
  have hcard_nat :
      ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ S).card ≤
        ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ T).card :=
    Finset.card_le_card hsubset
  have hcard :
      (((Finset.Icc 1 (N + 1)).filter fun n => n ∈ S).card : ℝ) ≤
        (((Finset.Icc 1 (N + 1)).filter fun n => n ∈ T).card : ℝ) := by
    exact_mod_cast hcard_nat
  exact div_le_div_of_nonneg_right hcard (by positivity)

/-- Monotonicity of `finiteMultiplesDensity` under inclusion of positive finite divisor sets. -/
theorem finiteMultiplesDensity_mono_of_subset
  {F G : Finset ℕ}
  (hFG : ((F : Set ℕ) ⊆ (G : Set ℕ)))
  (hFpos : PositiveFinset F) (hGpos : PositiveFinset G) :
    finiteMultiplesDensity F ≤ finiteMultiplesDensity G := by
  exact natDensity_mono (Multiples_mono hFG)
    (hasNatDensity_multiples_finset F hFpos)
    (hasNatDensity_multiples_finset G hGpos)

/-- Every positive finite subset `F ⊆ A` is contained in the truncation of `A` at `sup F`. -/
lemma subset_trunc_sup_of_subset
    {A : Set ℕ} {F : Finset ℕ}
    (hFpos : PositiveFinset F)
    (hFA : ((F : Set ℕ) ⊆ A)) :
    ((F : Set ℕ) ⊆ ((trunc A (F.sup id) : Finset ℕ) : Set ℕ)) := by
  intro a ha
  have haF : a ∈ F := ha
  have haA : a ∈ A := hFA ha
  have ha_pos : 0 < a := hFpos haF
  have ha_le : a ≤ F.sup id := Finset.le_sup (f := id) haF
  exact (mem_trunc (A := A) (N := F.sup id) (a := a)).2
    ⟨⟨Nat.succ_le_of_lt ha_pos, ha_le⟩, haA⟩

/-- Finite-subset densities are bounded by a suitable truncation density.

This is the formal version of the TeX observation that every finite `F ⊆ A`
is contained in `A_N` for all sufficiently large `N`. -/
lemma finiteMultiplesDensity_le_trunc_sup
    {A : Set ℕ} {F : Finset ℕ}
    (hFpos : PositiveFinset F)
    (hFA : ((F : Set ℕ) ⊆ A)) :
    finiteMultiplesDensity F ≤ finiteMultiplesDensity (trunc A (F.sup id)) := by
  exact finiteMultiplesDensity_mono_of_subset
    (subset_trunc_sup_of_subset hFpos hFA) hFpos (trunc_positive A (F.sup id))

/-- `N ↦ finiteMultiplesDensity (trunc A N)` is monotone increasing.

Proof idea: `trunc A N ⊆ trunc A M` for `N ≤ M`, hence
`Multiples (trunc A N) ⊆ Multiples (trunc A M)`, then apply
`finiteMultiplesDensity_mono_of_subset`. -/
theorem finiteMultiplesDensity_trunc_mono (A : Set ℕ) :
    Monotone (fun N => finiteMultiplesDensity (trunc A N)) := by
  intro N M hNM
  have htrunc :
      (((trunc A N : Finset ℕ) : Set ℕ) ⊆ ((trunc A M : Finset ℕ) : Set ℕ)) := by
    intro a ha
    have ha' := (mem_trunc (A := A) (N := N) (a := a)).1 ha
    exact (mem_trunc (A := A) (N := M) (a := a)).2
      ⟨⟨ha'.1.1, le_trans ha'.1.2 hNM⟩, ha'.2⟩
  exact finiteMultiplesDensity_mono_of_subset htrunc
    (trunc_positive A N) (trunc_positive A M)

/-! ## Elementary limit helpers -/

/-- Every density sequence is bounded above by `1`. -/
theorem densSeq_le_one (S : Set ℕ) (N : ℕ) :
    densSeq S N ≤ 1 := by
  unfold densSeq
  have hle_nat : countUpTo S (N + 1) ≤ N + 1 := by
    unfold countUpTo
    calc
      ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ S).card
          ≤ (Finset.Icc 1 (N + 1)).card := Finset.card_filter_le _ _
      _ = N + 1 := by simp
  have hle : (countUpTo S (N + 1) : ℝ) ≤ (N + 1 : ℝ) := by
    exact_mod_cast hle_nat
  have hpos : 0 < (N + 1 : ℝ) := by positivity
  exact (div_le_one hpos).2 hle

/-- Monotonicity of density sequences under inclusion. -/
theorem densSeq_mono_of_subset
  {S T : Set ℕ} (hST : S ⊆ T) :
    ∀ N : ℕ, densSeq S N ≤ densSeq T N := by
  intro N
  unfold densSeq countUpTo
  have hsubset :
      ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ S) ⊆
        ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ T) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnS⟩
    exact Finset.mem_filter.mpr ⟨hnIcc, hST hnS⟩
  have hcard_nat :
      ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ S).card ≤
        ((Finset.Icc 1 (N + 1)).filter fun n => n ∈ T).card :=
    Finset.card_le_card hsubset
  have hcard :
      (((Finset.Icc 1 (N + 1)).filter fun n => n ∈ S).card : ℝ) ≤
        (((Finset.Icc 1 (N + 1)).filter fun n => n ∈ T).card : ℝ) := by
    exact_mod_cast hcard_nat
  exact div_le_div_of_nonneg_right hcard (by positivity)

/-- A standard squeeze-lemma package tailored to this file.

If eventually `densSeq S N > 1 - ε` for every `ε > 0`, and the sequence is always `≤ 1`,
then `S` has natural density `1`. -/
theorem hasNatDensity_one_of_eventually_ge
  {S : Set ℕ}
  (hlower :
    ∀ ε > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 1 - ε < densSeq S N)
  (hupper : ∀ N : ℕ, densSeq S N ≤ 1) :
    HasNatDensity S 1 := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let ε : ℝ := 1 - a
    have hε : 0 < ε := by
      simpa [ε] using sub_pos.mpr ha
    rcases hlower ε hε with ⟨N0, hN0⟩
    exact Filter.eventually_atTop.2 ⟨N0, fun N hN => by
      simpa [ε] using hN0 N hN⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun N => lt_of_le_of_lt (hupper N) ha

/-! ## Analytic-to-finite approximation bridge -/

/-- If `Multiples A` has density `1`, then for every `ε > 0` there exists `s > 1` with
`mu s (Multiples A) > 1 - ε`.  This is just the neighbourhood formulation of
`tendsto_mu_of_hasNatDensity`. -/
theorem exists_s_gt_one_of_mu_gt
  {A : Set ℕ} {ε : ℝ}
  (hA : IsBehrend A) (hε : 0 < ε) :
    ∃ s : ℝ, 1 < s ∧ 1 - ε < mu s (Multiples A) := by
  have hmu :
      Tendsto (fun s : ℝ => mu s (Multiples A))
        (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (1 : ℝ)) :=
    tendsto_mu_of_hasNatDensity hA
  have hgt :
      ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        1 - ε < mu s (Multiples A) :=
    (tendsto_order.1 hmu).1 _ (by linarith)
  rcases (hgt.and self_mem_nhdsWithin).exists with ⟨s, hs, hsIoi⟩
  exact ⟨s, by simpa [Set.mem_Ioi] using hsIoi, hs⟩

/-- Partial sums suffice for the forward implication.

If `mu s (Multiples A) > 1 - ε`, then some truncation already has weighted density
`> 1 - ε`.

Proof idea:
* choose `K` so that the partial Dirichlet sum up to `K` exceeds `1 - ε`;
* for every `n ≤ K`, use `mem_Multiples_trunc_iff_of_le` to replace `A` by `trunc A K`;
* conclude that `mu s (Multiples (trunc A K)) > 1 - ε`. -/
theorem exists_trunc_of_mu_gt
  {A : Set ℕ} {ε s : ℝ}
  (hs : 1 < s)
  (hmu : 1 - ε < mu s (Multiples A)) :
    ∃ N : ℕ, 1 - ε < mu s (Multiples (((trunc A N : Finset ℕ) : Set ℕ))) := by
  let f : ℕ → ℝ := fun n => if n + 1 ∈ Multiples A then zetaTerm s n else 0
  have hzetaTerm_pos : ∀ n : ℕ, 0 < zetaTerm s n := by
    intro n
    have hbase : 0 < (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    simpa [zetaTerm] using one_div_pos.mpr (Real.rpow_pos_of_pos hbase s)
  have hzetaTerm_nonneg : ∀ n : ℕ, 0 ≤ zetaTerm s n := fun n => (hzetaTerm_pos n).le
  have hzetaSummable : Summable (fun n : ℕ => zetaTerm s n) := by
    have hpowInv : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ s)⁻¹) := by
      exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) 1).2
        (Real.summable_nat_rpow_inv.mpr hs)
    simpa [zetaTerm, one_div, Real.rpow_natCast] using hpowInv
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    by_cases hn : n + 1 ∈ Multiples A
    · simp [f, hn, hzetaTerm_nonneg n]
    · simp [f, hn]
  have hf_le : ∀ n : ℕ, f n ≤ zetaTerm s n := by
    intro n
    by_cases hn : n + 1 ∈ Multiples A
    · simp [f, hn]
    · simp [f, hn, hzetaTerm_nonneg n]
  have hfSummable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hf_le hzetaSummable
  have hzeta_pos : 0 < zetaReal s := by
    simpa [zetaReal] using hzetaSummable.tsum_pos hzetaTerm_nonneg 0 (hzetaTerm_pos 0)
  have hnum_gt : (1 - ε) * zetaReal s < ∑' n : ℕ, f n := by
    have hmu' : 1 - ε < (∑' n : ℕ, f n) / zetaReal s := by
      simpa [mu, f] using hmu
    exact (lt_div_iff₀ hzeta_pos).1 hmu'
  have hpartial :
      ∀ᶠ N in Filter.atTop, (1 - ε) * zetaReal s < Finset.sum (Finset.range N) f := by
    have hconv :
        Tendsto (fun N : ℕ => Finset.sum (Finset.range N) f)
          Filter.atTop (nhds (∑' n : ℕ, f n)) :=
      hfSummable.hasSum.tendsto_sum_nat
    exact hconv (Ioi_mem_nhds hnum_gt)
  rw [eventually_atTop] at hpartial
  rcases hpartial with ⟨N, hNpartial⟩
  refine ⟨N, ?_⟩
  let T : Set ℕ := Multiples (((trunc A N : Finset ℕ) : Set ℕ))
  let g : ℕ → ℝ := fun n => if n + 1 ∈ T then zetaTerm s n else 0
  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    by_cases hn : n + 1 ∈ T
    · simp [g, hn, hzetaTerm_nonneg n]
    · simp [g, hn]
  have hg_le : ∀ n : ℕ, g n ≤ zetaTerm s n := by
    intro n
    by_cases hn : n + 1 ∈ T
    · simp [g, hn]
    · simp [g, hn, hzetaTerm_nonneg n]
  have hgSummable : Summable g :=
    Summable.of_nonneg_of_le hg_nonneg hg_le hzetaSummable
  have hsum_eq :
      Finset.sum (Finset.range N) f = Finset.sum (Finset.range N) g := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn_lt : n < N := Finset.mem_range.1 hn
    have hmem : n + 1 ∈ Multiples A ↔ n + 1 ∈ T := by
      simpa [T] using
        (mem_Multiples_trunc_iff_of_le (A := A) (n := n + 1) (N := N)
          (Nat.succ_le_of_lt hn_lt))
    by_cases hA : n + 1 ∈ Multiples A
    · have hT : n + 1 ∈ T := hmem.mp hA
      simp [f, g, hA, hT]
    · have hT : ¬ n + 1 ∈ T := by
        exact fun hTmem => hA (hmem.mpr hTmem)
      simp [f, g, hA, hT]
  have hpartialT : (1 - ε) * zetaReal s < Finset.sum (Finset.range N) g := by
    calc
      (1 - ε) * zetaReal s < Finset.sum (Finset.range N) f := hNpartial N le_rfl
      _ = Finset.sum (Finset.range N) g := hsum_eq
  have hnumT : (1 - ε) * zetaReal s < ∑' n : ℕ, g n := by
    exact lt_of_lt_of_le hpartialT <|
      hgSummable.sum_le_tsum (Finset.range N) (fun n _ => hg_nonneg n)
  have : 1 - ε < (∑' n : ℕ, g n) / zetaReal s := by
    exact (lt_div_iff₀ hzeta_pos).2 hnumT
  simpa [mu, T, g] using this


/-! ## General form of Lemma 6 for divisibility-upward-closed subsets of `ℕ` -/

/-- Upward-closed for divisibility on the positive integers.

This is the exact closure condition used in the revised TeX statement of **Lemma 6**.
We only care about positive targets because `mu` is indexed by `n + 1`, and `Multiples A`
was defined to ignore `0`. -/
def DivisibilityUpwardClosed (U : Set ℕ) : Prop :=
  ∀ ⦃n m : ℕ⦄, n ∈ U → 0 < m → n ∣ m → m ∈ U

lemma divisibilityUpwardClosed_Multiples (A : Set ℕ) :
    DivisibilityUpwardClosed (Multiples A) := by
  intro n m hn hmpos hnm
  rcases hn with ⟨hnpos, a, haA, hapos, hadiv⟩
  exact ⟨hmpos, a, haA, hapos, dvd_trans hadiv hnm⟩

lemma zetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaTerm s n := by
  unfold zetaTerm
  exact one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) s)

lemma zetaTerm_pos (s : ℝ) (n : ℕ) : 0 < zetaTerm s n := by
  unfold zetaTerm
  have hbase : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  exact one_div_pos.mpr (Real.rpow_pos_of_pos hbase s)

lemma summable_zetaTerm {s : ℝ} (hs : 1 < s) :
    Summable (zetaTerm s) := by
  have hzetaEq : zetaTerm s = fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ s)⁻¹) := by
    funext n
    simp [zetaTerm, one_div]
  rw [hzetaEq]
  exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) 1).2
    (Real.summable_nat_rpow_inv.mpr hs)

lemma zetaReal_pos {s : ℝ} (hs : 1 < s) : 0 < zetaReal s := by
  have hzetaSummable : Summable (zetaTerm s) := summable_zetaTerm hs
  simpa [zetaReal] using hzetaSummable.tsum_pos (zetaTerm_nonneg s) 0 (zetaTerm_pos s 0)

/-- Monotonicity of `mu` under set inclusion for `s > 1`. -/
lemma mu_mono_set {S T : Set ℕ} {s : ℝ}
    (hST : S ⊆ T) (hs : 1 < s) :
    mu s S ≤ mu s T := by
  let f : ℕ → ℝ := fun n => if n + 1 ∈ S then zetaTerm s n else 0
  let g : ℕ → ℝ := fun n => if n + 1 ∈ T then zetaTerm s n else 0
  have hzetaSummable : Summable (zetaTerm s) := summable_zetaTerm hs
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    by_cases hn : n + 1 ∈ S
    · simp [f, hn, zetaTerm_nonneg s n]
    · simp [f, hn]
  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    by_cases hn : n + 1 ∈ T
    · simp [g, hn, zetaTerm_nonneg s n]
    · simp [g, hn]
  have hf_le_zeta : ∀ n : ℕ, f n ≤ zetaTerm s n := by
    intro n
    by_cases hn : n + 1 ∈ S
    · simp [f, hn]
    · simp [f, hn, zetaTerm_nonneg s n]
  have hg_le_zeta : ∀ n : ℕ, g n ≤ zetaTerm s n := by
    intro n
    by_cases hn : n + 1 ∈ T
    · simp [g, hn]
    · simp [g, hn, zetaTerm_nonneg s n]
  have hfSummable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hf_le_zeta hzetaSummable
  have hgSummable : Summable g :=
    Summable.of_nonneg_of_le hg_nonneg hg_le_zeta hzetaSummable
  have hfg : ∀ n : ℕ, f n ≤ g n := by
    intro n
    by_cases hnS : n + 1 ∈ S
    · have hnT : n + 1 ∈ T := hST hnS
      simp [f, g, hnS, hnT]
    · by_cases hnT : n + 1 ∈ T
      · simp [f, g, hnS, hnT, zetaTerm_nonneg s n]
      · simp [f, g, hnS, hnT]
  have hnum : ∑' n : ℕ, f n ≤ ∑' n : ℕ, g n :=
    hfSummable.tsum_le_tsum hfg hgSummable
  have hzeta_pos : 0 < zetaReal s := zetaReal_pos hs
  unfold mu
  simpa [f, g] using div_le_div_of_nonneg_right hnum hzeta_pos.le

lemma mu_eq_of_pos_mem_iff {S T : Set ℕ} {s : ℝ}
    (hST : ∀ ⦃n : ℕ⦄, 0 < n → (n ∈ S ↔ n ∈ T)) :
    mu s S = mu s T := by
  have hfun :
      (fun n : ℕ => if n + 1 ∈ S then zetaTerm s n else 0) =
        (fun n : ℕ => if n + 1 ∈ T then zetaTerm s n else 0) := by
    funext n
    have hmem : n + 1 ∈ S ↔ n + 1 ∈ T := hST (n := n + 1) (Nat.succ_pos n)
    by_cases hnS : n + 1 ∈ S
    · have hnT : n + 1 ∈ T := hmem.mp hnS
      simp [hnS, hnT]
    · have hnT : ¬ n + 1 ∈ T := by
        intro hT
        exact hnS (hmem.mpr hT)
      simp [hnS, hnT]
  simp [mu, hfun]

lemma mu_multiples_eq_self_of_divisibilityUpwardClosed {U : Set ℕ} (hU : DivisibilityUpwardClosed U)
    (s : ℝ) :
    mu s (Multiples U) = mu s U := by
  refine mu_eq_of_pos_mem_iff ?_
  intro n hn
  constructor
  · intro hnM
    rcases hnM with ⟨hnpos, a, haU, hapos, hadiv⟩
    exact hU haU hn hadiv
  · intro hnU
    exact ⟨hn, n, hnU, hn, dvd_rfl⟩

lemma multiples_trunc_subset_of_divisibilityUpwardClosed {U : Set ℕ}
    (hU : DivisibilityUpwardClosed U) (N : ℕ) :
    Multiples (((trunc U N : Finset ℕ) : Set ℕ)) ⊆ U := by
  intro n hn
  rcases hn with ⟨hnpos, a, haF, hapos, hadiv⟩
  have haU : a ∈ U := ((mem_trunc (A := U) (N := N) (a := a)).1 haF).2
  exact hU haU hnpos hadiv

lemma mu_univ_eq_one {s : ℝ} (hs : 1 < s) :
    mu s (Set.univ : Set ℕ) = 1 := by
  have hzeta_pos : 0 < zetaReal s := zetaReal_pos hs
  calc
    mu s (Set.univ : Set ℕ) = zetaReal s / zetaReal s := by
      simp [mu, zetaReal]
    _ = 1 := div_self hzeta_pos.ne'

lemma mu_le_one {S : Set ℕ} {s : ℝ} (hs : 1 < s) :
    mu s S ≤ 1 := by
  calc
    mu s S ≤ mu s (Set.univ : Set ℕ) :=
      mu_mono_set (S := S) (T := Set.univ) (by intro n hn; trivial) hs
    _ = 1 := mu_univ_eq_one hs

/-- **Lemma 6** (`lem:divisibility-monotone`) in the revised self-contained TeX note.

Proof sketch in Lean:

1. assume `mu s U < mu t U` with `1 < s ≤ t`;
2. pick the midpoint `a`;
3. rewrite `mu t U` as `mu t (Multiples U)` using divisibility-upward-closedness;
4. apply `exists_trunc_of_mu_gt` to find a finite truncation with
   `a < mu t (Multiples (trunc U N))`;
5. apply the already formalized finite theorem `mu_multiples_finset_antitone`;
6. use `Multiples (trunc U N) ⊆ U` and `mu_mono_set` to contradict `mu s U < a`.

This upgrades the existing finite formalization to the exact statement appearing in the TeX file,
without introducing an infinite product probability space over all primes. -/
theorem mu_le_of_divisibilityUpwardClosed
    {U : Set ℕ} (hU : DivisibilityUpwardClosed U)
    {s t : ℝ} (hs : 1 < s) (ht : 1 < t) (hst : s ≤ t) :
    mu t U ≤ mu s U := by
  by_contra hcontra
  let a : ℝ := (mu s U + mu t U) / 2
  have hs_lt_a : mu s U < a := by
    dsimp [a]
    linarith
  have ha_lt_t : a < mu t U := by
    dsimp [a]
    linarith
  have ht_le_one : mu t U ≤ 1 := mu_le_one (S := U) ht
  have ha_lt_one : a < 1 := lt_of_lt_of_le ha_lt_t ht_le_one
  have hε : 0 < 1 - a := by
    linarith
  have happrox_input : 1 - (1 - a) < mu t (Multiples U) := by
    simpa [mu_multiples_eq_self_of_divisibilityUpwardClosed (U := U) hU t] using ha_lt_t
  rcases exists_trunc_of_mu_gt (A := U) (ε := 1 - a) (s := t) ht happrox_input with ⟨N, hN⟩
  have hfin_mono := mu_multiples_finset_antitone (trunc U N) (trunc_positive U N)
  have hN' : a < mu t (Multiples (((trunc U N : Finset ℕ) : Set ℕ))) := by
    simpa using hN
  have hfin_step : a < mu s (Multiples (((trunc U N : Finset ℕ) : Set ℕ))) := by
    exact lt_of_lt_of_le hN' (hfin_mono hs ht hst)
  have hsubset : Multiples (((trunc U N : Finset ℕ) : Set ℕ)) ⊆ U :=
    multiples_trunc_subset_of_divisibilityUpwardClosed (U := U) hU N
  have hmono_set :
      mu s (Multiples (((trunc U N : Finset ℕ) : Set ℕ))) ≤ mu s U :=
    mu_mono_set hsubset hs
  have : a < mu s U := lt_of_lt_of_le hfin_step hmono_set
  exact (not_lt_of_ge hs_lt_a.le) this

/-- Antitone reformulation of **Lemma 6** (`lem:divisibility-monotone`). -/
theorem mu_antitone_of_divisibilityUpwardClosed
    {U : Set ℕ} (hU : DivisibilityUpwardClosed U) :
    AntitoneOn (fun s : ℝ => mu s U) (Set.Ioi (1 : ℝ)) := by
  intro s hs t ht hst
  exact mu_le_of_divisibilityUpwardClosed hU hs ht hst

/-- Useful corollary: **Lemma 6** now applies to `Multiples A` for arbitrary `A`, not only finite ones. -/
theorem mu_multiples_antitone (A : Set ℕ) :
    AntitoneOn (fun s : ℝ => mu s (Multiples A)) (Set.Ioi (1 : ℝ)) := by
  exact mu_antitone_of_divisibilityUpwardClosed
    (U := Multiples A) (divisibilityUpwardClosed_Multiples A)

/-! ## Finite approximation criterion -/

/-- **Theorem 1** (`thm:finite-approx`) in truncation `ε`-form.

This is the Lean-friendly version of the finite-approximation criterion in the revised TeX note. -/
theorem behrend_iff_finiteApprox_eps (A : Set ℕ) :
    IsBehrend A ↔
      ∀ ε > 0, ∃ N : ℕ, 1 - ε < finiteMultiplesDensity (trunc A N) := by
  constructor
  · intro hA
    intro ε hε
    rcases exists_s_gt_one_of_mu_gt (A := A) hA hε with ⟨s, hs, hsA⟩
    rcases exists_trunc_of_mu_gt (A := A) (ε := ε) (s := s) hs hsA with ⟨N, hN⟩
    refine ⟨N, lt_of_lt_of_le hN ?_⟩
    exact mu_multiples_finset_le_density (trunc A N) (trunc_positive A N) hs
  · intro happrox
    apply hasNatDensity_one_of_eventually_ge
    · intro ε hε
      rcases happrox ε hε with ⟨N, hN⟩
      have hdensN :
          HasNatDensity (Multiples (((trunc A N : Finset ℕ) : Set ℕ)))
            (finiteMultiplesDensity (trunc A N)) :=
        hasNatDensity_multiples_finset (trunc A N) (trunc_positive A N)
      have hEv :
          ∀ᶠ K : ℕ in Filter.atTop,
            1 - ε < densSeq (Multiples (((trunc A N : Finset ℕ) : Set ℕ))) K :=
        (tendsto_order.1 hdensN).1 _ hN
      rcases Filter.eventually_atTop.1 hEv with ⟨N0, hN0⟩
      refine ⟨N0, fun K hK => ?_⟩
      have hsubset :
          Multiples (((trunc A N : Finset ℕ) : Set ℕ)) ⊆ Multiples A :=
        Multiples_mono (trunc_subset A N)
      exact lt_of_lt_of_le (hN0 K hK) ((densSeq_mono_of_subset hsubset) K)
    · intro N
      exact densSeq_le_one (Multiples A) N

/-- Truncation-based and arbitrary finite-subset `ε`-approximations are equivalent.

This is the bridge between the current `trunc A N` formulation and the TeX form
`∀ ε > 0, ∃ finite F ⊆ A, d(M_F) > 1 - ε`.

Because the ambient type is Lean's `ℕ`, we keep the harmless positivity side condition
`PositiveFinset F`; all relevant divisor sets live in positive integers anyway. -/
theorem finiteApprox_eps_iff_finiteSubsetApprox_eps (A : Set ℕ) :
    (∀ ε > 0, ∃ N : ℕ, 1 - ε < finiteMultiplesDensity (trunc A N)) ↔
      ∀ ε > 0, ∃ F : Finset ℕ,
        PositiveFinset F ∧ ((F : Set ℕ) ⊆ A) ∧
        1 - ε < finiteMultiplesDensity F := by
  constructor
  · intro htrunc ε hε
    rcases htrunc ε hε with ⟨N, hN⟩
    exact ⟨trunc A N, trunc_positive A N, trunc_subset A N, hN⟩
  · intro hfin ε hε
    rcases hfin ε hε with ⟨F, hFpos, hFA, hFdens⟩
    exact ⟨F.sup id, lt_of_lt_of_le hFdens (finiteMultiplesDensity_le_trunc_sup hFpos hFA)⟩

/-- **Theorem 1** (`thm:finite-approx`) in arbitrary finite-subset `ε`-form.

This is the version that most closely matches the final displayed `ε`-criterion in the revised
TeX note. -/
theorem behrend_iff_finiteSubsetApprox_eps (A : Set ℕ) :
    IsBehrend A ↔
      ∀ ε > 0, ∃ F : Finset ℕ,
        PositiveFinset F ∧ ((F : Set ℕ) ⊆ A) ∧
        1 - ε < finiteMultiplesDensity F := by
  exact (behrend_iff_finiteApprox_eps A).trans
    (finiteApprox_eps_iff_finiteSubsetApprox_eps A)

/-
From `behrend_iff_finiteSubsetApprox_eps`, one can recover the literal TeX statement
`sup_{F ⊆ A, F finite} d(M_F) = 1` by defining the set of finite-stage densities

  `{x : ℝ | ∃ F : Finset ℕ, PositiveFinset F ∧ ((F : Set ℕ) ⊆ A) ∧ x = finiteMultiplesDensity F}`

and then using a routine `sSup` argument.  The new theorem above is the combinatorial core:
* forward direction: choose `F = trunc A N`;
* reverse direction: replace `F` by the truncation at `F.sup id` and use monotonicity.
-/

/-- **Theorem 1** (`thm:finite-approx`) in sequence form.

Proof idea:
* use `behrend_iff_finiteApprox_eps`;
* use the monotonicity of `N ↦ finiteMultiplesDensity (trunc A N)`;
* a monotone sequence bounded above by `1` tends to `1` iff it is eventually
  above `1 - ε` for every `ε > 0`. -/
theorem behrend_iff_truncFiniteDensities_tendsto_one (A : Set ℕ) :
    IsBehrend A ↔
      Tendsto (fun N : ℕ => finiteMultiplesDensity (trunc A N)) Filter.atTop (nhds 1) := by
  constructor
  · intro hA
    have happrox :
        ∀ ε > 0, ∃ N : ℕ, 1 - ε < finiteMultiplesDensity (trunc A N) :=
      (behrend_iff_finiteApprox_eps A).1 hA
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      let ε : ℝ := 1 - a
      have hε : 0 < ε := by
        simpa [ε] using sub_pos.mpr ha
      rcases happrox ε hε with ⟨N0, hN0⟩
      exact Filter.eventually_atTop.2 ⟨N0, fun N hN => by
        have hmono := (finiteMultiplesDensity_trunc_mono A) hN
        have : 1 - ε < finiteMultiplesDensity (trunc A N) :=
          lt_of_lt_of_le hN0 hmono
        simpa [ε] using this⟩
    · intro a ha
      have hupper :
          ∀ N : ℕ, finiteMultiplesDensity (trunc A N) ≤ 1 := by
        intro N
        let S : Set ℕ := Multiples (((trunc A N : Finset ℕ) : Set ℕ))
        have hdens : HasNatDensity S (finiteMultiplesDensity (trunc A N)) := by
          simpa [S] using hasNatDensity_multiples_finset (trunc A N) (trunc_positive A N)
        exact le_of_tendsto_of_tendsto' hdens tendsto_const_nhds fun K => densSeq_le_one S K
      exact Filter.Eventually.of_forall fun N => lt_of_le_of_lt (hupper N) ha
  · intro hlim
    refine (behrend_iff_finiteApprox_eps A).2 ?_
    intro ε hε
    have hEv :
        ∀ᶠ N : ℕ in Filter.atTop, 1 - ε < finiteMultiplesDensity (trunc A N) :=
      (tendsto_order.1 hlim).1 _ (by linarith)
    rcases Filter.eventually_atTop.1 hEv with ⟨N, hN⟩
    exact ⟨N, hN N le_rfl⟩

/-! ## Primitive-kernel reduction -/

/-- **Lemma 8** (`lem:primitive-same`) in the revised self-contained TeX note.

Removing non-primitive elements does not change the set of multiples.

Proof idea:
if `n ∈ Multiples A`, choose a witness `a ∈ A`, `a ∣ n`.
Among the finitely many elements of `A ∩ n.divisors`, choose a minimal one;
it lies in `primitiveKernel A`, and still divides `n`. -/
theorem multiples_primitiveKernel (A : Set ℕ) :
    Multiples A = Multiples (primitiveKernel A) := by
  classical
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnpos, a, haA, hapos, hadiv⟩
    let D : Finset ℕ := n.divisors.filter fun d => d ∈ A
    have haD : a ∈ D := by
      refine Finset.mem_filter.mpr ⟨?_, haA⟩
      exact Nat.mem_divisors.2 ⟨hadiv, Nat.ne_of_gt hnpos⟩
    have hDne : D.Nonempty := ⟨a, haD⟩
    set m : ℕ := D.min' hDne with hm
    have hmD : m ∈ D := by
      rw [hm]
      exact Finset.min'_mem D hDne
    have hmDiv : m ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hmD).1
    have hmPos : 0 < m := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hmD).1
    have hmA : m ∈ A := (Finset.mem_filter.mp hmD).2
    have hmPrim : m ∈ primitiveKernel A := by
      refine ⟨hmA, hmPos, ?_⟩
      intro b hbA hbPos hbDiv
      have hbDn : b ∣ n := dvd_trans hbDiv hmDiv
      have hbD : b ∈ D := by
        refine Finset.mem_filter.mpr ⟨?_, hbA⟩
        exact Nat.mem_divisors.2 ⟨hbDn, Nat.ne_of_gt hnpos⟩
      rw [hm]
      exact Finset.min'_le D b hbD
    exact ⟨hnpos, m, hmPrim, hmPos, hmDiv⟩
  · intro hn
    exact (Multiples_mono (primitiveKernel_subset A)) hn

/-! ## Explicit sieve criterion -/

/-- Standalone nonempty-subset inclusion-exclusion form of the finite density
`finiteMultiplesDensity F`.  This matches the second displayed formula in the
revised TeX corollary. -/
theorem finiteMultiplesDensity_eq_nonempty_powerset_sum (F : Finset ℕ) :
    finiteMultiplesDensity F =
      ∑ G ∈ F.powerset with G.Nonempty, (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ) := by
  classical
  let A : Finset (Finset ℕ) := F.powerset.filter (·.Nonempty)
  let f : Finset ℕ → ℝ := fun G => (-1 : ℝ) ^ G.card / (lcm0 G : ℝ)
  let S : ℝ := Finset.sum A f
  have hempty_not_mem_A : ∅ ∉ A := by
    simp [A]
  have hpowerset : F.powerset = insert ∅ A := by
    ext G
    by_cases hG : G = ∅
    · simp [A, hG]
    · have hGne : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hG
      simp [A, hG, hGne]
  have havoid : finiteAvoidDensity F = 1 + S := by
    calc
      finiteAvoidDensity F = Finset.sum F.powerset f := by
        simp [finiteAvoidDensity, f]
      _ = Finset.sum (insert ∅ A) f := by rw [hpowerset]
      _ = f ∅ + Finset.sum A f := by rw [Finset.sum_insert hempty_not_mem_A]
      _ = 1 + S := by
            simp [f, lcm0, S]
  have hneg :
      -S =
        Finset.sum A (fun G => (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ)) := by
    calc
      -S = -(Finset.sum A f) := by simp [S]
      _ = Finset.sum A (fun G => -f G) := by simp
      _ = Finset.sum A (fun G => (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro G hG
            dsimp [f]
            calc
              -(((-1 : ℝ) ^ G.card) / (lcm0 G : ℝ))
                  = (-((-1 : ℝ) ^ G.card)) / (lcm0 G : ℝ) := by rw [neg_div]
              _ = (((-1 : ℝ) ^ G.card) * (-1)) / (lcm0 G : ℝ) := by ring
              _ = (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ) := by rw [pow_succ]
  calc
    finiteMultiplesDensity F = 1 - finiteAvoidDensity F := by rfl
    _ = 1 - (1 + S) := by rw [havoid]
    _ = -S := by ring
    _ = Finset.sum A (fun G => (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ)) := hneg
    _ = ∑ G ∈ F.powerset with G.Nonempty, (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ) := by
          simp [A]

/-- Density statement used in **Corollary 2** (`cor:main-sieve-answer`) and
**Corollary 9** (`cor:sieve-criterion`).

`R A N` is the natural density of the integers divisible by none of the elements of
`B_N = A^{prim} ∩ [1,N]`. -/
theorem hasNatDensity_avoidSet_eq_R (A : Set ℕ) (N : ℕ) :
    HasNatDensity (AvoidSet (primitiveTrunc A N)) (R A N) := by
  simpa [R] using
    hasNatDensity_avoidSet_finset (primitiveTrunc A N) (primitiveTrunc_positive A N)

/-- Corollary-style reformulation: the nonempty-subset sum for `B_N` is exactly
`1 - R_N`. -/
theorem one_sub_R_eq_nonempty_powerset_sum (A : Set ℕ) (N : ℕ) :
    1 - R A N =
      ∑ G ∈ (primitiveTrunc A N).powerset with G.Nonempty,
        (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ) := by
  calc
    1 - R A N = finiteMultiplesDensity (primitiveTrunc A N) := by
      symm
      exact finiteMultiplesDensity_eq_one_sub_R A N
    _ =
        ∑ G ∈ (primitiveTrunc A N).powerset with G.Nonempty,
          (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ) :=
      finiteMultiplesDensity_eq_nonempty_powerset_sum (primitiveTrunc A N)

/-- **Corollary 2** (`cor:main-sieve-answer`) and equivalently **Corollary 9**
(`cor:sieve-criterion`) in `R_N → 0` form. -/
theorem behrend_iff_R_tendsto_zero (A : Set ℕ) :
    IsBehrend A ↔ Tendsto (R A) Filter.atTop (nhds 0) := by
  constructor
  · intro hA
    have hprim : IsBehrend (primitiveKernel A) := by
      simpa [IsBehrend, multiples_primitiveKernel A] using hA
    have hdens :
        Tendsto (fun N : ℕ => finiteMultiplesDensity (primitiveTrunc A N))
          Filter.atTop (nhds 1) := by
      simpa [primitiveTrunc] using
        (behrend_iff_truncFiniteDensities_tendsto_one (primitiveKernel A)).1 hprim
    have hsub : Tendsto (fun N : ℕ => 1 - R A N) Filter.atTop (nhds 1) := by
      simpa [finiteMultiplesDensity_eq_one_sub_R] using hdens
    have hzero' :
        Tendsto (fun N : ℕ => 1 - (1 - R A N)) Filter.atTop (nhds (1 - 1)) :=
      tendsto_const_nhds.sub hsub
    convert hzero' using 1
    · ext N
      ring
    · ring
  · intro hR
    have hsub : Tendsto (fun N : ℕ => 1 - R A N) Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hR)
    have hdens :
        Tendsto (fun N : ℕ => finiteMultiplesDensity (primitiveTrunc A N))
          Filter.atTop (nhds 1) := by
      simpa [finiteMultiplesDensity_eq_one_sub_R] using hsub
    have hprim : IsBehrend (primitiveKernel A) := by
      exact (behrend_iff_truncFiniteDensities_tendsto_one (primitiveKernel A)).2
        (by simpa [primitiveTrunc] using hdens)
    simpa [IsBehrend, multiples_primitiveKernel A] using hprim



/-- Second displayed equivalence in **Corollary 2** (`cor:main-sieve-answer`) and
**Corollary 9** (`cor:sieve-criterion`). -/
theorem behrend_iff_nonempty_powerset_sum_tendsto_one (A : Set ℕ) :
    IsBehrend A ↔
      Tendsto
        (fun N : ℕ =>
          ∑ G ∈ (primitiveTrunc A N).powerset with G.Nonempty,
            (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ))
        Filter.atTop (nhds 1) := by
  constructor
  · intro hA
    have hsub : Tendsto (fun N : ℕ => 1 - R A N) Filter.atTop (nhds 1) := by
      have hR : Tendsto (R A) Filter.atTop (nhds 0) :=
        (behrend_iff_R_tendsto_zero A).1 hA
      simpa using (tendsto_const_nhds.sub hR)
    convert hsub using 1
    ext N
    exact (one_sub_R_eq_nonempty_powerset_sum A N).symm
  · intro hsum
    have hsub : Tendsto (fun N : ℕ => 1 - R A N) Filter.atTop (nhds 1) := by
      convert hsum using 1
      ext N
      exact one_sub_R_eq_nonempty_powerset_sum A N
    have hR : Tendsto (R A) Filter.atTop (nhds 0) := by
      have hzero' :
          Tendsto (fun N : ℕ => 1 - (1 - R A N)) Filter.atTop (nhds (1 - 1)) :=
        tendsto_const_nhds.sub hsub
      convert hzero' using 1
      · ext N
        ring
      · ring
    exact (behrend_iff_R_tendsto_zero A).2 hR


end Erdos691


/-! Source module Pruning -/

/-!
Quantitative lemmas for the adaptive-tree argument in Erdős 691.
These lemmas establish finite pruning from a small conditional defect.
-/

open scoped BigOperators Topology
open Filter Set

namespace Erdos691.Adaptive

section WeightedPruning

variable {α : Type*}

noncomputable def mass (w : α → ℝ) (s : Set α) : ℝ :=
  ∑' x, s.indicator w x

lemma summable_mass {w : α → ℝ} (hw : Summable w) (s : Set α) :
    Summable (s.indicator w) := hw.indicator s

lemma mass_nonneg {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (s : Set α) :
    0 ≤ mass w s :=
  tsum_nonneg fun x => Set.indicator_nonneg (fun _ _ => hw _) _

lemma mass_mono {w : α → ℝ} (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    {s t : Set α} (hst : s ⊆ t) : mass w s ≤ mass w t := by
  apply Summable.tsum_le_tsum _ (hw.indicator s) (hw.indicator t)
  intro x
  exact Set.indicator_le_indicator_of_subset hst hw0 x

lemma finite_mass_approximation {w : α → ℝ} (hw : Summable w)
    (s : Set α) {b : ℝ} (hb : b < mass w s) :
    ∃ t : Finset α, (↑t : Set α) ⊆ s ∧ b < ∑ x ∈ t, w x := by
  classical
  have he := ((tendsto_order.1 (hw.indicator s).hasSum).1 b hb).exists
  obtain ⟨t, ht⟩ := he
  refine ⟨t.filter (· ∈ s), ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.1 hx).2
  · simpa only [Finset.sum_filter, Set.indicator_apply] using ht

/-- A weighted Markov estimate on the safe but low-score states. -/
lemma low_score_mass_bound {w score : α → ℝ} {safe : Set α} {δ : ℝ}
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1) (hδ : 0 < δ)
    (hdefect : mass (fun x => w x * (1 - score x)) safe < δ * δ) :
    mass w {x | x ∈ safe ∧ score x < 1 - δ} < δ := by
  classical
  let bad : Set α := {x | x ∈ safe ∧ score x < 1 - δ}
  have hs_defect : Summable (fun x => w x * (1 - score x)) := by
    apply Summable.of_nonneg_of_le (fun x => mul_nonneg (hw0 x) (by linarith [(hscore x).2]))
      (fun x => ?_) hw
    nlinarith [hw0 x, (hscore x).1]
  have hcompare : δ * mass w bad ≤ mass (fun x => w x * (1 - score x)) safe := by
    rw [mass, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ ((hw.indicator bad).mul_left δ) (hs_defect.indicator safe)
    intro x
    by_cases hb : x ∈ bad
    · have hsafe : x ∈ safe := hb.1
      simp only [Set.indicator_of_mem hb, Set.indicator_of_mem hsafe]
      nlinarith [hw0 x, hb.2]
    · simp only [Set.indicator_of_notMem hb, mul_zero]
      exact Set.indicator_nonneg (fun x _ => mul_nonneg (hw0 x) (by linarith [(hscore x).2])) x
  have := lt_of_le_of_lt hcompare hdefect
  nlinarith

/-- High-score states retain the safe mass except for the Markov loss. -/
lemma high_score_mass_bound {w score : α → ℝ} {safe : Set α} {δ : ℝ}
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1) (hδ : 0 < δ)
    (hdefect : mass (fun x => w x * (1 - score x)) safe < δ * δ) :
    mass w safe - δ < mass w {x | x ∈ safe ∧ 1 - δ ≤ score x} := by
  classical
  let good : Set α := {x | x ∈ safe ∧ 1 - δ ≤ score x}
  let bad : Set α := {x | x ∈ safe ∧ score x < 1 - δ}
  have hsplit : mass w safe = mass w good + mass w bad := by
    rw [mass, mass, mass, ← (hw.indicator good).tsum_add (hw.indicator bad)]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ safe
    · by_cases h : 1 - δ ≤ score x
      · have hg : x ∈ good := ⟨hx, h⟩
        have hb : x ∉ bad := fun hb => (not_lt_of_ge h) hb.2
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hg, Set.indicator_of_notMem hb]
        simp
      · have hg : x ∉ good := fun hg => h hg.2
        have hb : x ∈ bad := ⟨hx, lt_of_not_ge h⟩
        rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hg, Set.indicator_of_mem hb]
        simp
    · have hg : x ∉ good := fun hg => hx hg.1
      have hb : x ∉ bad := fun hb => hx hb.1
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hg, Set.indicator_of_notMem hb]
      simp
  have hbad := low_score_mass_bound hw hw0 hscore hδ hdefect
  change mass w bad < δ at hbad
  linarith

/-- A finite subset of high-score states retains almost all safe mass. -/
theorem finite_pruning {w score : α → ℝ} {safe : Set α} {δ : ℝ}
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1) (hδ : 0 < δ)
    (hdefect : mass (fun x => w x * (1 - score x)) safe < δ * δ) :
    ∃ t : Finset α,
      (∀ x ∈ t, x ∈ safe ∧ 1 - δ ≤ score x) ∧
      mass w safe - 2 * δ < ∑ x ∈ t, w x := by
  have hmass := high_score_mass_bound hw hw0 hscore hδ hdefect
  have hlt : mass w safe - 2 * δ < mass w {x | x ∈ safe ∧ 1 - δ ≤ score x} := by
    linarith
  obtain ⟨t, ht, hsum⟩ := finite_mass_approximation hw _ hlt
  exact ⟨t, fun x hx => ht hx, hsum⟩

end WeightedPruning

section DownwardClosure

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrderBot α]

/-- Closing a finite set downwards preserves membership in a lower set. -/
theorem finite_lower_closure (s : Set α) (hs : IsLowerSet s) (t : Finset α)
    (ht : (↑t : Set α) ⊆ s) :
    ∃ u : Finset α, (↑t : Set α) ⊆ u ∧ (↑u : Set α) ⊆ s ∧ IsLowerSet (↑u : Set α) := by
  classical
  let u := t.biUnion (fun x => Finset.Iic x)
  have hmem : ∀ x, x ∈ u ↔ ∃ y ∈ t, x ≤ y := by simp [u]
  refine ⟨u, ?_, ?_, ?_⟩
  · intro x hx
    exact (hmem x).2 ⟨x, hx, le_rfl⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := (hmem x).1 hx
    exact hs hxy (ht hy)
  · intro y x hxy hy
    obtain ⟨z, hz, hyz⟩ := (hmem y).1 hy
    exact (hmem x).2 ⟨z, hz, hxy.trans hyz⟩

/-- Finite pruning can be performed with a divisor-closed or coordinate-lower set. -/
theorem finite_lower_pruning {w score : α → ℝ} {safe : Set α} {δ : ℝ}
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1) (hδ : 0 < δ)
    (hdefect : mass (fun x => w x * (1 - score x)) safe < δ * δ)
    (hsafe : IsLowerSet safe) (hanti : Antitone score) :
    ∃ t : Finset α,
      IsLowerSet (↑t : Set α) ∧
      (∀ x ∈ t, x ∈ safe ∧ 1 - δ ≤ score x) ∧
      mass w safe - 2 * δ < ∑ x ∈ t, w x := by
  classical
  obtain ⟨t, ht, hsum⟩ := finite_pruning hw hw0 hscore hδ hdefect
  let good : Set α := {x | x ∈ safe ∧ 1 - δ ≤ score x}
  have hgood : IsLowerSet good := by
    intro y x hxy hy
    exact ⟨hsafe hxy hy.1, hy.2.trans (hanti hxy)⟩
  obtain ⟨u, htu, hug, hlu⟩ := finite_lower_closure good hgood t (fun x hx => ht x hx)
  refine ⟨u, hlu, fun x hx => hug hx, hsum.trans_le ?_⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg htu (fun x _ _ => hw0 x)

end DownwardClosure

end Erdos691.Adaptive


/-! Source module Specification -/

/-!
The proposed arithmetic criterion, with all quantifiers and admissibility
conditions stated explicitly. The proposition `FullSolution` is proved
in the final necessity module.

The first prime has index zero. Thus the paper's indices (ell, ell'] become
the half-open interval [cutoff, cutoff') used below.
-/

open scoped BigOperators Topology
open Filter Set

namespace Erdos691.Adaptive

noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime i

theorem prime_is_prime (i : ℕ) : Nat.Prime (prime i) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i

theorem prime_pos (i : ℕ) : 0 < prime i := (prime_is_prime i).pos

/-- The part of an integer supported on the first `l` primes. -/
noncomputable def primePrefix (l n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range l, prime i ^ n.factorization (prime i)

theorem primePrefix_one (l : ℕ) : primePrefix l 1 = 1 := by
  simp [primePrefix]

theorem primePrefix_pos (l n : ℕ) : 0 < primePrefix l n := by
  apply Finset.prod_pos
  intro i _
  exact pow_pos (prime_pos i) _

/-- Positive integers all of whose prime divisors lie in the specified block. -/
def SupportedOn (lo hi n : ℕ) : Prop :=
  0 < n ∧ ∀ p ∈ n.primeFactors, ∃ i, lo ≤ i ∧ i < hi ∧ prime i = p

theorem supportedOn_one (lo hi : ℕ) : SupportedOn lo hi 1 := by
  simp [SupportedOn]

/-- Probability that all valuations in a finite prime block vanish. -/
noncomputable def blockNormalization (lo hi : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico lo hi, (1 - (1 : ℝ) / prime i)

theorem blockNormalization_pos (lo hi : ℕ) : 0 < blockNormalization lo hi := by
  apply Finset.prod_pos
  intro i _
  have hp : (1 : ℝ) < prime i := by exact_mod_cast (prime_is_prime i).one_lt
  have hpp : (0 : ℝ) < prime i := lt_trans zero_lt_one hp
  have : (1 : ℝ) / prime i < 1 := (div_lt_one hpp).2 hp
  linarith

/-- The paper's loss at transition `k` to `k+1`. -/
noncomputable def loss (k : ℕ) : ℝ := (1 : ℝ) / 2 ^ (k + 3)

/-- New-prime factors extending a fixed old parent. -/
noncomputable def fiber (next : Finset ℕ) (oldCutoff parent : ℕ) : Finset ℕ := by
  classical
  exact (next.filter (fun m => primePrefix oldCutoff m = parent)).image (fun m => m / parent)

/-- A universal finite test family, chosen independently of `A`. -/
structure AdmissibleTest where
  cutoff : ℕ → ℕ
  increasing : StrictMono cutoff
  level : ℕ → Finset ℕ
  start : level 0 = {1}
  supported : ∀ k, ∀ m ∈ level k, SupportedOn (cutoff 0) (cutoff k) m
  downward : ∀ k, ∀ m ∈ level k, ∀ d, 0 < d → d ∣ m → d ∈ level k
  projects : ∀ k, ∀ m ∈ level (k + 1), primePrefix (cutoff k) m ∈ level k
  retention : ∀ k, ∀ m ∈ level k,
    1 - loss k ≤ blockNormalization (cutoff k) (cutoff (k + 1)) *
      ∑ n ∈ fiber (level (k + 1)) (cutoff k) m, (1 : ℝ) / n

def MeetsEveryTest (A : Set ℕ) : Prop :=
  ∀ T : AdmissibleTest, ∃ k, ∃ m ∈ T.level k, m ∈ A

/-- Natural density uses positive integers and ignores zero. -/
noncomputable def densitySequence (B : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact (((Finset.Icc 1 (N + 1)).filter (· ∈ B)).card : ℝ) / (N + 1)

def multiples (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ a ∈ A, 0 < a ∧ a ∣ n}

def HasMultiplesDensityOne (A : Set ℕ) : Prop :=
  Tendsto (densitySequence (multiples A)) atTop (𝓝 1)

/-- Exact universal arithmetic statement. -/
def FullSolution : Prop :=
  ∀ A : Set ℕ, HasMultiplesDensityOne A ↔ MeetsEveryTest A

theorem meetsEveryTest_of_one_mem {A : Set ℕ} (h : 1 ∈ A) : MeetsEveryTest A := by
  intro T
  exact ⟨0, 1, T.start ▸ Finset.mem_singleton_self 1, h⟩

theorem meetsEveryTest_mono {A B : Set ℕ} (hAB : A ⊆ B)
    (hA : MeetsEveryTest A) : MeetsEveryTest B := by
  intro T
  obtain ⟨k, m, hm, hA⟩ := hA T
  exact ⟨k, m, hm, hAB hA⟩

theorem test_entries_positive (T : AdmissibleTest) (k : ℕ) {m : ℕ}
    (hm : m ∈ T.level k) : 0 < m := (T.supported k m hm).1

theorem test_levels_nonempty (T : AdmissibleTest) (k : ℕ) : (T.level k).Nonempty := by
  induction k with
  | zero => simp [T.start]
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    have hr := T.retention k m hm
    have hl : 0 < 1 - loss k := by
      have hp : (1 : ℝ) < 2 ^ (k + 3) := one_lt_pow₀ (by norm_num) (by omega)
      have hpp : (0 : ℝ) < 2 ^ (k + 3) := by positivity
      have : (1 : ℝ) / 2 ^ (k + 3) < 1 := (div_lt_one hpp).2 hp
      unfold loss
      linarith
    by_contra h
    have he : T.level (k + 1) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [fiber, he] at hr
    linarith

end Erdos691.Adaptive


/-! Source module Survival -/

open scoped BigOperators Topology
open Filter

namespace Erdos691.Adaptive

theorem loss_eq_geometric (k : ℕ) : loss k = (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ k := by
  simp only [loss, pow_add, div_pow]
  norm_num

theorem loss_nonneg (k : ℕ) : 0 ≤ loss k := by
  rw [loss_eq_geometric]
  positivity

theorem loss_lt_one (k : ℕ) : loss k < 1 := by
  rw [loss_eq_geometric]
  have h : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem sum_loss (n : ℕ) :
    ∑ k ∈ Finset.range n, loss k = (1 / 4 : ℝ) * (1 - (1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, loss_eq_geometric, pow_succ]
    ring

theorem sum_loss_le_quarter (n : ℕ) : ∑ k ∈ Finset.range n, loss k ≤ (1 / 4 : ℝ) := by
  rw [sum_loss]
  have h : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

theorem product_retention_bound (n : ℕ) :
    1 - ∑ k ∈ Finset.range n, loss k ≤ ∏ k ∈ Finset.range n, (1 - loss k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hl : 0 ≤ 1 - loss n := le_of_lt (sub_pos.2 (loss_lt_one n))
    have hs : 0 ≤ ∑ k ∈ Finset.range n, loss k :=
      Finset.sum_nonneg fun k _ => loss_nonneg k
    have hmul := mul_le_mul_of_nonneg_right ih hl
    have hcross := mul_nonneg hs (loss_nonneg n)
    nlinarith

/-- Every finite number of pruning steps retains at least three quarters. -/
theorem product_retention_ge_three_quarters (n : ℕ) :
    (3 / 4 : ℝ) ≤ ∏ k ∈ Finset.range n, (1 - loss k) := by
  have hsum := sum_loss_le_quarter n
  have hprod := product_retention_bound n
  linarith

/-- A flow satisfying the per-parent retention estimate stays uniformly positive. -/
theorem positive_flow_lower_bound {M : ℕ → ℝ} {initial : ℝ}
    (hinit : 0 ≤ initial) (hzero : initial ≤ M 0)
    (hstep : ∀ k, (1 - loss k) * M k ≤ M (k + 1)) (n : ℕ) :
    initial * (3 / 4 : ℝ) ≤ M n := by
  have hprod : ∀ n, initial * (∏ k ∈ Finset.range n, (1 - loss k)) ≤ M n := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      have hl : 0 ≤ 1 - loss n := le_of_lt (sub_pos.2 (loss_lt_one n))
      have hb := mul_le_mul_of_nonneg_left ih hl
      have hc := hb.trans (hstep n)
      simpa [Finset.prod_range_succ, mul_assoc, mul_comm, mul_left_comm] using hc
  exact (mul_le_mul_of_nonneg_left (product_retention_ge_three_quarters n) hinit).trans (hprod n)

/-- The stronger error schedule used to construct an avoiding family. -/
noncomputable def constructionError (k : ℕ) : ℝ := (1 : ℝ) / 2 ^ (k + 5)

theorem constructionError_pos (k : ℕ) : 0 < constructionError k := by
  unfold constructionError
  positivity

theorem constructionError_budget (k : ℕ) :
    constructionError k + 2 * constructionError (k + 1) ≤ loss k := by
  simp only [constructionError, loss, pow_add]
  norm_num
  have h : (0 : ℝ) < 2 ^ k := by positivity
  field_simp
  norm_num

end Erdos691.Adaptive


/-! Source module ProductSpace -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos691.Adaptive

/-- Split an infinite product into the products on two disjoint index types. -/
theorem infinitePi_sum_split {ι κ : Type*} {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i))) (Measure.infinitePi μ) where
  measurable := (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  map_eq := by
    classical
    apply Measure.eq_infinitePi
    intro s t ht
    have hpre :
        (MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' Set.pi (↑s) t =
          (Set.pi (↑s.toLeft) (fun i => t (.inl i))) ×ˢ
            (Set.pi (↑s.toRight) (fun i => t (.inr i))) := by
      ext x
      simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_prod,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm]
      constructor
      · intro h
        constructor
        · intro i hi
          exact h (.inl i) (Finset.mem_toLeft.1 hi)
        · intro i hi
          exact h (.inr i) (Finset.mem_toRight.1 hi)
      · rintro ⟨hl, hr⟩ (i | i) hi
        · exact hl i (Finset.mem_toLeft.2 hi)
        · exact hr i (Finset.mem_toRight.2 hi)
    rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)), hpre,
      Measure.prod_prod,
      Measure.infinitePi_pi _ (fun i _ => ht (.inl i)),
      Measure.infinitePi_pi _ (fun i _ => ht (.inr i)),
      Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

abbrev ValuationSpace := ℕ → ℕ

def valuationPrefix (n : ℕ) (x : ValuationSpace) : Fin n → ℕ := fun i => x i

def reset (n : ℕ) (u : Fin n → ℕ) (x : ValuationSpace) : ValuationSpace :=
  fun i => if h : i < n then u ⟨i, h⟩ else x i

def zeroExtension (n : ℕ) (u : Fin n → ℕ) : ValuationSpace := reset n u 0

theorem measurable_reset (n : ℕ) (u : Fin n → ℕ) : Measurable (reset n u) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i < n
  · simpa [reset, h] using (measurable_const : Measurable (fun _ : ValuationSpace => u ⟨i, h⟩))
  · simpa [reset, h] using (measurable_pi_apply i : Measurable (fun x : ValuationSpace => x i))

theorem reset_mono {n : ℕ} {u v : Fin n → ℕ} (h : u ≤ v) (x : ValuationSpace) :
    reset n u x ≤ reset n v x := by
  intro i
  by_cases hi : i < n
  · simpa only [reset, dif_pos hi] using h ⟨i, hi⟩
  · simp [reset, hi]

theorem zeroExtension_le_reset (n : ℕ) (u : Fin n → ℕ) (x : ValuationSpace) :
    zeroExtension n u ≤ reset n u x := by
  intro i
  by_cases hi : i < n <;> simp [zeroExtension, reset, hi]

theorem zeroExtension_prefix_le (n : ℕ) (x : ValuationSpace) :
    zeroExtension n (valuationPrefix n x) ≤ x := by
  intro i
  by_cases hi : i < n <;> simp [zeroExtension, reset, valuationPrefix, hi]

/-- Conditional survival probability obtained by fixing a finite prefix. -/
noncomputable def continuation (μ : Measure ValuationSpace) (C : Set ValuationSpace)
    (n : ℕ) (u : Fin n → ℕ) : ℝ := μ.real ((reset n u) ⁻¹' C)

theorem continuation_nonneg (μ : Measure ValuationSpace) (C : Set ValuationSpace)
    (n : ℕ) (u : Fin n → ℕ) : 0 ≤ continuation μ C n u := ENNReal.toReal_nonneg

theorem continuation_le_one (μ : Measure ValuationSpace) [IsProbabilityMeasure μ]
    (C : Set ValuationSpace) (n : ℕ) (u : Fin n → ℕ) : continuation μ C n u ≤ 1 := by
  exact measureReal_le_one

theorem continuation_antitone (μ : Measure ValuationSpace) [IsProbabilityMeasure μ]
    (C : Set ValuationSpace) (hC : IsLowerSet C) (n : ℕ) :
    Antitone (continuation μ C n) := by
  intro u v huv
  apply measureReal_mono
  · intro x hx
    exact hC (reset_mono huv x) hx
  · exact measure_ne_top _ _

theorem continuation_zero_of_unsafe (μ : Measure ValuationSpace)
    (C : Set ValuationSpace) (hC : IsLowerSet C) (n : ℕ) (u : Fin n → ℕ)
    (hu : zeroExtension n u ∉ C) : continuation μ C n u = 0 := by
  have hempty : (reset n u) ⁻¹' C = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hu (hC (zeroExtension_le_reset n u x) hx)
  simp [continuation, hempty]

def prefixSafe (C : Set ValuationSpace) (n : ℕ) : Set ValuationSpace :=
  {x | zeroExtension n (valuationPrefix n x) ∈ C}

theorem subset_prefixSafe (C : Set ValuationSpace) (hC : IsLowerSet C) (n : ℕ) :
    C ⊆ prefixSafe C n := by
  intro x hx
  exact hC (zeroExtension_prefix_le n x) hx

theorem prefixSafe_antitone (C : Set ValuationSpace) (hC : IsLowerSet C) :
    Antitone (prefixSafe C) := by
  intro n m hnm x hx
  apply hC _ hx
  intro i
  by_cases hi : i < n
  · have hm : i < m := hi.trans_le hnm
    simp [zeroExtension, reset, valuationPrefix, hi, hm]
  · simp [zeroExtension, reset, valuationPrefix, hi]

end Erdos691.Adaptive


/-! Source module Conditioning -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos691.Adaptive

noncomputable def joinEquiv (n : ℕ) : ((Fin n → ℕ) × ValuationSpace) ≃ᵐ ValuationSpace :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ ℕ => ℕ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℕ) (finSumNatEquiv n))

theorem joinEquiv_apply (n : ℕ) (u : Fin n → ℕ) (x : ValuationSpace) (i : ℕ) :
    joinEquiv n (u, x) i = if h : i < n then u ⟨i, h⟩ else x (i - n) := by
  by_cases h : i < n
  · simp [joinEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, h,
      finSumNatEquiv_symm_apply_of_lt h]
    rfl
  · simp [joinEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, h,
      finSumNatEquiv_symm_apply_of_ge (Nat.le_of_not_gt h)]
    rfl

theorem valuationPrefix_join (n : ℕ) (u : Fin n → ℕ) (x : ValuationSpace) :
    valuationPrefix n (joinEquiv n (u, x)) = u := by
  funext i
  simp [valuationPrefix, joinEquiv_apply, i.isLt]

def prefixAtom (n : ℕ) (u : Fin n → ℕ) : Set ValuationSpace :=
  {x | valuationPrefix n x = u}

theorem measurable_prefixAtom (n : ℕ) (u : Fin n → ℕ) :
    MeasurableSet (prefixAtom n u) := by
  have hm : Measurable (valuationPrefix n) := by
    unfold valuationPrefix
    fun_prop
  exact hm (measurableSet_singleton u)

noncomputable def fullLaw (μ : ℕ → Measure ℕ) : Measure ValuationSpace := Measure.infinitePi μ
noncomputable def headLaw (μ : ℕ → Measure ℕ) (n : ℕ) : Measure (Fin n → ℕ) :=
  Measure.infinitePi (fun i : Fin n => μ i)
noncomputable def tailLaw (μ : ℕ → Measure ℕ) (n : ℕ) : Measure ValuationSpace :=
  Measure.infinitePi (fun i => μ (n + i))

instance fullLaw_probability (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (fullLaw μ) := by unfold fullLaw; infer_instance

instance headLaw_probability (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) :
    IsProbabilityMeasure (headLaw μ n) := by unfold headLaw; infer_instance

instance tailLaw_probability (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) :
    IsProbabilityMeasure (tailLaw μ n) := by unfold tailLaw; infer_instance

theorem measurePreserving_join (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) :
    MeasurePreserving (joinEquiv n) ((headLaw μ n).prod (tailLaw μ n)) (fullLaw μ) := by
  let e := finSumNatEquiv n
  have h1 := infinitePi_sum_split (fun i : Fin n ⊕ ℕ => μ (e i))
  have h2 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℕ) e)
      (Measure.infinitePi (fun i => μ (e i))) (Measure.infinitePi μ) :=
    ⟨(MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℕ) e).measurable,
      Measure.infinitePi_map_piCongrLeft μ e⟩
  exact h1.trans h2

noncomputable def tailContinuation (μ : ℕ → Measure ℕ) (C : Set ValuationSpace)
    (n : ℕ) (u : Fin n → ℕ) : ℝ :=
  (tailLaw μ n).real {x | joinEquiv n (u, x) ∈ C}

theorem join_section_measurable (C : Set ValuationSpace) (hC : MeasurableSet C)
    (n : ℕ) (u : Fin n → ℕ) : MeasurableSet {x | joinEquiv n (u, x) ∈ C} := by
  exact hC.preimage ((joinEquiv n).measurable.comp (measurable_const.prodMk measurable_id))

theorem tailContinuation_bounds (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (n : ℕ) (u : Fin n → ℕ) :
    0 ≤ tailContinuation μ C n u ∧ tailContinuation μ C n u ≤ 1 := by
  haveI : IsProbabilityMeasure (tailLaw μ n) := by unfold tailLaw; infer_instance
  exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

theorem tailContinuation_antitone (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : IsLowerSet C) (n : ℕ) :
    Antitone (tailContinuation μ C n) := by
  haveI : IsProbabilityMeasure (tailLaw μ n) := by unfold tailLaw; infer_instance
  intro u v huv
  apply measureReal_mono
  · intro x hx
    apply hC _ hx
    intro i
    by_cases hi : i < n
    · simpa [joinEquiv_apply, hi] using huv ⟨i, hi⟩
    · simp [joinEquiv_apply, hi]
  · exact measure_ne_top _ _

/-- The exact atomic conditioning formula for a finite prefix. -/
theorem prefix_intersection_measure (μ : ℕ → Measure ℕ)
    [∀ i, IsProbabilityMeasure (μ i)] (C : Set ValuationSpace) (hC : MeasurableSet C)
    (n : ℕ) (u : Fin n → ℕ) :
    (fullLaw μ).real (C ∩ prefixAtom n u) =
      (headLaw μ n).real {u} * tailContinuation μ C n u := by
  have hpre : (joinEquiv n) ⁻¹' (C ∩ prefixAtom n u) =
      ({u} : Set (Fin n → ℕ)) ×ˢ {x | joinEquiv n (u, x) ∈ C} := by
    ext x
    rcases x with ⟨v, x⟩
    simp only [mem_preimage, mem_inter_iff, prefixAtom, mem_setOf_eq,
      valuationPrefix_join, mem_prod, mem_singleton_iff]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩
      exact ⟨h, rfl⟩
  have he := (measurePreserving_join μ n).measure_preimage
    (hC.inter (measurable_prefixAtom n u)).nullMeasurableSet
  simp only [tailContinuation, measureReal_def]
  rw [← he, hpre, Measure.prod_prod, ENNReal.toReal_mul]

end Erdos691.Adaptive


/-! Source module ConditionalMass -/

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical

namespace Erdos691.Adaptive

theorem real_measure_partition {α β : Type*} [MeasurableSpace α] [Countable β]
    (μ : Measure α) [IsFiniteMeasure μ] (s : β → Set α)
    (hm : ∀ b, MeasurableSet (s b)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    HasSum (fun b => μ.real (s b)) (μ.real (⋃ b, s b)) := by
  have ht : ∑' b, μ (s b) ≠ ∞ := by
    rw [← measure_iUnion hd hm]
    exact measure_ne_top _ _
  have hs := ENNReal.summable_toReal ht
  convert hs.hasSum using 1
  · rfl
  · change (μ (⋃ b, s b)).toReal = ∑' b, (μ (s b)).toReal
    rw [measure_iUnion hd hm, ENNReal.tsum_toReal_eq (fun b => measure_ne_top μ (s b))]

theorem prefixAtoms_disjoint (n : ℕ) : Pairwise (fun u v => Disjoint (prefixAtom n u) (prefixAtom n v)) := by
  intro u v huv
  apply Set.disjoint_left.2
  intro x hu hv
  exact huv (hu.symm.trans hv)

theorem union_prefix_intersections (C : Set ValuationSpace) (n : ℕ) :
    (⋃ u, C ∩ prefixAtom n u) = C := by
  ext x
  simp only [mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨u, hx, _⟩
    exact hx
  · intro hx
    exact ⟨valuationPrefix n x, hx, rfl⟩

theorem conditional_total_mass (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (n : ℕ) :
    HasSum (fun u => (headLaw μ n).real {u} * tailContinuation μ C n u) ((fullLaw μ).real C) := by
  have h := real_measure_partition (fullLaw μ) (fun u => C ∩ prefixAtom n u)
    (fun u => hC.inter (measurable_prefixAtom n u))
    (fun u v huv => (prefixAtoms_disjoint n huv).mono inter_subset_right inter_subset_right)
  simpa only [union_prefix_intersections, prefix_intersection_measure μ C hC n] using h

theorem head_weights_sum_one (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) :
    HasSum (fun u : Fin n → ℕ => (headLaw μ n).real {u}) 1 := by
  have h := conditional_total_mass μ Set.univ MeasurableSet.univ n
  simpa [tailContinuation] using h

theorem tailContinuation_zero_of_unsafe (μ : ℕ → Measure ℕ)
    (C : Set ValuationSpace) (hC : IsLowerSet C) (n : ℕ) (u : Fin n → ℕ)
    (hu : zeroExtension n u ∉ C) : tailContinuation μ C n u = 0 := by
  have he : {x | joinEquiv n (u, x) ∈ C} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    apply hu
    apply hC _ hx
    intro i
    by_cases hi : i < n <;> simp [zeroExtension, reset, joinEquiv_apply, hi]
  simp [tailContinuation, he]

theorem prefixSafe_measurable (C : Set ValuationSpace) (hC : MeasurableSet C) (n : ℕ) :
    MeasurableSet (prefixSafe C n) := by
  apply hC.preimage
  apply Measurable.of_eval
  intro i
  by_cases hi : i < n
  · simpa [zeroExtension, reset, valuationPrefix, hi] using
      (measurable_pi_apply i : Measurable (fun x : ValuationSpace => x i))
  · simpa [zeroExtension, reset, hi] using
      (measurable_const : Measurable (fun _ : ValuationSpace => (0 : ℕ)))

theorem tailContinuation_prefixSafe (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (n : ℕ) (u : Fin n → ℕ) :
    tailContinuation μ (prefixSafe C n) n u = if zeroExtension n u ∈ C then 1 else 0 := by
  classical
  by_cases hu : zeroExtension n u ∈ C
  · have he : {x | joinEquiv n (u, x) ∈ prefixSafe C n} = univ := by
      ext x
      simp [prefixSafe, valuationPrefix_join, hu]
    simp [tailContinuation, he, hu]
  · have he : {x | joinEquiv n (u, x) ∈ prefixSafe C n} = ∅ := by
      ext x
      simp [prefixSafe, valuationPrefix_join, hu]
    simp [tailContinuation, he, hu]

theorem prefixSafe_mass (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (n : ℕ) :
    (fullLaw μ).real (prefixSafe C n) =
      mass (fun u => (headLaw μ n).real {u}) {u | zeroExtension n u ∈ C} := by
  classical
  have h := conditional_total_mass μ (prefixSafe C n) (prefixSafe_measurable C hC n) n
  rw [← h.tsum_eq]
  unfold mass
  apply tsum_congr
  intro u
  rw [tailContinuation_prefixSafe]
  by_cases hu : zeroExtension n u ∈ C <;> simp [hu, Set.indicator]

/-- The zero prefix maximizes survival among all prefixes of a fixed length. -/
theorem total_mass_le_zero_prefix (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (hdown : IsLowerSet C) (n : ℕ) :
    (fullLaw μ).real C ≤ tailContinuation μ C n 0 * (fullLaw μ).real (prefixSafe C n) := by
  classical
  let w : (Fin n → ℕ) → ℝ := fun u => (headLaw μ n).real {u}
  let safe : Set (Fin n → ℕ) := {u | zeroExtension n u ∈ C}
  have hw := (head_weights_sum_one μ n).summable
  have hs := conditional_total_mass μ C hC n
  rw [← hs.tsum_eq, prefixSafe_mass μ C hC n, mass, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hs.summable ((hw.indicator safe).mul_left _)
  intro u
  have hnon : 0 ≤ w u := ENNReal.toReal_nonneg
  by_cases hu : u ∈ safe
  · rw [Set.indicator_of_mem hu]
    have hh := tailContinuation_antitone μ C hdown n (show (0 : Fin n → ℕ) ≤ u from fun i => Nat.zero_le _)
    exact (mul_le_mul_of_nonneg_left hh hnon).trans_eq (mul_comm _ _)
  · rw [Set.indicator_of_notMem hu, mul_zero]
    rw [tailContinuation_zero_of_unsafe μ C hdown n u hu, mul_zero]

def DeterminedByPrefixes (C : Set ValuationSpace) : Prop :=
  ∀ x, (∀ n, zeroExtension n (valuationPrefix n x) ∈ C) → x ∈ C

theorem intersection_prefixSafe (C : Set ValuationSpace) (hdown : IsLowerSet C)
    (hclosed : DeterminedByPrefixes C) : (⋂ n, prefixSafe C n) = C := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hclosed x (mem_iInter.1 hx)
  · exact subset_iInter fun n => subset_prefixSafe C hdown n

/-- Finite safe prefixes converge in probability to the closed avoidance event. -/
theorem prefixSafe_mass_tendsto (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (hdown : IsLowerSet C)
    (hclosed : DeterminedByPrefixes C) :
    Tendsto (fun n => (fullLaw μ).real (prefixSafe C n)) atTop (𝓝 ((fullLaw μ).real C)) := by
  have ht := tendsto_measure_iInter_atTop
    (μ := fullLaw μ) (fun n => (prefixSafe_measurable C hC n).nullMeasurableSet)
    (prefixSafe_antitone C hdown) (show ∃ n, (fullLaw μ) (prefixSafe C n) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  rw [intersection_prefixSafe C hdown hclosed] at ht
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp ht

/-- Positive survival admits arbitrarily long zero prefixes with conditional survival
arbitrarily close to one. -/
theorem exists_zero_prefix_near_one (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (hdown : IsLowerSet C)
    (hclosed : DeterminedByPrefixes C) (hc : 0 < (fullLaw μ).real C)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (N : ℕ) :
    ∃ n ≥ N, 1 - δ < tailContinuation μ C n 0 := by
  let c := (fullLaw μ).real C
  have hd : 0 < 1 - δ := sub_pos.2 hδ1
  have hcd : c < c / (1 - δ) := by
    apply (lt_div_iff₀ hd).2
    change 0 < c at hc
    nlinarith
  have ht := prefixSafe_mass_tendsto μ C hC hdown hclosed
  have he := (tendsto_order.1 ht).2 _ hcd
  obtain ⟨n, hn, hp⟩ := ((eventually_ge_atTop N).and he).exists
  refine ⟨n, hn, ?_⟩
  by_contra h
  have hh : tailContinuation μ C n 0 ≤ 1 - δ := le_of_not_gt h
  have hbound := total_mass_le_zero_prefix μ C hC hdown n
  have hp0 : 0 ≤ (fullLaw μ).real (prefixSafe C n) := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_right hh hp0
  have hlt : (1 - δ) * (fullLaw μ).real (prefixSafe C n) < c := by
    have := (lt_div_iff₀ hd).1 hp
    nlinarith
  linarith

end Erdos691.Adaptive


/-! Source module Avoidance -/

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical

namespace Erdos691.Adaptive

theorem prime_index_le (i : ℕ) : i ≤ prime i := by
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le i

theorem factorization_eventually_zero (a i : ℕ) (hi : a < i) :
    a.factorization (prime i) = 0 :=
  Nat.factorization_eq_zero_of_lt (hi.trans_le (prime_index_le i))

/-- A positive integer divides an infinite valuation vector. -/
def DividesValuation (a : ℕ) (x : ValuationSpace) : Prop :=
  ∀ i, a.factorization (prime i) ≤ x i

/-- The event that no positive member of `A` divides the valuation vector. -/
def avoidance (A : Set ℕ) : Set ValuationSpace :=
  {x | ∀ a ∈ A, 0 < a → ¬DividesValuation a x}

theorem avoidance_lower (A : Set ℕ) : IsLowerSet (avoidance A) := by
  intro x y hyx hx a ha hapos hdiv
  apply hx a ha hapos
  intro i
  exact (hdiv i).trans (hyx i)

theorem avoidance_measurable (A : Set ℕ) : MeasurableSet (avoidance A) := by
  have hdiv (a : ℕ) : MeasurableSet {x : ValuationSpace | DividesValuation a x} := by
    have he : {x : ValuationSpace | DividesValuation a x} =
        ⋂ i, {x | a.factorization (prime i) ≤ x i} := by
      ext x
      simp [DividesValuation]
    rw [he]
    apply MeasurableSet.iInter
    intro i
    exact (measurable_pi_apply i) (measurableSet_Ici)
  have he : avoidance A = ⋂ a : ℕ, ⋂ (_ : a ∈ A), ⋂ (_ : 0 < a),
      {x : ValuationSpace | ¬DividesValuation a x} := by
    ext x
    simp [avoidance]
  rw [he]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => (hdiv a).compl

theorem avoidance_determined (A : Set ℕ) : DeterminedByPrefixes (avoidance A) := by
  intro x hx a ha hapos hdiv
  apply hx (a + 1) a ha hapos
  intro i
  by_cases hi : i < a + 1
  · simpa [zeroExtension, reset, valuationPrefix, hi] using hdiv i
  · have hzero : a.factorization (prime i) = 0 := factorization_eventually_zero a i (by omega)
    simp [zeroExtension, reset, valuationPrefix, hi, hzero]

/-- The underlying probability measure has the geometric valuation law at every prime. -/
noncomputable def primeSuccess (i : ℕ) : unitInterval :=
  ⟨1 - (1 : ℝ) / prime i, by
    have hp : (1 : ℝ) < prime i := by exact_mod_cast (prime_is_prime i).one_lt
    constructor
    · have h : (1 : ℝ) / prime i < 1 := (div_lt_one (by linarith)).2 hp
      linarith
    · have h : (0 : ℝ) ≤ 1 / prime i := by positivity
      linarith⟩

noncomputable def primeLaw (i : ℕ) : Measure ℕ :=
  ProbabilityTheory.geometricMeasure (primeSuccess i)

instance primeLaw_probability (i : ℕ) : IsProbabilityMeasure (primeLaw i) := by
  unfold primeLaw
  infer_instance

theorem primeSuccess_ne_zero (i : ℕ) : primeSuccess i ≠ 0 := by
  intro h
  have hval := congrArg Subtype.val h
  have hp : (1 : ℝ) < prime i := by exact_mod_cast (prime_is_prime i).one_lt
  have hlt : (1 : ℝ) / prime i < 1 := (div_lt_one (by linarith)).2 hp
  change 1 - (1 : ℝ) / prime i = 0 at hval
  linarith

theorem primeLaw_singleton (i e : ℕ) :
    (primeLaw i).real {e} = (1 - (1 : ℝ) / prime i) * ((1 : ℝ) / prime i) ^ e := by
  unfold primeLaw
  rw [ProbabilityTheory.geometricMeasure_real_singleton (primeSuccess_ne_zero i)]
  change (1 - (1 - (1 : ℝ) / prime i)) ^ e * (1 - (1 : ℝ) / prime i) = _
  ring

/-- The conditional survival probability can be made arbitrarily close to one
by fixing a sufficiently long zero prefix, provided avoidance has positive measure. -/
theorem avoidance_zero_prefix (A : Set ℕ)
    (hA : 0 < (fullLaw primeLaw).real (avoidance A))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (N : ℕ) :
    ∃ n ≥ N, 1 - δ < tailContinuation primeLaw (avoidance A) n 0 :=
  exists_zero_prefix_near_one primeLaw (avoidance A) (avoidance_measurable A)
    (avoidance_lower A) (avoidance_determined A) hA hδ hδ1 N

end Erdos691.Adaptive


/-! Source module ArithmeticProbability -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology Classical

namespace Erdos691.Adaptive

theorem prime_injective : Function.Injective prime :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective

theorem primeFactors_subset_initial (a : ℕ) :
    a.primeFactors ⊆ (Finset.range (a + 1)).image prime := by
  intro p hp
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  obtain ⟨i, hi⟩ := Nat.subset_range_nth hpprime
  have hi' : prime i = p := hi
  apply Finset.mem_image.2
  refine ⟨i, Finset.mem_range.2 ?_, hi'⟩
  have hle : i ≤ p := hi' ▸ prime_index_le i
  have hp_le : p ≤ a := Nat.le_of_mem_primeFactors hp
  omega

theorem reconstruct_from_initial_primes (a : ℕ) (ha : a ≠ 0) :
    (∏ i ∈ Finset.range (a + 1), prime i ^ a.factorization (prime i)) = a := by
  have hp : (∏ p ∈ (Finset.range (a + 1)).image prime, p ^ a.factorization p) =
      ∏ p ∈ a.primeFactors, p ^ a.factorization p := by
    symm
    apply Finset.prod_subset (primeFactors_subset_initial a)
    intro p hp hpn
    have hz : a.factorization p = 0 := Finsupp.notMem_support_iff.1 hpn
    simp [hz]
  rw [Finset.prod_image] at hp
  · exact hp.trans (Nat.prod_primeFactors_pow_factorization ha).symm
  · exact fun i _ j _ h => prime_injective h

theorem geometric_prefix_sum (q : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 - q) * q ^ k) = 1 - q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem primeLaw_tail (i e : ℕ) :
    (primeLaw i).real (Set.Ici e) = ((1 : ℝ) / prime i) ^ e := by
  have hs : (primeLaw i).real (Set.Iio e) = 1 - ((1 : ℝ) / prime i) ^ e := by
    rw [← Finset.coe_range, ← sum_measureReal_singleton]
    simp_rw [primeLaw_singleton]
    exact geometric_prefix_sum _ _
  have hc := measureReal_add_measureReal_compl (μ := primeLaw i) (s := Set.Iio e) measurableSet_Iio
  rw [Set.compl_Iio, probReal_univ, hs] at hc
  linarith

theorem divisibility_event_is_cylinder (a : ℕ) :
    {x : ValuationSpace | DividesValuation a x} =
      Set.pi (↑(Finset.range (a + 1))) (fun i => Set.Ici (a.factorization (prime i))) := by
  ext x
  constructor
  · intro hx i hi
    exact hx i
  · intro hx i
    by_cases hi : i < a + 1
    · exact hx i (Finset.mem_range.2 hi)
    · rw [factorization_eventually_zero a i (by omega)]
      exact Nat.zero_le _

theorem divisibility_event_measurable (a : ℕ) :
    MeasurableSet {x : ValuationSpace | DividesValuation a x} := by
  rw [divisibility_event_is_cylinder]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_Ici)

/-- A fixed integer divides the random valuation vector with probability `1/a`. -/
theorem divisibility_probability (a : ℕ) (ha : 0 < a) :
    (fullLaw primeLaw).real {x | DividesValuation a x} = (1 : ℝ) / a := by
  rw [divisibility_event_is_cylinder, fullLaw, measureReal_def,
    Measure.infinitePi_pi primeLaw (fun i _ => measurableSet_Ici)]
  rw [ENNReal.toReal_prod]
  simp_rw [← measureReal_def, primeLaw_tail]
  have hprod : (∏ i ∈ Finset.range (a + 1), ((1 : ℝ) / prime i) ^ a.factorization (prime i)) =
      (∏ i ∈ Finset.range (a + 1), (prime i : ℝ) ^ a.factorization (prime i))⁻¹ := by
    simp only [one_div, inv_pow, Finset.prod_inv_distrib]
  rw [hprod]
  have hrec : (∏ i ∈ Finset.range (a + 1), (prime i : ℝ) ^ a.factorization (prime i)) = a := by
    exact_mod_cast reconstruct_from_initial_primes a (Nat.ne_of_gt ha)
  rw [hrec, one_div]

theorem factorization_lcm_bound (F : Finset ℕ) (hF : Erdos691.PositiveFinset F)
    (p b : ℕ) : (Erdos691.lcm0 F).factorization p ≤ b ↔ ∀ a ∈ F, a.factorization p ≤ b := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [Erdos691.lcm0]
  | @insert a F ha ih =>
    have ha0 : a ≠ 0 := Nat.ne_of_gt (hF (Finset.mem_insert_self _ _))
    have hF0 : Erdos691.PositiveFinset F := fun _ hx => hF (Finset.mem_insert_of_mem hx)
    have hL0 : Erdos691.lcm0 F ≠ 0 := Nat.ne_of_gt (Erdos691.lcm0_pos F hF0)
    have he : Erdos691.lcm0 (insert a F) = Nat.lcm a (Erdos691.lcm0 F) := by
      simp [Erdos691.lcm0]
      rfl
    rw [he, Nat.factorization_lcm ha0 hL0]
    simpa only [Finsupp.sup_apply, sup_le_iff, ih hF0, Finset.mem_insert,
      forall_eq_or_imp] 

theorem intersection_divisibility_events (F : Finset ℕ) (hF : Erdos691.PositiveFinset F) :
    (⋂ a ∈ F, {x : ValuationSpace | DividesValuation a x}) =
      {x | DividesValuation (Erdos691.lcm0 F) x} := by
  ext x
  simp only [mem_iInter, mem_setOf_eq, DividesValuation]
  constructor
  · intro h i
    exact (factorization_lcm_bound F hF (prime i) (x i)).2 (fun a ha => h a ha i)
  · intro h a ha i
    exact (factorization_lcm_bound F hF (prime i) (x i)).1 (h i) a ha

theorem finite_multiple_probability (F : Finset ℕ) (hF : Erdos691.PositiveFinset F) :
    (fullLaw primeLaw).real (⋃ a ∈ F, {x | DividesValuation a x}) =
      Erdos691.finiteMultiplesDensity F := by
  rw [measureReal_biUnion_eq_sum_powerset (fun a _ => divisibility_event_measurable a),
    Erdos691.finiteMultiplesDensity_eq_nonempty_powerset_sum]
  apply Finset.sum_congr rfl
  intro G hG
  have hsub : G ⊆ F := Finset.mem_powerset.1 (Finset.mem_filter.1 hG).1
  have hGpos : Erdos691.PositiveFinset G := fun _ ha => hF (hsub ha)
  rw [intersection_divisibility_events G hGpos,
    divisibility_probability _ (Erdos691.lcm0_pos G hGpos)]
  ring

theorem finite_avoidance_probability (F : Finset ℕ) (hF : Erdos691.PositiveFinset F) :
    (fullLaw primeLaw).real (avoidance (↑F)) = Erdos691.finiteAvoidDensity F := by
  have he : avoidance (↑F) = (⋃ a ∈ F, {x | DividesValuation a x})ᶜ := by
    ext x
    simp only [avoidance, mem_setOf_eq, Finset.mem_coe, mem_compl_iff, mem_iUnion,
      not_exists]
    constructor
    · intro h a ha
      exact h a ha (hF ha)
    · intro h a ha _
      exact h a ha
  rw [he, measureReal_compl (by
    exact MeasurableSet.biUnion (Finset.countable_toSet F) (fun a _ => divisibility_event_measurable a)),
    probReal_univ, finite_multiple_probability F hF]
  unfold Erdos691.finiteMultiplesDensity
  ring

theorem avoidance_truncation_antitone (A : Set ℕ) :
    Antitone (fun n => avoidance ((Erdos691.trunc A n : Finset ℕ) : Set ℕ)) := by
  intro n m hnm x hx a ha hapos
  apply hx a _ hapos
  change a ∈ Erdos691.trunc A n at ha
  change a ∈ Erdos691.trunc A m
  rw [Erdos691.mem_trunc] at ha ⊢
  exact ⟨⟨ha.1.1, ha.1.2.trans hnm⟩, ha.2⟩

theorem intersection_truncated_avoidance (A : Set ℕ) :
    (⋂ n, avoidance ((Erdos691.trunc A n : Finset ℕ) : Set ℕ)) = avoidance A := by
  ext x
  simp only [mem_iInter, avoidance, mem_setOf_eq, Finset.mem_coe]
  constructor
  · intro h a ha hapos
    exact h a a ((Erdos691.mem_trunc).2 ⟨⟨hapos, le_rfl⟩, ha⟩) hapos
  · intro h n a ha hapos
    exact h a (Erdos691.trunc_subset A n ha) hapos

theorem truncated_avoidance_tendsto (A : Set ℕ) :
    Tendsto (fun n => (fullLaw primeLaw).real (avoidance ((Erdos691.trunc A n : Finset ℕ) : Set ℕ)))
      atTop (𝓝 ((fullLaw primeLaw).real (avoidance A))) := by
  have ht := tendsto_measure_iInter_atTop
    (μ := fullLaw primeLaw) (fun n => (avoidance_measurable (↑(Erdos691.trunc A n))).nullMeasurableSet)
    (avoidance_truncation_antitone A)
    (show ∃ n, (fullLaw primeLaw) (avoidance (↑(Erdos691.trunc A n))) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  rw [intersection_truncated_avoidance] at ht
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp ht

/-- The classical density-one condition is exactly zero probability of avoidance. -/
theorem density_one_iff_avoidance_zero (A : Set ℕ) :
    HasMultiplesDensityOne A ↔ (fullLaw primeLaw).real (avoidance A) = 0 := by
  have hclassical : HasMultiplesDensityOne A ↔ Erdos691.IsBehrend A := by rfl
  rw [hclassical, Erdos691.behrend_iff_truncFiniteDensities_tendsto_one]
  have he (n : ℕ) : Erdos691.finiteMultiplesDensity (Erdos691.trunc A n) =
      1 - (fullLaw primeLaw).real (avoidance (↑(Erdos691.trunc A n))) := by
    rw [finite_avoidance_probability _ (Erdos691.trunc_positive A n)]
    rfl
  simp_rw [he]
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have ht := hc.sub (truncated_avoidance_tendsto A)
  constructor
  · intro h
    have hu := tendsto_nhds_unique h ht
    linarith
  · intro h
    simpa [h] using ht

end Erdos691.Adaptive


/-! Source module GoodPrefixes -/

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical

namespace Erdos691.Adaptive

/-- The conditional defect on finite safe prefixes is exactly their excess mass. -/
theorem safe_prefix_defect (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (hdown : IsLowerSet C) (n : ℕ) :
    mass (fun u => (headLaw μ n).real {u} * (1 - tailContinuation μ C n u))
      {u | zeroExtension n u ∈ C} =
      (fullLaw μ).real (prefixSafe C n) - (fullLaw μ).real C := by
  let w : (Fin n → ℕ) → ℝ := fun u => (headLaw μ n).real {u}
  let h : (Fin n → ℕ) → ℝ := tailContinuation μ C n
  let s : Set (Fin n → ℕ) := {u | zeroExtension n u ∈ C}
  have hw : Summable w := (head_weights_sum_one μ n).summable
  have hh : Summable (fun u => w u * h u) := (conditional_total_mass μ C hC n).summable
  have he : s.indicator (fun u => w u * (1 - h u)) =
      fun u => s.indicator w u - w u * h u := by
    funext u
    by_cases hu : u ∈ s
    · simp only [Set.indicator_of_mem hu]
      ring
    · have hz : h u = 0 := tailContinuation_zero_of_unsafe μ C hdown n u hu
      simp [Set.indicator_of_notMem hu, hz]
  change ∑' u, s.indicator (fun u => w u * (1 - h u)) u = _
  rw [he, (hw.indicator s).tsum_sub hh]
  have hm : (∑' u, s.indicator w u) = (fullLaw μ).real (prefixSafe C n) :=
    (prefixSafe_mass μ C hC n).symm
  have ht : (∑' u, w u * h u) = (fullLaw μ).real C :=
    (conditional_total_mass μ C hC n).tsum_eq
  rw [hm, ht]

theorem good_prefixes_eventually (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (hdown : IsLowerSet C)
    (hclosed : DeterminedByPrefixes C) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ S : Finset (Fin n → ℕ),
      IsLowerSet (↑S : Set (Fin n → ℕ)) ∧
      (∀ u ∈ S, zeroExtension n u ∈ C ∧ 1 - δ ≤ tailContinuation μ C n u) ∧
      (fullLaw μ).real C - 2 * δ < ∑ u ∈ S, (headLaw μ n).real {u} := by
  have hc := prefixSafe_mass_tendsto μ C hC hdown hclosed
  have hc' : Tendsto (fun n => (fullLaw μ).real (prefixSafe C n) - (fullLaw μ).real C)
      atTop (𝓝 0) := by
    simpa using hc.sub_const ((fullLaw μ).real C)
  have hd : 0 < δ * δ := mul_pos hδ hδ
  filter_upwards [(tendsto_order.1 hc').2 _ hd] with n hn
  have hsmall : mass (fun u => (headLaw μ n).real {u} * (1 - tailContinuation μ C n u))
      {u | zeroExtension n u ∈ C} < δ * δ := by
    rw [safe_prefix_defect μ C hC hdown n]
    exact hn
  have hsafe : IsLowerSet {u : Fin n → ℕ | zeroExtension n u ∈ C} := by
    intro v u huv hv
    apply hdown _ hv
    exact reset_mono huv 0
  obtain ⟨S, hlower, hgood, hmass⟩ := finite_lower_pruning
    (head_weights_sum_one μ n).summable (fun _ => ENNReal.toReal_nonneg)
    (tailContinuation_bounds μ C n) hδ hsmall hsafe (tailContinuation_antitone μ C hdown n)
  refine ⟨S, hlower, hgood, lt_of_le_of_lt ?_ hmass⟩
  rw [← prefixSafe_mass μ C hC n]
  apply sub_le_sub_right
  exact measureReal_mono (subset_prefixSafe C hdown n)

end Erdos691.Adaptive


/-! Source module PrefixExtensions -/

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical

namespace Erdos691.Adaptive

def appendPrefix {n m : ℕ} (u : Fin n → ℕ) (v : Fin m → ℕ) : Fin (n + m) → ℕ :=
  fun i => if h : i.val < n then u ⟨i.val, h⟩ else v ⟨i.val - n, by omega⟩

def restrictPrefix {n m : ℕ} (hnm : n ≤ m) (v : Fin m → ℕ) : Fin n → ℕ :=
  fun i => v ⟨i, i.isLt.trans_le hnm⟩

theorem restrict_append {n m : ℕ} (u : Fin n → ℕ) (v : Fin m → ℕ) :
    restrictPrefix (Nat.le_add_right n m) (appendPrefix u v) = u := by
  funext i
  simp [restrictPrefix, appendPrefix, i.isLt]

theorem append_injective_right {n m : ℕ} (u : Fin n → ℕ) :
    Function.Injective (appendPrefix (m := m) u) := by
  intro v w hvw
  funext i
  have h := congrFun hvw ⟨n + i, by omega⟩
  simpa [appendPrefix] using h

theorem join_append {n m : ℕ} (u : Fin n → ℕ) (v : Fin m → ℕ) (x : ValuationSpace) :
    joinEquiv (n + m) (appendPrefix u v, x) = joinEquiv n (u, joinEquiv m (v, x)) := by
  funext i
  by_cases hi : i < n
  · have him : i < n + m := by omega
    simp [joinEquiv_apply, appendPrefix, hi, him]
  · by_cases him : i < n + m
    · have hdiff : i - n < m := by omega
      simp [joinEquiv_apply, appendPrefix, hi, him, hdiff]
    · have hdiff : ¬ i - n < m := by omega
      simp [joinEquiv_apply, hi, him, hdiff, Nat.sub_sub]

theorem zeroExtension_eq_join (n : ℕ) (u : Fin n → ℕ) :
    zeroExtension n u = joinEquiv n (u, 0) := by
  funext i
  simp [zeroExtension, reset, joinEquiv_apply]

theorem join_prefix_zero (n m : ℕ) (u : Fin n → ℕ) (x : ValuationSpace) :
    zeroExtension (n + m) (valuationPrefix (n + m) (joinEquiv n (u, x))) =
      joinEquiv n (u, zeroExtension m (valuationPrefix m x)) := by
  funext i
  by_cases hi : i < n
  · have him : i < n + m := by omega
    simp [zeroExtension, reset, valuationPrefix, joinEquiv_apply, hi, him]
  · by_cases him : i < n + m
    · have hdiff : i - n < m := by omega
      simp [zeroExtension, reset, valuationPrefix, joinEquiv_apply, hi, him, hdiff]
    · have hdiff : ¬ i - n < m := by omega
      simp [zeroExtension, reset, valuationPrefix, joinEquiv_apply, hi, him, hdiff]

def prefixSection (C : Set ValuationSpace) {n : ℕ} (u : Fin n → ℕ) : Set ValuationSpace :=
  {x | joinEquiv n (u, x) ∈ C}

theorem prefixSection_lower (C : Set ValuationSpace) (hC : IsLowerSet C)
    {n : ℕ} (u : Fin n → ℕ) : IsLowerSet (prefixSection C u) := by
  intro x y hyx hx
  apply hC _ hx
  intro i
  by_cases hi : i < n
  · simp [joinEquiv_apply, hi]
  · simpa [joinEquiv_apply, hi] using hyx (i - n)

theorem prefixSection_determined (C : Set ValuationSpace) (hdown : IsLowerSet C)
    (hclosed : DeterminedByPrefixes C) {n : ℕ} (u : Fin n → ℕ) :
    DeterminedByPrefixes (prefixSection C u) := by
  intro x hx
  apply hclosed
  intro m
  have hbig : zeroExtension (n + m)
      (valuationPrefix (n + m) (joinEquiv n (u, x))) ∈ C := by
    rw [join_prefix_zero]
    exact hx m
  have hmono := prefixSafe_antitone C hdown (show m ≤ n + m by omega)
  exact hmono hbig

theorem tailContinuation_append (μ : ℕ → Measure ℕ) (C : Set ValuationSpace)
    {n m : ℕ} (u : Fin n → ℕ) (v : Fin m → ℕ) :
    tailContinuation (fun i => μ (n + i)) (prefixSection C u) m v =
      tailContinuation μ C (n + m) (appendPrefix u v) := by
  have hlaw : tailLaw (fun i => μ (n + i)) m = tailLaw μ (n + m) := by
    unfold tailLaw
    congr 1
    funext i
    simp [Nat.add_assoc]
  unfold tailContinuation
  rw [hlaw]
  congr 1
  ext x
  simp [prefixSection, join_append]

/-- For any fixed parent, a long enough block has a finite set of continuations
with high future survival, retaining the parent's survival mass up to `2*δ`. -/
theorem parent_extensions_eventually (μ : ℕ → Measure ℕ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (C : Set ValuationSpace) (hC : MeasurableSet C) (hdown : IsLowerSet C)
    (hclosed : DeterminedByPrefixes C) {n : ℕ} (u : Fin n → ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∃ V : Finset (Fin m → ℕ),
      IsLowerSet (↑V : Set (Fin m → ℕ)) ∧
      (∀ v ∈ V, zeroExtension (n + m) (appendPrefix u v) ∈ C ∧
        1 - δ ≤ tailContinuation μ C (n + m) (appendPrefix u v)) ∧
      tailContinuation μ C n u - 2 * δ <
        ∑ v ∈ V, (headLaw (fun i => μ (n + i)) m).real {v} := by
  have ht := good_prefixes_eventually (fun i => μ (n + i)) (prefixSection C u)
    (join_section_measurable C hC n u) (prefixSection_lower C hdown u)
    (prefixSection_determined C hdown hclosed u) hδ
  filter_upwards [ht] with m hm
  obtain ⟨V, hV, hgood, hmass⟩ := hm
  refine ⟨V, hV, ?_, hmass⟩
  intro v hv
  have hg := hgood v hv
  constructor
  · rw [zeroExtension_eq_join, join_append, ← zeroExtension_eq_join]
    exact hg.1
  · simpa only [tailContinuation_append] using hg.2

end Erdos691.Adaptive


/-! Source module Encoding -/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Erdos691.Adaptive

noncomputable def encodeBlock (lo len : ℕ) (u : Fin len → ℕ) : ℕ :=
  ∏ i : Fin len, prime (lo + i) ^ u i

noncomputable def decodePrefix (len a : ℕ) : Fin len → ℕ :=
  fun i => a.factorization (prime i)

theorem encodeBlock_pos (lo len : ℕ) (u : Fin len → ℕ) : 0 < encodeBlock lo len u := by
  apply Finset.prod_pos
  intro i _
  exact pow_pos (prime_pos _) _

theorem encodeBlock_factorization (lo len p : ℕ) (u : Fin len → ℕ) :
    (encodeBlock lo len u).factorization p =
      ∑ i : Fin len, if prime (lo + i) = p then u i else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ => f p)
    (Nat.factorization_prod (S := Finset.univ) (g := fun i : Fin len => prime (lo + i) ^ u i)
      (fun i _ => (pow_pos (prime_pos _) _).ne'))
  simpa only [encodeBlock, Finsupp.finset_sum_apply,
    (prime_is_prime _).factorization_pow, Finsupp.single_apply] using h

theorem encodeBlock_factorization_inside (lo len : ℕ) (u : Fin len → ℕ) (i : Fin len) :
    (encodeBlock lo len u).factorization (prime (lo + i)) = u i := by
  rw [encodeBlock_factorization]
  have he (j : Fin len) : prime (lo + j) = prime (lo + i) ↔ j = i := by
    constructor
    · intro h
      apply Fin.ext
      exact Nat.add_left_cancel (prime_injective h)
    · rintro rfl
      rfl
  simp only [he]
  simp

theorem encodeBlock_factorization_outside (lo len j : ℕ) (u : Fin len → ℕ)
    (hj : j < lo ∨ lo + len ≤ j) : (encodeBlock lo len u).factorization (prime j) = 0 := by
  rw [encodeBlock_factorization]
  apply Finset.sum_eq_zero
  intro i _
  have hneq : prime (lo + i) ≠ prime j := by
    intro h
    have h' := prime_injective h
    rcases hj with hj | hj <;> have hi := i.isLt <;> omega
  simp [hneq]

theorem decode_encode (n : ℕ) (u : Fin n → ℕ) : decodePrefix n (encodeBlock 0 n u) = u := by
  funext i
  simpa [decodePrefix] using encodeBlock_factorization_inside 0 n u i

theorem encodeBlock_injective (lo len : ℕ) : Function.Injective (encodeBlock lo len) := by
  intro u v huv
  funext i
  have h := congrArg (fun a : ℕ => a.factorization (prime (lo + i))) huv
  simpa only [encodeBlock_factorization_inside] using h

theorem encodeBlock_supported (lo len : ℕ) (u : Fin len → ℕ) :
    SupportedOn lo (lo + len) (encodeBlock lo len u) := by
  refine ⟨encodeBlock_pos lo len u, ?_⟩
  intro p hp
  have hp0 : (encodeBlock lo len u).factorization p ≠ 0 := Finsupp.mem_support_iff.1 hp
  rw [encodeBlock_factorization] at hp0
  by_contra h
  push_neg at h
  apply hp0
  apply Finset.sum_eq_zero
  intro i _
  have he : prime (lo + i) ≠ p := h (lo + i) (by omega) (by have hi := i.isLt; omega)
  simp [he]

theorem encode_decode_of_supported {n a : ℕ} (ha : SupportedOn 0 n a) :
    encodeBlock 0 n (decodePrefix n a) = a := by
  have hsub : a.primeFactors ⊆ (Finset.univ : Finset (Fin n)).image (fun i : Fin n => prime i) := by
    intro p hp
    obtain ⟨i, _, hi, he⟩ := ha.2 p hp
    exact Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_univ _, he⟩
  have hp : (∏ p ∈ (Finset.univ : Finset (Fin n)).image (fun i : Fin n => prime i), p ^ a.factorization p) =
      ∏ p ∈ a.primeFactors, p ^ a.factorization p := by
    symm
    apply Finset.prod_subset hsub
    intro p _ hpn
    have hz : a.factorization p = 0 := Finsupp.notMem_support_iff.1 hpn
    simp [hz]
  rw [Finset.prod_image] at hp
  · simpa [encodeBlock, decodePrefix] using hp.trans (Nat.prod_primeFactors_pow_factorization ha.1.ne').symm
  · intro i _ j _ hij
    exact Fin.ext (prime_injective hij)

theorem encode_prefix (n : ℕ) (u : Fin n → ℕ) (l : ℕ) (hl : l ≤ n) :
    primePrefix l (encodeBlock 0 n u) = encodeBlock 0 l (restrictPrefix hl u) := by
  unfold primePrefix encodeBlock
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Nat.zero_add]
  congr 1
  simpa only [Nat.zero_add, restrictPrefix, encodeBlock] using
    encodeBlock_factorization_inside 0 n u ⟨i, i.isLt.trans_le hl⟩

theorem headLaw_singleton_formula (lo len : ℕ) (u : Fin len → ℕ) :
    (headLaw (fun i => primeLaw (lo + i)) len).real {u} =
      blockNormalization lo (lo + len) / encodeBlock lo len u := by
  unfold headLaw
  rw [measureReal_def, Measure.infinitePi_singleton_of_fintype, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, primeLaw_singleton]
  rw [Finset.prod_mul_distrib]
  have hp : (∏ i : Fin len, ((1 : ℝ) / prime (lo + i)) ^ u i) =
      (encodeBlock lo len u : ℝ)⁻¹ := by
    simp [encodeBlock, one_div, inv_pow, Finset.prod_inv_distrib]
  rw [hp]
  have hb : (∏ i : Fin len, (1 - (1 : ℝ) / prime (lo + i))) = blockNormalization lo (lo + len) := by
    unfold blockNormalization
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 - (1 : ℝ) / prime (lo + i))]
    simpa [Nat.add_comm] using
      (Finset.prod_Ico_add (fun i : ℕ => 1 - (1 : ℝ) / prime i) 0 len lo)
  rw [hb, div_eq_mul_inv]

end Erdos691.Adaptive


/-! Source module ArithmeticTreeTools -/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Erdos691.Adaptive

theorem supported_weaken {a lo hi lo' hi' : ℕ} (ha : SupportedOn lo hi a)
    (hl : lo' ≤ lo) (hh : hi ≤ hi') : SupportedOn lo' hi' a := by
  refine ⟨ha.1, ?_⟩
  intro p hp
  obtain ⟨i, hli, hih, he⟩ := ha.2 p hp
  exact ⟨i, hl.trans hli, hih.trans_le hh, he⟩

theorem supported_divisor {a d lo hi : ℕ} (ha : SupportedOn lo hi a)
    (hd : 0 < d) (hda : d ∣ a) : SupportedOn lo hi d := by
  refine ⟨hd, ?_⟩
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpa : p ∣ a := (Nat.dvd_of_mem_primeFactors hp).trans hda
  exact ha.2 p (hpp.mem_primeFactors hpa ha.1.ne')

theorem supported_mul {a b lo hi : ℕ} (ha : SupportedOn lo hi a) (hb : SupportedOn lo hi b) :
    SupportedOn lo hi (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, ?_⟩
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  obtain hp | hp := hpp.dvd_mul.1 (Nat.dvd_of_mem_primeFactors hp)
  · exact ha.2 p (hpp.mem_primeFactors hp ha.1.ne')
  · exact hb.2 p (hpp.mem_primeFactors hp hb.1.ne')

theorem encode_append {n m : ℕ} (u : Fin n → ℕ) (v : Fin m → ℕ) :
    encodeBlock 0 (n + m) (appendPrefix u v) = encodeBlock 0 n u * encodeBlock n m v := by
  unfold encodeBlock
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [appendPrefix, i.isLt]
  · apply Finset.prod_congr rfl
    intro i _
    simp [appendPrefix]

theorem decode_prefix_supported_zero {lo n a : ℕ} (ha : SupportedOn lo n a)
    (i : Fin n) (hi : i.val < lo) : decodePrefix n a i = 0 := by
  by_contra hn
  have hp : prime i ∈ a.primeFactors := Finsupp.mem_support_iff.2 hn
  obtain ⟨j, hj, _, he⟩ := ha.2 (prime i) hp
  have he' := prime_injective he
  omega

theorem prefix_dvd_of_dvd {d a : ℕ} (hd : 0 < d) (ha : 0 < a) (hda : d ∣ a) (n : ℕ) :
    primePrefix n d ∣ primePrefix n a := by
  have hf := (Nat.factorization_le_iff_dvd hd.ne' ha.ne').2 hda
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  exact pow_dvd_pow (prime i) (hf _)

theorem prefix_extended_parent {lo n m a : ℕ} (ha : SupportedOn lo n a)
    (v : Fin m → ℕ) : primePrefix n (a * encodeBlock n m v) = a := by
  have har : encodeBlock 0 n (decodePrefix n a) = a :=
    encode_decode_of_supported (supported_weaken ha (Nat.zero_le _) le_rfl)
  rw [← har, ← encode_append, encode_prefix _ _ _ (Nat.le_add_right n m), restrict_append, har]

theorem extended_parent_supported {lo n m a : ℕ} (hlo : lo ≤ n)
    (ha : SupportedOn lo n a) (v : Fin m → ℕ) :
    SupportedOn lo (n + m) (a * encodeBlock n m v) := by
  apply supported_mul
  · exact supported_weaken ha le_rfl (Nat.le_add_right n m)
  · exact supported_weaken (encodeBlock_supported n m v) hlo le_rfl

theorem avoidance_excludes_its_supported_members (A : Set ℕ) {n a : ℕ}
    (ha : SupportedOn 0 n a) (hA : a ∈ A) :
    zeroExtension n (decodePrefix n a) ∉ avoidance A := by
  intro hC
  apply hC a hA ha.1
  intro i
  by_cases hi : i < n
  · simp [zeroExtension, reset, decodePrefix, hi]
  · have hz : a.factorization (prime i) = 0 := by
      by_contra hn
      have hp : prime i ∈ a.primeFactors := Finsupp.mem_support_iff.2 hn
      obtain ⟨j, _, hj, he⟩ := ha.2 (prime i) hp
      have he' := prime_injective he
      omega
    simp [zeroExtension, reset, hi, hz]

theorem high_score_excludes_members (A : Set ℕ) {n a : ℕ}
    (ha : SupportedOn 0 n a) (hscore : 0 < tailContinuation primeLaw (avoidance A) n (decodePrefix n a)) :
    a ∉ A := by
  intro hA
  have hz : tailContinuation primeLaw (avoidance A) n (decodePrefix n a) = 0 := by
    have hzero := avoidance_excludes_its_supported_members A ha hA
    have he : {x | joinEquiv n (decodePrefix n a, x) ∈ avoidance A} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      apply hzero
      apply avoidance_lower A _ hx
      rw [zeroExtension_eq_join]
      intro i
      by_cases hi : i < n <;> simp [joinEquiv_apply, hi]
    simp [tailContinuation, he]
  linarith

end Erdos691.Adaptive


/-! Source module StageExtension -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology Classical

namespace Erdos691.Adaptive

def divisorClosure (R : Finset ℕ) : Finset ℕ := R.biUnion Nat.divisors

theorem mem_divisorClosure {R : Finset ℕ} {d : ℕ} :
    d ∈ divisorClosure R ↔ ∃ r ∈ R, d ∣ r ∧ r ≠ 0 := by
  simp [divisorClosure, Nat.mem_divisors]

theorem constructionError_lt_one (k : ℕ) : constructionError k < 1 := by
  have hb := constructionError_budget k
  have hp := constructionError_pos (k + 1)
  have hl := loss_lt_one k
  linarith

def GoodLevel (A : Set ℕ) (base k n : ℕ) (S : Finset ℕ) : Prop :=
  base ≤ n ∧ 1 ∈ S ∧
  (∀ a ∈ S, SupportedOn base n a) ∧
  (∀ a ∈ S, ∀ d, 0 < d → d ∣ a → d ∈ S) ∧
  (∀ a ∈ S, 1 - constructionError k ≤ tailContinuation primeLaw (avoidance A) n (decodePrefix n a))

/-- One finite extension step, including all arithmetic admissibility requirements. -/
theorem extend_good_level (A : Set ℕ) {base k n : ℕ} {S : Finset ℕ}
    (hS : GoodLevel A base k n S) :
    ∃ m > 0, ∃ T : Finset ℕ, GoodLevel A base (k + 1) (n + m) T ∧
      (∀ a ∈ T, primePrefix n a ∈ S) ∧
      (∀ a ∈ S, 1 - loss k ≤ blockNormalization n (n + m) *
        ∑ b ∈ fiber T n a, (1 : ℝ) / b) := by
  rcases hS with ⟨hbase, hOne, hsupport, hlower, hhigh⟩
  have heach (a : ℕ) (ha : a ∈ S) :=
    parent_extensions_eventually primeLaw (avoidance A) (avoidance_measurable A)
      (avoidance_lower A) (avoidance_determined A) (decodePrefix n a)
      (constructionError_pos (k + 1))
  have hall := (eventually_all_finset S).2 heach
  obtain ⟨m, hmpos, hm⟩ := ((eventually_gt_atTop 0).and hall).exists
  choose V hVL hVG hVM using (fun a : S => hm a a.2)
  let R : Finset ℕ := S.attach.biUnion (fun a => (V a).image (fun v => a.1 * encodeBlock n m v))
  let T := divisorClosure R
  have hRmem : ∀ r, r ∈ R ↔ ∃ a : S, ∃ v ∈ V a, r = a.1 * encodeBlock n m v := by
    intro r
    simp [R, eq_comm]
  have hRpos (r : ℕ) (hr : r ∈ R) : 0 < r := by
    obtain ⟨a, v, hv, rfl⟩ := (hRmem r).1 hr
    exact Nat.mul_pos (hsupport a a.2).1 (encodeBlock_pos n m v)
  have hraw (a : S) (v : Fin m → ℕ) (hv : v ∈ V a) : a.1 * encodeBlock n m v ∈ T := by
    apply mem_divisorClosure.2
    refine ⟨a.1 * encodeBlock n m v, (hRmem _).2 ⟨a, v, hv, rfl⟩, dvd_rfl, ?_⟩
    exact (Nat.mul_pos (hsupport a a.2).1 (encodeBlock_pos n m v)).ne'
  have hTsupport (d : ℕ) (hd : d ∈ T) : SupportedOn base (n + m) d := by
    obtain ⟨r, hr, hdr, hr0⟩ := mem_divisorClosure.1 hd
    obtain ⟨a, v, hv, rfl⟩ := (hRmem r).1 hr
    exact supported_divisor (extended_parent_supported hbase (hsupport a a.2) v)
      (Nat.pos_of_mem_divisors (Nat.mem_divisors.2 ⟨hdr, hr0⟩)) hdr
  have hThigh (d : ℕ) (hd : d ∈ T) :
      1 - constructionError (k + 1) ≤ tailContinuation primeLaw (avoidance A) (n + m)
        (decodePrefix (n + m) d) := by
    obtain ⟨r, hr, hdr, hr0⟩ := mem_divisorClosure.1 hd
    obtain ⟨a, v, hv, heq⟩ := (hRmem r).1 hr
    have har : encodeBlock 0 n (decodePrefix n a.1) = a.1 :=
      encode_decode_of_supported (supported_weaken (hsupport a a.2) (Nat.zero_le _) le_rfl)
    have hrenc : r = encodeBlock 0 (n + m) (appendPrefix (decodePrefix n a.1) v) := by
      rw [encode_append, har]
      exact heq
    have hgd := (hVG a v hv).2
    have hdr0 : d ≠ 0 := (hTsupport d hd).1.ne'
    have hfac := (Nat.factorization_le_iff_dvd hdr0 hr0).2 hdr
    have hdecode : decodePrefix (n + m) d ≤ decodePrefix (n + m) r := fun i => hfac _
    have hmono := tailContinuation_antitone primeLaw (avoidance A) (avoidance_lower A) (n + m) hdecode
    rw [hrenc, decode_encode] at hmono
    exact hgd.trans hmono
  have hproject (d : ℕ) (hd : d ∈ T) : primePrefix n d ∈ S := by
    obtain ⟨r, hr, hdr, hr0⟩ := mem_divisorClosure.1 hd
    obtain ⟨a, v, hv, rfl⟩ := (hRmem r).1 hr
    have hdiv := prefix_dvd_of_dvd (hTsupport d hd).1
      (Nat.mul_pos (hsupport a a.2).1 (encodeBlock_pos n m v)) hdr n
    rw [prefix_extended_parent (hsupport a a.2)] at hdiv
    exact hlower a a.2 _ (primePrefix_pos _ _) hdiv
  have hret (a : ℕ) (ha : a ∈ S) :
      1 - loss k ≤ blockNormalization n (n + m) * ∑ b ∈ fiber T n a, (1 : ℝ) / b := by
    let aa : S := ⟨a, ha⟩
    have hsub : (V aa).image (encodeBlock n m) ⊆ fiber T n a := by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
      apply Finset.mem_image.2
      refine ⟨a * encodeBlock n m v, ?_, ?_⟩
      · apply Finset.mem_filter.2
        exact ⟨hraw aa v hv, prefix_extended_parent (hsupport a ha) v⟩
      · exact Nat.mul_div_cancel_left _ (hsupport a ha).1
    have hsum : (∑ v ∈ V aa, (headLaw (fun i => primeLaw (n + i)) m).real {v}) ≤
        blockNormalization n (n + m) * ∑ b ∈ fiber T n a, (1 : ℝ) / b := by
      simp_rw [headLaw_singleton_formula, div_eq_mul_inv]
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (blockNormalization_pos _ _).le
      have he : (∑ v ∈ V aa, (encodeBlock n m v : ℝ)⁻¹) =
          ∑ b ∈ (V aa).image (encodeBlock n m), (b : ℝ)⁻¹ := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h => encodeBlock_injective n m h
      rw [he]
      simp only [one_mul]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by positivity)
    have hbound := hVM aa
    have hhigha := hhigh a ha
    have hbudget := constructionError_budget k
    linarith
  have hOneT : 1 ∈ T := by
    have hvsum := hVM (⟨1, hOne⟩ : S)
    have hhigh1 := hhigh 1 hOne
    have hbudget := constructionError_budget k
    have hpositive := loss_lt_one k
    have hvne : (V (⟨1, hOne⟩ : S)).Nonempty := by
      by_contra h
      have he : V (⟨1, hOne⟩ : S) = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
      simp [he] at hvsum
      linarith
    obtain ⟨v, hv⟩ := hvne
    apply mem_divisorClosure.2
    exact ⟨1 * encodeBlock n m v, (hRmem _).2 ⟨⟨1, hOne⟩, v, hv, rfl⟩,
      one_dvd _, (by simpa using (encodeBlock_pos n m v).ne')⟩
  refine ⟨m, hmpos, T, ?_, hproject, hret⟩
  refine ⟨by omega, hOneT, hTsupport, ?_, hThigh⟩
  intro a ha d hd hda
  obtain ⟨r, hr, har, hr0⟩ := mem_divisorClosure.1 ha
  exact mem_divisorClosure.2 ⟨r, hr, hda.trans har, hr0⟩

end Erdos691.Adaptive


/-! Source module BuildTest -/

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical

namespace Erdos691.Adaptive

structure LevelState (A : Set ℕ) (base k : ℕ) where
  cutoff : ℕ
  elements : Finset ℕ
  good : GoodLevel A base k cutoff elements

theorem successor_exists (A : Set ℕ) (base k : ℕ) (s : LevelState A base k) :
    ∃ t : LevelState A base (k + 1), s.cutoff < t.cutoff ∧
      (∀ a ∈ t.elements, primePrefix s.cutoff a ∈ s.elements) ∧
      (∀ a ∈ s.elements, 1 - loss k ≤ blockNormalization s.cutoff t.cutoff *
        ∑ b ∈ fiber t.elements s.cutoff a, (1 : ℝ) / b) := by
  obtain ⟨m, hm, T, hgood, hproject, hret⟩ := extend_good_level A s.good
  exact ⟨⟨s.cutoff + m, T, hgood⟩, by change s.cutoff < s.cutoff + m; omega, hproject, hret⟩

noncomputable def nextLevel (A : Set ℕ) (base k : ℕ) (s : LevelState A base k) :
    LevelState A base (k + 1) := Classical.choose (successor_exists A base k s)

theorem nextLevel_spec (A : Set ℕ) (base k : ℕ) (s : LevelState A base k) :
    s.cutoff < (nextLevel A base k s).cutoff ∧
      (∀ a ∈ (nextLevel A base k s).elements, primePrefix s.cutoff a ∈ s.elements) ∧
      (∀ a ∈ s.elements, 1 - loss k ≤
        blockNormalization s.cutoff (nextLevel A base k s).cutoff *
        ∑ b ∈ fiber (nextLevel A base k s).elements s.cutoff a, (1 : ℝ) / b) :=
  Classical.choose_spec (successor_exists A base k s)

noncomputable def levelSequence (A : Set ℕ) (base : ℕ) (s₀ : LevelState A base 0) :
    (k : ℕ) → LevelState A base k
  | 0 => s₀
  | k + 1 => nextLevel A base k (levelSequence A base s₀ k)

noncomputable def testFromRoot (A : Set ℕ) (base : ℕ) (s₀ : LevelState A base 0)
    (hbase : s₀.cutoff = base) (hstart : s₀.elements = {1}) : AdmissibleTest where
  cutoff k := (levelSequence A base s₀ k).cutoff
  increasing := strictMono_nat_of_lt_succ fun k => (nextLevel_spec A base k _).1
  level k := (levelSequence A base s₀ k).elements
  start := hstart
  supported k a ha := by
    change SupportedOn s₀.cutoff (levelSequence A base s₀ k).cutoff a
    rw [hbase]
    exact (levelSequence A base s₀ k).good.2.2.1 a ha
  downward k a ha d hd hda := (levelSequence A base s₀ k).good.2.2.2.1 a ha d hd hda
  projects k a ha := (nextLevel_spec A base k _).2.1 a ha
  retention k a ha := (nextLevel_spec A base k _).2.2 a ha

theorem testFromRoot_avoids (A : Set ℕ) (base : ℕ) (s₀ : LevelState A base 0)
    (hbase : s₀.cutoff = base) (hstart : s₀.elements = {1}) :
    ∀ k, ∀ a ∈ (testFromRoot A base s₀ hbase hstart).level k, a ∉ A := by
  intro k a ha
  let s := levelSequence A base s₀ k
  have hsupport := s.good.2.2.1 a ha
  have hscore := s.good.2.2.2.2 a ha
  apply high_score_excludes_members A (supported_weaken hsupport (Nat.zero_le _) le_rfl)
  have hpos : 0 < 1 - constructionError k := sub_pos.2 (constructionError_lt_one k)
  exact hpos.trans_le hscore

/-- Positive avoidance probability yields an admissible test missing every element of `A`. -/
theorem exists_avoiding_test (A : Set ℕ)
    (hA : 0 < (fullLaw primeLaw).real (avoidance A)) :
    ∃ T : AdmissibleTest, ∀ k, ∀ a ∈ T.level k, a ∉ A := by
  obtain ⟨base, _, hb⟩ := avoidance_zero_prefix A hA (constructionError_pos 0)
    (constructionError_lt_one 0) 0
  have hgood : GoodLevel A base 0 base {1} := by
    refine ⟨le_rfl, Finset.mem_singleton_self 1, ?_, ?_, ?_⟩
    · intro a ha
      have : a = 1 := Finset.mem_singleton.1 ha
      subst a
      exact supportedOn_one _ _
    · intro a ha d hd hda
      have : a = 1 := Finset.mem_singleton.1 ha
      subst a
      exact Finset.mem_singleton.2 (Nat.dvd_one.1 hda)
    · intro a ha
      have : a = 1 := Finset.mem_singleton.1 ha
      subst a
      have he : decodePrefix base 1 = 0 := by funext i; simp [decodePrefix]
      rw [he]
      exact hb.le
  let s₀ : LevelState A base 0 := ⟨base, {1}, hgood⟩
  exact ⟨testFromRoot A base s₀ rfl rfl, testFromRoot_avoids A base s₀ rfl rfl⟩

/-- The adaptive test condition implies density one for every set of integers. -/
theorem density_one_of_meets_every_test (A : Set ℕ) (hA : MeetsEveryTest A) :
    HasMultiplesDensityOne A := by
  rw [density_one_iff_avoidance_zero]
  by_contra hz
  have hp : 0 < (fullLaw primeLaw).real (avoidance A) :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  obtain ⟨T, hT⟩ := exists_avoiding_test A hp
  obtain ⟨k, a, ha, hAa⟩ := hA T
  exact hT k a ha hAa

end Erdos691.Adaptive


/-! Source module TestMass -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology Classical

namespace Erdos691.Adaptive

theorem encode_dvd_iff (lo len : ℕ) (u : Fin len → ℕ) {a : ℕ} (ha : 0 < a) :
    encodeBlock lo len u ∣ a ↔ ∀ i, u i ≤ a.factorization (prime (lo + i)) := by
  rw [← Nat.factorization_le_iff_dvd (encodeBlock_pos lo len u).ne' ha.ne']
  constructor
  · intro h i
    simpa only [encodeBlock_factorization_inside] using h (prime (lo + i))
  · intro h p
    by_cases hex : ∃ i : Fin len, prime (lo + i) = p
    · obtain ⟨i, rfl⟩ := hex
      simpa only [encodeBlock_factorization_inside] using h i
    · rw [encodeBlock_factorization]
      have hz : (∑ i : Fin len, if prime (lo + i) = p then u i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [show prime (lo + i) ≠ p from fun hp => hex ⟨i, hp⟩]
      rw [hz]
      exact Nat.zero_le _

theorem primePrefix_eq_encode (n a : ℕ) :
    primePrefix n a = encodeBlock 0 n (decodePrefix n a) := by
  unfold primePrefix encodeBlock decodePrefix
  simp only [Nat.zero_add]
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => prime i ^ a.factorization (prime i)) n).symm

theorem primePrefix_dvd (n : ℕ) {a : ℕ} (ha : 0 < a) : primePrefix n a ∣ a := by
  rw [primePrefix_eq_encode, encode_dvd_iff _ _ _ ha]
  intro i
  simp [decodePrefix]

theorem decode_primePrefix (n a : ℕ) : decodePrefix n (primePrefix n a) = decodePrefix n a := by
  rw [primePrefix_eq_encode, decode_encode]

theorem blockNormalization_split {n m : ℕ} (hnm : n ≤ m) :
    blockNormalization 0 m = blockNormalization 0 n * blockNormalization n m := by
  unfold blockNormalization
  exact (Finset.prod_Ico_consecutive (fun i : ℕ => 1 - (1 : ℝ) / prime i) (Nat.zero_le n) hnm).symm

theorem reciprocal_sum_by_fibers (n : ℕ) (S T : Finset ℕ)
    (hpos : ∀ a ∈ T, 0 < a) (hproject : ∀ a ∈ T, primePrefix n a ∈ S) :
    (∑ x ∈ T, (1 : ℝ) / x) =
      ∑ a ∈ S, ((1 : ℝ) / a) * ∑ b ∈ fiber T n a, (1 : ℝ) / b := by
  have hf := Finset.sum_fiberwise_of_maps_to hproject (fun x : ℕ => (1 : ℝ) / x)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro a ha
  have hdiv (x : ℕ) (hx : x ∈ T.filter (fun x => primePrefix n x = a)) : a ∣ x := by
    have hm := Finset.mem_filter.1 hx
    rw [← hm.2]
    exact primePrefix_dvd n (hpos x hm.1)
  have hmul (x : ℕ) (hx : x ∈ T.filter (fun x => primePrefix n x = a)) : a * (x / a) = x :=
    Nat.mul_div_cancel' (hdiv x hx)
  unfold fiber
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hc : (x : ℝ) = (a : ℝ) * (x / a : ℕ) := by exact_mod_cast (hmul x hx).symm
    rw [hc]
    simp [one_div, mul_inv_rev, mul_comm]
  · intro x hx y hy he
    change x / a = y / a at he
    rw [← hmul x hx, ← hmul y hy, he]

noncomputable def levelMass (n : ℕ) (S : Finset ℕ) : ℝ :=
  blockNormalization 0 n * ∑ a ∈ S, (1 : ℝ) / a

theorem test_mass_step (T : AdmissibleTest) (k : ℕ) :
    (1 - loss k) * levelMass (T.cutoff k) (T.level k) ≤
      levelMass (T.cutoff (k + 1)) (T.level (k + 1)) := by
  have hmono : T.cutoff k ≤ T.cutoff (k + 1) := T.increasing.monotone (Nat.le_succ k)
  unfold levelMass
  rw [blockNormalization_split hmono,
    reciprocal_sum_by_fibers (T.cutoff k) (T.level k) (T.level (k + 1))
      (fun a ha => (T.supported (k + 1) a ha).1) (T.projects k)]
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hret := T.retention k a ha
  have hp : 0 ≤ blockNormalization 0 (T.cutoff k) * ((1 : ℝ) / a) := by
    exact mul_nonneg (blockNormalization_pos _ _).le (by positivity)
  have h := mul_le_mul_of_nonneg_left hret hp
  nlinarith

theorem test_mass_initial (T : AdmissibleTest) :
    levelMass (T.cutoff 0) (T.level 0) = blockNormalization 0 (T.cutoff 0) := by
  simp [levelMass, T.start]

theorem test_mass_lower_bound (T : AdmissibleTest) (k : ℕ) :
    blockNormalization 0 (T.cutoff 0) * (3 / 4 : ℝ) ≤ levelMass (T.cutoff k) (T.level k) := by
  exact positive_flow_lower_bound (blockNormalization_pos _ _).le (test_mass_initial T).ge
    (test_mass_step T) k

def levelEvent (n : ℕ) (S : Finset ℕ) : Set ValuationSpace :=
  ⋃ a ∈ S, prefixAtom n (decodePrefix n a)

theorem levelEvent_measurable (n : ℕ) (S : Finset ℕ) : MeasurableSet (levelEvent n S) :=
  MeasurableSet.biUnion (Finset.countable_toSet S) (fun a _ => measurable_prefixAtom n _)

theorem levelEvent_mass (n : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, SupportedOn 0 n a) :
    (fullLaw primeLaw).real (levelEvent n S) = levelMass n S := by
  have hd : Set.PairwiseDisjoint (↑S) (fun a => prefixAtom n (decodePrefix n a)) := by
    intro a ha b hb hne
    apply Set.disjoint_left.2
    intro x hx hy
    have he : decodePrefix n a = decodePrefix n b := hx.symm.trans hy
    apply hne
    rw [← encode_decode_of_supported (hS a ha), ← encode_decode_of_supported (hS b hb), he]
  rw [levelEvent, measureReal_biUnion_finset hd (fun a _ => measurable_prefixAtom n _)]
  unfold levelMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he := prefix_intersection_measure primeLaw Set.univ MeasurableSet.univ n (decodePrefix n a)
  simp only [Set.univ_inter, tailContinuation, Set.mem_univ, Set.setOf_true, probReal_univ, mul_one] at he
  rw [he]
  have hf := headLaw_singleton_formula 0 n (decodePrefix n a)
  simpa only [Nat.zero_add, encode_decode_of_supported (hS a ha), div_eq_mul_inv,
    one_mul, one_div] using hf

end Erdos691.Adaptive


/-! Source module Necessity -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology Classical

namespace Erdos691.Adaptive

theorem test_events_step (T : AdmissibleTest) (k : ℕ) :
    levelEvent (T.cutoff (k + 1)) (T.level (k + 1)) ⊆ levelEvent (T.cutoff k) (T.level k) := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ : ∃ a ∈ T.level (k + 1), x ∈ prefixAtom (T.cutoff (k + 1))
      (decodePrefix (T.cutoff (k + 1)) a) := by simpa [levelEvent] using hx
  apply Set.mem_iUnion.2
  refine ⟨primePrefix (T.cutoff k) a, Set.mem_iUnion.2 ⟨T.projects k a ha, ?_⟩⟩
  change valuationPrefix (T.cutoff k) x = decodePrefix (T.cutoff k) (primePrefix (T.cutoff k) a)
  rw [decode_primePrefix]
  funext i
  have hi : i.val < T.cutoff (k + 1) := i.isLt.trans_le (T.increasing.monotone (Nat.le_succ k))
  exact congrFun hxa ⟨i, hi⟩

theorem test_events_antitone (T : AdmissibleTest) :
    Antitone (fun k => levelEvent (T.cutoff k) (T.level k)) :=
  antitone_nat_of_succ_le (test_events_step T)

theorem test_intersection_avoids (A : Set ℕ) (T : AdmissibleTest)
    (hmiss : ∀ k, ∀ a ∈ T.level k, a ∉ A) :
    (⋂ k, levelEvent (T.cutoff k) (T.level k)) ⊆ avoidance A := by
  intro x hx a ha hapos hdiv
  have hlevel := Set.mem_iInter.1 hx (a + 1)
  obtain ⟨b, hb, hxb⟩ : ∃ b ∈ T.level (a + 1), x ∈ prefixAtom (T.cutoff (a + 1))
      (decodePrefix (T.cutoff (a + 1)) b) := by simpa [levelEvent] using hlevel
  have hbpos : 0 < b := (T.supported (a + 1) b hb).1
  have hcut : a + 1 ≤ T.cutoff (a + 1) := T.increasing.id_le _
  have hab : a ∣ b := by
    apply (Nat.factorization_le_iff_dvd hapos.ne' hbpos.ne').1
    intro p
    by_cases hp : Nat.Prime p
    · obtain ⟨i, hi⟩ := Nat.subset_range_nth hp
      have hip : prime i = p := hi
      by_cases hil : i < T.cutoff (a + 1)
      · have hval := congrFun hxb ⟨i, hil⟩
        change x i = b.factorization (prime i) at hval
        rw [← hip, ← hval]
        exact hdiv i
      · have hia : a < i := by omega
        rw [← hip, factorization_eventually_zero a i hia]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime a hp]
      exact Nat.zero_le _
  exact hmiss (a + 1) a (T.downward (a + 1) b hb a hapos hab) ha

theorem missing_test_positive_avoidance (A : Set ℕ) (T : AdmissibleTest)
    (hmiss : ∀ k, ∀ a ∈ T.level k, a ∉ A) :
    0 < (fullLaw primeLaw).real (avoidance A) := by
  let E : ℕ → Set ValuationSpace := fun k => levelEvent (T.cutoff k) (T.level k)
  have hlim := tendsto_measure_iInter_atTop (μ := fullLaw primeLaw)
    (fun k => (levelEvent_measurable _ _).nullMeasurableSet)
    (test_events_antitone T) (show ∃ k, (fullLaw primeLaw) (E k) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  have hr : Tendsto (fun k => (fullLaw primeLaw).real (E k)) atTop
      (𝓝 ((fullLaw primeLaw).real (⋂ k, E k))) :=
    (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hlim
  let c : ℝ := blockNormalization 0 (T.cutoff 0) * (3 / 4 : ℝ)
  have hc : 0 < c := mul_pos (blockNormalization_pos _ _) (by norm_num)
  have hbound : ∀ k, c ≤ (fullLaw primeLaw).real (E k) := by
    intro k
    rw [show E k = levelEvent (T.cutoff k) (T.level k) from rfl]
    rw [levelEvent_mass _ _ (fun a ha => supported_weaken (T.supported k a ha) (Nat.zero_le _) le_rfl)]
    exact test_mass_lower_bound T k
  have hcE : c ≤ (fullLaw primeLaw).real (⋂ k, E k) :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hr hbound
  have hmono : (fullLaw primeLaw).real (⋂ k, E k) ≤ (fullLaw primeLaw).real (avoidance A) :=
    measureReal_mono (test_intersection_avoids A T hmiss)
  exact hc.trans_le (hcE.trans hmono)

/-- Density one forces every universal admissible test to meet `A`. -/
theorem meets_every_test_of_density_one (A : Set ℕ) (hA : HasMultiplesDensityOne A) :
    MeetsEveryTest A := by
  intro T
  by_contra h
  have hmiss : ∀ k, ∀ a ∈ T.level k, a ∉ A := by simpa using h
  have hp := missing_test_positive_avoidance A T hmiss
  have hz := (density_one_iff_avoidance_zero A).1 hA
  linarith

/-- The full proposed structural criterion for Erdős problem 691. -/
theorem erdos691 (A : Set ℕ) : HasMultiplesDensityOne A ↔ MeetsEveryTest A :=
  ⟨meets_every_test_of_density_one A, density_one_of_meets_every_test A⟩

theorem fullSolution : FullSolution := erdos691

end Erdos691.Adaptive


/-! Source module ExactFibers -/

open scoped BigOperators Classical

namespace Erdos691.Adaptive

theorem supported_factorization_before {lo hi a : ℕ} (ha : SupportedOn lo hi a)
    {i : ℕ} (hi' : i < lo) : a.factorization (prime i) = 0 := by
  by_contra h
  have hp : prime i ∈ a.primeFactors := Finsupp.mem_support_iff.2 h
  obtain ⟨j, hj, _, he⟩ := ha.2 _ hp
  have he' := prime_injective he
  omega

theorem prefix_of_supported {lo hi a : ℕ} (ha : SupportedOn lo hi a) : primePrefix hi a = a := by
  rw [primePrefix_eq_encode, encode_decode_of_supported (supported_weaken ha (Nat.zero_le _) le_rfl)]

theorem prefix_of_block_product {base old next m n : ℕ}
    (hm : SupportedOn base old m) (hn : SupportedOn old next n) :
    primePrefix old (m * n) = m := by
  have he : primePrefix old (m * n) = primePrefix old m := by
    unfold primePrefix
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    rw [Nat.factorization_mul hm.1.ne' hn.1.ne', Finsupp.add_apply,
      supported_factorization_before hn (Finset.mem_range.1 hi), add_zero]
  rw [he, prefix_of_supported hm]

/-- The quotient-image fibers in the formal statement are exactly the original
new-prime multiplier fibers. -/
theorem exact_fiber_characterization (T : AdmissibleTest) (k m : ℕ) (hm : m ∈ T.level k) (n : ℕ) :
    n ∈ fiber (T.level (k + 1)) (T.cutoff k) m ↔
      SupportedOn (T.cutoff k) (T.cutoff (k + 1)) n ∧ m * n ∈ T.level (k + 1) := by
  constructor
  · intro hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨haT, hprefix⟩ := Finset.mem_filter.1 ha
    have haS := T.supported (k + 1) a haT
    have hmS := T.supported k m hm
    have hma : m ∣ a := by rw [← hprefix]; exact primePrefix_dvd _ haS.1
    have hmul : m * (a / m) = a := Nat.mul_div_cancel' hma
    have hquot : 0 < a / m := by
      by_contra h
      have hz : a / m = 0 := Nat.eq_zero_of_not_pos h
      rw [hz, mul_zero] at hmul
      exact haS.1.ne' hmul.symm
    refine ⟨⟨hquot, ?_⟩, ?_⟩
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ a / m := Nat.dvd_of_mem_primeFactors hp
      have hpa : p ∣ a := by rw [← hmul]; exact dvd_mul_of_dvd_right hpn m
      have hpA : p ∈ a.primeFactors := hpp.mem_primeFactors hpa haS.1.ne'
      obtain ⟨i, _, hi, he⟩ := haS.2 p hpA
      refine ⟨i, ?_, hi, he⟩
      by_contra hbefore
      have hlt : i < T.cutoff k := Nat.lt_of_not_ge hbefore
      have hpref := congrFun (decode_primePrefix (T.cutoff k) a) ⟨i, hlt⟩
      change (primePrefix (T.cutoff k) a).factorization (prime i) = a.factorization (prime i) at hpref
      rw [hprefix, he] at hpref
      have hzero : (a / m).factorization p = 0 := by
        rw [Nat.factorization_div hma, Finsupp.tsub_apply, hpref, tsub_self]
      exact (Finsupp.mem_support_iff.1 hp) hzero
    · simpa only [hmul] using haT
  · rintro ⟨hn, hmn⟩
    apply Finset.mem_image.2
    refine ⟨m * n, ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨hmn, prefix_of_block_product (T.supported k m hm) hn⟩
    · exact Nat.mul_div_cancel_left n (T.supported k m hm).1

end Erdos691.Adaptive
