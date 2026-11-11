import Mathlib

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
      simpa [f] using hcount.mul hrpow
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
    simpa [fs] using herr.mul hrpow
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
    simpa [fs] using herr.mul hrpow
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
    simpa [MeasureTheory.IntegrableOn] using
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
  constructor <;> intro h <;>
    simpa [HasNatDensity, Erdos691.DensityToDirichlet.HasNatDensity, densSeq,
      Erdos691.DensityToDirichlet.densSeq, countUpTo, Erdos691.DensityToDirichlet.countUpTo]
      using h

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
  simpa [geomWeightOfRatio] using (summable_geometric_of_lt_one hq0 hq1).mul_left (1 - q)

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
      simpa [optionVecEquivProd, q'] using (vecWeight_consVec q k w)
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
        simpa [optionVecEquivProd, q'] using (vecWeight_consVec q k w)
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
        · simpa [U'] using hv
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
      simpa [Set.indicator, Set.mem_setOf_eq] using
        (tsum_subtype {v : ι → ℕ | e ≤ v} (vecWeight q))
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
          simpa [lcm0, Finset.lcm_insert, ha] using hp
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


/-! ## TeX-facing aliases matching the revised write-up -/

/-- Lean alias for **Definition 7** (primitive part). -/
abbrev tex_def_primitive_part (A : Set ℕ) : Set ℕ := primitiveKernel A

/-- Lean alias for **Lemma 5** (`lem:density-to-Dirichlet`). -/
theorem tex_lem_density_to_Dirichlet
    {S : Set ℕ} {δ : ℝ}
    (hS : HasNatDensity S δ) :
    Tendsto (fun s : ℝ => mu s S)
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds δ) :=
  tendsto_mu_of_hasNatDensity hS

/-- Lean alias for **Lemma 6** (`lem:divisibility-monotone`). -/
theorem tex_lem_divisibility_monotone
    {U : Set ℕ} (hU : DivisibilityUpwardClosed U)
    {s t : ℝ} (hs : 1 < s) (ht : 1 < t) (hst : s ≤ t) :
    mu t U ≤ mu s U :=
  mu_le_of_divisibilityUpwardClosed hU hs ht hst

/-- TeX-facing sequence form of **Theorem 1** (`thm:finite-approx`). -/
theorem tex_thm_finite_approx_seq (A : Set ℕ) :
    IsBehrend A ↔
      Tendsto (fun N : ℕ => finiteMultiplesDensity (trunc A N)) Filter.atTop (nhds 1) :=
  behrend_iff_truncFiniteDensities_tendsto_one A

/-- TeX-facing finite-subset `ε`-form of **Theorem 1** (`thm:finite-approx`).

This is the Lean replacement for the finite-subset supremum clause in the revised theorem. -/
theorem tex_thm_finite_approx_finiteSubset_eps (A : Set ℕ) :
    IsBehrend A ↔
      ∀ ε > 0, ∃ F : Finset ℕ,
        PositiveFinset F ∧ ((F : Set ℕ) ⊆ A) ∧
        1 - ε < finiteMultiplesDensity F :=
  behrend_iff_finiteSubsetApprox_eps A

/-- Bundled Lean-facing version of **Theorem 1** (`thm:finite-approx`). -/
theorem tex_thm_finite_approx (A : Set ℕ) :
    (IsBehrend A ↔
      Tendsto (fun N : ℕ => finiteMultiplesDensity (trunc A N)) Filter.atTop (nhds 1)) ∧
    (IsBehrend A ↔
      ∀ ε > 0, ∃ F : Finset ℕ,
        PositiveFinset F ∧ ((F : Set ℕ) ⊆ A) ∧
        1 - ε < finiteMultiplesDensity F) := by
  exact ⟨tex_thm_finite_approx_seq A, tex_thm_finite_approx_finiteSubset_eps A⟩

/-- Lean alias for **Lemma 8** (`lem:primitive-same`). -/
theorem tex_lem_primitive_same (A : Set ℕ) :
    Multiples A = Multiples (primitiveKernel A) :=
  multiples_primitiveKernel A

/-- Lean alias for the density sentence in **Corollary 2** / **Corollary 9**. -/
theorem tex_cor_main_sieve_answer_density (A : Set ℕ) (N : ℕ) :
    HasNatDensity (AvoidSet (primitiveTrunc A N)) (R A N) :=
  hasNatDensity_avoidSet_eq_R A N

/-- Lean alias for the `R_N → 0` form of **Corollary 2** (`cor:main-sieve-answer`). -/
theorem tex_cor_main_sieve_answer_limit (A : Set ℕ) :
    IsBehrend A ↔ Tendsto (R A) Filter.atTop (nhds 0) :=
  behrend_iff_R_tendsto_zero A

/-- Lean alias for the second displayed equivalence in **Corollary 2**. -/
theorem tex_cor_main_sieve_answer_nonempty_sum (A : Set ℕ) :
    IsBehrend A ↔
      Tendsto
        (fun N : ℕ =>
          ∑ G ∈ (primitiveTrunc A N).powerset with G.Nonempty,
            (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ))
        Filter.atTop (nhds 1) :=
  behrend_iff_nonempty_powerset_sum_tendsto_one A

/-- Lean alias for the density sentence in **Corollary 9** (`cor:sieve-criterion`). -/
theorem tex_cor_sieve_criterion_density (A : Set ℕ) (N : ℕ) :
    HasNatDensity (AvoidSet (primitiveTrunc A N)) (R A N) :=
  tex_cor_main_sieve_answer_density A N

/-- Lean alias for the `R_N → 0` form of **Corollary 9** (`cor:sieve-criterion`). -/
theorem tex_cor_sieve_criterion_limit (A : Set ℕ) :
    IsBehrend A ↔ Tendsto (R A) Filter.atTop (nhds 0) :=
  tex_cor_main_sieve_answer_limit A

/-- Lean alias for the second displayed equivalence in **Corollary 9**. -/
theorem tex_cor_sieve_criterion_nonempty_sum (A : Set ℕ) :
    IsBehrend A ↔
      Tendsto
        (fun N : ℕ =>
          ∑ G ∈ (primitiveTrunc A N).powerset with G.Nonempty,
            (-1 : ℝ) ^ (G.card + 1) / (lcm0 G : ℝ))
        Filter.atTop (nhds 1) :=
  tex_cor_main_sieve_answer_nonempty_sum A

/-! ## Remark 4: pairwise-coprime case -/

section PairwiseCoprimeRemark

/-- Convenience predicate for the pairwise-coprime condition used in the final remark. -/
def PairwiseCoprime (S : Set ℕ) : Prop :=
  Set.Pairwise S (fun a b => Nat.Coprime a b)

/-- Reciprocal indicator sequence of `A^{prim}`.

This is the Lean avatar of the formal series `∑_{a ∈ A^{prim}} 1 / a`: the `n`-th term is
`1 / n` if `n ∈ primitiveKernel A`, and `0` otherwise.  Since `primitiveKernel A` only contains
positive integers, the `n = 0` term is automatically `0`. -/
noncomputable def primitiveRecipSeq (A : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ primitiveKernel A then 1 / (n : ℝ) else 0

lemma primitiveRecipSeq_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ primitiveRecipSeq A n := by
  by_cases h : n ∈ primitiveKernel A
  · simp [primitiveRecipSeq, h]
  · simp [primitiveRecipSeq, h]

/-- Partial sums of `primitiveRecipSeq` are exactly the reciprocal sums over `B_N = A^{prim} ∩ [1,N]`.

This is the bookkeeping lemma needed to pass between the finitary notation in the TeX note and
`Summable` / `Tendsto` statements over `ℕ`. -/
lemma sum_range_succ_primitiveRecipSeq_eq (A : Set ℕ) (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (primitiveRecipSeq A)
      = Finset.sum (primitiveTrunc A N) (fun a => (1 : ℝ) / (a : ℝ)) := by
  classical
  have hfilter :
      (Finset.range (N + 1)).filter (fun n => n ∈ primitiveKernel A) = primitiveTrunc A N := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hrange, hprim⟩
      have hn1 : 1 ≤ n := Nat.succ_le_of_lt hprim.2.1
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
      exact (mem_trunc (A := primitiveKernel A) (N := N) (a := n)).2
        ⟨⟨hn1, hnN⟩, hprim⟩
    · intro hn
      rcases (mem_trunc (A := primitiveKernel A) (N := N) (a := n)).1 hn with
        ⟨hnIcc, hprim⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hnIcc.2), hprim⟩
  calc
    Finset.sum (Finset.range (N + 1)) (primitiveRecipSeq A)
        = Finset.sum (Finset.range (N + 1))
            (fun n => if n ∈ primitiveKernel A then (1 : ℝ) / (n : ℝ) else 0) := by
            simp [primitiveRecipSeq]
    _ = Finset.sum ((Finset.range (N + 1)).filter (fun n => n ∈ primitiveKernel A))
          (fun n => (1 : ℝ) / (n : ℝ)) := by
          rw [← Finset.sum_filter]
    _ = Finset.sum (primitiveTrunc A N) (fun a => (1 : ℝ) / (a : ℝ)) := by
          rw [hfilter]

/-- If a finite set is pairwise coprime, then its finite lcm is just its product. -/
lemma lcm0_eq_prod_of_pairwise_coprime
    {F G : Finset ℕ}
    (hpair : PairwiseCoprime (F : Set ℕ))
    (hGF : G ⊆ F) :
    lcm0 G = G.prod id := by
  have hpairG : PairwiseCoprime (G : Set ℕ) := by
    unfold PairwiseCoprime at hpair ⊢
    exact Set.Pairwise.mono
      (show (G : Set ℕ) ⊆ F from by
        intro a ha
        exact hGF ha)
      hpair
  unfold PairwiseCoprime at hpairG
  simpa [lcm0] using (Finset.lcm_eq_prod (s := G) (f := id) hpairG)

/-- Finite product formula in the pairwise-coprime case.

This is the finite identity
`R_N = ∏_{a ∈ B_N} (1 - 1 / a)` from the final remark in the TeX note. -/
lemma finiteAvoidDensity_eq_prod_one_sub_of_pairwise_coprime
    {F : Finset ℕ}
    (hpair : PairwiseCoprime (F : Set ℕ)) :
    finiteAvoidDensity F = ∏ a ∈ F, (1 - 1 / (a : ℝ)) := by
  classical
  symm
  calc
    ∏ a ∈ F, (1 - 1 / (a : ℝ))
        = ∑ G ∈ F.powerset, (-1 : ℝ) ^ G.card / ((G.prod id : ℕ) : ℝ) := by
          calc
            ∏ a ∈ F, (1 - 1 / (a : ℝ))
                = ∑ G ∈ F.powerset, (-1 : ℝ) ^ G.card * ∏ a ∈ G, (1 / (a : ℝ)) := by
                    simpa using
                      (Finset.prod_sub
                        (f := fun _ : ℕ => (1 : ℝ))
                        (g := fun a : ℕ => (1 : ℝ) / (a : ℝ))
                        F)
            _ = ∑ G ∈ F.powerset, (-1 : ℝ) ^ G.card / ((G.prod id : ℕ) : ℝ) := by
                  refine Finset.sum_congr rfl ?_
                  intro G hG
                  have hprod :
                      (∏ a ∈ G, (1 / (a : ℝ))) = ((∏ a ∈ G, (a : ℝ)))⁻¹ := by
                    simp [one_div, Finset.prod_inv_distrib]
                  rw [div_eq_mul_inv, hprod]
                  congr 1
                  simpa using (Finset.prod_natCast (s := G) (f := id) (R := ℝ))
    _ = finiteAvoidDensity F := by
          unfold finiteAvoidDensity
          refine Finset.sum_congr rfl ?_
          intro G hG
          have hGF : G ⊆ F := Finset.mem_powerset.mp hG
          have hlcm : ((lcm0 G : ℕ) : ℝ) = ((G.prod id : ℕ) : ℝ) := by
            exact congrArg (fun n : ℕ => (n : ℝ))
              (lcm0_eq_prod_of_pairwise_coprime (F := F) (G := G) hpair hGF)
          simpa [hlcm]

/-- The corollary's finite remainder `R_N` becomes an Euler product in the pairwise-coprime case. -/
theorem R_eq_prod_one_sub_of_pairwise_coprime
    (A : Set ℕ)
    (hpair : PairwiseCoprime (primitiveKernel A)) :
    ∀ N, R A N = ∏ a ∈ primitiveTrunc A N, (1 - 1 / (a : ℝ)) := by
  intro N
  have hpairN : PairwiseCoprime ((primitiveTrunc A N : Finset ℕ) : Set ℕ) := by
    unfold PairwiseCoprime at hpair ⊢
    exact Set.Pairwise.mono (trunc_subset (primitiveKernel A) N) hpair
  simpa [R] using
    (finiteAvoidDensity_eq_prod_one_sub_of_pairwise_coprime
      (F := primitiveTrunc A N) hpairN)

/-- Under `1 ∉ A^{prim}`, every element of `B_N` is at least `2`. -/
lemma one_lt_of_mem_primitiveTrunc_of_h1
    {A : Set ℕ} {N a : ℕ}
    (h1 : 1 ∉ primitiveKernel A)
    (ha : a ∈ primitiveTrunc A N) :
    1 < a := by
  have haPrim : a ∈ primitiveKernel A := trunc_subset (primitiveKernel A) N ha
  have hapos : 0 < a := haPrim.2.1
  have hne : a ≠ 1 := by
    intro h
    apply h1
    simpa [h] using haPrim
  exact lt_of_le_of_ne (Nat.succ_le_of_lt hapos) (Ne.symm hne)

lemma two_le_of_mem_primitiveTrunc_of_h1
    {A : Set ℕ} {N a : ℕ}
    (h1 : 1 ∉ primitiveKernel A)
    (ha : a ∈ primitiveTrunc A N) :
    2 ≤ a := by
  exact Nat.succ_le_of_lt (one_lt_of_mem_primitiveTrunc_of_h1 h1 ha)

/-- Positivity of the Euler factors in the pairwise-coprime remark. -/
lemma one_sub_inv_pos_of_mem_primitiveTrunc
    {A : Set ℕ} {N a : ℕ}
    (h1 : 1 ∉ primitiveKernel A)
    (ha : a ∈ primitiveTrunc A N) :
    0 < 1 - 1 / (a : ℝ) := by
  have ha_gt_one : (1 : ℝ) < a := by
    exact_mod_cast (one_lt_of_mem_primitiveTrunc_of_h1 h1 ha)
  have hapos : 0 < (a : ℝ) := by
    linarith
  have haminus : 0 < (a : ℝ) - 1 := by
    linarith
  have hrewrite : 1 - 1 / (a : ℝ) = ((a : ℝ) - 1) / (a : ℝ) := by
    field_simp [hapos.ne']
  rw [hrewrite]
  exact div_pos haminus hapos

/-- Quantitative logarithmic bounds for the Euler factors `1 - 1 / a` when `a ≥ 2`.

These are the two inequalities needed to compare `log R_N` with `-∑_{a ∈ B_N} 1 / a`. -/
lemma log_one_sub_inv_bounds_of_two_le {a : ℕ} (ha : 2 ≤ a) :
    -(2 : ℝ) / (a : ℝ) ≤ Real.log (1 - 1 / (a : ℝ)) ∧
      Real.log (1 - 1 / (a : ℝ)) ≤ -(1 : ℝ) / (a : ℝ) := by
  have ha_real : (2 : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast ha
  have ha1_nat : 1 < a := lt_of_lt_of_le (by decide : 1 < 2) ha
  have hapos_nat : 0 < a := lt_trans Nat.zero_lt_one ha1_nat
  have hapos : 0 < (a : ℝ) := by
    exact_mod_cast hapos_nat
  have haminus : 0 < (a : ℝ) - 1 := by
    linarith
  have hrewrite : 1 - 1 / (a : ℝ) = ((a : ℝ) - 1) / (a : ℝ) := by
    field_simp [ne_of_gt hapos]
  have hx : 0 < 1 - 1 / (a : ℝ) := by
    rw [hrewrite]
    exact div_pos haminus hapos
  constructor
  · have hlog :
        1 - (1 - 1 / (a : ℝ))⁻¹ ≤ Real.log (1 - 1 / (a : ℝ)) :=
      Real.one_sub_inv_le_log_of_pos hx
    have hfrac :
        (1 : ℝ) / ((a : ℝ) - 1) ≤ 2 / (a : ℝ) := by
      rw [div_le_div_iff₀ haminus hapos]
      nlinarith [ha_real]
    have hdivne : ((a : ℝ) - 1) / (a : ℝ) ≠ 0 := by
      exact div_ne_zero (ne_of_gt haminus) (ne_of_gt hapos)
    have hleft :
        1 - (1 - 1 / (a : ℝ))⁻¹ = -(1 : ℝ) / ((a : ℝ) - 1) := by
      rw [hrewrite]
      field_simp [hdivne, ne_of_gt hapos, ne_of_gt haminus]
      ring
    have hlog' :
        -(1 : ℝ) / ((a : ℝ) - 1) ≤ Real.log (1 - 1 / (a : ℝ)) := by
      rw [hleft] at hlog
      exact hlog
    have hnegfrac : -(2 : ℝ) / (a : ℝ) ≤ -(1 : ℝ) / ((a : ℝ) - 1) := by
      simpa [neg_div] using (neg_le_neg hfrac)
    exact le_trans hnegfrac hlog'
  · calc
      Real.log (1 - 1 / (a : ℝ)) ≤ (1 - 1 / (a : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos hx
      _ = -(1 : ℝ) / (a : ℝ) := by ring_nf

lemma sum_log_lower_bound
    (A : Set ℕ) (N : ℕ)
    (h1 : 1 ∉ primitiveKernel A) :
    -(2 : ℝ) * (∑ a ∈ primitiveTrunc A N, (1 : ℝ) / (a : ℝ))
      ≤ ∑ a ∈ primitiveTrunc A N, Real.log (1 - 1 / (a : ℝ)) := by
  classical
  calc
    -(2 : ℝ) * (∑ a ∈ primitiveTrunc A N, (1 : ℝ) / (a : ℝ))
        = ∑ a ∈ primitiveTrunc A N, (-(2 : ℝ) / (a : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro a ha
            ring
    _ ≤ ∑ a ∈ primitiveTrunc A N, Real.log (1 - 1 / (a : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact (log_one_sub_inv_bounds_of_two_le
            (two_le_of_mem_primitiveTrunc_of_h1 h1 ha)).1

lemma sum_log_upper_bound
    (A : Set ℕ) (N : ℕ)
    (h1 : 1 ∉ primitiveKernel A) :
    ∑ a ∈ primitiveTrunc A N, Real.log (1 - 1 / (a : ℝ))
      ≤ - (∑ a ∈ primitiveTrunc A N, (1 : ℝ) / (a : ℝ)) := by
  classical
  calc
    ∑ a ∈ primitiveTrunc A N, Real.log (1 - 1 / (a : ℝ))
        ≤ ∑ a ∈ primitiveTrunc A N, (-(1 : ℝ) / (a : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro a ha
            exact (log_one_sub_inv_bounds_of_two_le
              (two_le_of_mem_primitiveTrunc_of_h1 h1 ha)).2
    _ = - (∑ a ∈ primitiveTrunc A N, (1 : ℝ) / (a : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro a ha
          ring

/-- Rewrite the finite Euler product as an exponential of a finite logarithmic sum. -/
lemma R_eq_exp_sum_log_of_pairwise_coprime
    (A : Set ℕ)
    (h1 : 1 ∉ primitiveKernel A)
    (hpair : PairwiseCoprime (primitiveKernel A))
    (N : ℕ) :
    R A N = Real.exp
      (Finset.sum (primitiveTrunc A N) (fun a => Real.log (1 - 1 / (a : ℝ)))) := by
  calc
    R A N = ∏ a ∈ primitiveTrunc A N, (1 - 1 / (a : ℝ)) :=
      R_eq_prod_one_sub_of_pairwise_coprime A hpair N
    _ = ∏ a ∈ primitiveTrunc A N, Real.exp (Real.log (1 - 1 / (a : ℝ))) := by
          refine Finset.prod_congr rfl ?_
          intro a ha
          rw [Real.exp_log (one_sub_inv_pos_of_mem_primitiveTrunc h1 ha)]
    _ = Real.exp
          (Finset.sum (primitiveTrunc A N) (fun a => Real.log (1 - 1 / (a : ℝ)))) := by
          symm
          simpa using
            (Real.exp_sum (primitiveTrunc A N) (fun a => Real.log (1 - 1 / (a : ℝ))))

/-- **Remark 4** (pairwise coprime case) from the revised TeX note, in partial-sum form.

This is the formal version of
`M_A has density 1 ↔ ∑_{a ∈ A^{prim} ∩ [1,N]} 1 / a → ∞`
under the assumptions that `1 ∉ A^{prim}` and the elements of `A^{prim}` are pairwise coprime. -/
theorem behrend_iff_primitiveRecipPartialSums_tendsto_atTop_of_pairwise_coprime
    (A : Set ℕ)
    (h1 : 1 ∉ primitiveKernel A)
    (hpair : PairwiseCoprime (primitiveKernel A)) :
    IsBehrend A ↔
      Tendsto (fun N : ℕ => Finset.sum (primitiveTrunc A N) (fun a => (1 : ℝ) / (a : ℝ)))
        Filter.atTop Filter.atTop := by
  let S : ℕ → ℝ := fun N => Finset.sum (primitiveTrunc A N) (fun a => (1 : ℝ) / (a : ℝ))
  let L : ℕ → ℝ := fun N =>
    Finset.sum (primitiveTrunc A N) (fun a => Real.log (1 - 1 / (a : ℝ)))
  change IsBehrend A ↔ Tendsto S Filter.atTop Filter.atTop
  constructor
  · intro hA
    have hR : Tendsto (R A) Filter.atTop (nhds 0) :=
      (behrend_iff_R_tendsto_zero A).1 hA
    have hExp : Tendsto (fun N => Real.exp (L N)) Filter.atTop (nhds 0) := by
      refine Tendsto.congr' ?_ hR
      exact Filter.Eventually.of_forall (fun N => by
        simp [L, R_eq_exp_sum_log_of_pairwise_coprime, h1, hpair])
    have hL : Tendsto L Filter.atTop atBot :=
      Real.tendsto_exp_comp_nhds_zero.mp hExp
    have hnegTwoS : Tendsto (fun N => (-2 : ℝ) * S N) Filter.atTop atBot := by
      apply Filter.tendsto_atBot_mono
      · intro N
        simpa [S, L] using sum_log_lower_bound A N h1
      · simpa [L] using hL
    have hS' :
        Tendsto (fun N => (-(1 / 2 : ℝ)) * (((-2 : ℝ) * S N))) Filter.atTop Filter.atTop :=
      (tendsto_const_mul_atTop_of_neg
        (l := Filter.atTop) (f := fun N => (-2 : ℝ) * S N) (r := -(1 / 2 : ℝ))
        (by norm_num)).2 hnegTwoS
    convert hS' using 1
    ext N
    ring_nf
  · intro hS
    have hnegS : Tendsto (fun N => (-1 : ℝ) * S N) Filter.atTop atBot :=
      (tendsto_const_mul_atBot_of_neg
        (l := Filter.atTop) (f := S) (r := (-1 : ℝ)) (by norm_num)).2 hS
    have hL : Tendsto L Filter.atTop atBot := by
      apply Filter.tendsto_atBot_mono
      · intro N
        simpa [S, L] using sum_log_upper_bound A N h1
      · simpa [S] using hnegS
    have hExp : Tendsto (fun N => Real.exp (L N)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hL
    have hR : Tendsto (R A) Filter.atTop (nhds 0) := by
      refine Tendsto.congr' ?_ hExp
      exact Filter.Eventually.of_forall (fun N => by
        symm
        simp [L, R_eq_exp_sum_log_of_pairwise_coprime, h1, hpair])
    exact (behrend_iff_R_tendsto_zero A).2 hR

/-- **Remark 4** again, now in "divergent reciprocal series" form.

Because `primitiveRecipSeq A` is the indicator reciprocal sequence of `A^{prim}`, this is the Lean
version of
`M_A has density 1 ↔ ∑_{a ∈ A^{prim}} 1 / a = ∞`
under the pairwise-coprime hypothesis. -/
theorem behrend_iff_not_summable_primitiveRecipSeq_of_pairwise_coprime
    (A : Set ℕ)
    (h1 : 1 ∉ primitiveKernel A)
    (hpair : PairwiseCoprime (primitiveKernel A)) :
    IsBehrend A ↔ ¬ Summable (primitiveRecipSeq A) := by
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := primitiveRecipSeq A) (by intro n; exact primitiveRecipSeq_nonneg A n)]
  let P : ℕ → ℝ := fun N => Finset.sum (Finset.range N) (primitiveRecipSeq A)
  have hshift :
      Tendsto (fun N : ℕ => P (N + 1)) Filter.atTop Filter.atTop
        ↔ Tendsto P Filter.atTop Filter.atTop := by
    simpa [P] using (tendsto_add_atTop_iff_nat (f := P) 1)
  constructor
  · intro hA
    have hmain :
        Tendsto (fun N : ℕ => Finset.sum (primitiveTrunc A N) (fun a => (1 : ℝ) / (a : ℝ)))
          Filter.atTop Filter.atTop :=
      (behrend_iff_primitiveRecipPartialSums_tendsto_atTop_of_pairwise_coprime
        A h1 hpair).1 hA
    have hmain' :
        Tendsto (fun N : ℕ => P (N + 1)) Filter.atTop Filter.atTop := by
      simpa [P, sum_range_succ_primitiveRecipSeq_eq] using hmain
    exact hshift.mp hmain'
  · intro hP
    have hP' : Tendsto (fun N : ℕ => P (N + 1)) Filter.atTop Filter.atTop :=
      hshift.mpr hP
    have hmain :
        Tendsto (fun N : ℕ => Finset.sum (primitiveTrunc A N) (fun a => (1 : ℝ) / (a : ℝ)))
          Filter.atTop Filter.atTop := by
      simpa [P, sum_range_succ_primitiveRecipSeq_eq] using hP'
    exact (behrend_iff_primitiveRecipPartialSums_tendsto_atTop_of_pairwise_coprime
      A h1 hpair).2 hmain

end PairwiseCoprimeRemark

#print axioms Erdos691.tex_thm_finite_approx
-- 'Erdos691.tex_thm_finite_approx' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos691
