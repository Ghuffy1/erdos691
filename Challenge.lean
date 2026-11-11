import Erdos691

/-!
Independent statement bridge for the all-A arithmetic criterion.
The data and hypotheses below are spelled out without using AdmissibleTest.
-/

open Filter Set
open scoped BigOperators Topology Classical

namespace Erdos691Audit

def PositiveMultiples (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ a ∈ A, 0 < a ∧ a ∣ n}

def DensityOne (A : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ =>
    ((((Finset.Icc 1 (N + 1)).filter (fun n => n ∈ PositiveMultiples A)).card : ℝ) /
      (N + 1 : ℝ))) atTop (𝓝 1)

noncomputable def PrimePrefix (l n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range l, (Nat.nth Nat.Prime i) ^ n.factorization (Nat.nth Nat.Prime i)

def Supported (lo hi n : ℕ) : Prop :=
  0 < n ∧ ∀ p ∈ n.primeFactors, ∃ i, lo ≤ i ∧ i < hi ∧ Nat.nth Nat.Prime i = p

noncomputable def NewFactors (S : Finset ℕ) (l m : ℕ) : Finset ℕ :=
  (S.filter (fun a => PrimePrefix l a = m)).image (fun a => a / m)

def TestsMeet (A : Set ℕ) : Prop :=
  ∀ (l : ℕ → ℕ) (S : ℕ → Finset ℕ),
    StrictMono l →
    S 0 = {1} →
    (∀ k, ∀ m ∈ S k, Supported (l 0) (l k) m) →
    (∀ k, ∀ m ∈ S k, ∀ d, 0 < d → d ∣ m → d ∈ S k) →
    (∀ k, ∀ m ∈ S (k + 1), PrimePrefix (l k) m ∈ S k) →
    (∀ k, ∀ m ∈ S k,
      1 - (1 : ℝ) / 2 ^ (k + 3) ≤
        (∏ i ∈ Finset.Ico (l k) (l (k + 1)), (1 - (1 : ℝ) / Nat.nth Nat.Prime i)) *
          ∑ n ∈ NewFactors (S (k + 1)) (l k) m, (1 : ℝ) / n) →
    ∃ k, ∃ m ∈ S k, m ∈ A

def IntendedStatement : Prop := ∀ A : Set ℕ, DensityOne A ↔ TestsMeet A

theorem density_bridge (A : Set ℕ) : DensityOne A ↔ Erdos691.Adaptive.HasMultiplesDensityOne A := by
  rfl

theorem test_bridge (A : Set ℕ) : TestsMeet A ↔ Erdos691.Adaptive.MeetsEveryTest A := by
  constructor
  · intro h T
    exact h T.cutoff T.level T.increasing T.start T.supported T.downward T.projects T.retention
  · intro h l S hl hS0 hs hd hp hr
    let T : Erdos691.Adaptive.AdmissibleTest :=
      { cutoff := l, increasing := hl, level := S, start := hS0,
        supported := hs, downward := hd, projects := hp, retention := hr }
    exact h T

theorem original_statement_verified : IntendedStatement := by
  intro A
  rw [density_bridge, test_bridge]
  exact Erdos691.Adaptive.erdos691 A

example : IntendedStatement := original_statement_verified

#check @Erdos691.Adaptive.erdos691
#check @Erdos691.Adaptive.fullSolution
#check @original_statement_verified
#print axioms Erdos691.Adaptive.erdos691
#print axioms Erdos691.Adaptive.fullSolution
#print axioms original_statement_verified

end Erdos691Audit
