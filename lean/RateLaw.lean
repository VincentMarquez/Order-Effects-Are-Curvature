/-
  Consensus Curvature — the commutator rate law, formalized.
  Theorem: for row-stochastic A₁ A₂ with Dobrushin coefficients τᵢ < 1 and
  stationary vectors πᵢ:  ‖π₁ − π₂‖₁ ≤ ‖[A₁,A₂]‖∞ / ((1−τ₁)(1−τ₂)).

  Statement is PAPER-LITERAL: dob(A) = (1/2)·max_{i,i'} Σⱼ|Aᵢⱼ−Aᵢ'ⱼ| and
  ‖M‖∞ = max_i Σⱼ|Mᵢⱼ| are defined below, and `rate_law` is Theorem E
  verbatim. The bounds-style core it wraps (τ, Cb as hypotheses — fully
  general, and how the proof actually runs) is kept as
  `rate_law_of_bounds`.
  Proof is FINITARY: two one-step recursions with fixed-point invariants,
  a k-step contraction, and an ε-squeeze by contradiction. No limits.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

open Finset BigOperators

namespace RateLaw

variable {n : ℕ}

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Fin n → Fin n → ℝ

def vmul (w : Vec n) (A : Mat n) : Vec n := fun j => ∑ i, w i * A i j
def mmul (A B : Mat n) : Mat n := fun i k => ∑ j, A i j * B j k
def l1 (w : Vec n) : ℝ := ∑ j, |w j|
def rowStoch (A : Mat n) : Prop := (∀ i j, 0 ≤ A i j) ∧ ∀ i, ∑ j, A i j = 1

/-- k-fold application of `vmul · A`. -/
def itv (w : Vec n) (A : Mat n) : ℕ → Vec n
  | 0 => w
  | k + 1 => vmul (itv w A k) A

/- ### Basic algebra -/

lemma vmul_sub (w v : Vec n) (A : Mat n) :
    vmul (w - v) A = vmul w A - vmul v A := by
  funext j; simp [vmul, sub_mul, Finset.sum_sub_distrib]

lemma vmul_matsub (w : Vec n) (M N : Mat n) :
    vmul w (fun i k => M i k - N i k) = vmul w M - vmul w N := by
  funext j; simp [vmul, mul_sub, Finset.sum_sub_distrib]

lemma vmul_assoc (w : Vec n) (A B : Mat n) :
    vmul (vmul w A) B = vmul w (mmul A B) := by
  funext k
  simp only [vmul, mmul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma sum_vmul (w : Vec n) {A : Mat n} (hA : rowStoch A) :
    ∑ j, vmul w A j = ∑ i, w i := by
  simp only [vmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, hA.2 i, mul_one]

lemma l1_nonneg (w : Vec n) : 0 ≤ l1 w :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1_zero : l1 (0 : Vec n) = 0 := by simp [l1]

lemma l1_add_le (w v : Vec n) : l1 (w + v) ≤ l1 w + l1 v := by
  rw [l1, l1, l1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => abs_add_le _ _

... (file continues)
