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

lemma l1_triangle (a b c : Vec n) : l1 (a - c) ≤ l1 (a - b) + l1 (b - c) := by
  have h : a - c = (a - b) + (b - c) := by abel
  rw [h]; exact l1_add_le _ _

lemma l1_neg (w : Vec n) : l1 (-w) = l1 w := by
  rw [l1, l1]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.neg_apply, abs_neg]

lemma l1_sub_le (w v : Vec n) : l1 (w - v) ≤ l1 w + l1 v := by
  have h : w - v = w + (-v) := by abel
  rw [h]
  exact (l1_add_le _ _).trans (by rw [l1_neg])

lemma l1_sub_comm (w v : Vec n) : l1 (w - v) = l1 (v - w) := by
  have h : v - w = -(w - v) := by abel
  rw [h, l1_neg]

/-- Row-stochastic matrices are ℓ¹-nonexpansive on all row vectors. -/
lemma l1_vmul_le (w : Vec n) {A : Mat n} (hA : rowStoch A) :
    l1 (vmul w A) ≤ l1 w := by
  calc l1 (vmul w A) = ∑ j, |∑ i, w i * A i j| := rfl
    _ ≤ ∑ j, ∑ i, |w i| * A i j := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hA.1 i j)]
    _ = ∑ i, |w i| * ∑ j, A i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = l1 w := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hA.2 i, mul_one]

/-- Generic row-sum bound: if every row of M has ℓ¹ mass ≤ c then
    ‖wM‖₁ ≤ c‖w‖₁ (for c ≥ 0). -/
lemma l1_vmul_gen (w : Vec n) (M : Mat n) {c : ℝ} (_hc : 0 ≤ c)
    (hM : ∀ i, ∑ j, |M i j| ≤ c) : l1 (vmul w M) ≤ c * l1 w := by
  calc l1 (vmul w M) ≤ ∑ j, ∑ i, |w i| * |M i j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun i _ => le_of_eq (abs_mul _ _)
    _ = ∑ i, |w i| * ∑ j, |M i j| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, |w i| * c :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hM i) (abs_nonneg _)
    _ = c * l1 w := by rw [l1, ← Finset.sum_mul, mul_comm]

/- ### The Dobrushin contraction (M1) -/

/-- Zero-sum row vectors contract by τ whenever all row pairs of A are
    within 2τ in ℓ¹.  The classical pairing proof, made finite. -/
theorem dobrushin_contract {A : Mat n} (hA : rowStoch A) {τ : ℝ}
    (hτ : ∀ i i', ∑ j, |A i j - A i' j| ≤ 2 * τ)
    {w : Vec n} (hw : ∑ i, w i = 0) :
    l1 (vmul w A) ≤ τ * l1 w := by
  classical
  set P : Finset (Fin n) := Finset.univ.filter (fun i => 0 ≤ w i) with hP
  set N : Finset (Fin n) := Finset.univ.filter (fun i => ¬ 0 ≤ w i) with hN
  set S : ℝ := ∑ i ∈ P, w i with hS
  have hsplit : ∀ f : Fin n → ℝ, ∑ i, f i = ∑ i ∈ P, f i + ∑ i ∈ N, f i := by
    intro f
    rw [hP, hN, Finset.sum_filter_add_sum_filter_not]
  have hNsum : ∑ i ∈ N, w i = -S := by
    have := hsplit w; rw [hw] at this; linarith
  have habs : l1 w = 2 * S := by
    have h1 : ∑ i ∈ P, |w i| = ∑ i ∈ P, w i :=
      Finset.sum_congr rfl fun i hi => abs_of_nonneg (by
        simpa [hP] using (Finset.mem_filter.mp hi).2)
    have h2 : ∑ i ∈ N, |w i| = ∑ i ∈ N, (-(w i)) :=
      Finset.sum_congr rfl fun i hi => abs_of_neg (by
        have := (Finset.mem_filter.mp hi).2
        simpa [hN] using lt_of_not_ge (by simpa [hP] using this))
    have := hsplit (fun i => |w i|)
    rw [l1, this, h1, h2, Finset.sum_neg_distrib, hNsum]
    ring
  have hS0 : 0 ≤ S :=
    Finset.sum_nonneg fun i hi => by simpa [hP] using (Finset.mem_filter.mp hi).2
  rcases eq_or_lt_of_le hS0 with hS0' | hSpos
  · -- S = 0 ⇒ w = 0 ⇒ trivial
    have hl1 : l1 w = 0 := by rw [habs, ← hS0']; ring
    have hw0 : ∀ j, w j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => abs_nonneg (w i))).mp hl1 j (Finset.mem_univ j)
      exact abs_eq_zero.mp this
    have : vmul w A = 0 := by
      funext j; simp [vmul, hw0]
    rw [this, l1_zero, hl1, mul_zero]
  · -- S > 0: the pairing identity, multiplied through by S
    have hNneg : ∑ i' ∈ N, (-(w i')) = S := by
      rw [Finset.sum_neg_distrib, hNsum, neg_neg]
    have keyR : ∀ j, ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * (A i j - A i' j)
        = S * (vmul w A j) := by
      intro j
      have hA1 : ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * A i j
          = S * ∑ i ∈ P, w i * A i j := by
        calc ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * A i j
            = ∑ i ∈ P, (w i * A i j) * ∑ i' ∈ N, (-(w i')) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i' _ => by ring
          _ = ∑ i ∈ P, (w i * A i j) * S := by rw [hNneg]
          _ = S * ∑ i ∈ P, w i * A i j := by
              rw [← Finset.sum_mul, mul_comm]
      have hA2 : ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * A i' j
          = S * (-(∑ i' ∈ N, w i' * A i' j)) := by
        calc ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * A i' j
            = ∑ i ∈ P, w i * ∑ i' ∈ N, (-(w i' * A i' j)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i' _ => by ring
          _ = ∑ i ∈ P, w i * (-(∑ i' ∈ N, w i' * A i' j)) := by
              rw [Finset.sum_neg_distrib]
          _ = (∑ i ∈ P, w i) * (-(∑ i' ∈ N, w i' * A i' j)) := by
              rw [← Finset.sum_mul]
          _ = S * (-(∑ i' ∈ N, w i' * A i' j)) := by rw [← hS]
      have hsplitv : vmul w A j
          = ∑ i ∈ P, w i * A i j + ∑ i' ∈ N, w i' * A i' j := by
        rw [vmul, hsplit (fun i => w i * A i j)]
      calc ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * (A i j - A i' j)
          = ∑ i ∈ P, (∑ i' ∈ N, (w i * (-(w i'))) * A i j
              - ∑ i' ∈ N, (w i * (-(w i'))) * A i' j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i' _ => by ring
        _ = (∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * A i j)
            - ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * A i' j := by
            rw [Finset.sum_sub_distrib]
        _ = S * ∑ i ∈ P, w i * A i j
            - S * (-(∑ i' ∈ N, w i' * A i' j)) := by rw [hA1, hA2]
        _ = S * (vmul w A j) := by rw [hsplitv]; ring
    have step : S * l1 (vmul w A) ≤ S * (τ * l1 w) := by
      have lhs : S * l1 (vmul w A) = ∑ j, |S * vmul w A j| := by
        rw [l1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [abs_mul, abs_of_nonneg hS0]
      rw [lhs]
      have bound1 : ∀ j, |S * vmul w A j| ≤
          ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * |A i j - A i' j| := by
        intro j
        rw [← keyR j]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i hi => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i' hi' => ?_
        have hwi : 0 ≤ w i := by simpa [hP] using (Finset.mem_filter.mp hi).2
        have hwi' : 0 ≤ -(w i') := by
          have hmem := (Finset.mem_filter.mp hi').2
          have : w i' < 0 := lt_of_not_ge (by simpa [hN] using hmem)
          linarith
        rw [abs_mul, abs_of_nonneg (mul_nonneg hwi hwi')]
      calc ∑ j, |S * vmul w A j|
          ≤ ∑ j, ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * |A i j - A i' j| :=
            Finset.sum_le_sum fun j _ => bound1 j
        _ = ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * ∑ j, |A i j - A i' j| := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i' _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ i ∈ P, ∑ i' ∈ N, (w i * (-(w i'))) * (2 * τ) := by
            refine Finset.sum_le_sum fun i hi => ?_
            refine Finset.sum_le_sum fun i' hi' => ?_
            have hwi : 0 ≤ w i := by simpa [hP] using (Finset.mem_filter.mp hi).2
            have hwi' : 0 ≤ -(w i') := by
              have hmem := (Finset.mem_filter.mp hi').2
              have : w i' < 0 := lt_of_not_ge (by simpa [hN] using hmem)
              linarith
            exact mul_le_mul_of_nonneg_left (hτ i i') (mul_nonneg hwi hwi')
        _ = ∑ i ∈ P, (w i * (2 * τ)) * ∑ i' ∈ N, (-(w i')) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i' _ => by ring
        _ = ∑ i ∈ P, (w i * (2 * τ)) * S := by rw [hNneg]
        _ = ((∑ i ∈ P, w i) * (2 * τ)) * S := by
            rw [Finset.sum_mul, Finset.sum_mul]
        _ = S * (τ * l1 w) := by rw [← hS, habs]; ring
    exact le_of_mul_le_mul_left step hSpos

/- ### Iterates -/

lemma itv_fixed {w : Vec n} {A : Mat n} (hs : vmul w A = w) :
    ∀ k, itv w A k = w
  | 0 => rfl
  | k + 1 => by rw [itv, itv_fixed hs k, hs]

lemma itv_sub (x y : Vec n) (A : Mat n) :
    ∀ k, itv (x - y) A k = itv x A k - itv y A k
  | 0 => rfl
  | k + 1 => by rw [itv, itv_sub x y A k, vmul_sub, itv, itv]

lemma sum_itv {w : Vec n} {A : Mat n} (hA : rowStoch A) :
    ∀ k, ∑ j, itv w A k j = ∑ i, w i
  | 0 => rfl
  | k + 1 => by rw [itv, sum_vmul _ hA, sum_itv hA k]

lemma l1_itv_zero_sum {z : Vec n} {A : Mat n} (hA : rowStoch A) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : ∀ i i', ∑ j, |A i j - A i' j| ≤ 2 * τ)
    (hz : ∑ i, z i = 0) :
    ∀ k, l1 (itv z A k) ≤ τ ^ k * l1 z
  | 0 => by simp [itv]
  | k + 1 => by
      have hzk : ∑ i, itv z A k i = 0 := by rw [sum_itv hA k, hz]
      calc l1 (itv z A (k + 1)) = l1 (vmul (itv z A k) A) := rfl
        _ ≤ τ * l1 (itv z A k) := dobrushin_contract hA hτ hzk
        _ ≤ τ * (τ ^ k * l1 z) :=
            mul_le_mul_of_nonneg_left (l1_itv_zero_sum hA hτ0 hτ hz k) hτ0
        _ = τ ^ (k + 1) * l1 z := by ring

/-- Elementary: powers of r < 1 drop below any ε > 0 (Bernoulli + archimedean). -/
lemma pow_small {r ε : ℝ} (hε : 0 < ε) (hr : r < 1) : ∃ N : ℕ, r ^ N < ε := by
  by_cases h0 : r ≤ 0
  · exact ⟨1, by simpa using lt_of_le_of_lt h0 hε⟩
  · push_neg at h0
    have hinv : 1 < 1 / r := (one_lt_div h0).mpr hr
    set a : ℝ := 1 / r - 1 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 / ε - 1) / a)
    refine ⟨N, ?_⟩
    have hb : 1 / ε < 1 + (N : ℝ) * a := by
      have h2 : 1 / ε - 1 < (N : ℝ) * a := (div_lt_iff₀ ha0).mp hN
      linarith
    have hpow : 1 + (N : ℝ) * a ≤ (1 / r) ^ N := by
      have h := one_add_mul_le_pow (a := a) (by linarith : (-2 : ℝ) ≤ a) N
      have hra : (1 + a) = 1 / r := by rw [ha]; ring
      rw [hra] at h
      linarith [h]
    have hεr : 1 / ε < (1 / r) ^ N := lt_of_lt_of_le hb hpow
    have hrN : (0 : ℝ) < (1 / r) ^ N := pow_pos (one_div_pos.mpr h0) N
    have hrw : r ^ N = 1 / (1 / r) ^ N := by
      rw [one_div, ← inv_pow, one_div, inv_inv]
    rw [hrw, div_lt_iff₀ hrN]
    calc (1 : ℝ) = ε * (1 / ε) := by field_simp
      _ < ε * (1 / r) ^ N := mul_lt_mul_of_pos_left hεr hε

/- ### The main theorem -/

theorem rate_law_of_bounds
    (A₁ A₂ : Mat n) (h₁ : rowStoch A₁) (h₂ : rowStoch A₂)
    (τ₁ τ₂ : ℝ) (hτ₁0 : 0 ≤ τ₁) (hτ₂0 : 0 ≤ τ₂)
    (hτ₁1 : τ₁ < 1) (hτ₂1 : τ₂ < 1)
    (hd₁ : ∀ i i', ∑ j, |A₁ i j - A₁ i' j| ≤ 2 * τ₁)
    (hd₂ : ∀ i i', ∑ j, |A₂ i j - A₂ i' j| ≤ 2 * τ₂)
    (π₁ π₂ : Vec n)
    (hp₁ : (∀ j, 0 ≤ π₁ j) ∧ ∑ j, π₁ j = 1)
    (hp₂ : (∀ j, 0 ≤ π₂ j) ∧ ∑ j, π₂ j = 1)
    (hs₁ : vmul π₁ A₁ = π₁) (hs₂ : vmul π₂ A₂ = π₂)
    (Cb : ℝ) (hCb0 : 0 ≤ Cb)
    (hC : ∀ i, ∑ j, |mmul A₁ A₂ i j - mmul A₂ A₁ i j| ≤ Cb) :
    l1 (π₁ - π₂) ≤ Cb / ((1 - τ₁) * (1 - τ₂)) := by
  classical
  set γ₁ : ℝ := 1 - τ₁ with hγ₁
  set γ₂ : ℝ := 1 - τ₂ with hγ₂
  have hγ₁pos : 0 < γ₁ := by rw [hγ₁]; linarith
  have hγ₂pos : 0 < γ₂ := by rw [hγ₂]; linarith
  set Cmat : Mat n := fun i k => mmul A₁ A₂ i k - mmul A₂ A₁ i k with hCmat
  set v : ℕ → Vec n := itv π₁ A₂ with hv
  set D : ℝ := l1 (π₁ - π₂) with hD
  have hD0 : 0 ≤ D := l1_nonneg _
  have hl1π₁ : l1 π₁ = 1 := by
    rw [l1]
    rw [show ∑ j, |π₁ j| = ∑ j, π₁ j from
      Finset.sum_congr rfl fun j _ => abs_of_nonneg (hp₁.1 j)]
    exact hp₁.2
  have hl1v : ∀ k, l1 (v k) ≤ 1 := by
    intro k; induction k with
    | zero => rw [hv]; exact le_of_eq hl1π₁
    | succ k ih =>
        calc l1 (v (k+1)) = l1 (vmul (v k) A₂) := rfl
          _ ≤ l1 (v k) := l1_vmul_le _ h₂
          _ ≤ 1 := ih
  have hB : ∀ k, l1 (v k - vmul (v k) A₁) ≤ Cb / γ₂ := by
    intro k; induction k with
    | zero =>
        have : v 0 - vmul (v 0) A₁ = 0 := by
          rw [hv]; show π₁ - vmul π₁ A₁ = 0; rw [hs₁]; abel
        rw [this, l1_zero]
        exact div_nonneg hCb0 hγ₂pos.le
    | succ k ih =>
        have hrec : v (k+1) - vmul (v (k+1)) A₁
            = vmul (v k - vmul (v k) A₁) A₂ + vmul (v k) Cmat := by
          show vmul (v k) A₂ - vmul (vmul (v k) A₂) A₁ = _
          rw [vmul_sub, hCmat, vmul_matsub, vmul_assoc, vmul_assoc]
          abel
        have hzs : ∑ i, (v k - vmul (v k) A₁) i = 0 := by
          have h1 : ∑ i, v k i = 1 := by rw [hv, sum_itv h₂, hp₁.2]
          have h2 : ∑ i, vmul (v k) A₁ i = 1 := by rw [sum_vmul _ h₁, h1]
          simp [Pi.sub_apply, Finset.sum_sub_distrib, h1, h2]
        calc l1 (v (k+1) - vmul (v (k+1)) A₁)
            = l1 (vmul (v k - vmul (v k) A₁) A₂ + vmul (v k) Cmat) := by rw [hrec]
          _ ≤ l1 (vmul (v k - vmul (v k) A₁) A₂) + l1 (vmul (v k) Cmat) :=
              l1_add_le _ _
          _ ≤ τ₂ * l1 (v k - vmul (v k) A₁) + Cb * l1 (v k) := by
              gcongr <;> first
                | exact dobrushin_contract h₂ hd₂ hzs
                | exact l1_vmul_gen _ _ hCb0 (by rw [hCmat]; exact hC)
          _ ≤ τ₂ * (Cb / γ₂) + Cb * 1 := by
              gcongr
              exact hl1v k
          _ = Cb / γ₂ := by field_simp [hγ₂pos.ne']; ring
  have hu : ∀ k, l1 (π₂ - vmul π₂ A₁) ≤ 2 * (τ₂ ^ k * D) + Cb / γ₂ := by
    intro k
    have hπ₂fix : itv π₂ A₂ k = π₂ := itv_fixed hs₂ k
    have hdiff : π₂ - v k = itv (π₂ - π₁) A₂ k := by
      rw [itv_sub, hπ₂fix, hv]
    have hzsum : ∑ i, (π₂ - π₁) i = 0 := by
      simp [Pi.sub_apply, Finset.sum_sub_distrib, hp₁.2, hp₂.2]
    have hgeom : l1 (π₂ - v k) ≤ τ₂ ^ k * D := by
      rw [hdiff]
      calc l1 (itv (π₂ - π₁) A₂ k) ≤ τ₂ ^ k * l1 (π₂ - π₁) :=
            l1_itv_zero_sum h₂ hτ₂0 hd₂ hzsum k
        _ = τ₂ ^ k * D := by
            rw [hD]
            congr 1
            rw [l1, l1]
            exact Finset.sum_congr rfl fun j _ => by
              rw [Pi.sub_apply, Pi.sub_apply, abs_sub_comm]
    have hdecomp : π₂ - vmul π₂ A₁
        = (π₂ - v k) - vmul (π₂ - v k) A₁ + (v k - vmul (v k) A₁) := by
      rw [vmul_sub]; abel
    calc l1 (π₂ - vmul π₂ A₁)
        ≤ l1 ((π₂ - v k) - vmul (π₂ - v k) A₁) + l1 (v k - vmul (v k) A₁) := by
          rw [hdecomp]; exact l1_add_le _ _
      _ ≤ (l1 (π₂ - v k) + l1 (vmul (π₂ - v k) A₁)) + Cb / γ₂ := by
          gcongr <;> first
            | exact l1_sub_le _ _
            | exact hB k
      _ ≤ (τ₂ ^ k * D + τ₂ ^ k * D) + Cb / γ₂ := by
          gcongr <;> first
            | exact (l1_vmul_le _ h₁).trans hgeom
            | exact hgeom
      _ = 2 * (τ₂ ^ k * D) + Cb / γ₂ := by ring
  have hDK : ∀ K, l1 (π₂ - itv π₂ A₁ K) ≤ l1 (π₂ - vmul π₂ A₁) / γ₁ := by
    intro K; induction K with
    | zero =>
        have : π₂ - itv π₂ A₁ 0 = 0 := by rw [itv]; abel
        rw [this, l1_zero]
        exact div_nonneg (l1_nonneg _) hγ₁pos.le
    | succ K ih =>
        have hrec : π₂ - itv π₂ A₁ (K+1)
            = (π₂ - vmul π₂ A₁) + vmul (π₂ - itv π₂ A₁ K) A₁ := by
          rw [itv, vmul_sub]; abel
        have hzs : ∑ i, (π₂ - itv π₂ A₁ K) i = 0 := by
          have h1 : ∑ i, itv π₂ A₁ K i = 1 := by rw [sum_itv h₁, hp₂.2]
          simp [Pi.sub_apply, Finset.sum_sub_distrib, hp₂.2, h1]
        calc l1 (π₂ - itv π₂ A₁ (K+1))
            ≤ l1 (π₂ - vmul π₂ A₁) + l1 (vmul (π₂ - itv π₂ A₁ K) A₁) := by
              rw [hrec]; exact l1_add_le _ _
          _ ≤ l1 (π₂ - vmul π₂ A₁) + τ₁ * l1 (π₂ - itv π₂ A₁ K) := by
              gcongr
              exact dobrushin_contract h₁ hd₁ hzs
          _ ≤ l1 (π₂ - vmul π₂ A₁) + τ₁ * (l1 (π₂ - vmul π₂ A₁) / γ₁) := by
              gcongr
          _ = l1 (π₂ - vmul π₂ A₁) / γ₁ := by field_simp [hγ₁pos.ne']; ring
  have hmain : ∀ k K,
      D ≤ (2 * (τ₂ ^ k * D) + Cb / γ₂) / γ₁ + τ₁ ^ K * D := by
    intro k K
    have hπ₁fix : itv π₁ A₁ K = π₁ := itv_fixed hs₁ K
    have hzsum : ∑ i, (π₂ - π₁) i = 0 := by
      simp [Pi.sub_apply, Finset.sum_sub_distrib, hp₁.2, hp₂.2]
    have htail : l1 (itv π₂ A₁ K - π₁) ≤ τ₁ ^ K * D := by
      have : itv π₂ A₁ K - π₁ = itv (π₂ - π₁) A₁ K := by
        rw [itv_sub, hπ₁fix]
      rw [this]
      calc l1 (itv (π₂ - π₁) A₁ K) ≤ τ₁ ^ K * l1 (π₂ - π₁) :=
            l1_itv_zero_sum h₁ hτ₁0 hd₁ hzsum K
        _ = τ₁ ^ K * D := by
            rw [hD]; congr 1
            rw [l1, l1]
            exact Finset.sum_congr rfl fun j _ => by
              rw [Pi.sub_apply, Pi.sub_apply, abs_sub_comm]
    calc D = l1 (π₁ - π₂) := hD
      _ ≤ l1 (π₁ - itv π₂ A₁ K) + l1 (itv π₂ A₁ K - π₂) := l1_triangle _ _ _
      _ = l1 (π₂ - itv π₂ A₁ K) + l1 (itv π₂ A₁ K - π₁) := by
          rw [l1_sub_comm (π₁) (itv π₂ A₁ K), l1_sub_comm (itv π₂ A₁ K) π₂]
          ring
      _ ≤ l1 (π₂ - vmul π₂ A₁) / γ₁ + τ₁ ^ K * D := by
          gcongr <;> first
            | exact hDK K
            | exact htail
      _ ≤ (2 * (τ₂ ^ k * D) + Cb / γ₂) / γ₁ + τ₁ ^ K * D := by
          gcongr
          exact hu k
  by_contra hcon
  push_neg at hcon
  set T : ℝ := Cb / (γ₁ * γ₂) with hT
  have hT0 : 0 ≤ T := by
    rw [hT]; exact div_nonneg hCb0 (mul_nonneg hγ₁pos.le hγ₂pos.le)
  set M : ℝ := 2 * D / γ₁ + D with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have h2D : 0 ≤ 2 * D := by linarith
    exact add_nonneg (div_nonneg h2D hγ₁pos.le) hD0
  set δ : ℝ := (D - T) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set ε : ℝ := δ / (M + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; exact div_pos hδpos (by linarith)
  obtain ⟨k, hk⟩ := pow_small hεpos hτ₂1
  obtain ⟨K, hK⟩ := pow_small hεpos hτ₁1
  have hDle : D ≤ T + δ := by
    have h := hmain k K
    have hchain : D ≤ (2 * (ε * D) + Cb / γ₂) / γ₁ + ε * D := by
      refine h.trans ?_
      gcongr <;> first
        | exact mul_le_mul_of_nonneg_right (le_of_lt hk) hD0
        | exact mul_le_mul_of_nonneg_right (le_of_lt hK) hD0
    have hexp : (2 * (ε * D) + Cb / γ₂) / γ₁ + ε * D = T + ε * M := by
      rw [hT, hM]; field_simp [hγ₁pos.ne', hγ₂pos.ne']; ring
    rw [hexp] at hchain
    have hεM : ε * M ≤ δ := by
      rw [hε]
      rw [div_mul_eq_mul_div]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < M + 1)]
      nlinarith
    linarith
  rw [hδ] at hDle
  linarith

/- ### Paper-literal statement (Theorem E verbatim) -/

/-- The Dobrushin ergodicity coefficient, exactly as in the paper:
    `dob A = (1/2) · max_{i,i'} Σⱼ |A i j − A i' j|`.
    (Over `Fin 0` the supremum of the empty family is `0`.) -/
noncomputable def dob (A : Mat n) : ℝ :=
  (1 / 2) * ⨆ p : Fin n × Fin n, ∑ j, |A p.1 j - A p.2 j|

/-- The row-sup matrix norm `‖M‖∞ = max_i Σⱼ |M i j|`. -/
noncomputable def normInf (M : Mat n) : ℝ := ⨆ i, ∑ j, |M i j|

/-- The commutator `[A,B] = AB − BA`. -/
def comm (A B : Mat n) : Mat n := fun i k => mmul A B i k - mmul B A i k

lemma dob_nonneg (A : Mat n) : 0 ≤ dob A := by
  have h : 0 ≤ ⨆ p : Fin n × Fin n, ∑ j, |A p.1 j - A p.2 j| :=
    Real.iSup_nonneg fun p => Finset.sum_nonneg fun j _ => abs_nonneg _
  unfold dob; linarith

lemma dob_pair_le (A : Mat n) (i i' : Fin n) :
    ∑ j, |A i j - A i' j| ≤ 2 * dob A := by
  have hb : BddAbove (Set.range fun p : Fin n × Fin n => ∑ j, |A p.1 j - A p.2 j|) :=
    (Set.finite_range _).bddAbove
  have h := le_ciSup hb (i, i')
  unfold dob; linarith

lemma row_le_normInf (M : Mat n) (i : Fin n) : ∑ j, |M i j| ≤ normInf M := by
  have hb : BddAbove (Set.range fun i : Fin n => ∑ j, |M i j|) :=
    (Set.finite_range _).bddAbove
  exact le_ciSup hb i

lemma normInf_nonneg (M : Mat n) : 0 ≤ normInf M :=
  Real.iSup_nonneg fun i => Finset.sum_nonneg fun j _ => abs_nonneg _

/-- The Dobrushin contraction in the paper's constants. -/
theorem dobrushin_contract' {A : Mat n} (hA : rowStoch A)
    {w : Vec n} (hw : ∑ i, w i = 0) :
    l1 (vmul w A) ≤ dob A * l1 w :=
  dobrushin_contract hA (dob_pair_le A) hw

/-- **Theorem E of the paper, verbatim**: for scrambling row-stochastic
    chains (`dob Aᵢ < 1`) with stationary probability vectors `πᵢ`,
    `‖π₁ − π₂‖₁ ≤ ‖[A₁,A₂]‖∞ / ((1 − τ(A₁))(1 − τ(A₂)))`. -/
theorem rate_law
    (A₁ A₂ : Mat n) (h₁ : rowStoch A₁) (h₂ : rowStoch A₂)
    (hτ₁ : dob A₁ < 1) (hτ₂ : dob A₂ < 1)
    (π₁ π₂ : Vec n)
    (hp₁ : (∀ j, 0 ≤ π₁ j) ∧ ∑ j, π₁ j = 1)
    (hp₂ : (∀ j, 0 ≤ π₂ j) ∧ ∑ j, π₂ j = 1)
    (hs₁ : vmul π₁ A₁ = π₁) (hs₂ : vmul π₂ A₂ = π₂) :
    l1 (π₁ - π₂) ≤ normInf (comm A₁ A₂) / ((1 - dob A₁) * (1 - dob A₂)) :=
  rate_law_of_bounds A₁ A₂ h₁ h₂ (dob A₁) (dob A₂)
    (dob_nonneg A₁) (dob_nonneg A₂) hτ₁ hτ₂
    (dob_pair_le A₁) (dob_pair_le A₂)
    π₁ π₂ hp₁ hp₂ hs₁ hs₂
    (normInf (comm A₁ A₂)) (normInf_nonneg _)
    (fun i => by simpa [comm] using row_le_normInf (comm A₁ A₂) i)

/- ### The exact commutator representation (Theorem thm:rep of the paper) -/

/-- The identity matrix as a `Mat n`. -/
def idM : Mat n := fun i j => if i = j then 1 else 0

lemma vmul_idM (w : Vec n) : vmul w idM = w := by
  funext j
  simp [vmul, idM, mul_ite, Finset.sum_ite_eq']

lemma vmul_neg (w : Vec n) (A : Mat n) : vmul (-w) A = -(vmul w A) := by
  funext j
  simp [vmul, Finset.sum_neg_distrib, neg_mul]

lemma mmul_addL (X Y Z : Mat n) : mmul (X + Y) Z = mmul X Z + mmul Y Z := by
  funext i k
  simp [mmul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- **Theorem thm:rep of the paper (first formula), hypothesis-style.**
    `Z` is any right inverse of `I - A + 𝟙π` (the fundamental matrix when it
    exists); with that, the stationary gap *is* the transported commutator:
    `π₂ [A₁,A₂] Z₂ Z₁ = π₂ - π₁`. Only row sums of `A₁`, stationarity, and
    the two `Z` equations are used --- no positivity, no scrambling. -/
theorem rep_identity
    (A₁ A₂ : Mat n) (h₁row : ∀ i, ∑ j, A₁ i j = 1)
    (π₁ π₂ : Vec n) (hp₁ : ∑ j, π₁ j = 1) (hp₂ : ∑ j, π₂ j = 1)
    (hs₁ : vmul π₁ A₁ = π₁) (hs₂ : vmul π₂ A₂ = π₂)
    (Z₁ Z₂ : Mat n)
    (hZ₁ : mmul (fun i j => idM i j - A₁ i j + π₁ j) Z₁ = idM)
    (hZ₂ : mmul (fun i j => idM i j - A₂ i j + π₂ j) Z₂ = idM) :
    vmul (vmul (vmul π₂ (fun i k => mmul A₁ A₂ i k - mmul A₂ A₁ i k)) Z₂) Z₁
      = π₂ - π₁ := by
  classical
  -- generic transport: for any y,  (y - yA) Z = y - (∑y)·π
  have key : ∀ (A : Mat n) (π : Vec n), (∑ j, π j = 1) → vmul π A = π →
      ∀ Z : Mat n, mmul (fun i j => idM i j - A i j + π j) Z = idM →
      ∀ y : Vec n, vmul (y - vmul y A) Z = y - (fun k => (∑ i, y i) * π k) := by
    intro A π hπ hs Z hZ y
    have hπM : vmul π (fun i j => idM i j - A i j + π j) = π := by
      funext j
      have h1 : (∑ i, π i * idM i j) = π j := congrFun (vmul_idM π) j
      have h2 : (∑ i, π i * A i j) = π j := congrFun hs j
      have h3 : (∑ i, π i * π j) = π j := by
        rw [← Finset.sum_mul, hπ, one_mul]
      simp only [vmul, mul_sub, mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3]
      ring
    have hπZ : vmul π Z = π := by
      calc vmul π Z
          = vmul (vmul π (fun i j => idM i j - A i j + π j)) Z := by rw [hπM]
        _ = vmul π (mmul (fun i j => idM i j - A i j + π j) Z) := vmul_assoc _ _ _
        _ = vmul π idM := by rw [hZ]
        _ = π := vmul_idM _
    have hyA : y - vmul y A = vmul y (fun i j => idM i j - A i j) := by
      rw [vmul_matsub, vmul_idM]
    have hIW : mmul (fun i j => idM i j - A i j) Z
        = (fun i j => idM i j - π j) := by
      have hsplit : (fun i j => idM i j - A i j + π j)
          = (fun i j => idM i j - A i j) + (fun _ j => π j) := by
        funext i j
        simp [Pi.add_apply]
      have hW : mmul (fun _ j => π j) Z = (fun _ j => π j) := by
        funext i k
        show (∑ j, π j * Z j k) = π k
        exact congrFun hπZ k
      have hh := hZ
      rw [hsplit, mmul_addL, hW] at hh
      funext i k
      have hk := congrFun (congrFun hh i) k
      simp only [Pi.add_apply] at hk
      linarith [hk]
    calc vmul (y - vmul y A) Z
        = vmul (vmul y (fun i j => idM i j - A i j)) Z := by rw [hyA]
      _ = vmul y (mmul (fun i j => idM i j - A i j) Z) := vmul_assoc _ _ _
      _ = vmul y (fun i j => idM i j - π j) := by rw [hIW]
      _ = y - (fun k => (∑ i, y i) * π k) := by
          rw [vmul_matsub, vmul_idM]
          funext k
          simp only [Pi.sub_apply, vmul]
          rw [← Finset.sum_mul]
  set y : Vec n := vmul π₂ A₁ with hy
  have hysum : ∑ i, y i = 1 := by
    rw [hy]
    have hsum : ∑ j, vmul π₂ A₁ j = ∑ i, π₂ i := by
      simp only [vmul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum, h₁row i, mul_one]
    rw [hsum, hp₂]
  have hA : vmul π₂ (fun i k => mmul A₁ A₂ i k - mmul A₂ A₁ i k)
      = -(y - vmul y A₂) := by
    rw [vmul_matsub, ← vmul_assoc, ← vmul_assoc, hs₂, ← hy]
    abel
  have stepA : vmul (vmul π₂ (fun i k => mmul A₁ A₂ i k - mmul A₂ A₁ i k)) Z₂
      = π₂ - y := by
    rw [hA, vmul_neg, key A₂ π₂ hp₂ hs₂ Z₂ hZ₂ y]
    funext k
    simp only [Pi.neg_apply, Pi.sub_apply]
    rw [hysum]
    ring
  have stepB : vmul (π₂ - y) Z₁ = π₂ - π₁ := by
    have h := key A₁ π₁ hp₁ hs₁ Z₁ hZ₁ π₂
    rw [← hy] at h
    rw [h]
    funext k
    simp only [Pi.sub_apply]
    rw [hp₂]
    ring
  rw [stepA]
  exact stepB

/-- The symmetric order, by exchanging the chains. -/
theorem rep_identity'
    (A₁ A₂ : Mat n) (h₂row : ∀ i, ∑ j, A₂ i j = 1)
    (π₁ π₂ : Vec n) (hp₁ : ∑ j, π₁ j = 1) (hp₂ : ∑ j, π₂ j = 1)
    (hs₁ : vmul π₁ A₁ = π₁) (hs₂ : vmul π₂ A₂ = π₂)
    (Z₁ Z₂ : Mat n)
    (hZ₁ : mmul (fun i j => idM i j - A₁ i j + π₁ j) Z₁ = idM)
    (hZ₂ : mmul (fun i j => idM i j - A₂ i j + π₂ j) Z₂ = idM) :
    vmul (vmul (vmul π₁ (fun i k => mmul A₂ A₁ i k - mmul A₁ A₂ i k)) Z₁) Z₂
      = π₁ - π₂ :=
  rep_identity A₂ A₁ h₂row π₂ π₁ hp₂ hp₁ hs₂ hs₁ Z₂ Z₁ hZ₂ hZ₁

#print axioms rate_law
#print axioms rep_identity

end RateLaw
