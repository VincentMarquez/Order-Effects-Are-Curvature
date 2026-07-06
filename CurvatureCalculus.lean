/-
  CurvatureCalculus.lean --- the operational core of the consensus-curvature
  calculus, kernel-checked. Companion to RateLaw.lean (the stochastic sector:
  rate_law, rep_identity). Paper: "Order Effects Are Curvature" v2.38, sec 1.1.
  Style as in RateLaw.lean: hypothesis-style statements, elementary proofs.
-/
import Mathlib

open Finset

namespace CurvatureCalculus

/-! ### Section 1: Projection (paper Proposition 5.1) -/
section Projection
variable {A : Type*} [CompleteLattice A] (H : Set (A → A))

/-- The robust core: common fixed points of every holonomy in `H`. -/
def RobustCore : Set A := {x | ∀ h ∈ H, h x = x}

theorem bot_mem_robustCore (hd : ∀ h ∈ H, ∀ x, h x ≤ x) :
    ⊥ ∈ RobustCore H := fun h hh => le_antisymm (hd h hh ⊥) bot_le

theorem sSup_mem_robustCore (hm : ∀ h ∈ H, Monotone h)
    (hd : ∀ h ∈ H, ∀ x, h x ≤ x)
    {S : Set A} (hS : S ⊆ RobustCore H) : sSup S ∈ RobustCore H := by
  intro h hh
  refine le_antisymm (hd h hh _) (sSup_le fun y hy => ?_)
  calc y = h y := (hS hy h hh).symm
    _ ≤ h (sSup S) := hm h hh (le_sSup hy)

/-- Robustification: the largest robust minorant. -/
noncomputable def robustify (x : A) : A :=
  sSup {y | y ∈ RobustCore H ∧ y ≤ x}

theorem robustify_le (x : A) : robustify H x ≤ x :=
  sSup_le fun _ hy => hy.2

theorem robustify_mono : Monotone (robustify H) := fun _ _ hab =>
  sSup_le_sSup fun y hy => ⟨hy.1, hy.2.trans hab⟩

theorem robustify_mem (hm : ∀ h ∈ H, Monotone h)
    (hd : ∀ h ∈ H, ∀ x, h x ≤ x) (x : A) :
    robustify H x ∈ RobustCore H :=
  sSup_mem_robustCore H hm hd (fun _ hy => hy.1)

theorem robustify_of_mem {x : A} (hx : x ∈ RobustCore H) :
    robustify H x = x :=
  le_antisymm (robustify_le H x) (le_sSup ⟨hx, le_rfl⟩)

theorem robustify_idem (hm : ∀ h ∈ H, Monotone h)
    (hd : ∀ h ∈ H, ∀ x, h x ≤ x) (x : A) :
    robustify H (robustify H x) = robustify H x :=
  robustify_of_mem H (robustify_mem H hm hd x)

end Projection

/-! ### Section 2: The move and the accounting rule (Theorems 4.1 and 4.4).
A staircase is a word over Bool (false = horizontal, true = vertical);
`T w i j` transports from grid position (i,j), composing as traversed. -/
section Stokes
variable {A : Type*} (h v : ℕ → ℕ → A → A)

def T : List Bool → ℕ → ℕ → A → A
  | [],          _, _ => id
  | false :: w, i, j => fun x => T w i (j+1) (h i j x)
  | true  :: w, i, j => fun x => T w (i+1) j (v i j x)

variable (d : A → A → ℝ) (δ : ℕ → ℕ → ℝ)

theorem T_nonexpansive
    (Hh : ∀ i j x y, d (h i j x) (h i j y) ≤ d x y)
    (Hv : ∀ i j x y, d (v i j x) (v i j y) ≤ d x y) :
    ∀ (w : List Bool) (i j : ℕ) (x y : A),
      d (T h v w i j x) (T h v w i j y) ≤ d x y := by
  intro w
  induction w with
  | nil => intro i j x y; simp [T]
  | cons b w ih =>
    intro i j x y
    cases b with
    | false => simpa [T] using (ih i (j+1) (h i j x) (h i j y)).trans (Hh i j x y)
    | true  => simpa [T] using (ih (i+1) j (v i j x) (v i j y)).trans (Hv i j x y)

/-- THE MOVE: an elementary flip across one square costs at most that
square's face defect (paper Theorem 4.1, elementary-flip step). -/
theorem flip_bound
    (Hh : ∀ i j x y, d (h i j x) (h i j y) ≤ d x y)
    (Hv : ∀ i j x y, d (v i j x) (v i j y) ≤ d x y)
    (Hδ : ∀ i j x, d (v i (j+1) (h i j x)) (h (i+1) j (v i j x)) ≤ δ i j)
    (suf : List Bool) (i j : ℕ) (x : A) :
    d (T h v (false :: true :: suf) i j x)
      (T h v (true :: false :: suf) i j x) ≤ δ i j := by
  have e1 : T h v (false :: true :: suf) i j x
      = T h v suf (i+1) (j+1) (v i (j+1) (h i j x)) := by simp [T]
  have e2 : T h v (true :: false :: suf) i j x
      = T h v suf (i+1) (j+1) (h (i+1) j (v i j x)) := by simp [T]
  rw [e1, e2]
  exact (T_nonexpansive h v d Hh Hv suf (i+1) (j+1) _ _).trans (Hδ i j x)

/-- Peeling a vertical prefix. -/
theorem pre_repV : ∀ (m : ℕ) (w : List Bool) (i j : ℕ) (x : A),
    T h v (List.replicate m true ++ w) i j x
      = T h v w (i + m) j (T h v (List.replicate m true) i j x) := by
  intro m
  induction m with
  | zero => intro w i j x; simp [T]
  | succ m ih =>
    intro w i j x
    simp only [List.replicate_succ, List.cons_append, T]
    rw [ih]
    have hI : i + 1 + m = i + (m + 1) := by omega
    rw [hI]

/-- Transport of a snoc-ed vertical step. -/
theorem snoc_true : ∀ (w : List Bool) (i j : ℕ) (x : A),
    T h v (w ++ [true]) i j x
      = v (i + w.count true) (j + w.count false) (T h v w i j x) := by
  intro w
  induction w with
  | nil => intro i j x; simp [T]
  | cons b w ih =>
    intro i j x
    cases b with
    | false =>
      simp only [List.cons_append, T]
      rw [ih]
      have h1 : (false :: w).count true = w.count true := by simp
      have h2 : (false :: w).count false = w.count false + 1 := by simp
      rw [h1, h2]
      have hJ : j + 1 + w.count false = j + (w.count false + 1) := by omega
      rw [hJ]
    | true =>
      simp only [List.cons_append, T]
      rw [ih]
      have h1 : (true :: w).count true = w.count true + 1 := by simp
      have h2 : (true :: w).count false = w.count false := by simp
      rw [h1, h2]
      have hI : i + 1 + w.count true = i + (w.count true + 1) := by omega
      rw [hI]

/-- THE ACCOUNTING RULE on one row: bubbling a vertical step through n
horizontal steps is a chain of n flips, one bill per cell. -/
theorem row_pass
    (Hd0 : ∀ x : A, d x x = 0)
    (Hdsymm : ∀ x y : A, d x y = d y x)
    (Hdtri : ∀ x y z : A, d x z ≤ d x y + d y z)
    (Hh : ∀ i j x y, d (h i j x) (h i j y) ≤ d x y)
    (Hv : ∀ i j x y, d (v i j x) (v i j y) ≤ d x y)
    (Hδ : ∀ i j x, d (v i (j+1) (h i j x)) (h (i+1) j (v i j x)) ≤ δ i j) :
    ∀ (n i j : ℕ) (x : A),
      d (T h v (true :: List.replicate n false) i j x)
        (T h v (List.replicate n false ++ [true]) i j x)
        ≤ ∑ jj ∈ range n, δ i (j + jj) := by
  intro n
  induction n with
  | zero =>
    intro i j x
    simp only [List.replicate, List.nil_append, Finset.range_zero,
      Finset.sum_empty]
    exact le_of_eq (Hd0 _)
  | succ n ih =>
    intro i j x
    have key := Hdtri (T h v (true :: List.replicate (n+1) false) i j x)
      (T h v (false :: true :: List.replicate n false) i j x)
      (T h v (List.replicate (n+1) false ++ [true]) i j x)
    have step1 : d (T h v (true :: List.replicate (n+1) false) i j x)
        (T h v (false :: true :: List.replicate n false) i j x) ≤ δ i j := by
      have hw : (true :: List.replicate (n+1) false)
          = true :: false :: List.replicate n false := by
        simp [List.replicate_succ]
      rw [hw, Hdsymm]
      exact flip_bound h v d δ Hh Hv Hδ (List.replicate n false) i j x
    have step2 : d (T h v (false :: true :: List.replicate n false) i j x)
        (T h v (List.replicate (n+1) false ++ [true]) i j x)
        ≤ ∑ jj ∈ range n, δ i (j + 1 + jj) := by
      have hw2 : (List.replicate (n+1) false ++ [true])
          = false :: (List.replicate n false ++ [true]) := by
        simp [List.replicate_succ]
      rw [hw2]
      have e1 : T h v (false :: true :: List.replicate n false) i j x
          = T h v (true :: List.replicate n false) i (j+1) (h i j x) := by
        simp [T]
      have e2 : T h v (false :: (List.replicate n false ++ [true])) i j x
          = T h v (List.replicate n false ++ [true]) i (j+1) (h i j x) := by
        simp [T]
      rw [e1, e2]
      exact ih i (j+1) (h i j x)
    have total := key.trans (add_le_add step1 step2)
    refine total.trans (le_of_eq ?_)
    rw [Finset.sum_range_succ']
    have hc : ∀ jj, δ i (j + (jj + 1)) = δ i (j + 1 + jj) := by
      intro jj; congr 1; omega
    simp only [hc, Nat.add_zero]
    ring

theorem replicate_snoc (m : ℕ) (b : Bool) :
    List.replicate (m+1) b = List.replicate m b ++ [b] := by
  rw [List.replicate_add, List.replicate_one]

/-- The two extreme boundary staircases of the full m by n grid. -/
def Wb (m n : ℕ) : List Bool := List.replicate m true ++ List.replicate n false
def Wt (m n : ℕ) : List Bool := List.replicate n false ++ List.replicate m true

theorem count_true_VF (m n : ℕ) : (Wb m n).count true = m := by
  simp [Wb, List.count_append, List.count_replicate]

theorem count_false_VF (m n : ℕ) : (Wb m n).count false = n := by
  simp [Wb, List.count_append, List.count_replicate]

theorem count_true_FV (m n : ℕ) : (Wt m n).count true = m := by
  simp [Wt, List.count_append, List.count_replicate]

theorem count_false_FV (m n : ℕ) : (Wt m n).count false = n := by
  simp [Wt, List.count_append, List.count_replicate]

/-- THE ACCOUNTING RULE (paper Theorem 4.1, boundary form): the defect of
the two extreme staircases of the full grid is at most the sum of all
face defects. Proof: m*n elementary flips, each cell billed exactly once. -/
theorem stokes_boundary
    (Hd0 : ∀ x : A, d x x = 0)
    (Hdsymm : ∀ x y : A, d x y = d y x)
    (Hdtri : ∀ x y z : A, d x z ≤ d x y + d y z)
    (Hh : ∀ i j x y, d (h i j x) (h i j y) ≤ d x y)
    (Hv : ∀ i j x y, d (v i j x) (v i j y) ≤ d x y)
    (Hδ : ∀ i j x, d (v i (j+1) (h i j x)) (h (i+1) j (v i j x)) ≤ δ i j) :
    ∀ (m n : ℕ) (x : A),
      d (T h v (Wb m n) 0 0 x) (T h v (Wt m n) 0 0 x)
        ≤ ∑ i ∈ range m, ∑ j ∈ range n, δ i j := by
  intro m
  induction m with
  | zero =>
    intro n x
    have : Wb 0 n = Wt 0 n := by simp [Wb, Wt]
    rw [this]
    simpa using le_of_eq (Hd0 _)
  | succ m ih =>
    intro n x
    -- Wb (m+1) n = V^m ++ (true :: F^n) ; Mid = V^m ++ (F^n ++ [true])
    have hWb : Wb (m+1) n
        = List.replicate m true ++ (true :: List.replicate n false) := by
      simp [Wb, replicate_snoc m true, List.append_assoc]
    have hMid : List.replicate m true ++ (List.replicate n false ++ [true])
        = Wb m n ++ [true] := by
      simp [Wb, List.append_assoc]
    have hWt : Wt (m+1) n = Wt m n ++ [true] := by
      simp [Wt, replicate_snoc m true, List.append_assoc]
    have step1 : d (T h v (Wb (m+1) n) 0 0 x)
        (T h v (List.replicate m true ++ (List.replicate n false ++ [true])) 0 0 x)
        ≤ ∑ j ∈ range n, δ m j := by
      rw [hWb, pre_repV, pre_repV]
      have := row_pass h v d δ Hd0 Hdsymm Hdtri Hh Hv Hδ n m 0
        (T h v (List.replicate m true) 0 0 x)
      simpa using this
    have step2 : d
        (T h v (List.replicate m true ++ (List.replicate n false ++ [true])) 0 0 x)
        (T h v (Wt (m+1) n) 0 0 x)
        ≤ ∑ i ∈ range m, ∑ j ∈ range n, δ i j := by
      rw [hMid, hWt, snoc_true, snoc_true,
        count_true_VF, count_false_VF, count_true_FV, count_false_FV]
      exact (Hv _ _ _ _).trans (ih n x)
    calc d (T h v (Wb (m+1) n) 0 0 x) (T h v (Wt (m+1) n) 0 0 x)
        ≤ _ + _ := Hdtri _ _ _
      _ ≤ (∑ j ∈ range n, δ m j) + ∑ i ∈ range m, ∑ j ∈ range n, δ i j :=
          add_le_add step1 step2
      _ = ∑ i ∈ range (m+1), ∑ j ∈ range n, δ i j := by
          rw [Finset.sum_range_succ]; ring

end Stokes

/-! ### Section 2b: Optimal constant exactly 1 (paper Theorem 4.4).
The translation ladder: at every grid size the boundary defect equals the
sum of the face defects, so no constant below 1 can replace it. -/
section Tight

def hL : ℕ → ℕ → ℝ → ℝ := fun i _ x => if i = 0 then x + 1 else x
def vL : ℕ → ℕ → ℝ → ℝ := fun _ _ x => x
def dR : ℝ → ℝ → ℝ := fun x y => |x - y|
def δL : ℕ → ℕ → ℝ := fun i _ => if i = 0 then 1 else 0

theorem tight_Hd0 : ∀ x : ℝ, dR x x = 0 := by intro x; simp [dR]
theorem tight_Hdsymm : ∀ x y : ℝ, dR x y = dR y x := by
  intro x y; simp [dR, abs_sub_comm]
theorem tight_Hdtri : ∀ x y z : ℝ, dR x z ≤ dR x y + dR y z := by
  intro x y z; exact abs_sub_le x y z
theorem tight_Hh : ∀ i j x y, dR (hL i j x) (hL i j y) ≤ dR x y := by
  intro i j x y
  by_cases hi : i = 0 <;> simp [hL, hi, dR]
theorem tight_Hv : ∀ i j x y, dR (vL i j x) (vL i j y) ≤ dR x y := by
  intro i j x y; simp [vL]
theorem tight_Hδ : ∀ i j x,
    dR (vL i (j+1) (hL i j x)) (hL (i+1) j (vL i j x)) ≤ δL i j := by
  intro i j x
  by_cases hi : i = 0
  · simp [hL, vL, dR, δL, hi]
  · simp [hL, vL, dR, δL, hi]

theorem T_F_row0 : ∀ (n j : ℕ) (x : ℝ),
    T hL vL (List.replicate n false) 0 j x = x + n := by
  intro n
  induction n with
  | zero => intro j x; simp [T]
  | succ n ih =>
    intro j x
    simp only [List.replicate_succ, T, hL]
    rw [if_true, ih]
    push_cast; ring

theorem T_F_row1 : ∀ (n j : ℕ) (x : ℝ),
    T hL vL (List.replicate n false) 1 j x = x := by
  intro n
  induction n with
  | zero => intro j x; simp [T]
  | succ n ih =>
    intro j x
    simp only [List.replicate_succ, T, hL]
    rw [if_neg (by norm_num : (1 : ℕ) ≠ 0), ih]

theorem stokes_tight (n : ℕ) (x : ℝ) :
    dR (T hL vL (Wb 1 n) 0 0 x) (T hL vL (Wt 1 n) 0 0 x)
      = ∑ i ∈ range 1, ∑ j ∈ range n, δL i j := by
  have hb : T hL vL (Wb 1 n) 0 0 x = x := by
    have : Wb 1 n = true :: List.replicate n false := by
      simp [Wb]
    rw [this]
    simp only [T, vL]
    exact T_F_row1 n 0 x
  have ht : T hL vL (Wt 1 n) 0 0 x = x + n := by
    have hW : Wt 1 n = List.replicate n false ++ [true] := by
      simp [Wt]
    rw [hW, snoc_true]
    simp only [vL]
    exact T_F_row0 n 0 x
  rw [hb, ht]
  have h0 : ∀ j : ℕ, δL 0 j = 1 := fun j => by simp [δL]
  have hsum : (∑ i ∈ range 1, ∑ j ∈ range n, δL i j) = (n : ℝ) := by
    rw [Finset.sum_range_one]
    simp [h0]
  rw [hsum]
  simp only [dR]
  rw [show x - (x + (n:ℝ)) = -(n:ℝ) by ring, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]

end Tight

/-! ### Section 3: Protocol test (paper Theorem 6.1).
The linear meeting rule R(x,y) = ((1-a)x+ay, bx+(1-b)y), acting on triples
as R12 = M ⊕ 1 and R23 = 1 ⊕ M. The braid obstruction factors globally. -/
section Braid
open Matrix

noncomputable section
abbrev P2 := MvPolynomial (Fin 2) ℚ
def pa : P2 := MvPolynomial.X 0
def pb : P2 := MvPolynomial.X 1

def R12 : Matrix (Fin 3) (Fin 3) P2 :=
  !![1 - pa, pa, 0; pb, 1 - pb, 0; 0, 0, 1]
def R23 : Matrix (Fin 3) (Fin 3) P2 :=
  !![1, 0, 0; 0, 1 - pa, pa; 0, pb, 1 - pb]
def NB : Matrix (Fin 3) (Fin 3) P2 :=
  !![-pa, pa, 0; pb, pa - pb, -pa; 0, -pb, pb]

/-- The braid obstruction carries the single common factor (1-a)(1-b),
exactly as in paper Theorem 6.1 (exact symbolic identity). -/
theorem braid_factorization :
    R12 * R23 * R12 - R23 * R12 * R23 = ((1 - pa) * (1 - pb)) • NB := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [R12, R23, NB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      smul_eq_mul] <;>
    ring

end

def r12 (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - a, a, 0; b, 1 - b, 0; 0, 0, 1]
def r23 (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1 - a, a; 0, b, 1 - b]
def nb (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-a, a, 0; b, a - b, -a; 0, -b, b]

theorem braid_factorization_real (a b : ℝ) :
    r12 a b * r23 a b * r12 a b - r23 a b * r12 a b * r23 a b
      = ((1 - a) * (1 - b)) • nb a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [r12, r23, nb, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      smul_eq_mul] <;>
    ring

/-- A linear protocol is braided when the Yang--Baxter relation holds. -/
def IsBraided (a b : ℝ) : Prop :=
  r12 a b * r23 a b * r12 a b = r23 a b * r12 a b * r23 a b

/-- Paper Theorem 6.1: exactly the scribe families and the identity. -/
theorem braid_classification (a b : ℝ) :
    IsBraided a b ↔ a = 1 ∨ b = 1 ∨ (a = 0 ∧ b = 0) := by
  have hiff : IsBraided a b ↔ ((1 - a) * (1 - b)) • nb a b = 0 := by
    rw [IsBraided, ← sub_eq_zero, braid_factorization_real]
  rw [hiff]
  constructor
  · intro hz
    by_cases ha : a = 1
    · exact Or.inl ha
    by_cases hb : b = 1
    · exact Or.inr (Or.inl hb)
    have hne : (1 - a) * (1 - b) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr fun h => ha h.symm)
        (sub_ne_zero.mpr fun h => hb h.symm)
    have h01 : ((1 - a) * (1 - b)) * a = 0 := by
      have := congrFun (congrFun hz 0) 1
      simpa [nb, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] using this
    have h10 : ((1 - a) * (1 - b)) * b = 0 := by
      have := congrFun (congrFun hz 1) 0
      simpa [nb, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] using this
    exact Or.inr (Or.inr ⟨(mul_eq_zero.mp h01).resolve_left hne,
      (mul_eq_zero.mp h10).resolve_left hne⟩)
  · rintro (ha | hb | ⟨ha, hb⟩)
    · subst ha; simp
    · subst hb; simp
    · subst ha; subst hb
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nb, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The 1/8 witness: symmetric compromise a=b=1/2 at the point (1,0,0). -/
theorem braid_defect_witness :
    (r12 (1/2) (1/2) * r23 (1/2) (1/2) * r12 (1/2) (1/2)
      - r23 (1/2) (1/2) * r12 (1/2) (1/2) * r23 (1/2) (1/2))
        *ᵥ ![1, 0, 0] = ![-(1/8 : ℝ), 1/8, 0] := by
  funext i
  fin_cases i <;>
    simp [r12, r23, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecHead, Matrix.vecTail] <;>
    norm_num

theorem braid_defect_eighth :
    |((r12 (1/2) (1/2) * r23 (1/2) (1/2) * r12 (1/2) (1/2)
      - r23 (1/2) (1/2) * r12 (1/2) (1/2) * r23 (1/2) (1/2))
        *ᵥ ![1, 0, 0]) 0| = 1/8 := by
  rw [braid_defect_witness]
  norm_num

end Braid

/-! ### Section 4: Triviality test (paper Theorem 3.2).
A finite quiver is (V, E, s, t); a walk composes edges head to tail;
transport folds edge maps along the walk. Flat for every assignment iff
the shape is a multitree (at most one walk between any ordered pair,
which subsumes acyclicity since nil : Walk a a). -/
section Multitree
variable {V : Type*} {E : Type*} (s t : E → V)

inductive Walk : V → V → Type _ where
  | nil (a : V) : Walk a a
  | cons (e : E) {b : V} (rest : Walk (t e) b) : Walk (s e) b

namespace Walk

def edges {a b : V} : Walk s t a b → List E
  | .nil _ => []
  | .cons e rest => e :: rest.edges

def transport {A : Type} (Emap : E → A → A) {a b : V} :
    Walk s t a b → A → A
  | .nil _ => id
  | .cons e rest => fun x => rest.transport Emap (Emap e x)

def append {a b c : V} : Walk s t a b → Walk s t b c → Walk s t a c
  | .nil _, w => w
  | .cons e rest, w => .cons e (rest.append w)

end Walk

/-- A shape is a multitree when walks are unique (hence no cycles). -/
def IsMultitree : Prop := ∀ a b : V, Subsingleton (Walk s t a b)

variable [DecidableEq E]

/-- The detector bundle: cap the fiber to `false` across one edge. -/
def capE (e0 : E) : E → Bool → Bool :=
  fun f => if f = e0 then (fun _ => false) else id

theorem transport_false (e0 : E) {a b : V} (w : Walk s t a b) :
    w.transport s t (capE e0) false = false := by
  induction w with
  | nil a => rfl
  | cons e rest ih =>
    show rest.transport s t (capE e0) (capE e0 e false) = false
    by_cases he : e = e0 <;> simp [capE, he, ih]

theorem transport_true_of_mem (e0 : E) {a b : V} (w : Walk s t a b)
    (hmem : e0 ∈ w.edges s t) :
    w.transport s t (capE e0) true = false := by
  induction w with
  | nil a => simp [Walk.edges] at hmem
  | cons e rest ih =>
    simp only [Walk.edges, List.mem_cons] at hmem
    show rest.transport s t (capE e0) (capE e0 e true) = false
    rcases hmem with he | hmem
    · have : capE e0 e true = false := by simp [capE, he.symm]
      rw [this]; exact transport_false s t e0 rest
    · by_cases he : e = e0
      · simp only [capE, if_pos he]
        exact transport_false s t e0 rest
      · simp only [capE, if_neg he, id]
        exact ih hmem

theorem transport_true_of_not_mem (e0 : E) {a b : V} (w : Walk s t a b)
    (hmem : e0 ∉ w.edges s t) :
    w.transport s t (capE e0) true = true := by
  induction w with
  | nil a => rfl
  | cons e rest ih =>
    simp only [Walk.edges, List.mem_cons, not_or] at hmem
    show rest.transport s t (capE e0) (capE e0 e true) = true
    rw [show capE e0 e true = true by simp [capE, Ne.symm hmem.1]]
    exact ih hmem.2

/-- Splitting a walk at an occurring edge. -/
theorem exists_split_of_mem {a b : V} (q : Walk s t a b) {e : E}
    (he : e ∈ q.edges s t) :
    ∃ (q1 : Walk s t a (s e)) (q2 : Walk s t (t e) b),
      q = q1.append s t (Walk.cons e q2) := by
  induction q with
  | nil a => simp [Walk.edges] at he
  | cons f q2 ih =>
    simp only [Walk.edges, List.mem_cons] at he
    rcases eq_or_ne e f with rfl | hne
    · exact ⟨Walk.nil (s e), q2, rfl⟩
    · obtain ⟨w1, w2, hw⟩ := ih (he.resolve_left hne)
      exact ⟨Walk.cons f w1, w2, by rw [hw]; rfl⟩

/-- The selection lemma: in an acyclic shape, edge containment forces
walk equality. -/
theorem eq_of_edges_subset
    (hacyc : ∀ (c : V) (w : Walk s t c c), w = Walk.nil c)
    {a b : V} (p : Walk s t a b) :
    ∀ q : Walk s t a b, p.edges s t ⊆ q.edges s t → p = q := by
  induction p with
  | nil a =>
    intro q _
    exact (hacyc a q).symm
  | cons e p2 ih =>
    intro q hsub
    have he : e ∈ q.edges s t := hsub (by simp [Walk.edges])
    obtain ⟨q1, q2, hq⟩ := exists_split_of_mem s t q he
    have hq1 : q1 = Walk.nil (s e) := hacyc (s e) q1
    subst hq1
    have hq2 : q = Walk.cons e q2 := hq
    subst hq2
    have hsub2 : p2.edges s t ⊆ q2.edges s t := by
      intro x hx
      have hx2 : x ∈ (Walk.cons e p2).edges s t := by
        simp [Walk.edges, hx]
      rcases List.mem_cons.mp (hsub hx2) with hxe | hxq
      · exfalso
        subst hxe
        obtain ⟨w1, w2, _⟩ := exists_split_of_mem s t p2 hx
        have hcyc : Walk.cons x w1 = Walk.nil (s x) :=
          hacyc (s x) (Walk.cons x w1)
        have hlen := congrArg (Walk.edges s t) hcyc
        simp [Walk.edges] at hlen
      · exact hxq
    rw [ih q2 hsub2]

/-- One direction: multitrees are universally flat. -/
theorem flat_of_multitree (hmt : IsMultitree s t)
    {A : Type} (Emap : E → A → A) {a b : V} (p q : Walk s t a b) (x : A) :
    p.transport s t Emap x = q.transport s t Emap x := by
  have := (hmt a b).elim p q
  rw [this]

/-- The converse: a shape that is not a multitree is curved for some
Bool-fibered assignment (the cap bundle detects it). -/
theorem not_flat_of_not_multitree (h : ¬ IsMultitree s t) :
    ∃ (a b : V) (p q : Walk s t a b) (Emap : E → Bool → Bool) (x : Bool),
      p.transport s t Emap x ≠ q.transport s t Emap x := by
  simp only [IsMultitree, not_forall] at h
  obtain ⟨a, b, hab⟩ := h
  rw [not_subsingleton_iff_nontrivial] at hab
  obtain ⟨p, q, hpq⟩ := hab.exists_pair_ne
  by_cases hacyc : ∀ (c : V) (w : Walk s t c c), w = Walk.nil c
  · -- acyclic: an edge separates the two walks
    have hnsub : ¬ (p.edges s t ⊆ q.edges s t) ∨
        ¬ (q.edges s t ⊆ p.edges s t) := by
      by_contra hc
      push_neg at hc
      exact hpq (eq_of_edges_subset s t hacyc p q hc.1)
    rcases hnsub with hns | hns
    · rw [List.subset_def] at hns
      push_neg at hns
      obtain ⟨e, hep, heq⟩ := hns
      refine ⟨a, b, p, q, capE e, true, ?_⟩
      rw [transport_true_of_mem s t e p hep,
        transport_true_of_not_mem s t e q heq]
      simp
    · rw [List.subset_def] at hns
      push_neg at hns
      obtain ⟨e, heq, hep⟩ := hns
      refine ⟨a, b, p, q, capE e, true, ?_⟩
      rw [transport_true_of_mem s t e q heq,
        transport_true_of_not_mem s t e p hep]
      simp
  · -- a cycle exists: compare it against the empty walk
    push_neg at hacyc
    obtain ⟨c, w, hw⟩ := hacyc
    cases w with
    | nil => exact absurd rfl hw
    | cons e rest =>
      refine ⟨_, _, Walk.cons e rest, Walk.nil (s e), capE e, true, ?_⟩
      rw [transport_true_of_mem s t e (Walk.cons e rest)
        (by simp [Walk.edges])]
      simp [Walk.transport]

/-- Paper Theorem 3.2, both directions packaged. -/
theorem flat_iff_multitree :
    (∀ (A : Type) (Emap : E → A → A) (a b : V) (p q : Walk s t a b) (x : A),
      p.transport s t Emap x = q.transport s t Emap x)
      ↔ IsMultitree s t := by
  constructor
  · intro hflat
    by_contra h
    obtain ⟨a, b, p, q, Emap, x, hne⟩ := not_flat_of_not_multitree s t h
    exact hne (hflat Bool Emap a b p q x)
  · intro hmt A Emap a b p q x
    exact flat_of_multitree s t hmt Emap p q x

end Multitree

/-! ### Section 5: Rate--curvature bound (paper Theorem 5.2), pairs engine.
Merging is by generated equivalence; each added pair costs at most one
class. Cardinalities are classical (`Quotient.fintype` via choice). -/
section Orbit
open Relation
open scoped Classical
variable {α : Type*} [Fintype α]

/-- My own monotonicity, to stay name-stable. -/
theorem eqvGen_mono {r r2 : α → α → Prop} (h : ∀ a b, r a b → r2 a b)
    {a b : α} (hab : EqvGen r a b) : EqvGen r2 a b := by
  induction hab with
  | rel x y hxy => exact EqvGen.rel x y (h x y hxy)
  | refl x => exact EqvGen.refl x
  | symm x y _ ih => exact EqvGen.symm x y ih
  | trans x y z _ _ ih1 ih2 => exact EqvGen.trans x y z ih1 ih2

/-- Adjoining one pair (u,w): the generated equivalence grows exactly by
the u-w bridge. -/
theorem eqvGen_pair_iff (r : α → α → Prop) (u w : α) {x y : α} :
    EqvGen (fun a b => r a b ∨ (a = u ∧ b = w)) x y ↔
      EqvGen r x y ∨ (EqvGen r x u ∧ EqvGen r w y) ∨
        (EqvGen r x w ∧ EqvGen r u y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel a b hab =>
      rcases hab with hab | ⟨rfl, rfl⟩
      · exact Or.inl (EqvGen.rel a b hab)
      · exact Or.inr (Or.inl ⟨EqvGen.refl a, EqvGen.refl b⟩)
    | refl a => exact Or.inl (EqvGen.refl a)
    | symm a b _ ih =>
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (EqvGen.symm a b h1)
      · exact Or.inr (Or.inr ⟨EqvGen.symm _ _ h2, EqvGen.symm _ _ h1⟩)
      · exact Or.inr (Or.inl ⟨EqvGen.symm _ _ h2, EqvGen.symm _ _ h1⟩)
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases ih2 with g1 | ⟨g1, g2⟩ | ⟨g1, g2⟩
      · exact Or.inl (EqvGen.trans _ _ _ h1 g1)
      · exact Or.inr (Or.inl ⟨EqvGen.trans _ _ _ h1 g1, g2⟩)
      · exact Or.inr (Or.inr ⟨EqvGen.trans _ _ _ h1 g1, g2⟩)
      · exact Or.inr (Or.inl ⟨h1, EqvGen.trans _ _ _ h2 g1⟩)
      · exact Or.inl (EqvGen.trans _ _ _
          (EqvGen.trans _ _ _ h1 (EqvGen.symm _ _ g1))
          (EqvGen.trans _ _ _ (EqvGen.symm _ _ h2) g2))
      · exact Or.inl (EqvGen.trans _ _ _ h1 g2)
      · exact Or.inr (Or.inr ⟨h1, EqvGen.trans _ _ _ h2 g1⟩)
      · exact Or.inl (EqvGen.trans _ _ _ h1 g2)
      · exact Or.inr (Or.inr ⟨h1, g2⟩)
  · intro hxy
    have lift : ∀ {a b : α}, EqvGen r a b →
        EqvGen (fun a b => r a b ∨ (a = u ∧ b = w)) a b :=
      fun hab => eqvGen_mono (fun a b h => Or.inl h) hab
    have huw : EqvGen (fun a b => r a b ∨ (a = u ∧ b = w)) u w :=
      EqvGen.rel u w (Or.inr ⟨rfl, rfl⟩)
    rcases hxy with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lift h1
    · exact EqvGen.trans _ _ _ (lift h1) (EqvGen.trans _ _ _ huw (lift h2))
    · exact EqvGen.trans _ _ _ (lift h1)
        (EqvGen.trans _ _ _ (EqvGen.symm _ _ huw) (lift h2))

/-- Same relation, same class count. -/
theorem card_quot_eq_of_iff (s1 s2 : Setoid α)
    (h : ∀ a b, s1.r a b ↔ s2.r a b) :
    Fintype.card (Quotient s1) = Fintype.card (Quotient s2) := by
  refine Fintype.card_congr
    ⟨Quotient.map' id fun a b hab => (h a b).mp hab,
     Quotient.map' id fun a b hab => (h a b).mpr hab, ?_, ?_⟩
  · intro q; refine Quotient.inductionOn' q fun a => rfl
  · intro q; refine Quotient.inductionOn' q fun a => rfl

/-- THE DROP: one added pair merges at most one class. -/
theorem card_quot_pair_drop (r : α → α → Prop) (u w : α) :
    Fintype.card (Quotient (EqvGen.setoid r)) ≤
      Fintype.card (Quotient (EqvGen.setoid
        (fun a b => r a b ∨ (a = u ∧ b = w)))) + 1 := by
  set r2 := fun a b => r a b ∨ (a = u ∧ b = w) with hr2
  have hchar : ∀ x y : α, EqvGen r2 x y ↔
      EqvGen r x y ∨ (EqvGen r x u ∧ EqvGen r w y) ∨
        (EqvGen r x w ∧ EqvGen r u y) := fun x y => eqvGen_pair_iff r u w
  -- inject old classes into (new classes) ⊕ one extra point
  have hinj : Function.Injective
      (fun q : Quotient (EqvGen.setoid r) =>
        Quotient.liftOn q
          (fun a => if EqvGen r a u then (none : Option (Quotient (EqvGen.setoid r2)))
            else some (Quotient.mk (EqvGen.setoid r2) a))
          (by
            intro a b hab
            by_cases hau : EqvGen r a u
            · rw [if_pos hau, if_pos ((EqvGen.symm _ _ hab).trans _ _ _ hau)]
            · rw [if_neg hau,
                if_neg (fun hbu => hau (hab.trans _ _ _ hbu))]
              exact congrArg some (Quotient.sound
                (eqvGen_mono (fun a b h => Or.inl h) hab)))) := by
    intro q1 q2
    refine Quotient.inductionOn₂ q1 q2 fun a b => ?_
    by_cases hau : EqvGen r a u <;> by_cases hbu : EqvGen r b u <;>
      simp only [Quotient.liftOn_mk, if_pos, if_neg, hau, hbu, if_true,
        if_false, reduceIte]
    · intro _; exact Quotient.sound (hau.trans _ _ _ (EqvGen.symm _ _ hbu))
    · intro hcon; exact absurd hcon (Option.some_ne_none _).symm
    · intro hcon; exact absurd hcon (Option.some_ne_none _)
    · intro hsome
      have hab2 : EqvGen r2 a b := Quotient.exact (Option.some_injective _ hsome)
      rcases (hchar a b).mp hab2 with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Quotient.sound h1
      · exact absurd h1 hau
      · exact absurd (EqvGen.symm _ _ h2) hbu
  calc Fintype.card (Quotient (EqvGen.setoid r))
      ≤ Fintype.card (Option (Quotient (EqvGen.setoid r2))) :=
        Fintype.card_le_of_injective _ hinj
    _ = _ + 1 := Fintype.card_option

/-- Iterating the drop over a list of pairs. -/
def relOfPairs (L : List (α × α)) : α → α → Prop :=
  fun x y => (x, y) ∈ L

theorem card_quot_pairs (r : α → α → Prop) (L : List (α × α)) :
    Fintype.card (Quotient (EqvGen.setoid r)) ≤
      Fintype.card (Quotient (EqvGen.setoid
        (fun a b => r a b ∨ relOfPairs L a b))) + L.length := by
  induction L generalizing r with
  | nil =>
    have := card_quot_eq_of_iff (EqvGen.setoid r)
      (EqvGen.setoid (fun a b => r a b ∨ relOfPairs ([] : List (α × α)) a b))
      (fun a b => by
        constructor
        · exact fun h => eqvGen_mono (fun a b h => Or.inl h) h
        · exact fun h => eqvGen_mono (fun a b h => by
            rcases h with h | h
            · exact h
            · simp [relOfPairs] at h) h)
    simp [this]
  | cons p L ih =>
    obtain ⟨u, w⟩ := p
    have step := card_quot_pair_drop r u w
    have next := ih (fun a b => r a b ∨ (a = u ∧ b = w))
    have hiff : ∀ a b : α,
        EqvGen (fun a b => (r a b ∨ (a = u ∧ b = w)) ∨ relOfPairs L a b) a b ↔
        EqvGen (fun a b => r a b ∨ relOfPairs ((u, w) :: L) a b) a b := by
      intro a b
      constructor <;> refine fun h => eqvGen_mono (fun a b h => ?_) h
      · rcases h with (h | ⟨rfl, rfl⟩) | h
        · exact Or.inl h
        · exact Or.inr (by simp [relOfPairs])
        · exact Or.inr (by simp [relOfPairs] at h ⊢; exact Or.inr h)
      · rcases h with h | h
        · exact Or.inl (Or.inl h)
        · simp only [relOfPairs, List.mem_cons, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩ | h
          · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
          · exact Or.inr h
    have heq := card_quot_eq_of_iff
      (EqvGen.setoid (fun a b => (r a b ∨ (a = u ∧ b = w)) ∨ relOfPairs L a b))
      (EqvGen.setoid (fun a b => r a b ∨ relOfPairs ((u, w) :: L) a b)) hiff
    calc Fintype.card (Quotient (EqvGen.setoid r))
        ≤ Fintype.card (Quotient (EqvGen.setoid
            (fun a b => r a b ∨ (a = u ∧ b = w)))) + 1 := step
      _ ≤ (Fintype.card (Quotient (EqvGen.setoid
            (fun a b => (r a b ∨ (a = u ∧ b = w)) ∨ relOfPairs L a b)))
            + L.length) + 1 := Nat.add_le_add_right next 1
      _ = Fintype.card (Quotient (EqvGen.setoid
            (fun a b => r a b ∨ relOfPairs ((u, w) :: L) a b)))
            + ((u, w) :: L).length := by
          rw [heq]
          simp [List.length_cons]
          omega

end Orbit

/-! ### Section 5b: permutations pay |support| - 1 (paper Theorem 5.2). -/
section OrbitPerm
open Relation
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem eqvGen_closure {r r2 : α → α → Prop}
    (h : ∀ a b, r a b → EqvGen r2 a b) {a b : α}
    (hab : EqvGen r a b) : EqvGen r2 a b := by
  induction hab with
  | rel x y hxy => exact h x y hxy
  | refl x => exact EqvGen.refl x
  | symm x y _ ih => exact EqvGen.symm x y ih
  | trans x y z _ _ ih1 ih2 => exact EqvGen.trans x y z ih1 ih2

theorem perm_pow_apply (σ : Equiv.Perm α) :
    ∀ (n : ℕ) (x : α), (σ ^ n) x = (⇑σ)^[n] x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply, ih]

/-- One pair per support element except the anchor (the head of the
support list). Length is |support| - 1. -/
noncomputable def pairsOf (σ : Equiv.Perm α) : List (α × α) :=
  σ.support.toList.tail.map fun x => (x, σ x)

theorem pairsOf_length (σ : Equiv.Perm α) :
    (pairsOf σ).length = σ.support.card - 1 := by
  simp [pairsOf, List.length_tail, Finset.length_toList]

/-- The redundancy: every atom (x, σ x) is generated by the anchor-free
pairs. The anchor rides its own cycle backward to the pairs. -/
theorem eqvGen_pairsOf_apply (σ : Equiv.Perm α) (x : α) :
    EqvGen (relOfPairs (pairsOf σ)) x (σ x) := by
  by_cases hfix : σ x = x
  · rw [hfix]; exact EqvGen.refl x
  have hxsupp : x ∈ σ.support := Equiv.Perm.mem_support.mpr hfix
  have hxl : x ∈ σ.support.toList := Finset.mem_toList.mpr hxsupp
  cases hl : σ.support.toList with
  | nil => rw [hl] at hxl; exact (List.not_mem_nil hxl).elim
  | cons s0 rest =>
    have hpo : pairsOf σ = rest.map fun y => (y, σ y) := by
      rw [pairsOf, hl, List.tail_cons]
    by_cases hxs : x = s0
    · -- the anchor: chase the cycle backward
      subst hxs
      set f : α → α := ⇑σ with hf
      have hpern : Function.IsPeriodicPt f (orderOf σ) x := by
        show f^[orderOf σ] x = x
        rw [← perm_pow_apply, pow_orderOf_eq_one]
        rfl
      have hL0 : 0 < Function.minimalPeriod f x :=
        Function.minimalPeriod_pos_of_mem_periodicPts
          ⟨orderOf σ, orderOf_pos σ, hpern⟩
      set L := Function.minimalPeriod f x with hLdef
      have hLs : f^[L] x = x := Function.isPeriodicPt_minimalPeriod f x
      have hmin : ∀ k, 0 < k → k < L → f^[k] x ≠ x := by
        intro k hk0 hkL hcon
        exact absurd (Function.IsPeriodicPt.minimalPeriod_le hk0 hcon) 
          (by omega)
      have hsupp_iter : ∀ k, f^[k] x ∈ σ.support := by
        intro k
        induction k with
        | zero => exact hxsupp
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact Equiv.Perm.apply_mem_support.mpr ih
      have key : ∀ j, j ≤ L - 1 →
          EqvGen (relOfPairs (pairsOf σ)) (f^[L - j] x) x := by
        intro j
        induction j with
        | zero =>
          intro _
          rw [Nat.sub_zero, hLs]
          exact EqvGen.refl x
        | succ j ih =>
          intro hj
          have prev := ih (by omega)
          have hk1 : 1 ≤ L - (j + 1) := by omega
          have hkL : L - (j + 1) < L := by omega
          have hkne : f^[L - (j + 1)] x ≠ x := hmin _ hk1 hkL
          have hkmem : f^[L - (j + 1)] x ∈ σ.support := hsupp_iter _
          have hx2 : f^[L - (j + 1)] x ∈ rest := by
            have hmem : f^[L - (j + 1)] x ∈ σ.support.toList :=
              Finset.mem_toList.mpr hkmem
            rw [hl, List.mem_cons] at hmem
            exact hmem.resolve_left hkne
          have hpair : (f^[L - (j + 1)] x, σ (f^[L - (j + 1)] x))
              ∈ pairsOf σ := by
            rw [hpo]
            exact List.mem_map.mpr ⟨_, hx2, rfl⟩
          have hstep : EqvGen (relOfPairs (pairsOf σ))
              (f^[L - (j + 1)] x) (σ (f^[L - (j + 1)] x)) :=
            EqvGen.rel _ _ hpair
          have hnext : σ (f^[L - (j + 1)] x) = f^[L - j] x := by
            have h1 : L - j = (L - (j + 1)) + 1 := by omega
            rw [h1, Function.iterate_succ_apply']
          refine EqvGen.trans _ _ _ hstep ?_
          rw [hnext]
          exact prev
      have hfin := key (L - 1) le_rfl
      have hone : L - (L - 1) = 1 := by omega
      rw [hone] at hfin
      have : f^[1] x = σ x := by rw [Function.iterate_one]
      rw [this] at hfin
      exact EqvGen.symm _ _ hfin
    · -- not the anchor: (x, σ x) is one of the pairs
      have hx2 : x ∈ rest := by
        rw [hl, List.mem_cons] at hxl
        exact hxl.resolve_left hxs
      refine EqvGen.rel _ _ ?_
      rw [hpo]
      exact List.mem_map.mpr ⟨_, hx2, rfl⟩

/-- The merge relation of a list of permutations. -/
def Rel (σs : List (Equiv.Perm α)) : α → α → Prop :=
  fun x y => ∃ σ ∈ σs, σ x = y

theorem eqvGen_rel_cons_iff (σ : Equiv.Perm α) (σs : List (Equiv.Perm α))
    (x y : α) :
    EqvGen (Rel (σ :: σs)) x y ↔
      EqvGen (fun a b => Rel σs a b ∨ relOfPairs (pairsOf σ) a b) x y := by
  constructor
  · refine fun h => eqvGen_closure (fun a b hab => ?_) h
    obtain ⟨τ, hτ, rfl⟩ := hab
    rcases List.mem_cons.mp hτ with rfl | hτ2
    · exact eqvGen_mono (fun a b h => Or.inr h) (eqvGen_pairsOf_apply τ a)
    · exact EqvGen.rel _ _ (Or.inl ⟨τ, hτ2, rfl⟩)
  · refine fun h => eqvGen_closure (fun a b hab => ?_) h
    rcases hab with ⟨τ, hτ, rfl⟩ | hpair
    · exact EqvGen.rel _ _ ⟨τ, List.mem_cons_of_mem σ hτ, rfl⟩
    · obtain ⟨z, _, hz⟩ := List.mem_map.mp hpair
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hz
      exact EqvGen.rel _ _ ⟨σ, List.mem_cons_self .., rfl⟩

theorem eqvGen_rel_nil {a b : α}
    (h : EqvGen (Rel ([] : List (Equiv.Perm α))) a b) : a = b := by
  induction h with
  | rel x y hxy => obtain ⟨τ, hτ, _⟩ := hxy; exact (List.not_mem_nil hτ).elim
  | refl x => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem card_quot_rel_nil :
    Fintype.card (Quotient (EqvGen.setoid
      (Rel ([] : List (Equiv.Perm α))))) = Fintype.card α := by
  refine Fintype.card_congr
    ⟨Quotient.lift id fun a b hab => eqvGen_rel_nil hab,
     fun a => Quotient.mk _ a, ?_, ?_⟩
  · intro q; refine Quotient.inductionOn q fun a => rfl
  · intro a; rfl

/-- PAPER THEOREM 5.2 (counting form): merging along permutations
sigma_1, ..., sigma_k leaves at least  n - sum (|support| - 1)  classes.
With rho := classes/n and kappa_i := (|supp| - 1)/n this is the sharp
rate-curvature bound  rho >= 1 - sum kappa_i. -/
theorem orbit_rate_bound (σs : List (Equiv.Perm α)) :
    Fintype.card α ≤
      Fintype.card (Quotient (EqvGen.setoid (Rel σs)))
        + (σs.map fun σ => σ.support.card - 1).sum := by
  induction σs with
  | nil => simp [card_quot_rel_nil]
  | cons σ σs ih =>
    have hpairs := card_quot_pairs (Rel σs) (pairsOf σ)
    have hcongr := card_quot_eq_of_iff
      (EqvGen.setoid (fun a b => Rel σs a b ∨ relOfPairs (pairsOf σ) a b))
      (EqvGen.setoid (Rel (σ :: σs)))
      (fun a b => (eqvGen_rel_cons_iff σ σs a b).symm)
    calc Fintype.card α
        ≤ Fintype.card (Quotient (EqvGen.setoid (Rel σs)))
            + (σs.map fun σ => σ.support.card - 1).sum := ih
      _ ≤ (Fintype.card (Quotient (EqvGen.setoid
            (fun a b => Rel σs a b ∨ relOfPairs (pairsOf σ) a b)))
            + (pairsOf σ).length)
            + (σs.map fun σ => σ.support.card - 1).sum :=
          Nat.add_le_add_right hpairs _
      _ = Fintype.card (Quotient (EqvGen.setoid (Rel (σ :: σs))))
            + ((σ :: σs).map fun σ => σ.support.card - 1).sum := by
          rw [hcongr, pairsOf_length]
          simp only [List.map_cons, List.sum_cons]
          omega

end OrbitPerm

end CurvatureCalculus
