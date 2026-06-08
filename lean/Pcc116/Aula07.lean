import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Plausible

set_option autoImplicit false
set_option tactic.hygienic false

/-!
   Recursão geral
-/

/-! ## Divisão Euclidiana por Subtração Repetida -/

/-- Quociente da divisão euclidiana de `n` por `d`. -/

def natDiv (n d : ℕ) : ℕ :=
  if d = 0 ∨ n < d then 0
  else 1 + natDiv (n - d) d
termination_by n
decreasing_by omega

/-- Resto da divisão euclidiana de `n` por `d`. -/
def natMod (n d : ℕ) : ℕ :=
  if d = 0 ∨ n < d then n
  else natMod (n - d) d
termination_by n
decreasing_by omega

#eval natDiv 17  5    -- 3
#eval natMod 17  5    -- 2
#eval natDiv 10  3    -- 3
#eval natMod 10  3    -- 1
#eval natDiv  0  5    -- 0
#eval natMod  0  5    -- 0
#eval natDiv 10  0    -- 0   
#eval natMod 10  0    -- 10

-- Verificação empírica com Plausible
example (n d : ℕ) : d * natDiv n d + natMod n d = n 
  := by plausible


lemma natDiv_base (n d : ℕ) (h : d = 0 ∨ n < d) :
    natDiv n d = 0 := by
  rw [natDiv.eq_1, if_pos h]

lemma natDiv_step (n d : ℕ) (h : ¬(d = 0 ∨ n < d)) :
    natDiv n d = 1 + natDiv (n - d) d := by
  rw [natDiv.eq_1]
  exact if_neg h

lemma natMod_base (n d : ℕ) (h : d = 0 ∨ n < d) :
    natMod n d = n := by
  rw [natMod.eq_1, if_pos h]

lemma natMod_step (n d : ℕ) (h : ¬(d = 0 ∨ n < d)) :
    natMod n d = natMod (n - d) d := by
  rw [natMod.eq_1]
  exact if_neg h


/-- O resto é menor que o divisor (quando d ≠ 0).
    A prova usa a mesma recursão bem fundada em `n`. -/
theorem natMod_lt (n d : ℕ) (hd : d ≠ 0) : natMod n d < d := by
  by_cases h : d = 0 ∨ n < d
  · -- caso base: natMod n d = n; como d ≠ 0, temos n < d
    cases h with
    | inl h0 => exact absurd h0 hd
    | inr hn =>
      rw [natMod_base n d (Or.inr hn)]
      exact hn
  · -- natMod n d = natMod (n - d) d
    rw [natMod_step n d h]
    apply natMod_lt
    exact hd
termination_by n
decreasing_by omega

/-- divisão euclidiana: d · q + r = n. -/
theorem div_spec (n d : ℕ) : 
  d * natDiv n d + natMod n d = n := by
  by_cases h : d = 0 ∨ n < d
  · rw [natDiv_base n d h, natMod_base n d h]
    simp
  · rw [natDiv_step n d h, natMod_step n d h]
    have IH  : d * natDiv (n - d) d + 
               natMod (n - d) d = n - d :=
      div_spec (n - d) d
    have hge : d ≤ n := by
      push Not at h; omega
    rw [Nat.mul_add, Nat.mul_one]
    omega
termination_by n
decreasing_by omega

/- ## Intercalação de Listas Ordenadas -/

inductive Sorted : List ℕ → Prop where
  | nil  : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ}
      (hle : x ≤ y) (hs : Sorted (y :: zs)) :
      Sorted (x :: y :: zs)

inductive Perm {α : Type} : List α → List α → Prop where
  | nil  : Perm [] []
  | skip (x : α) {xs ys : List α} :
      Perm xs ys → Perm (x :: xs) (x :: ys)
  | swap (x y : α) (xs : List α) :
      Perm (x :: y :: xs) (y :: x :: xs)
  | trans {xs ys zs : List α} :
      Perm xs ys → Perm ys zs → Perm xs zs

infix:50 " ~ " => Perm

private lemma Perm_refl {α : Type} (xs : List α) : xs ~ xs := by
  induction xs with
  | nil         => exact Perm.nil
  | cons x xs IH => apply Perm.skip; exact IH

private lemma Perm_sym {α : Type} {xs ys : List α} (h : xs ~ ys) : ys ~ xs := by
  induction h with
  | nil             => exact Perm.nil
  | skip x _ IH     => apply Perm.skip; exact IH
  | swap x y zs     => apply Perm.swap
  | trans _ _ IH1 IH2 =>
    apply Perm.trans
    · exact IH2
    · exact IH1

/-- Intercalação ordenada de duas listas. -/
def merge : List ℕ → List ℕ → List ℕ
  | [],      ys      => ys
  | x :: xs, []     => x :: xs
  | x :: xs, y :: ys =>
      if x ≤ y then x :: merge xs (y :: ys)
      else          y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length
decreasing_by
  all_goals (simp only [List.length_cons]; omega)

#eval merge [1, 3, 5] [2, 4, 6]  -- [1, 2, 3, 4, 5, 6]
#eval merge [] [1, 2, 3]          -- [1, 2, 3]
#eval merge [1, 2, 3] []          -- [1, 2, 3]

def isSorted : List ℕ → Bool
  | [] | [_]         => true
  | x :: y :: t => x ≤ y && isSorted (y :: t)

def isPermOf (xs ys : List ℕ) : Bool :=
  (xs ++ ys).all (fun n => xs.count n == ys.count n)

example (xs ys : List ℕ) :
    isSorted xs = true → 
    isSorted ys = true → 
    isSorted (merge xs ys) = true := by
  plausible

example (xs ys : List ℕ) : isPermOf (xs ++ ys) (merge xs ys) = true := by
  plausible


lemma merge_le (x : ℕ) (xs : List ℕ) (y : ℕ) (ys : List ℕ) (h : x ≤ y) :
    merge (x :: xs) (y :: ys) = x :: merge xs (y :: ys) := by
  rw [merge.eq_3, if_pos h]

lemma merge_gt (x : ℕ) (xs : List ℕ) (y : ℕ) (ys : List ℕ) (h : ¬ x ≤ y) :
    merge (x :: xs) (y :: ys) = y :: merge (x :: xs) ys := by
  rw [merge.eq_3]; exact if_neg h

/-- Em uma lista ordenada `x :: xs`, `x` minora todos os elementos de `xs`. -/
lemma sorted_head_le : ∀ (x : ℕ) (xs : List ℕ), Sorted (x :: xs) → ∀ z ∈ xs, x ≤ z := by
  intro x xs
  induction xs generalizing x with
  | nil =>
    intro _ z hz
    exact absurd hz List.not_mem_nil
  | cons y ys IH =>
    intro hs z hz
    cases hs with
    | two_or_more _ _ hle hs' =>
      rw [List.mem_cons] at hz
      rcases hz with rfl | hmem
      · exact hle
      · exact Nat.le_trans hle (IH y hs' z hmem)

lemma merge_lb (a : ℕ) : ∀ (xs ys : List ℕ),
    (∀ z ∈ xs, a ≤ z) → 
    (∀ z ∈ ys, a ≤ z) → 
    ∀ z ∈ merge xs ys, a ≤ z := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ hys z hz
    rw [merge.eq_1] at hz
    exact hys z hz
  | cons x xs IHxs =>
    intro ys
    induction ys with
    | nil =>
      intro hxs _ z hz
      rw [merge.eq_2] at hz
      exact hxs z hz
    | cons y ys IHys =>
      intro hxs hys z hz
      by_cases h : x ≤ y
      · rw [merge_le x xs y ys h] at hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hmem
        · apply hxs; exact List.mem_cons.mpr (Or.inl rfl)
        · exact IHxs (y :: ys)
            (fun w hw => hxs w (List.mem_cons_of_mem x hw))
            hys z hmem
      · rw [merge_gt x xs y ys h] at hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hmem
        · apply hys; exact List.mem_cons.mpr (Or.inl rfl)
        · exact IHys hxs
            (fun w hw => hys w (List.mem_cons_of_mem y hw))
            z hmem

theorem merge_sorted : ∀ xs ys, 
    Sorted xs → 
    Sorted ys → 
    Sorted (merge xs ys) := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ hys
    rw [merge.eq_1]
    exact hys
  | cons x xs IHxs =>
    intro ys hxs hys
    induction ys with
    | nil =>
      rw [merge.eq_2]; exact hxs
    | cons y ys IHys =>
      by_cases h : x ≤ y
      · -- merge (x::xs) (y::ys) = x :: merge xs (y::ys)
        rw [merge_le x xs y ys h]
        have hxs' : Sorted xs :=
          match hxs with
          | Sorted.single _        => Sorted.nil
          | Sorted.two_or_more _ _ _ hs => hs
        have hsm : Sorted (merge xs (y :: ys)) := 
          IHxs (y :: ys) hxs' hys
        cases hmerge : merge xs (y :: ys) with
        | nil => exact Sorted.single x
        | cons w ws =>
          apply Sorted.two_or_more
          · have hmem : w ∈ merge xs (y :: ys) := 
              hmerge ▸ List.mem_cons.mpr (Or.inl rfl)
            exact merge_lb x xs (y :: ys)
              (sorted_head_le x xs hxs)
              (fun z hz => by
                rw [List.mem_cons] at hz
                rcases hz with rfl | hmem'
                · exact h
                · exact Nat.le_trans h (sorted_head_le y ys hys z hmem'))
              w hmem
          · rw [← hmerge]; exact hsm
      · rw [merge_gt x xs y ys h]
        have hys' : Sorted ys :=
          match hys with
          | Sorted.single _        => Sorted.nil
          | Sorted.two_or_more _ _ _ hs => hs
        have hsm : Sorted (merge (x :: xs) ys) := IHys hys'
        cases hmerge : merge (x :: xs) ys with
        | nil => exact Sorted.single y
        | cons w ws =>
          apply Sorted.two_or_more
          · have hmem : w ∈ merge (x :: xs) ys := 
              hmerge ▸ List.mem_cons.mpr (Or.inl rfl)
            have hyx : y ≤ x := 
              Nat.le_of_lt (Nat.lt_of_not_le h)
            exact merge_lb y (x :: xs) ys
              (fun z hz => by
                rw [List.mem_cons] at hz
                rcases hz with rfl | hmem'
                · exact hyx
                · exact Nat.le_trans hyx 
                      (sorted_head_le x xs hxs z hmem'))
              (sorted_head_le y ys hys)
              w hmem
          · rw [← hmerge]; exact hsm

lemma Perm_middle {α : Type} (x : α) (xs ys : List α) :
    x :: (xs ++ ys) ~ xs ++ (x :: ys) := by
  induction xs with
  | nil       => exact Perm_refl _
  | cons a xs IH =>
    apply Perm.trans
    · apply Perm.swap
    · apply Perm.skip; exact IH

theorem merge_perm : ∀ xs ys, xs ++ ys ~ merge xs ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys; rw [merge.eq_1]; exact Perm_refl ys
  | cons x xs IHxs =>
    intro ys
    induction ys with
    | nil =>
      rw [merge.eq_2, List.append_nil]
      exact Perm_refl _
    | cons y ys IHys =>
      by_cases h : x ≤ y
      · rw [merge_le x xs y ys h]
        apply Perm.skip
        exact IHxs (y :: ys)
      · rw [merge_gt x xs y ys h]
        apply Perm.trans
        · exact Perm_sym (Perm_middle y (x :: xs) ys)
        · apply Perm.skip; exact IHys


