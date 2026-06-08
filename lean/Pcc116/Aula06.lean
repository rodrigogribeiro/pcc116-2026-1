import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Plausible

set_option autoImplicit false
set_option tactic.hygienic false

/- Ordered insertion -/

def ins (x : ℕ) : List ℕ → List ℕ
  | []      => [x]
  | y :: ys =>
    if x <= y then x :: y :: ys
    else y :: ins x ys

/- Insertion sort -/

def isort : List ℕ → List ℕ
  | []      => []
  | x :: xs => ins x (isort xs)

/-
  Property-based testing with Plausible.
-/

def isSorted : List ℕ → Bool
  | []           => true
  | [_]          => true
  | x :: y :: t => x ≤ y && isSorted (y :: t)

def isPermOf (xs ys : List ℕ) : Bool :=
  (xs ++ ys).all (fun n => xs.count n == ys.count n)

/- Teste 1: ins preserva a ordenação -/
example (x : ℕ) (xs : List ℕ) :
    isSorted xs = true → isSorted (ins x xs) = true := by
  plausible

/- Teste 2: x :: xs é permutação de ins x xs -/
example (x : ℕ) (xs : List ℕ) :
    isPermOf (x :: xs) (ins x xs) = true := by
  plausible

/- Teste 3: isort sempre produz lista ordenada -/
example (xs : List ℕ) :
    isSorted (isort xs) = true := by
  plausible

/- Teste 4: isort xs é permutação de xs -/
example (xs : List ℕ) :
    isPermOf xs (isort xs) = true := by
  plausible


/- Sorted lists -/

inductive Sorted : List ℕ → Prop where
  | nil  : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ)
                {zs : List ℕ}
                (hle : x ≤ y)
                (hsorted : Sorted (y :: zs)) :
      Sorted (x :: y :: zs)

/- Permutations -/

inductive Perm {a : Type} : List a → List a → Prop where
  | nil  : Perm [] []
  | skip (x : a) {xs ys : List a} :
      Perm xs ys →
      Perm (x :: xs) (x :: ys)
  | swap (x y : a) (xs : List a)  :
      Perm (x :: y :: xs) (y :: x :: xs)
  | trans {xs ys zs : List a}     :
      Perm xs ys →
      Perm ys zs →
      Perm xs zs

infix:50 " ~ " => Perm

lemma Perm_refl {a : Type} : ∀ (xs : List a), xs ~ xs := by
  intro xs
  induction xs with
  | nil          => exact Perm.nil
  | cons x xs IH =>
    apply Perm.skip
    assumption

lemma Perm_sym {a : Type} : ∀ (xs ys : List a), xs ~ ys → ys ~ xs := by
  intros xs ys H
  induction H with
  | nil => exact Perm.nil
  | skip x _ IH =>
    apply Perm.skip
    assumption
  | swap x y zs =>
    apply Perm.swap
  | trans _ _ IH1 IH2 =>
    apply Perm.trans
    · assumption
    · assumption


-- Equations for ins; `change` uses definitional equality to expose these forms.
#check if_pos 
private lemma ins_pos {x y : ℕ} (ys : List ℕ) (h : x ≤ y) :
    ins x (y :: ys) = x :: y :: ys := by
  change (if x ≤ y then x :: y :: ys else y :: ins x ys) = x :: y :: ys
  exact if_pos h

private lemma ins_neg {x y : ℕ} (ys : List ℕ) (h : ¬ x ≤ y) :
    ins x (y :: ys) = y :: ins x ys := by
  change (if x ≤ y then x :: y :: ys else y :: ins x ys) = y :: ins x ys
  exact if_neg h

/-
  Helper lemma for ins_sorted:
  if y ≤ x and y :: xs is sorted and ins x xs is sorted,
  then y :: ins x xs is also sorted.
  The head of (ins x xs) is either x or the original head of xs, both ≥ y.
-/
private lemma ins_sorted_aux (y x : ℕ) (xs : List ℕ)
    (hyx : y ≤ x) (hys : Sorted (y :: xs)) (hins : Sorted (ins x xs)) :
    Sorted (y :: ins x xs) := by
  cases xs with
  | nil =>
    -- ins x [] reduces to [x], head is x, and y ≤ x
    apply Sorted.two_or_more
    · assumption
    · assumption
  | cons z zs =>
    have hyz : y ≤ z := by cases hys with | two_or_more _ _ h _ => exact h
    by_cases hxz : x ≤ z
    · -- head of ins x (z :: zs) is x; y ≤ x
      rw [ins_pos zs hxz] at hins ⊢
      apply Sorted.two_or_more
      · assumption
      · assumption
    · -- head of ins x (z :: zs) is z; y ≤ z
      rw [ins_neg zs hxz] at hins ⊢
      apply Sorted.two_or_more
      · assumption
      · assumption

/- Theorem 1: ins preserves Sorted -/

theorem ins_sorted (x : ℕ) : ∀ xs, Sorted xs → Sorted (ins x xs) := by
  intro xs hxs
  induction hxs with
  | nil =>
    apply Sorted.single
  | single y =>
    by_cases h : x ≤ y
    · rw [ins_pos [] h]
      apply Sorted.two_or_more
      · assumption
      · apply Sorted.single
    · rw [ins_neg [] h]
      apply Sorted.two_or_more
      · omega
      · apply Sorted.single
  | two_or_more y z hyz hsorted IH =>
    by_cases hxy : x ≤ y
    · rw [ins_pos (z :: zs) hxy]
      apply Sorted.two_or_more
      · assumption
      · apply Sorted.two_or_more
        · assumption
        · assumption
    · rw [ins_neg (z :: zs) hxy]
      apply ins_sorted_aux
      · omega
      · apply Sorted.two_or_more
        · assumption
        · assumption
      · assumption

/- Theorem 2: x :: xs is a permutation of ins x xs -/

theorem ins_perm (x : ℕ) : ∀ xs, (x :: xs) ~ (ins x xs) := by
  intro xs
  induction xs with
  | nil =>
    -- ins x [] = [x], so [x] ~ [x]
    apply Perm_refl
  | cons y ys IH =>
    by_cases h : x ≤ y
    · rw [ins_pos ys h]
      apply Perm_refl
    · rw [ins_neg ys h]
      -- x :: y :: ys ~(swap)~ y :: x :: ys ~(skip,IH)~ y :: ins x ys
      apply Perm.trans
      · apply Perm.swap
      · apply Perm.skip
        assumption

/- Theorem 3: isort returns a sorted list -/

theorem isort_sorted : ∀ xs, Sorted (isort xs) := by
  intro xs
  induction xs with
  | nil       => exact Sorted.nil
  | cons x xs IH =>
    apply ins_sorted
    assumption

/- Theorem 4: isort xs is a permutation of xs -/

theorem isort_perm : ∀ xs, xs ~ isort xs := by
  intro xs
  induction xs with
  | nil       => exact Perm.nil
  | cons x xs IH =>
    -- x :: xs ~(skip,IH)~ x :: isort xs ~(ins_perm)~ ins x (isort xs)
    apply Perm.trans
    · apply Perm.skip
      assumption
    · apply ins_perm


