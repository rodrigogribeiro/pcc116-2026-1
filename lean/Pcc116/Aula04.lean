import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option tactic.hygienic false

/- Even numbers -/ 

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

example : Even 4 := by 
  apply Even.add_two
  apply Even.add_two
  apply Even.zero 
  
example : ¬ Even 3 := by 
  intro H 
  cases H 
  simp at *
  cases a 

def evenRec : ℕ → Bool
  | 0     => true
  | 1     => false
  | k + 2 => evenRec k

lemma Even_twice (n : ℕ) 
  : Even (2 * n) := by 
  induction n with 
  | zero => 
    simp 
    constructor
  | succ m IHm => 
    rw [Nat.mul_add]
    simp 
    apply Even.add_two
    exact IHm 


lemma Even_add (n m : ℕ) 
  : Even n → Even m → Even (n + m) := by 
    intros Hn 
    revert m 
    induction Hn with 
    | zero => 
      intros p Hp 
      simp 
      exact Hp 
    | add_two p Hp IHp => 
      intros m Hm 
      rw [ Nat.add_assoc
         , Nat.add_comm 2 _
         , <- Nat.add_assoc
         ]
      apply Even.add_two
      apply IHp
      exact Hm 

lemma Even_inversion (n : ℕ) 
  : n = 0 ∨ ∃ m, n = m + 2 := by sorry 

theorem Even_evenRec (n : ℕ) 
  : Even n → evenRec n = true := by sorry 

theorem evenRec_Even (n : ℕ) 
  : evenRec n = true → Even n := by sorry 

lemma add_Even (n m : ℕ) 
  : Even (n + m) → Even n → Even m := by sorry 

def evenDec (n : ℕ) : Decidable (Even n) := 
  match n with 
  | 0 => Decidable.isTrue Even.zero
  | 1 => Decidable.isFalse 
            (by 
              intro Hc
              cases Hc) 
  | k + 2 => 
    match evenDec k with 
    | Decidable.isTrue p => 
        Decidable.isTrue (Even.add_two _ p) 
    | Decidable.isFalse np => 
        Decidable.isFalse (by 
          intros Hc 
          cases Hc 
          contradiction)

#print Decidable 

/- list membership -/

section MEMBERSHIP

variable {a : Type} 

inductive Mem (x : a) : List a -> Prop where 
| Here : ∀ {xs}, Mem x (x :: xs)
| There : ∀ {y ys}, 
    Mem x ys → 
    Mem x (y :: ys) 

example : Mem 1 [2, 3, 1, 5] := by 
  apply Mem.There
  apply Mem.There  
  apply Mem.Here

lemma Mem_append_left xs (x : a)
  : ∀ ys, Mem x xs → Mem x (xs ++ ys) := by 
    intros ys Hxs 
    revert ys 
    induction Hxs with
    | Here => 
      intros ys 
      apply Mem.Here 
    | There Hx IHx => 
      intros zs 
      apply Mem.There 
      apply IHx

lemma Mem_append_right xs (x : a)
  : ∀ ys, Mem x ys → Mem x (xs ++ ys) := sorry 

lemma Mem_append_inv (x : a) 
  : ∀ xs ys, Mem x (xs ++ ys) → 
             Mem x xs ∨ Mem x ys := sorry 

def Mem_dec [DecidableEq a] (x : a) (xs : List a) 
    : Decidable (Mem x xs) 
  := match xs with 
     | [] => 
        Decidable.isFalse 
            (by
              intros H 
              cases H) 
     | y :: ys => 
      match decEq x y with 
      | isFalse np => 
        match Mem_dec x ys with 
        | isFalse npp => by 
          apply Decidable.isFalse 
          intros H 
          cases H 
          · contradiction
          · contradiction
        | isTrue pp => by 
          apply Decidable.isTrue 
          apply Mem.There 
          exact pp 
      | isTrue p => by 
         rw [p] 
         apply Decidable.isTrue 
         exact Mem.Here 

end MEMBERSHIP 


/- Conectivos lógicos -/ 

namespace logical_symbols

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀a : α, P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀ x : α, Eq x x

end logical_symbols

#print And
#print Or
#print Iff
#print Exists
#print True
#print False
#print Eq

/- Rule Induction -/

theorem mod_two_Eq_zero_of_Even 
    (n : ℕ) (h : Even n) :
    n % 2 = 0 :=
  by
    induction h with 
    | zero =>
      simp 
    | add_two k Hk IHk => 
      simp [IHk]

theorem Not_Even_two_mul_add_one (m n : ℕ)
      (hm : m = 2 * n + 1) :
    ¬ Even m :=
  by
    intros Hcontra 
    have H1 : m % 2 = 0 := by 
      apply mod_two_Eq_zero_of_Even 
      assumption 
    rw [hm] at H1 
    simp at *

theorem omega_example (i : Int) (hi : i > 5) :
    2 * i + 3 > 11 :=
  by omega 

/- Elimination -/

theorem Even_Iff (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  by
    sorry

/- Sorted Lists -/

inductive Sorted : List ℕ → Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} 
        (hle : x ≤ y)
      : Sorted (y :: zs) -> 
        Sorted (x :: y :: zs)

theorem Sorted_2 :
    Sorted [2] :=
  Sorted.single 2

theorem Sorted_3_5 :
    Sorted [3, 5] :=
  by
    apply Sorted.two_or_more
    { simp }
    { constructor }

theorem sorted_7_9_9_11 :
    Sorted [7, 9, 9, 11] := by 
    apply Sorted.two_or_more 
    · simp 
    · apply Sorted.two_or_more 
      · simp 
      · apply Sorted.two_or_more 
        · simp 
        · apply Sorted.single 

theorem Not_Sorted_17_13 :
    ¬ Sorted [17, 13] :=
  by
    intro h
    cases h with
    | two_or_more _ _ hlet hsorted =>
      simp at hlet

/- Permutations -/

inductive Perm {a : Type} 
    : List a → List a → Prop where
  | nil : Perm [] []
  | skip (x : a) {xs ys : List a} 
      : Perm xs ys → 
        Perm (x :: xs) (x :: ys)
  | swap (x y : a) (xs : List a) 
      : Perm (x :: y :: xs) (y :: x :: xs)
  | trans {xs ys zs : List a} 
      : Perm xs ys → 
        Perm ys zs → 
        Perm xs zs

infix:50 " ~b " => Perm

lemma Perm_refl {a : Type} 
  : ∀ (xs : List a), xs ~b xs := by
    intros xs 
    induction xs with 
    | nil => 
      constructor 
    | cons y ys IHys => 
      apply Perm.skip
      exact IHys 

lemma Perm_sym {a : Type} 
  : ∀ (xs ys : List a), 
        xs ~b ys → 
        ys ~b xs := by 
    intros xs ys H 
    induction H with 
    | nil => 
      constructor
    | skip x H IH =>
      apply Perm.skip 
      exact IH 
    | swap x y zs =>
      apply Perm.swap 
    | trans H1 H2 IH1 IH2 =>
      apply Perm.trans 
      · exact IH2 
      · exact IH1 




