import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic 


def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)


theorem add_comm (n m : ℕ) : n + m = m + n := sorry 
theorem add_assoc (n m p : ℕ) 
  : n + (m + p) = (n + m) + p := sorry 

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m := sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) := sorry

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs := sorry


inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | mul : AExp → AExp → AExp

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i      => i
  | AExp.var x      => env x
  | AExp.add e₁ e₂  => eval env e₁ + eval env e₂
  | AExp.mul e₁ e₂  => eval env e₁ * eval env e₂

def simplify : AExp → AExp := sorry 



