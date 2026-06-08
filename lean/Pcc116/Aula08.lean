import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option tactic.hygienic false
set_option linter.hashCommand false

/-! # Programação com Tipos Dependentes -/


/-! ## Subtipos e o Predecessor Seguro -/


/-- Predecessor com pré-condição -/

def pred1 (n : ℕ) (_ : n > 0) : ℕ := n - 1

#eval pred1 5 (by omega)   -- 4

def pred2 (n : ℕ) (h : n > 0) : {m : ℕ // n = m + 1} :=
  ⟨n - 1, by omega⟩

#eval (pred2 5 (by omega)).val        -- 4
#eval (pred2 8 (by omega)).val        -- 7

-- Os dois componentes do par:
example : (pred2 5 (by omega)).val = 4           := rfl
example : (pred2 5 (by omega)).property = rfl    := rfl

def pred3 : (n : ℕ) → n > 0 → {m : ℕ // n = Nat.succ m}
  | Nat.succ k, _ => ⟨k, rfl⟩
  | 0,          h => absurd h (by omega)

#eval (pred3 7 (by omega)).val        -- 6
#eval (pred3 1 (by omega)).val        -- 0

example (h : 10 > 0) : 10 = Nat.succ (pred3 10 h).val :=
  (pred3 10 h).property

/- Listas Indexadas por Comprimento -/

inductive IList (A : Type) : ℕ → Type where
  | inil  : IList A 0
  | icons {n : ℕ} : A → IList A n → IList A (n + 1)

def ihead {A : Type} {n : ℕ} : IList A (n + 1) → A
  | .icons x _ => x

def itail {A : Type} {n : ℕ} : IList A (n + 1) → IList A n
  | .icons _ xs => xs

def iapp {A : Type} 
      : ∀ {m n : ℕ}, IList A m → 
                     IList A n → 
                     IList A (m + n)
  | 0,     n, .inil,       ys => (Nat.zero_add n).symm ▸ ys
  | m + 1, n, .icons x xs, ys =>
      have h : m + n + 1 = m + 1 + n := by omega
      h ▸ .icons x (iapp xs ys)

def inject {A : Type} : (l : List A) → IList A l.length
  | []      => .inil
  | x :: xs => .icons x (inject xs)

def eject {A : Type} {n : ℕ} : IList A n → List A
  | .inil       => []
  | .icons x xs => x :: eject xs

theorem eject_inject {A : Type} (l : List A) : eject (inject l) = l := by
  induction l with
  | nil         => rfl
  | cons x xs IH => simp [inject, eject, IH]

#eval ihead (.icons 1 (.icons 2 (.icons 3 .inil)))   -- 1
#eval eject (iapp (.icons 1 (.icons 2 .inil)) (.icons 3 .inil))  -- [1, 2, 3]

/-! Índices Seguros -/

inductive Idx : ℕ → Type where
  | zero {n : ℕ} : Idx (n + 1)
  | succ {n : ℕ} : Idx n → Idx (n + 1)

def iget {A : Type} : ∀ {n : ℕ}, IList A n → Idx n → A
  | _, .icons x _,  .zero    => x
  | _, .icons _ xs, .succ i  => iget xs i


private def lista123 : IList ℕ 3 := .icons 10 (.icons 20 (.icons 30 .inil))

#eval iget lista123 .zero
#eval iget lista123 (.succ .zero)
#eval iget lista123 (.succ (.succ .zero))


/- Listas Heterogêneas -/

universe u v

inductive HList {α : Type u} (B : α → Type v) : List α → Type (max u v) where
  | hnil  : HList B []
  | hcons {t : α} {ts : List α} : B t → HList B ts → HList B (t :: ts)

/-- Cabeça de uma `HList` não-vazia. -/
def hhd {α : Type u} {B : α → Type v} {t : α} {ts : List α} :
    HList B (t :: ts) → B t
  | .hcons x _ => x

/-- Cauda de uma `HList` não-vazia. -/
def htl {α : Type u} {B : α → Type v} {t : α} {ts : List α} :
    HList B (t :: ts) → HList B ts
  | .hcons _ xs => xs

/-- Concatenação: os esquemas se concatenam por `++`. -/

def happ {α : Type u} {B : α → Type v} :
    ∀ {ts ss : List α}, HList B ts → HList B ss → HList B (ts ++ ss)
  | [],     _, .hnil,       ys => ys
  | _ :: _, _, .hcons x xs, ys => .hcons x (happ xs ys)

inductive HMember {α : Type u} (t : α) : List α → Type u where
  | head {ts : List α} : HMember t (t :: ts)
  | tail {s : α} {ts : List α} 
    : HMember t ts → HMember t (s :: ts)

def hget {α : Type u} {B : α → Type v} {t : α} :
    ∀ {ts : List α}, HList B ts → HMember t ts → B t
  | _ :: _, .hcons x _,  .head   => x
  | _ :: _, .hcons _ xs, .tail m => hget xs m

@[reducible]
def FHList {α : Type} (B : α → Type) : List α → Type
  | []      => Unit
  | t :: ts => B t × FHList B ts

@[reducible]
def FHMember {α : Type} (t : α) : List α → Type
  | []      => Empty
  | s :: ts => Sum (PLift (s = t)) (FHMember t ts)

def fhget {α : Type} {B : α → Type} {t : α} :
    ∀ {ts : List α}, FHList B ts → FHMember t ts → B t
  | [],     _,   idx              => Empty.elim idx
  | _ :: _, fls, Sum.inl ⟨rfl⟩  => fls.1
  | _ :: _, fls, Sum.inr idx     => fhget fls.2 idx

/-! ### Exemplo: registros heterogêneos -/

inductive TipoBase where | TNat | TBool | TString deriving Repr

@[reducible]
def denotaBase : TipoBase → Type
  | .TNat    => ℕ
  | .TBool   => Bool
  | .TString => String

-- Esquema: [ℕ, Bool, String]
private def esquema : List TipoBase := [.TNat, .TBool, .TString]

private def registro : HList denotaBase esquema :=
  .hcons 42 (.hcons true (.hcons "Lean" .hnil))

#eval hhd registro                                   -- 42
#eval hhd (htl registro)                             -- true
#eval hget registro .head                            -- 42
#eval hget registro (.tail .head)                    -- true
#eval hget registro (.tail (.tail .head))            -- "Lean"

-- Variante recursiva com os mesmos dados
-- FHList denotaBase esquema = ℕ × Bool × String × Unit
private def registroF : FHList denotaBase esquema :=
  (42, (true, ("Lean", ())))

#eval fhget registroF (.inl ⟨rfl⟩)                  -- 42
#eval fhget registroF (.inr (.inl ⟨rfl⟩))           -- true
#eval fhget registroF (.inr (.inr (.inl ⟨rfl⟩)))    -- "Lean"

-- Concatenação de HLists
private def esquema2 : List TipoBase := [.TNat]
private def registro2 : HList denotaBase esquema2 := .hcons 100 .hnil

-- O índice .tail^3 .head acessa a 4.ª posição (primeiro elemento de registro2)
#eval hget (happ registro registro2) (.tail (.tail (.tail .head)))  -- 100
