/-!
# Lista de Exercícios

---

## Instruções gerais

Cada exercício abaixo deve ser resolvido em Lean 4 substituindo `sorry`
por uma prova ou definição completa. Sempre que possível, prefira provas
estruturais (por `induction`, `cases`, `match`) em vez de táticas
automáticas como `decide` ou `omega`, salvo quando o objetivo for
justamente exercitar essas táticas. Você pode usar `simp` com lemas
auxiliares, mas o foco é raciocínio indutivo explícito.

Em vários exercícios usamos as próprias definições de `Nat`, `List`,
etc., mas você pode usar as definições da biblioteca padrão quando o
enunciado pedir explicitamente.
-/

namespace Exercicios

/-!
---

## Parte 1 — Indução sobre números naturais

Nesta parte, considere a definição usual:
-/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

/-!
Você pode resolver os exercícios usando `MyNat` (definindo `add`, `sub`,
etc. do zero) **ou** usando o tipo `Nat` da biblioteca padrão. O
enunciado de cada exercício indica qual versão preferir.

### 1.1 Adição

Defina, se ainda não tiver, a função de adição recursivamente sobre o
segundo argumento:
-/

def MyNat.add : MyNat → MyNat → MyNat
  | n, .zero => n
  | n, .succ m => .succ (MyNat.add n m)

/-! **Exercício 1.** Prove que zero é elemento neutro à esquerda: -/

theorem add_zero_left (n : MyNat) : MyNat.add .zero n = n := by
  sorry

-- Exercício 1: zero à esquerda não altera n
#eval MyNat.add .zero .zero                  -- MyNat.zero
#eval MyNat.add .zero (.succ .zero)          -- MyNat.succ MyNat.zero
#eval MyNat.add .zero (.succ (.succ .zero))  -- MyNat.succ (MyNat.succ MyNat.zero)

/-! **Exercício 2.** Prove a comutatividade da soma: -/

theorem add_comm (n m : MyNat) : MyNat.add n m = MyNat.add m n := by
  sorry

-- Exercício 2: add(1,2) = add(2,1)
#eval MyNat.add (.succ .zero) (.succ (.succ .zero))  -- succ (succ (succ zero))
#eval MyNat.add (.succ (.succ .zero)) (.succ .zero)  -- succ (succ (succ zero))

/-! **Exercício 3.** Prove a associatividade: -/

theorem add_assoc (n m k : MyNat) :
    MyNat.add (MyNat.add n m) k = MyNat.add n (MyNat.add m k) := by
  sorry

-- Exercício 3: (1+1)+1 = 1+(1+1) = 3
#eval MyNat.add (MyNat.add (.succ .zero) (.succ .zero)) (.succ .zero)
#eval MyNat.add (.succ .zero) (MyNat.add (.succ .zero) (.succ .zero))

/-!
**Exercício 4.** Usando `Nat` da biblioteca padrão, prove que
`n + n = 2 * n` sem usar `ring` nem `omega`, apenas indução e os lemas
básicos `Nat.mul_succ`, `Nat.mul_zero`:
-/

theorem dobro (n : Nat) : n + n = 2 * n := by
  sorry

-- Exercício 4: n + n e 2 * n devem coincidir
#eval (3 : Nat) + 3    -- 6
#eval 2 * (3 : Nat)    -- 6
#eval (5 : Nat) + 5    -- 10
#eval 2 * (5 : Nat)    -- 10

/-!
### 1.2 Subtração truncada

Em `Nat`, a subtração é truncada: `0 - k = 0`. Defina:
-/

def MyNat.sub : MyNat → MyNat → MyNat
  | n, .zero => n
  | .zero, .succ _ => .zero
  | .succ n, .succ m => MyNat.sub n m

/-! **Exercício 5.** Prove que subtrair zero não altera o número: -/

theorem sub_zero (n : MyNat) : MyNat.sub n .zero = n := by
  sorry

-- Exercício 5: sub n zero = n
#eval MyNat.sub .zero .zero                  -- MyNat.zero
#eval MyNat.sub (.succ .zero) .zero          -- MyNat.succ MyNat.zero
#eval MyNat.sub (.succ (.succ .zero)) .zero  -- MyNat.succ (MyNat.succ MyNat.zero)

/-! **Exercício 6.** Prove que todo natural subtraído de si mesmo dá zero: -/

theorem sub_self (n : MyNat) : MyNat.sub n n = .zero := by
  sorry

-- Exercício 6: sub n n = zero
#eval MyNat.sub .zero .zero                                         -- MyNat.zero
#eval MyNat.sub (.succ .zero) (.succ .zero)                         -- MyNat.zero
#eval MyNat.sub (.succ (.succ .zero)) (.succ (.succ .zero))         -- MyNat.zero

/-!
**Exercício 7.** Prove em `Nat` (biblioteca padrão) que a subtração não
distribui livremente — mais especificamente, prove a desigualdade fraca:
-/

theorem sub_add_le (n m : Nat) : n - m + m ≥ n ∨ n ≤ m := by
  sorry

-- Exercício 7: n - m + m recupera n (ou n ≤ m)
#eval (5 - 3 + 3 : Nat)  -- 5  (≥ 5; primeiro disjunto)
#eval (3 - 5 + 5 : Nat)  -- 5  (3 ≤ 5; segundo disjunto)
#eval (0 - 2 + 2 : Nat)  -- 2  (0 ≤ 2; segundo disjunto)

/-!
Ou seja: ou `(n - m) + m` recupera `n`, ou então `n ≤ m` e o lado
esquerdo se anula trivialmente. Faça a prova por indução em `m` (ou em
`n`), evitando `omega`.

**Exercício 8.** Prove que a subtração é "monotônica decrescente" no
segundo argumento:
-/

theorem sub_le (n m : Nat) : n - m ≤ n := by
  sorry

-- Exercício 8: n - m ≤ n
#eval (5 - 0 : Nat)  -- 5  (≤ 5)
#eval (5 - 3 : Nat)  -- 2  (≤ 5)
#eval (5 - 7 : Nat)  -- 0  (≤ 5)
#eval (0 - 3 : Nat)  -- 0  (≤ 0)

/-!
### 1.3 Máximo e mínimo

Defina o máximo e o mínimo entre dois naturais:
-/

def MyNat.max : MyNat → MyNat → MyNat
  | .zero, m => m
  | n, .zero => n
  | .succ n, .succ m => .succ (MyNat.max n m)

def MyNat.min : MyNat → MyNat → MyNat
  | .zero, _ => .zero
  | _, .zero => .zero
  | .succ n, .succ m => .succ (MyNat.min n m)

/-! **Exercício 9.** Prove a comutatividade de `max`: -/

theorem max_comm (n m : MyNat) : MyNat.max n m = MyNat.max m n := by
  sorry

-- Exercício 9: max(1,2) = max(2,1)
#eval MyNat.max (.succ .zero) (.succ (.succ .zero))  -- succ (succ zero)  [= 2]
#eval MyNat.max (.succ (.succ .zero)) (.succ .zero)  -- succ (succ zero)  [= 2]

/-! **Exercício 10.** Prove a idempotência de `min`: -/

theorem min_idem (n : MyNat) : MyNat.min n n = n := by
  sorry

-- Exercício 10: min(n,n) = n
#eval MyNat.min .zero .zero                                  -- MyNat.zero
#eval MyNat.min (.succ .zero) (.succ .zero)                  -- MyNat.succ MyNat.zero
#eval MyNat.min (.succ (.succ .zero)) (.succ (.succ .zero))  -- succ (succ zero)

/-! **Exercício 11.** Prove a associatividade de `max`: -/

theorem max_assoc (n m k : MyNat) :
    MyNat.max (MyNat.max n m) k = MyNat.max n (MyNat.max m k) := by
  sorry

-- Exercício 11: max(max(1,3),2) = max(1,max(3,2)) = 3
private def n1 : MyNat := .succ .zero
private def n2 : MyNat := .succ (.succ .zero)
private def n3 : MyNat := .succ (.succ (.succ .zero))
#eval MyNat.max (MyNat.max n1 n3) n2  -- succ (succ (succ zero))  [= 3]
#eval MyNat.max n1 (MyNat.max n3 n2)  -- succ (succ (succ zero))  [= 3]

/-!
**Exercício 12.** Prove a *lei de absorção* relacionando `max` e `min`:
-/

theorem absorption (n m : MyNat) :
    MyNat.max n (MyNat.min n m) = n := by
  sorry

-- Exercício 12: max(n, min(n,m)) = n
#eval MyNat.max n3 (MyNat.min n3 n1)  -- n3 = 3
#eval MyNat.max n1 (MyNat.min n1 n3)  -- n1 = 1

/-!
**Exercício 13.** Prove, em `Nat`, que `max n m + min n m = n + m`.
Sugestão: faça indução simultânea em `n` e `m` usando `match`/`cases`.
-/

theorem max_add_min (n m : Nat) : max n m + min n m = n + m := by
  sorry

-- Exercício 13: max n m + min n m = n + m
#eval max 3 5 + min 3 5   -- 8 = 3 + 5
#eval max 7 2 + min 7 2   -- 9 = 7 + 2
#eval max 4 4 + min 4 4   -- 8 = 4 + 4

/-!
---

## Parte 2 — Listas polimórficas

Considere a definição usual:
-/

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
  deriving Repr

namespace MyList

infixr:67 " :: " => MyList.cons
notation "⟦⟧"   => MyList.nil

/-!
Defina as funções básicas (caso prefira usar `List` padrão, os
enunciados continuam válidos):
-/

def append {α} : MyList α → MyList α → MyList α
  | ⟦⟧, ys => ys
  | (x :: xs), ys => x :: (append xs ys)

def length {α}: MyList α → Nat
  | ⟦⟧ => 0
  | (_ :: xs) => 1 + length xs

def reverse {α} : MyList α → MyList α
  | ⟦⟧ => ⟦⟧
  | (x :: xs) => append (reverse xs) (x :: ⟦⟧)

def map {α β} (f : α → β) : MyList α → MyList β
  | ⟦⟧ => ⟦⟧
  | (x :: xs) => f x :: map f xs

/-! **Exercício 14.** Prove que `⟦⟧` é elemento neutro à direita do `append`: -/

theorem append_nil {α} (xs : MyList α) : append xs ⟦⟧ = xs := by
  sorry

-- Exercício 14: append xs ⟦⟧ = xs
#eval append (1 :: 2 :: ⟦⟧) (⟦⟧ : MyList Nat)  -- cons 1 (cons 2 nil)
#eval append (⟦⟧ : MyList Nat) ⟦⟧               -- nil

/-! **Exercício 15.** Prove a associatividade do `append`: -/

theorem append_assoc {α} (xs ys zs : MyList α) :
    append (append xs ys) zs = append xs (append ys zs) := by
  sorry

-- Exercício 15: (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
#eval append (append (1 :: ⟦⟧) (2 :: ⟦⟧)) (3 :: ⟦⟧)  -- cons 1 (cons 2 (cons 3 nil))
#eval append (1 :: ⟦⟧) (append (2 :: ⟦⟧) (3 :: ⟦⟧))  -- cons 1 (cons 2 (cons 3 nil))

/-! **Exercício 16.** Prove que `length` distribui sobre `append`: -/

theorem length_append {α} (xs ys : MyList α) :
    length (append xs ys) = length xs + length ys := by
  sorry

-- Exercício 16: |xs ++ ys| = |xs| + |ys|
#eval length (append (1 :: 2 :: ⟦⟧) (3 :: 4 :: 5 :: ⟦⟧))  -- 5
#eval length (1 :: 2 :: ⟦⟧) + length (3 :: 4 :: 5 :: ⟦⟧)  -- 5

/-!
**Exercício 17.** Prove que `reverse` distribui (com inversão) sobre
`append`:
-/

theorem reverse_append {α} (xs ys : MyList α) :
    reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  sorry

-- Exercício 17: reverse (xs ++ ys) = reverse ys ++ reverse xs
#eval reverse (append (1 :: 2 :: ⟦⟧) (3 :: 4 :: ⟦⟧))              -- cons 4 (cons 3 (cons 2 (cons 1 nil)))
#eval append (reverse (3 :: 4 :: ⟦⟧)) (reverse (1 :: 2 :: ⟦⟧))    -- cons 4 (cons 3 (cons 2 (cons 1 nil)))

/-! **Exercício 18.** Prove que `reverse` é involutiva: -/

theorem reverse_reverse {α} (xs : MyList α) : reverse (reverse xs) = xs := by
  sorry

-- Exercício 18: reverse (reverse xs) = xs
#eval reverse (reverse (1 :: 2 :: 3 :: ⟦⟧))  -- cons 1 (cons 2 (cons 3 nil))

/-!
Dica: você provavelmente precisará usar o `Exercício 17` como lema
auxiliar.

**Exercício 19.** Prove que `map` distribui sobre `append`:
-/

theorem map_append {α β} (f : α → β) (xs ys : MyList α) :
    map f (append xs ys) = append (map f xs) (map f ys) := by
  sorry

-- Exercício 19: map f (xs ++ ys) = map f xs ++ map f ys
#eval map (· * 2) (append (1 :: 2 :: ⟦⟧) (3 :: 4 :: ⟦⟧))           -- cons 2 (cons 4 (cons 6 (cons 8 nil)))
#eval append (map (· * 2) (1 :: 2 :: ⟦⟧)) (map (· * 2) (3 :: 4 :: ⟦⟧))  -- cons 2 (cons 4 (cons 6 (cons 8 nil)))

/-! **Exercício 20.** Prove que `map` preserva `length`: -/

theorem length_map {α β} (f : α → β) (xs : MyList α) :
    length (map f xs) = length xs := by
  sorry

-- Exercício 20: |map f xs| = |xs|
#eval length (map (· * 2) (1 :: 2 :: 3 :: ⟦⟧))  -- 3
#eval length (1 :: 2 :: 3 :: ⟦⟧)                 -- 3

end MyList

/-!
---

## Parte 3 — `zip`, `unzip` e `filter`

Para esta seção, use `List` da biblioteca padrão (ou redefina sobre
`MyList`, à sua escolha). As funções `zip`, `unzip` e `filter` da
biblioteca podem ser usadas, mas se preferir treinar indução, redefina:
-/

namespace MyFuncs

def zip {α β} : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys

def unzip {α β} : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xs  =>
    let (as, bs) := unzip xs
    (x :: as, y :: bs)

def filter {α} (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: filter p xs else filter p xs

/-!
### 3.1 Sobre `zip`

**Exercício 21.** Prove que o comprimento de `zip xs ys` é o mínimo dos
comprimentos:
-/

theorem length_zip {α β} (xs : List α) (ys : List β) :
    (zip xs ys).length = min xs.length ys.length := by
  sorry

-- Exercício 21: |zip xs ys| = min |xs| |ys|
#eval (zip [1, 2, 3] ['a', 'b']).length           -- 2 = min 3 2
#eval min [1, 2, 3].length ['a', 'b'].length      -- 2
#eval (zip [1] [10, 20, 30]).length               -- 1 = min 1 3

/-! **Exercício 22.** Prove que `zip` com lista vazia à direita produz a lista vazia: -/

theorem zip_nil_right {α β} (xs : List α) : zip xs ([] : List β) = [] := by
  sorry

-- Exercício 22: zip xs [] = []
#eval zip [1, 2, 3] ([] : List Nat)   -- []
#eval zip ([] : List Nat) []          -- []

/-!
**Exercício 23.** Prove que `zip` comuta com `map` em ambos os
componentes. Mais especificamente:
-/

theorem map_fst_zip {α β} (xs : List α) (ys : List β) :
    xs.length ≤ ys.length →
    (zip xs ys).map Prod.fst = xs := by
  sorry

-- Exercício 23: quando |xs| ≤ |ys|, map fst (zip xs ys) = xs
#eval (zip [1, 2] [10, 20, 30]).map Prod.fst    -- [1, 2]
#eval (zip [1, 2, 3] [10, 20, 30]).map Prod.fst -- [1, 2, 3]

/-!
### 3.2 Sobre `unzip`

**Exercício 24.** Prove que `unzip` de uma lista de pares devolve listas
de mesmo comprimento que a original:
-/

theorem length_unzip {α β} (xs : List (α × β)) :
    (unzip xs).1.length = xs.length ∧
    (unzip xs).2.length = xs.length := by
  sorry

-- Exercício 24: comprimentos das componentes de unzip
#eval (unzip [(1, 'a'), (2, 'b'), (3, 'c')]).1.length  -- 3
#eval (unzip [(1, 'a'), (2, 'b'), (3, 'c')]).2.length  -- 3

/-! **Exercício 25.** Prove a relação fundamental entre `zip` e `unzip`: -/

theorem zip_unzip {α β} (xs : List (α × β)) :
    let (as, bs) := unzip xs
    zip as bs = xs := by
  sorry

-- Exercício 25: zip (unzip xs) = xs
#eval let (as, bs) := unzip [(1, 'a'), (2, 'b'), (3, 'c')]; zip as bs
      -- [(1, 'a'), (2, 'b'), (3, 'c')]

/-!
**Exercício 26.** (Mais difícil) A volta nem sempre vale. Mostre por
contraexemplo (em Lean, como `example`) que existe `xs : List α` e
`ys : List β` tais que `unzip (zip xs ys) ≠ (xs, ys)`. Em seguida,
formule e prove uma versão correta com a hipótese
`xs.length = ys.length`:
-/

example : ∃ (xs : List Nat) (ys : List Nat), unzip (zip xs ys) ≠ (xs, ys) := by
  sorry

-- Exercício 26: contraexemplo — listas de comprimentos diferentes
#eval unzip (zip [1, 2, 3] [10, 20])  -- ([1, 2], [10, 20]) ≠ ([1,2,3], [10,20])

theorem unzip_zip {α β} (xs : List α) (ys : List β) :
    xs.length = ys.length → unzip (zip xs ys) = (xs, ys) := by
  sorry

-- Exercício 26 (versão correta): quando |xs| = |ys|
#eval unzip (zip [1, 2, 3] [10, 20, 30])  -- ([1, 2, 3], [10, 20, 30])

/-!
### 3.3 Sobre `filter`

**Exercício 27.** Prove que `filter` nunca aumenta o comprimento:
-/

theorem length_filter_le {α} (p : α → Bool) (xs : List α) :
    (filter p xs).length ≤ xs.length := by
  sorry

-- Exercício 27: |filter p xs| ≤ |xs|
#eval (filter (· % 2 == 0) [1, 2, 3, 4, 5]).length  -- 2 (≤ 5)
#eval (filter (fun _ => false) [1, 2, 3]).length     -- 0 (≤ 3)
#eval (filter (fun _ => true)  [1, 2, 3]).length     -- 3 (≤ 3)

/-! **Exercício 28.** Prove que `filter` é idempotente: -/

theorem filter_filter {α} (p : α → Bool) (xs : List α) :
    filter p (filter p xs) = filter p xs := by
  sorry

-- Exercício 28: filter p (filter p xs) = filter p xs
#eval filter (· % 2 == 0) (filter (· % 2 == 0) [1, 2, 3, 4, 5])  -- [2, 4]
#eval filter (· % 2 == 0) [1, 2, 3, 4, 5]                         -- [2, 4]

/-! **Exercício 29.** Prove que `filter` distribui sobre `append`: -/

theorem filter_append {α} (p : α → Bool) (xs ys : List α) :
    filter p (xs ++ ys) = filter p xs ++ filter p ys := by
  sorry

-- Exercício 29: filter p (xs ++ ys) = filter p xs ++ filter p ys
#eval filter (· % 2 == 0) ([1, 2, 3] ++ [4, 5, 6])                    -- [2, 4, 6]
#eval filter (· % 2 == 0) [1,2,3] ++ filter (· % 2 == 0) [4, 5, 6]   -- [2, 4, 6]

/-!
**Exercício 30.** Prove que filtrar por dois predicados sucessivamente
equivale a filtrar pela conjunção:
-/

theorem filter_and {α} (p q : α → Bool) (xs : List α) :
    filter q (filter p xs) = filter (fun x => p x && q x) xs := by
  sorry

-- Exercício 30: filter q (filter p xs) = filter (p && q) xs
#eval filter (· % 2 == 0) (filter (· > 2) [1, 2, 3, 4, 5])          -- [4]
#eval filter (fun x => x > 2 && x % 2 == 0) [1, 2, 3, 4, 5]         -- [4]

end MyFuncs

/-!
---

## Parte 4 — Árvores binárias de busca

Considere a seguinte definição polimórfica de árvore binária:
-/

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr

/-!
Em uma **árvore binária de busca (BST)** sobre `α` com uma ordem total
`<`, todo valor da subárvore esquerda é menor que a raiz e todo valor da
subárvore direita é maior. Vamos usar `Nat` como tipo de elementos para
simplificar (mas a generalização para qualquer `[LinearOrder α]` é
direta).

### 4.1 Predicados e funções

**Exercício 31.** Defina o predicado `Tree.mem : Nat → Tree Nat → Prop`
que indica que um elemento pertence à árvore:
-/

def Tree.mem (x : Nat) (t : Tree Nat) : Prop := sorry

-- Exercício 31 — comportamento esperado (após implementação):
--   Tree.mem 5 .leaf                                              = False
--   Tree.mem 5 (.node .leaf 5 .leaf)                             = True  (x = y)
--   Tree.mem 3 (.node (.node .leaf 3 .leaf) 5 .leaf)             = True  (subárvore esq.)
--   Tree.mem 9 (.node (.node .leaf 3 .leaf) 5 (.node .leaf 7 .leaf)) = False

/-!
**Exercício 32.** Defina os predicados auxiliares `allLT` e `allGT`, que
indicam que todos os elementos de uma árvore são, respectivamente,
menores ou maiores que um valor dado:
-/

def Tree.allLT (x : Nat) (t : Tree Nat) : Prop := sorry

def Tree.allGT (x : Nat) (t : Tree Nat) : Prop := sorry

-- Exercício 32 — comportamento esperado (após implementação):
--   Tree.allLT 5 .leaf                          = True
--   Tree.allLT 5 (.node .leaf 3 .leaf)          = True   (3 < 5)
--   Tree.allLT 5 (.node .leaf 7 .leaf)          = False  (7 ≥ 5)
--   Tree.allGT 5 .leaf                          = True
--   Tree.allGT 5 (.node .leaf 7 .leaf)          = True   (7 > 5)
--   Tree.allGT 5 (.node .leaf 3 .leaf)          = False  (3 ≤ 5)

/-!
**Exercício 33.** Defina o predicado `isBST`, que captura a invariante
de BST:
-/

def Tree.isBST (t : Tree Nat) : Prop := sorry

-- Exercício 33 — comportamento esperado (após implementação):
--   Tree.isBST .leaf                                                          = True
--   Tree.isBST (.node .leaf 5 .leaf)                                          = True
--   Tree.isBST (.node (.node .leaf 3 .leaf) 5 (.node .leaf 7 .leaf))         = True
--   Tree.isBST (.node (.node .leaf 7 .leaf) 5 (.node .leaf 3 .leaf))         = False

/-! **Exercício 34.** Defina a função de inserção em uma BST: -/

def Tree.insert (x : Nat) : Tree Nat → Tree Nat
   := sorry

-- Exercício 34: inserção em BST (após implementação)
#eval Tree.insert 5 .leaf
      -- Tree.node Tree.leaf 5 Tree.leaf
#eval Tree.insert 3 (Tree.insert 5 .leaf)
      -- Tree.node (Tree.node Tree.leaf 3 Tree.leaf) 5 Tree.leaf
#eval Tree.insert 7 (Tree.insert 3 (Tree.insert 5 .leaf))
      -- Tree.node (Tree.node Tree.leaf 3 Tree.leaf) 5 (Tree.node Tree.leaf 7 Tree.leaf)

/-!
**Exercício 35.** Defina a função `toList` que faz o percurso *in-order*
da árvore:
-/

def Tree.toList : Tree Nat → List Nat
  := sorry

-- Exercício 35: percurso in-order (esq, raiz, dir) — após implementação
#eval Tree.toList .leaf                                                             -- []
#eval Tree.toList (.node .leaf 5 .leaf)                                            -- [5]
#eval Tree.toList (.node (.node .leaf 3 .leaf) 5 (.node .leaf 7 .leaf))           -- [3, 5, 7] 

/-!
### 4.2 Teoremas

**Exercício 36.** Prove que `insert` preserva a relação `allLT`:
-/

theorem allLT_insert (x b : Nat) (t : Tree Nat) :
    x < b → Tree.allLT b t → Tree.allLT b (Tree.insert x t) := by
  sorry

/-!
Enuncie e prove também o resultado análogo para `allGT`:
-/

theorem allGT_insert (x b : Nat) (t : Tree Nat) :
    b < x → Tree.allGT b t → Tree.allGT b (Tree.insert x t) := by
  sorry

/-! **Exercício 37.** Prove que `insert` preserva a invariante de BST: -/

theorem isBST_insert (x : Nat) (t : Tree Nat) :
    Tree.isBST t → Tree.isBST (Tree.insert x t) := by
  sorry

/-!
Dica: você precisará do `Exercício 36` (e do análogo para `allGT`) como
lemas.

**Exercício 38.** Prove a especificação de `insert` quanto à
pertinência: após inserir `x`, o elemento `x` está na árvore e nenhum
elemento antigo desaparece:
-/

theorem mem_insert (x y : Nat) (t : Tree Nat) :
    Tree.mem y (Tree.insert x t) ↔ y = x ∨ Tree.mem y t := by
  sorry

/-!
**Exercício 39.** Use o predicado `List.Sorted` da biblioteca (ou
defina-o) e prove que o percurso in-order de uma BST produz uma lista
ordenada:
-/

theorem toList_sorted (t : Tree Nat) :
    Tree.isBST t → (Tree.toList t).Sorted (· < ·) := by
  sorry

/-!
Dica: você provavelmente precisará de um lema auxiliar relacionando
`Tree.allLT` / `Tree.allGT` com propriedades de listas (por exemplo,
"todos os elementos de `toList l` são menores que `x`").

**Exercício 40.** (Desafio) Defina uma função
`Tree.fromList : List Nat → Tree Nat` que constrói uma BST a partir de
uma lista, inserindo um elemento de cada vez:
-/

def Tree.fromList : List Nat → Tree Nat := sorry 
 

-- Exercício 40: construção de BST a partir de lista (após implementação de insert)
#eval Tree.fromList []
      -- Tree.leaf
#eval Tree.fromList [5]
      -- Tree.node Tree.leaf 5 Tree.leaf
#eval Tree.fromList [5, 3, 7]
      -- Tree.node (Tree.node Tree.leaf 3 Tree.leaf) 5 (Tree.node Tree.leaf 7 Tree.leaf)
#eval Tree.toList (Tree.fromList [5, 3, 7, 1, 4])
      -- [1, 3, 4, 5, 7]  (lista ordenada)

/-! Prove que o resultado é sempre uma BST: -/

theorem isBST_fromList (xs : List Nat) :
    Tree.isBST (Tree.fromList xs) := by
  sorry

/-! E prove a especificação de pertinência: -/

theorem mem_fromList (x : Nat) (xs : List Nat) :
    Tree.mem x (Tree.fromList xs) ↔ x ∈ xs := by
  sorry

/-!
---

## Dicas finais

- Para a maioria dos exercícios desta lista, o esqueleto da prova é
  `intro` + `induction` + `simp [definições_envolvidas]` + chamada
  recursiva da hipótese de indução. Quando não fechar, examine o estado
  do objetivo cuidadosamente.
- Para resultados sobre `Nat` que envolvem aritmética truncada
  (subtração), `omega` resolve quase tudo — mas pratique pelo menos uma
  vez sem ela.
- Para BSTs, o erro mais comum é esquecer de provar invariantes
  auxiliares sobre as subárvores. Se a sua prova de `isBST_insert`
  empacar, provavelmente está faltando um lema sobre `allLT`/`allGT`.
- Ao trabalhar com `if-then-else`, `split_ifs` é seu amigo. Para `match`
  em uma prova, considere usar `cases h : ...`.

Bom trabalho!
-/

end Exercicios
