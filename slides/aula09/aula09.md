---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Programas e Teoremas em Lean
---

# Objetivos

# Objetivos

- Apresentar os **tipos indutivos** do Lean como mecanismo para definir novos
  tipos de dados.

# Objetivos

- Mostrar como definir funções por **casamento de padrões** e **recursão
  estrutural**.

# Objetivos

- Introduzir **argumentos implícitos** e **funções de ordem superior** no Lean.

# Objetivos

- Apresentar o comando `theorem` para **enunciar propriedades** de programas
  como proposições formais.

# Motivação

# Motivação

- Na aula anterior estudamos a teoria de tipos simples: tipos, termos e regras
  de tipagem.

- Agora vamos ver como o Lean usa esses fundamentos para **definir tipos de
  dados e funções** e **enunciar teoremas**.

# Motivação

- O Lean suporta dois modos de uso:
  - **Programação**: definir funções verificadas por tipo.
  - **Prova**: enunciar e demonstrar propriedades formais.

# Motivação

- Nesta aula veremos **apenas** como definir e enunciar — as técnicas de prova
  serão introduzidas nas próximas aulas.

# Tipos Indutivos

# Tipos Indutivos

- Um **tipo indutivo** consiste em todos os valores que podem ser construídos
  por um número finito de aplicações de seus **construtores**, e somente esses.

# Tipos Indutivos

- Exemplo: números naturais em notação unária:

```lean
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat
```

- `zero` — o número zero.
- `succ n` — o sucessor de `n`.

# Tipos Indutivos

- Todo natural é obtido por finitas aplicações de `succ` a `zero`:

$$0,\quad \mathsf{succ}\;0,\quad \mathsf{succ}\;(\mathsf{succ}\;0),\quad \ldots$$

- Comandos úteis:

```lean
#check Nat.zero   -- Nat
#check Nat.succ   -- Nat → Nat
#print Nat
```

# Tipos Indutivos

- Exemplo: expressões aritméticas sobre inteiros:

```lean
inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
```

# Tipos Indutivos

- O tipo `AExp` representa **árvores de expressão**:
  - `num i` — literal inteiro $i$
  - `var x` — variável com nome `x`
  - `add e₁ e₂`, `mul e₁ e₂`, ... — operações binárias

# Tipos Indutivos

- Exemplo: **listas polimórficas**:

```lean
inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α
```

- `nil` — lista vazia.
- `cons x xs` — lista com cabeça `x` e cauda `xs`.

# Tipos Indutivos

- Lean fornece notações convenientes para listas:

| Notação       | Definição             |
| ------------- | --------------------- |
| `[]`          | `List.nil`            |
| `x :: xs`     | `List.cons x xs`      |
| `[x₁, …, xN]` | `x₁ :: … :: xN :: []` |

# Definição de Funções

# Definição de Funções

- Funções sobre tipos indutivos são definidas por **casamento de padrões**:

```lean
def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n
```

- Cada equação cobre um construtor (ou padrão numérico).

# Definição de Funções

- Adição de naturais por **recursão estrutural**:

```lean
def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)
```

- Recursão sobre o **segundo argumento**; cada chamada recursiva elimina um
  `succ`.

# Definição de Funções

- Avaliação: `#eval` e `#reduce`

```lean
#eval add 2 7     -- 9
#reduce add 2 7   -- 9
```

- `#eval` — avalia eficientemente (compila antes de executar).
- `#reduce` — reduz pelo kernel (mais lento, mas usa apenas a lógica central).

# Definição de Funções

- Multiplicação — usa `_` quando um argumento é irrelevante:

```lean
def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)
```

# Definição de Funções

- Exponenciação:

```lean
def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)
```

```lean
#eval power 2 5   -- 32
```

# Definição de Funções

- **Parâmetros nomeados**: quando não é necessário casar padrão sobre um
  argumento, ele fica à esquerda do `:`:

```lean
def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)
```

# Funções de Ordem Superior

# Funções de Ordem Superior

- Uma função de **ordem superior** recebe outra função como argumento.

- Exemplo: `iter` — aplica uma função `f` exatamente `n` vezes a um valor
  inicial `z`:

```lean
def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | Nat.zero   => z
  | Nat.succ n => f (iter α z f n)
```

# Funções de Ordem Superior

- Com `iter`, a exponenciação torna-se:

```lean
def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n
```

- Multiplica por `m` exatamente `n` vezes a partir de 1.

# Funções de Ordem Superior

- Concatenação de listas (com argumento de tipo **explícito**):

```lean
def append (α : Type) : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: append α xs ys
```

```lean
#eval append ℕ [3, 1] [4, 1, 5]   -- [3, 1, 4, 1, 5]
```

# Argumentos Implícitos

# Argumentos Implícitos

- **Argumento explícito** `( )`: devemos fornecer.

# Argumentos Implícitos

- **Argumento implícito** `{ }`: o Lean o **infere** do contexto. Podemos omitir

# Argumentos Implícitos

- Concatenação com argumento de tipo implícito:

```lean
def appendImplicit {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendImplicit xs ys
```

```lean
#eval appendImplicit [3, 1] [4, 1, 5]   -- sem precisar de ℕ
```

# Argumentos Implícitos

- Para tornar explícito um argumento implícito, use o prefixo `@`:

```lean
#check @appendImplicit
-- @appendImplicit : {α : Type} → List α → List α → List α

#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
```

# Argumentos Implícitos

- Inversão de lista:

```lean
def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]
```

```lean
#eval reverse [1, 2, 3]   -- [3, 2, 1]
```

# Avaliador de Expressões

# Avaliador de Expressões

- Um **ambiente** mapeia nomes de variáveis a valores inteiros:

$$\mathit{env} : \mathsf{String} \to \mathbb{Z}$$

- Exemplo: `fun x ↦ if x = "y" then 17 else 0`

# Avaliador de Expressões

- A função `eval` interpreta uma `AExp` num dado ambiente:

```lean
def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i      => i
  | AExp.var x      => env x
  | AExp.add e₁ e₂  => eval env e₁ + eval env e₂
  | AExp.mul e₁ e₂  => eval env e₁ * eval env e₂
```

# Avaliador de Expressões

- Um simplificador de expressões pode, por exemplo, eliminar neutros:

```lean
def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e => simplify e
  | AExp.add e (AExp.num 0) => simplify e
  -- ... mais casos ...
  | e => e
```

- A **correção** do simplificador é um teorema a ser provado.

# Terminação

# Terminação

- O Lean **só aceita** definições de funções para as quais consegue provar
  terminação.

- Para funções recursivas simples, o Lean verifica automaticamente a **recursão
  estrutural**: cada chamada recursiva recebe um argumento estritamente menor.

# Terminação

- Recursão estrutural sobre `Nat`:

$$\mathsf{add}\; m\; (\mathsf{succ}\; n) \;\text{ chama }\; \mathsf{add}\; m\; n$$

- $n < \mathsf{succ}\; n$ — o argumento diminui a cada passo, logo o Lean
  aceita.

# Terminação

- Consequência: todas as funções definidas em Lean são **totais** — retornam um
  valor para toda entrada.

- Isso é essencial para a **consistência lógica** do sistema.

# Enunciados de Teoremas

# Enunciados de Teoremas

- O comando `theorem` enuncia uma propriedade como proposição formal:

```lean
theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry
```

- `sorry` é um espaço reservado aceito pelo Lean (com aviso) — a prova será dada
  depois.

# Enunciados de Teoremas

- `theorem` é análogo a `def`: a **proposição** é o tipo, a **prova** é o corpo.

| Construção | Tipo         | Corpo     |
| ---------- | ------------ | --------- |
| `def`      | tipo de dado | definição |
| `theorem`  | proposição   | prova     |

# Enunciados de Teoremas

- Propriedades da adição:

```lean
theorem add_comm (m n : ℕ) :
    add m n = add n m := sorry

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) := sorry
```

# Enunciados de Teoremas

- Propriedades da multiplicação:

```lean
theorem mul_comm (m n : ℕ) :
    mul m n = mul n m := sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) := sorry
```

# Enunciados de Teoremas

- Propriedade de listas — reversão é uma involução:

```lean
theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs := sorry
```

# Enunciados de Teoremas

- Além de `theorem`, temos:
  - `axiom` — como `theorem`, mas **assumido** sem prova.
  - `opaque` — como `def`, mas **sem corpo** (valor não especificado).

# Enunciados de Teoremas

```lean
opaque a : ℤ
opaque b : ℤ

axiom a_less_b : a < b
```

# Conclusão

# Conclusão

- Nesta aula apresentamos tipos de dados indutivos e funções recursivas em Lean.

- Discutimos diferentes tipos de argumentos.

- Apresentamos sobre a definição de teoremas e exemplos de demonstrações.

# Referências

# Referências

- AVIGAD, Jeremy et al. _The Hitchhiker's Guide to Logical Verification_ (2025).
  Cap. 2: Programs and Theorems. Disponível em:
  `https://github.com/lean-forward/logical_verification_2025`

# Referências

- PIERCE, Benjamin C. _Types and Programming Languages_. MIT Press, 2002. (Cap.
  11: tipos simples com produtos e somas)

# Referências

- NIPKOW, Tobias; WENZEL, Markus; PAULSON, Lawrence C. _Isabelle/HOL: A Proof
  Assistant for Higher-Order Logic_. Springer, 2002. (Fundamentos de tipos
  indutivos em assistentes de prova)

# Referências

- DE MOURA, Leonardo et al. Lean 4: A Theorem Prover and Programming Language.
  In: _CADE-28_, 2021.
