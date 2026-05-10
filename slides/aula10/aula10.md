---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Táticas em Lean
---

# Objetivos

# Objetivos

- Introduzir o **modo de táticas** do Lean para construção interativa de provas.

# Objetivos

- Apresentar as táticas fundamentais: `intro`, `apply`, `exact`, `assumption`,
  `rfl`, `rw`, `simp` e `ac_rfl`.

# Objetivos

- Mostrar as **regras de introdução e eliminação** dos conectivos lógicos e
  quantificadores como lemmas do Lean.

# Objetivos

- Demonstrar **provas por indução matemática** sobre os naturais com a tática
  `induction`.

# Objetivos

- Apresentar a **equivalência entre** três axiomas da lógica clássica: Lei do
  Terceiro Excluído, Lei de Peirce e Dupla Negação.

# Motivação

# Motivação

- Na aula anterior, **enunciamos** teoremas com `theorem … := sorry`.

- Agora aprenderemos a **provar** esses teoremas usando táticas.

# Motivação

- Uma **tática** transforma o estado de prova atual em zero ou mais subgoals.

- O estado de prova tem a forma:

$$\underbrace{h_1 : P_1,\; \ldots,\; h_n : P_n}_{\text{hipóteses}} \;\vdash\; \underbrace{G}_{\text{meta}}$$

# Motivação

- **Backward proof** : partimos da **meta** e a decompomos em subgoals menores
  até chegarmos a hipóteses ou fatos já conhecidos.

- Contraste: **forward proof** parte das hipóteses em direção à conclusão —
  veremos posteriormente.

# Modo de Táticas

# Modo de Táticas

- A palavra-chave `by` introduz um bloco de táticas:

```lean
theorem nome : enunciado :=
  by
    tática₁
    …
    táticaN
```

# Modo de Táticas

- Exemplo mínimo — provar $\forall a\; b : \mathsf{Prop},\; a \to b \to a$:

```lean
theorem fst_of_two_props :
    ∀ a b : Prop, a → b → a :=
  by
    intro a b ha hb
    exact ha
```

# Modo de Táticas

- **Observação importante**: `Prop` é um tipo como `Nat` ou `List Bool`.
  Proposições são termos de tipo `Prop`.

# Táticas Básicas

# Táticas Básicas

- **`intro`**: move quantificadores $\forall$ e premissas $\to$ da conclusão
  para as hipóteses.

```lean
theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  by
    intro ha     -- meta: c
    apply hbc    -- meta: b
    apply hab    -- meta: a
    exact ha     -- fecha a meta
```

# Táticas Básicas

- **`apply`**: unifica a conclusão da meta com a conclusão do lemma fornecido;
  as premissas do lemma tornam-se novas metas.

- **`exact`**: como `apply`, mas exige correspondência exata — indica que a meta
  está completamente resolvida.

# Táticas Básicas

- **`assumption`**: busca automaticamente nas hipóteses locais uma que
  corresponda à meta.

```lean
theorem fst_of_two (a b : Prop) (ha : a) (hb : b) : a :=
  by assumption
```

# Tática `rfl`

# Tática `rfl`

- **`rfl`**: fecha metas da forma $l = r$ quando os dois lados são
  **definitivamente iguais** — iguais por computação.

# Tática `rfl`

- As reduções reconhecidas por `rfl`:

| Nome | Exemplo                                     |
| ---- | ------------------------------------------- |
| α    | `(fun x ↦ f x) = (fun y ↦ f y)`             |
| β    | `(fun x ↦ f x) a = f a`                     |
| δ    | `double 5 = 5 + 5` (onde `double n := n+n`) |

# Tática `rfl`

- As reduções reconhecidas por `rfl`:

| Nome | Exemplo                       |
| ---- | ----------------------------- |
| ζ    | `(let n : ℕ := 2; n + n) = 4` |
| η    | `(fun x ↦ f x) = f`           |
| ι    | `Prod.fst (a, b) = a`         |

# Tática `rfl`

- Exemplos em Lean:

```lean
theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x ↦ f x) a = f a := by rfl

def double (n : ℕ) : ℕ := n + n

theorem δ_example : double 5 = 5 + 5 := by rfl

theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a := by rfl
```

# Tática `rw`

# Tática `rw`

- **`rw [h]`**: reescreve usando a equação `h` **uma vez**, da esquerda para a
  direita.

- **`rw [← h]`**: reescreve da direita para a esquerda.

```lean
theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c :=
  by
    rw [hab]   -- b = c
    rw [hcb]   -- b = b → finaliza
```

# Tática `rw`

- `rw` pode também **expandir definições**:

```lean
theorem a_proof_of_negation (a : Prop) : a → ¬¬ a :=
  by
    rw [Not]    -- ¬¬a vira (¬a → False)
    rw [Not]    -- ¬a  vira (a  → False)
    intro ha hna
    apply hna
    exact ha
```

# Táticas `simp` e `ac_rfl`

# Táticas `simp` e `ac_rfl`

- **`simp`**: aplica exaustivamente um conjunto de regras de reescrita (o _simp
  set_).

# Táticas `simp` e `ac_rfl`

- Lemmas extras podem ser passados: `simp [h₁, …, hN]`.

```lean
theorem cong_two_args {α : Type} (a b c d : α)
    (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]
```

# Táticas `simp` e `ac_rfl`

- **`ac_rfl`**: fecha goals que são iguais módulo **associatividade e
  comutatividade** de `+`, `*` e outros operadores.

```lean
theorem abc_Eq_cba (a b c : ℕ) :
    a + b + c = c + b + a :=
  by ac_rfl
```

# Regras para Conectivos

# Regras para Conectivos

- Os conectivos lógicos possuem **regras de introdução** acessíveis como lemmas:

| Regra        | Tipo            |
| ------------ | --------------- |
| `True.intro` | `True`          |
| `And.intro`  | `a → b → a ∧ b` |
| `Or.inl`     | `a → a ∨ b`     |

# Regras para Conectivos

- Continuando.

| Regra       | Tipo                          |
| ----------- | ----------------------------- |
| `Or.inr`    | `b → a ∨ b`                   |
| `Iff.intro` | `(a → b) → (b → a) → (a ↔ b)` |

# Regras para Conectivos

- Continuando.

| Regra          | Tipo                       |
| -------------- | -------------------------- |
| `Exists.intro` | `(t : α) → p t → ∃ x, p x` |

# Regras para Conectivos

- E as **regras de eliminação**:

| Regra        | Tipo        |
| ------------ | ----------- |
| `False.elim` | `False → a` |
| `And.left`   | `a ∧ b → a` |
| `And.right`  | `a ∧ b → b` |

# Regras para Conectivos

- E as **regras de eliminação**:

| Regra     | Tipo                            |
| --------- | ------------------------------- |
| `Or.elim` | `a ∨ b → (a → c) → (b → c) → c` |
| `Iff.mp`  | `(a ↔ b) → a → b`               |

# Regras para Conectivos

- E as **regras de eliminação**:

| Regra         | Tipo                              |
| ------------- | --------------------------------- |
| `Iff.mpr`     | `(a ↔ b) → b → a`                 |
| `Exists.elim` | `(∃ x, p x) → (∀ x, p x → b) → b` |

# Regras para Conectivos

- Exemplo: conjunção é comutativa:

```lean
theorem And_swap (a b : Prop) : a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    · exact And.right hab
    · exact And.left  hab
```

# Regras para Conectivos

- Exemplo: comutatividade da disjunção:

```lean
theorem Or_swap (a b : Prop) : a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    · intro ha; exact Or.inr ha
    · intro hb; exact Or.inl hb
```

# Regras para Conectivos

- Exemplo: introdução de existencial com **evidência**:

```lean
def double (n : ℕ) : ℕ := n + n

theorem Exists_double_iden : ∃ n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl
```

# Negação

# Negação

- A negação é **definida** como implicação para `False`:

$$\neg P \;\stackrel{\text{def}}{=}\; P \to \mathsf{False}$$

```lean
#print Not   -- def Not : Prop → Prop := fun a => a → False
```

- Não há regra separada para $\neg$: usamos as mesmas regras de `→`.

# Negação

- Exemplo: dupla negação (sem lógica clássica):

```lean
theorem Not_Not_intro (a : Prop) : a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha
```

# Negação

- **Axiomas clássicos** disponíveis no Lean:

```lean
#check Classical.em
-- : ∀ (p : Prop), p ∨ ¬ p

#check Classical.byContradiction
-- : (¬ a → False) → a
```

# Igualdade

# Igualdade

- Quatro regras fundamentais da igualdade:

```lean
#check @Eq.refl   -- : ∀ {α} (a : α), a = a
#check @Eq.symm   -- : a = b → b = a
#check @Eq.trans  -- : a = b → b = c → a = c
#check @Eq.subst  -- : a = b → p a → p b
```

# Igualdade

- Exemplo usando `Eq.trans` e `Eq.symm` diretamente:

```lean
theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c :=
  by
    apply Eq.trans
    · exact hab
    · apply Eq.symm; exact hcb
```

# Igualdade

- A versão com `rw` é mais idiomática — use `Eq.trans`/`Eq.symm` quando precisar
  dos combinadores como termos de primeira classe.

# Tática `induction`

# Tática `induction`

- **`induction x with`**: realiza indução estrutural sobre `x`, criando um
  subgoal por construtor do tipo indutivo.

```lean
theorem add_zero (n : ℕ) : add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]
```

- `ih` — hipótese de indução para `n'`.

# Tática `induction`

- Comutatividade da adição — requer dois lemas auxiliares:

```lean
theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]
```

# Tática `induction`

```lean
theorem add_comm (m n : ℕ) : add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]
```

# Tática `induction`

- Distributividade — combina `simp` e `ac_rfl`:

```lean
theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl
```

# Foco em Subgoals

# Foco em Subgoals

- **`· tática`** (ou `{ tática }`): foca em um subgoal específico; a tática deve
  fechá-lo completamente.

```lean
theorem And_swap_braces : ∀ a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    · exact And.right hab
    · exact And.left  hab
```

# Foco em Subgoals

- O foco explícito deixa claro qual subgoal cada trecho de código resolve — útil
  quando `apply` gera múltiplas metas.

# Limpeza de Contexto

# Limpeza de Contexto

- **`clear h`**: remove a hipótese (ou variável) `h` do contexto.
- **`rename h => h'`**: renomeia uma hipótese.

```lean
theorem cleanup_example (a b c : Prop)
    (ha : a) (hb : b) (hab : a → b) (hbc : b → c) : c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename hb => h
    exact h
```

# Axiomas Clássicos

# Axiomas Clássicos

- Três axiomas da lógica clássica podem ser formulados como proposições:

```lean
def ExcludedMiddle : Prop :=
  ∀ a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀ a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀ a : Prop, ¬¬ a → a
```

# Axiomas Clássicos

- Esses três axiomas são **logicamente equivalentes**:

$$\mathsf{ExcludedMiddle} \;\Leftrightarrow\; \mathsf{Peirce}
  \;\Leftrightarrow\; \mathsf{DoubleNegation}$$

# Axiomas Clássicos

- Cadeia de implicações a provar:

$$\mathsf{EM} \xrightarrow{} \mathsf{Peirce}
              \xrightarrow{} \mathsf{DN}
              \xrightarrow{} \mathsf{EM}$$

```lean
theorem Peirce_of_EM : ExcludedMiddle → Peirce := sorry
theorem DN_of_Peirce : Peirce → DoubleNegation := sorry
theorem EM_of_DN     : DoubleNegation → ExcludedMiddle := sorry
```

# Conclusão

# Conclusão

- Nesta aula apresentamos algumas táticas do Lean e as utilizamos para
  demonstrar alguns teoremas simples.

# Referências

# Referências

- AVIGAD, Jeremy et al. _The Hitchhiker's Guide to Logical Verification_ (2025).
  Cap. 3: Backward Proofs. Disponível em:
  `https://github.com/lean-forward/logical_verification_2025`

# Referências

- PIERCE, Benjamin C. _Types and Programming Languages_. MIT Press, 2002. (Cap.
  9: sistema de tipos simples)

# Referências

- NIPKOW, Tobias; KLEIN, Gerwin. _Concrete Semantics: With Isabelle/HOL_.
  Springer, 2014. (Cap. 3: provas por indução em assistentes de prova)

# Referências

- DE MOURA, Leonardo et al. Lean 4: A Theorem Prover and Programming Language.
  In: _CADE-28_, 2021.
