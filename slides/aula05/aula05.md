---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lambda cálculo tipado simples
---

# Objetivos

# Objetivos

- Apresentar a sintaxe e o sistema de tipos do **lambda cálculo tipado simples**
  (STLC).

# Objetivos

- Enunciar o **Isomorfismo de Curry-Howard** e estabelecer a correspondência
  entre tipos e fórmulas lógicas.

# Objetivos

- Relacionar as **regras de dedução natural** da lógica proposicional com os
  **termos do STLC**.

# Objetivos

- Apresentar a propriedade de **normalização forte** e um esboço da demonstração
  via **redutibilidade lógica**.

# Objetivos

- Apresentar a implementação em Haskell do **verificador de tipos** e da
  **construção interativa de termos por táticas**.

# Motivação

# Motivação

- O lambda cálculo **não tipado** é Turing-completo, mas permite termos "sem
  sentido":

$$(\lambda x.\; x\; x)\; (\lambda x.\; x\; x) \;\longrightarrow\; \cdots$$

# Motivação

- Podemos aplicar qualquer termo a qualquer argumento — não há distinção entre
  funções, números ou booleanos.

# Motivação

- O lambda cálculo **tipado simples** (STLC) introduz um sistema de tipos que
  **rejeita** termos mal-formados.

# Motivação

- Todo termo bem-tipado **termina**: o sistema de tipos garante a ausência de
  loops infinitos.

# Motivação

- O STLC é a base de sistemas de tipos de linguagens funcionais modernas como
  Haskell e OCaml.

# Sintaxe

# Tipos

- Os **tipos** do STLC são definidos pela gramática:

$$
\begin{array}{lcl}
A, B & ::=  &  P \;\mid\; \top \;\mid\; \bot \;\mid\; A \to B \\
     & \mid &  A \times B \;\mid\; A + B
\end{array}
$$

# Tipos

- $P, Q, R, \ldots$ — **variáveis de tipo** (proposicionais)

# Tipos

- $\top$ — tipo **unit** (um único habitante)

- $\bot$ — tipo **void** (sem habitantes)

# Tipos

- $A \to B$ — tipo **função** (implicação); associa à direita

$$A \to B \to C \;=\; A \to (B \to C)$$

# Tipos

- $A \times B$ — tipo **produto** (par ordenado)

- $A + B$ — tipo **soma** (união disjunta)

# Termos

- Os **termos** do STLC são:

$$
\begin{array}{lcl}
t  & ::=  & x \;\mid\; \lambda x{:}A.\, t \;\mid\; t\;t\\
   & \mid & \mathbf{unit}\\
   & \mid & (t, t) \;\mid\; \mathbf{fst}\;t \;\mid\; \mathbf{snd}\;t\\
   & \mid &  \mathbf{inl}\;t \;\mid\; \mathbf{inr}\;t \\
   & \mid & \mathbf{case}\;t\;\mathbf{of}\;(\mathbf{inl}\;x \Rightarrow t \mid \mathbf{inr}\;y \Rightarrow t)\\
   & \mid & \mathbf{absurd}\;t
\end{array}
$$

# Termos

- $x$ — **variável** (hipótese)

- $\lambda x{:}A.\,t$ — **abstração** com anotação de tipo

- $t_1\;t_2$ — **aplicação**

# Termos

- $\mathbf{unit}$ — o único habitante de $\top$

- $(t_1, t_2)$ — **par**; $\mathbf{fst}\;t$, $\mathbf{snd}\;t$ — **projeções**

# Termos

- $\mathbf{inl}\;t$, $\mathbf{inr}\;t$ — **injeções** na soma

- $\mathbf{case}\;\cdots$ — **eliminação** da soma

- $\mathbf{absurd}\;t$ — **eliminação** do vazio ($t : \bot$)

# Sistema de tipos

# Sistema de tipos

- Um **contexto** $\Gamma$ é uma sequência de declarações:

$$\Gamma \;::=\; \emptyset \;\mid\; \Gamma,\, x : A$$

- Escrevemos $\Gamma \vdash t : A$ para dizer que, sob as hipóteses $\Gamma$, o
  termo $t$ tem tipo $A$.

# Sistema de tipos

$$
\dfrac{}{\Gamma,\, x : A \vdash x : A}
\quad\text{(Var)}
$$

$$
\dfrac{\Gamma,\, x : A \vdash t : B}
      {\Gamma \vdash \lambda x{:}A.\, t : A \to B}
\quad\text{(Abs)}
$$

# Sistema de tipos

$$
\dfrac{\Gamma \vdash t_1 : A \to B \qquad \Gamma \vdash t_2 : A}
      {\Gamma \vdash t_1\;t_2 : B}
\quad\text{(App)}
$$

# Sistema de tipos

$$
\dfrac{}{\Gamma \vdash \mathbf{unit} : \top}
\quad\text{($\top$-I)}
$$

# Sistema de tipos

$$
\dfrac{\Gamma \vdash t_1 : A \qquad \Gamma \vdash t_2 : B}
      {\Gamma \vdash (t_1, t_2) : A \times B}
\quad\text{($\times$-I)}
$$

# Sistema de tipos

$$
\dfrac{\Gamma \vdash t : A \times B}
      {\Gamma \vdash \mathbf{fst}\;t : A}
\quad\text{($\times$-E$_1$)}
$$

# Sistema de tipos

$$
\dfrac{\Gamma \vdash t : A \times B}
      {\Gamma \vdash \mathbf{snd}\;t : B}
\quad\text{($\times$-E$_2$)}
$$

# Sistema de tipos

$$
\dfrac{\Gamma \vdash t : A}
      {\Gamma \vdash \mathbf{inl}\;t : A + B}
\quad\text{($+$-I$_1$)}
$$

# Sistema de tipos

$$
\dfrac{\Gamma \vdash t : B}
      {\Gamma \vdash \mathbf{inr}\;t : A + B}
\quad\text{($+$-I$_2$)}
$$

# Sistema de tipos

$$
\dfrac{
  \Gamma \vdash t : A + B \qquad
  \Gamma, x{:}A \vdash t_1 : C \qquad
  \Gamma, y{:}B \vdash t_2 : C
}{
  \Gamma \vdash \mathbf{case}\;t\;\mathbf{of}\;
  (\mathbf{inl}\;x \Rightarrow t_1 \mid \mathbf{inr}\;y \Rightarrow t_2) : C
}
\quad\text{($+$-E)}
$$

# Sistema de tipos

$$
\dfrac{\Gamma \vdash t : \bot}
      {\Gamma \vdash \mathbf{absurd}\;t : C}
\quad\text{($\bot$-E)}
$$

# Exemplo

- Derivação para $\vdash \lambda x{:}A.\, x : A \to A$:

$$
\dfrac{
  \dfrac{}{x : A \vdash x : A}\;\text{(Var)}
}
{
  \vdash \lambda x{:}A.\, x : A \to A
}\;\text{(Abs)}
$$

# Exemplo

- Derivação para $h : A \times B \vdash \mathbf{fst}\;h : A$:

$$
\dfrac{
  \dfrac{}{h : A \times B \vdash h : A \times B}\;\text{(Var)}
}
{
  h : A \times B \vdash \mathbf{fst}\;h : A
}\;\text{($\times$-E$_1$)}
$$

# O Isomorfismo de Curry-Howard

# Curry-Howard

- Em 1934, Haskell Curry observou que os axiomas da lógica combinatória
  correspondiam a tipos de combinadores.

# Curry-Howard

- Em 1969, William Howard estendeu essa observação para o lambda cálculo tipado
  e a dedução natural.

# Curry-Howard

- **Isomorfismo de Curry-Howard**: existe uma correspondência biunívoca e
  estruturalmente preservada entre:

> **fórmulas lógicas** $\;\longleftrightarrow\;$ **tipos**

> **demonstrações** $\;\longleftrightarrow\;$ **termos**

# Curry-Howard

- A correspondência é um **isomorfismo**: não é apenas uma analogia superficial,
  mas uma identidade estrutural profunda.

# Curry-Howard

- Consequências:
  - Verificar um tipo ≡ verificar uma demonstração
  - Construir um termo ≡ construir uma prova
  - Redução de termos ≡ normalização de provas

# Lógica Proposicional e STLC

# Dedução Natural

- A **dedução natural** de Gentzen formaliza o raciocínio lógico através de
  regras de **introdução** e **eliminação** para cada conectivo.

# Dedução Natural

$$
\dfrac{}{\Gamma,\, A \vdash A}
\quad\text{(Hyp)}
$$

> Corresponde à regra **(Var)** do STLC.

# Dedução Natural

$$
\dfrac{\Gamma,\, A \vdash B}{\Gamma \vdash A \to B}
\quad\text{($\to$-I)}
$$

> Corresponde a **(Abs)** do STLC.

# Dedução Natural

$$
\dfrac{\Gamma \vdash A \to B \qquad \Gamma \vdash A} {\Gamma \vdash B}
\quad\text{($\to$-E)}
$$

> Corresponde a **(App)** do STLC.

# Dedução Natural

$$
\dfrac{\Gamma \vdash A \qquad \Gamma \vdash B}
      {\Gamma \vdash A \wedge B}
\quad\text{($\wedge$-I)}
$$

> Corresponde a **($\times$-I)** do STLC.

# Dedução Natural

$$
\dfrac{\Gamma \vdash A \wedge B}{\Gamma \vdash A} \quad\text{($\wedge$-E$_1$)}
\qquad
\dfrac{\Gamma \vdash A \wedge B}{\Gamma \vdash B}
\quad\text{($\wedge$-E$_2$)}
$$

> Correspondem a **($\times$-E$_1$)** e **($\times$-E$_2$)**.

# Dedução Natural

$$
\dfrac{\Gamma \vdash A}{\Gamma \vdash A \vee B}
\quad\text{($\vee$-I$_1$)}
\qquad
\dfrac{\Gamma \vdash B}{\Gamma \vdash A \vee B}
\quad\text{($\vee$-I$_2$)}
$$

> Correspondem a **(+I$_1$)** e **(+I$_2$)**.

# Dedução Natural

$$
\dfrac{\Gamma \vdash A \vee B \qquad \Gamma, A \vdash C \qquad \Gamma, B \vdash C}
      {\Gamma \vdash C}
\quad\text{($\vee$-E)}
$$

> Corresponde a **(+E)**

# Dedução Natural

$$
\dfrac{}{\Gamma \vdash \top}
\quad\text{($\top$-I)}
\qquad
\dfrac{\Gamma \vdash \bot}{\Gamma \vdash A}
\quad\text{($\bot$-E)}
$$

> Correspondem a **($\top$-I)** e **($\bot$-E)** do STLC.

# Resumo

| **Lógica proposicional** | **STLC**                     |
| ------------------------ | ---------------------------- |
| Fórmula $A$              | Tipo $A$                     |
| Demonstração de $A$      | Termo $t : A$                |
| Variável proposicional   | Tipo base / variável de tipo |
| $\top$                   | Tipo `unit`                  |

# Resumo

| **Lógica proposicional** | **STLC**                  |
| ------------------------ | ------------------------- |
| $\bot$                   | Tipo `void`               |
| $A \to B$                | Tipo função $A \to B$     |
| $A \wedge B$             | Tipo produto $A \times B$ |
| $A \vee B$               | Tipo soma $A + B$         |

# Resumo

| **Regra lógica** | **Construtor de termo**       |
| ---------------- | ----------------------------- |
| Hipótese         | Variável $x$                  |
| $\to$-I          | Abstração $\lambda x{:}A.\,t$ |
| $\to$-E          | Aplicação $t_1\;t_2$          |
| $\top$-I         | $\mathbf{unit}$               |
| $\wedge$-I       | Par $(t_1, t_2)$              |

# Resumo

| **Lógica proposicional** | **STLC**                             |
| ------------------------ | ------------------------------------ |
| $\wedge$-E               | $\mathbf{fst}$, $\mathbf{snd}$       |
| $\vee$-I                 | $\mathbf{inl}$, $\mathbf{inr}$       |
| $\vee$-E                 | $\mathbf{case}\;\cdots\;\mathbf{of}$ |
| $\bot$-E                 | $\mathbf{absurd}$                    |

# Exemplos

- A tautologia $A \to A$ é habitada por $\lambda x{:}A.\,x$.

# Exemplos

- A tautologia $A \wedge B \to B \wedge A$ é habitada por:

$$\lambda p{:}A \times B.\;(\mathbf{snd}\;p,\;\mathbf{fst}\;p)$$

# Exemplos

- A tautologia $(A \to B) \to (B \to C) \to A \to C$ é habitada por:

$$\lambda f{:}A{\to}B.\;\lambda g{:}B{\to}C.\;\lambda x{:}A.\;g\;(f\;x)$$

# Exemplos

- A fórmula $\bot \to A$ (ex falso quodlibet) é habitada por:

$$\lambda x{:}\bot.\;\mathbf{absurd}\;x$$

# Prop. Inabitadas

- Se uma fórmula é **não demonstrável** na lógica proposicional intuicionista, o
  tipo correspondente não possui habitantes (termos fechados e bem-tipados).

# Prop. Inabitadas

- Exemplo: $A + B \to A$ não é demonstrável.

- Não existe $t$ fechado tal que $\vdash t : A + B \to A$.

# Prop. Inabitadas

- Isso distingue a lógica **intuicionista** da lógica clássica:

  - $A \lor \neg A$ (lei do terceiro excluído) não é habitada no STLC puro.

  - Para adicionar lógica clássica precisamos de tipos adicionais (continuações,
    por exemplo).

# Normalização Forte

# Norm. Forte

- **Definição**: Um termo $t$ é **fortemente normalizável** (SN) se toda
  sequência de reduções a partir de $t$ termina.

# Norm. Forte

- **Teorema (Normalização Forte do STLC)**:

> Se $\Gamma \vdash t : A$, então $t$ é fortemente normalizável.

# Norm. Forte

- Corolário: o STLC não pode expressar funções que entram em loop

— Menos expressividade para ter garantia de terminação.

# Norm. Forte

- A demonstração utiliza o método de **logical relations** (Tait, 1967).

# Norm. Forte

- Via Curry-Howard: normalização forte significa que toda **demonstração** em
  lógica proposicional intuicionista pode ser **normalizada** em uma
  demonstração sem cortes (sem "detours" lógicos).

# Norm. Forte

- Este é o análogo computacional do **Teorema da Eliminação do Corte** de
  Gentzen para o cálculo de sequentes.

# Implementação em Haskell

# Tipos

```haskell
data Ty
  = TyVar  String   -- variável proposicional P, Q, ...
  | TyUnit          -- ⊤  (unit)
  | TyVoid          -- ⊥  (void)
  | TyArr  Ty Ty    -- A → B
  | TyProd Ty Ty    -- A ∧ B  (produto)
  | TySum  Ty Ty    -- A ∨ B  (soma)
  deriving (Eq, Show)
```

# Termos

```haskell
data Term
  = Var     String
  | Lam     String Ty Term       -- λx:A. t
  | App     Term   Term
  | TmUnit                       -- unit
  | TmPair  Term Term            -- (t, u)
  | TmFst   Term                 -- fst t
  | TmSnd   Term                 -- snd t
  | TmInl   Term Ty              -- inl t as A+B
  | TmInr   Term Ty              -- inr t as A+B
  | TmCase  Term String Term String Term
  | TmAbsurd Term Ty             -- absurd t as C
```

# Verificador de Tipos

```haskell
typecheck :: TyCtx -> Term -> Either String Ty
typecheck ctx (Var x) =
  case lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Unbound variable: " ++ x
```

# Verificador de Tipos

```haskell
typecheck ctx (Lam x ty body) = do
  bodyTy <- typecheck ((x, ty) : ctx) body
  return (TyArr ty bodyTy)
```

# Verificador de Tipos

```haskell
typecheck ctx (App t1 t2) = do
  ty1 <- typecheck ctx t1
  ty2 <- typecheck ctx t2
  case ty1 of
    TyArr a b | ty2 == a -> Right b
    TyArr a _ -> Left $ "type mismatch: expected "
                     ++ renderTy a ++ " got " ++ renderTy ty2
    _ -> Left $ "not a function type: " ++ renderTy ty1
```

# Verificador de Tipos

```haskell
typecheck ctx (TmPair t1 t2) = do
  a <- typecheck ctx t1
  b <- typecheck ctx t2
  return (TyProd a b)
```

# Verificador de Tipos

```haskell
typecheck ctx (TmFst t) = do
  ty <- typecheck ctx t
  case ty of
    TyProd a _ -> Right a
    _ -> Left $ "fst: not a product: " ++ renderTy ty
```

# Verificador de Tipos

```haskell
typecheck ctx (TmSnd t) = do
  ty <- typecheck ctx t
  case ty of
    TyProd _ b -> Right b
    _ -> Left $ "snd: not a product: " ++ renderTy ty
```

# Verificador de Tipos

```haskell
typecheck ctx (TmInl t (TySum a _)) = do
  ta <- typecheck ctx t
  if ta == a then Right (TySum a undefined)
  else Left "inl: type mismatch"
```

# Verificador de Tipos

```haskell
typecheck ctx (TmCase t x t1 y t2) = do
  TySum a b <- typecheck ctx t
  c1 <- typecheck ((x,a):ctx) t1
  c2 <- typecheck ((y,b):ctx) t2
  if c1 == c2 then Right c1
  else Left "case: branch type mismatch"
```

# Verificador de Tipos

```haskell
typecheck ctx (TmAbsurd t c) = do
  TyVoid <- typecheck ctx t
  return c
```

# Sistema de Táticas

- Construção interativa de termos usando **táticas** ao estilo de assistentes de
  provas como Lean e Coq.

# Estado de Prova

```haskell
data Goal = Goal
  { hyps   :: [(String, Ty)]  -- hipóteses disponíveis
  , goalTy :: Ty              -- tipo / fórmula a provar
  }

data ProofState = ProofState
  { goals    :: [Goal]
  , assemble :: [Term] -> Term  -- monta o termo final
  }
```

# Combinador `refine`

```haskell
refine :: (Goal -> Either String ([Goal], [Term] -> Term))
       -> ProofState -> Either String ProofState
refine f (ProofState (g:gs) asm) =
  case f g of
    Left err -> Left err
    Right (newGoals, comb) ->
      Right $ ProofState
        { goals = newGoals ++ gs
        , assemble = \ts ->
            let (here, rest) = splitAt (length newGoals) ts
            in  asm (comb here : rest)
        }
```

# Tática `intro`

```haskell
introTactic :: String -> ProofState -> Either String ProofState
introTactic x = refine $ \g ->
  case goalTy g of
    TyArr a b ->
      let newGoal = g { hyps   = (x, a) : hyps g
                      , goalTy = b }
      in  Right ([newGoal], \[t] -> Lam x a t)
    _ -> Left "intro: goal is not an implication"
```

# Tática `apply`

```haskell
applyTactic :: String -> ProofState -> Either String ProofState
applyTactic h = refine $ \g ->
  case lookup h (hyps g) of
    Nothing -> Left $ "apply: " ++ h ++ " not in context"
    Just ty ->
      let (args, ret) = unfoldArr ty
      in  if ret == goalTy g
          then Right ( map (\a -> g { goalTy = a }) args
                     , \ts -> foldl App (Var h) ts )
          else Left "apply: conclusion does not match goal"
```

# Táticas

| Tática       | Efeito                                                     |
| ------------ | ---------------------------------------------------------- |
| `intro x`    | $A \to B \;\Rightarrow\;$ adiciona $x:A$, goal passa a $B$ |
| `assumption` | fecha goal com hipótese igual                              |
| `exact t`    | fecha goal com termo $t$                                   |
| `apply h`    | aplica $h : A_1 \to \cdots \to B$ ao goal $B$              |

# Táticas

| Tática           | Efeito                                               |
| ---------------- | ---------------------------------------------------- |
| `split`          | $A \wedge B \;\Rightarrow\;$ abre subgoals $A$ e $B$ |
| `left` / `right` | $A \vee B \;\Rightarrow\;$ escolhe ramo              |
| `cases h x y`    | case-split em $h : A \vee B$                         |

# Táticas

| Tática             | Efeito                    |
| ------------------ | ------------------------- |
| `trivial`          | fecha goal $\top$         |
| `absurd h`         | fecha goal com $h : \bot$ |
| `destruct h h1 h2` | decompõe $h : A \wedge B$ |

# Exemplo

```
proof (P -> Q) -> (Q -> R) -> P -> R
```

# Exemplo

```
tactic(1)> intro hpq
tactic(1)> intro hqr
tactic(1)> intro hp
tactic(1)> apply hqr
tactic(1)> apply hpq
tactic(1)> assumption
tactic(0)> :qed
```

# Resultado

```
Proof complete!
  Term:  λhpq:P→Q hqr:Q→R hp:P. hqr (hpq hp)
  Type:  (P → Q) → (Q → R) → P → R
  DB:    λ:P→Q. λ:Q→R. λ:P. 1 (2 0)
  Value: λa:P→Q b:Q→R c:P. b (a c)
```

# Exemplo 2

```
proof (P * Q) -> (Q * P)
  intro h
  split
  -- subgoal 1: Q
  destruct h h1 h2
  assumption
  -- subgoal 2: P
  destruct h h1 h2
  assumption
  :qed
```

# Resultado 2

```
Proof complete!
  Term:  λh:P×Q. (snd h, fst h)
  Type:  P × Q → Q × P
```

# Conclusão

# Conclusão

- O **lambda cálculo tipado simples** é simultaneamente:
  - Uma linguagem de programação funcional com terminação garantida
  - Um sistema de demonstrações para a lógica proposicional intuicionista

# Conclusão

- O **Isomorfismo de Curry-Howard** estabelece que:
  - Tipos $\equiv$ Fórmulas
  - Termos $\equiv$ Demonstrações
  - Redução $\equiv$ Normalização de provas

# Conclusão

- A **normalização forte** garante que todo programa bem-tipado termina —
  demonstrada via logical relations (Tait).

# Conclusão

- A construção por **táticas** reflete o modo como assistentes de provas
  modernos (Coq, Lean) operam: cada tática constrói incrementalmente um termo
  bem-tipado.
