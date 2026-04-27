---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Introdução ao Lean — Termos e Tipos
---

# Objetivos

# Objetivos

- Apresentar o **Lean** como assistente de provas baseado no Cálculo de
  Construções Indutivas.

# Objetivos

- Descrever os **tipos básicos e funcionais** da teoria de tipos simples
  subjacente ao Lean.

# Objetivos

- Apresentar as quatro formas de **termos**: constantes, variáveis, aplicação e
  funções anônimas.

# Objetivos

- Formalizar as **regras de tipagem** e mostrar como construir árvores de
  derivação.

# Objetivos

- Introduzir o problema de **habitação de tipos** como fundamento do isomorfismo
  de Curry-Howard.

# Motivação

# Motivação

- Vimos o **Cálculo de Construções** (CoC) como fundamento teórico dos
  assistentes de prova modernos.

- Agora vamos estudar **Lean** — um assistente de provas que implementa esse
  fundamento de forma prática.

# Motivação

- O Lean pode ser visto como a fusão de dois mundos:

$$\text{Lean} = \text{programação funcional} + \text{lógica}$$

# Motivação

- Como **linguagem funcional**, o Lean permite definir funções, tipos de dados e
  programas que são verificados pelo compilador.

# Motivação

- Como **sistema lógico**, o Lean permite enunciar e provar teoremas
  matematicamente — com garantia formal de correção.

# Motivação

- Nesta aula, estudamos a **teoria de tipos simples**: um fragmento do Lean sem
  tipos dependentes, correspondente ao cálculo lambda simplesmente tipado.

# Tipos

# Tipos

- **Tipos primitivos** representam conjuntos básicos de valores:

$$\mathbb{Z},\quad \mathbb{Q},\quad \mathbb{B},\quad \mathbb{N}, \quad \ldots$$

- No Lean: `Int`, `Rat`, `Bool`, `Nat`, ...

# Tipos

- **Tipos funcionais** são construídos com o operador $\to$:

$$\sigma \to \tau$$

- Um valor de tipo $\sigma \to \tau$ é uma função total que mapeia cada elemento
  de $\sigma$ a um elemento de $\tau$.

# Tipos

- Exemplos de tipos funcionais:

| Tipo                                         | Significado                      |
| -------------------------------------------- | -------------------------------- |
| $\mathbb{Z} \to \mathbb{Z}$                  | função de inteiros para inteiros |
| $\mathbb{Z} \to \mathbb{B}$                  | predicado sobre inteiros         |
| $(\mathbb{Z} \to \mathbb{Z}) \to \mathbb{Q}$ | função de ordem superior         |

# Tipos

- O operador $\to$ é **associativo à direita**:

$$\sigma \to \tau \to \upsilon \;\stackrel{\text{def}}{=}\; \sigma \to (\tau \to \upsilon)$$

# Tipos

- **Disciplina de tipos**: o sistema de tipos garante que expressões sem sentido
  sejam rejeitadas.

- Em teoria de conjuntos, $1 \in 2$ pode ser escrito sem erro.
- Em Lean, a expressão correspondente seria um erro de tipo.

# Termos

# Termos

- Os termos da teoria de tipos simples têm quatro formas:

| Forma     | Notação                              | Significado        |
| --------- | ------------------------------------ | ------------------ |
| Constante | $c$                                  | símbolo global     |
| Variável  | $x$                                  | ligada ou livre    |
| Aplicação | $t\; u$                              | $t$ aplicado a $u$ |
| Abstração | $\mathbf{fun}\;x{:}\sigma \mapsto t$ | função anônima     |

# Termos

- **Constantes** são símbolos declarados globalmente com um tipo fixo:

$$0 : \mathbb{Z},\quad \mathsf{abs} : \mathbb{Z} \to \mathbb{N},\quad
  \mathsf{prime} : \mathbb{N} \to \mathbb{B}$$

- No Lean, constantes podem ser declaradas com `opaque`:

```lean
opaque abs : Int → Nat
opaque prime : Nat → Bool
```

# Termos

- **Variáveis** podem ser:
  - **Ligadas** — introduzidas por `fun` dentro de uma abstração;
  - **Livres** — declaradas no contexto local.

# Termos

- **Aplicação** $t\; u$: aplica a função $t : \sigma \to \tau$ ao argumento
  $u : \sigma$, produzindo um resultado de tipo $\tau$.

- A aplicação é **associativa à esquerda**:

$$t\; u\; v \;\stackrel{\text{def}}{=}\; (t\; u)\; v$$

# Termos

- Exemplos de aplicação:

| Termo                                  | Tipo         |
| -------------------------------------- | ------------ |
| $\mathsf{abs}\; 0$                     | $\mathbb{N}$ |
| $\mathsf{prime}\;(\mathsf{abs}\;0)$    | $\mathbb{B}$ |
| $\mathsf{prime}\;(\mathsf{abs}\;(-3))$ | $\mathbb{B}$ |

# Termos

- **Abstração** (função anônima):

$$\mathbf{fun}\; x : \sigma \mapsto t$$

- Introduz uma função total que mapeia $x : \sigma$ ao corpo $t$.
- No Lean: `fun x : σ ↦ t`

# Beta-Redução

# Beta-Redução

- A **beta-redução** define a semântica computacional das abstrações:

$$(\mathbf{fun}\; x{:}\sigma \mapsto t)\; u \;\longrightarrow_\beta\; t[x := u]$$

- Substituímos todas as ocorrências livres de $x$ em $t$ pelo argumento $u$.

# Beta-Redução

- Exemplos de beta-redução:

| Termo                                           | Redutor |
| ----------------------------------------------- | ------- |
| $(\mathbf{fun}\; n{:}\mathbb{N} \mapsto n)\; 4$ | $4$     |
| $(\mathbf{fun}\; y{:}\mathbb{Z} \mapsto 1)\; 0$ | $1$     |

# Beta-Redução

- Exemplo com função de ordem superior:

$$(\mathbf{fun}\; n{:}\mathbb{N} \mapsto \mathsf{square}\;(\mathsf{square}\; n))\; 5$$

$$\longrightarrow_\beta\; \mathsf{square}\;(\mathsf{square}\; 5)$$

# Beta-Redução

- Redução que produz outra abstração:

$$(\mathbf{fun}\; x{:}\mathbb{Z} \mapsto (\mathbf{fun}\; y{:}\mathbb{Z} \mapsto x))\; 1$$

$$\longrightarrow_\beta\; \mathbf{fun}\; y{:}\mathbb{Z} \mapsto 1$$

# Currying e Notação

# Currying e Notação

- Funções de múltiplos argumentos são representadas por **abstrações aninhadas**
  (_currying_):

$$\mathbf{fun}\; x{:}\sigma \mapsto (\mathbf{fun}\; y{:}\tau \mapsto t)
  \;:\; \sigma \to \tau \to \upsilon$$

# Currying e Notação

- Abreviações de notação:

| Notação abreviada              | Significado completo             |
| ------------------------------ | -------------------------------- |
| $\sigma \to \tau \to \upsilon$ | $\sigma \to (\tau \to \upsilon)$ |
| $t\; u\; v$                    | $(t\; u)\; v$                    |
| `fun (x : σ) (y : τ) ↦ t`      | `fun x : σ ↦ (fun y : τ ↦ t)`    |

# Currying e Notação

- **Inferência de tipos**: o Lean pode deduzir anotações de tipo omitidas:

```lean
-- Com anotação completa:
fun (x : Int) ↦ abs x

-- Com inferência:
fun x ↦ abs x
```

# Currying e Notação

- Comandos Lean usados para verificação de tipos:

| Comando  | Descrição                              |
| -------- | -------------------------------------- |
| `#check` | Exibe o tipo de um termo (diagnóstico) |
| `opaque` | Declara uma constante sem definição    |

# Regras de Tipagem

# Regras de Tipagem

- Um **julgamento de tipagem** tem a forma:

$$C \vdash t : \sigma$$

- "$t$ tem tipo $\sigma$ no contexto local $C$"

- O contexto $C$ é uma lista de declarações
  $x_1 : \sigma_1, \ldots, x_n : \sigma_n$.

# Regras de Tipagem

- **Constante** (Cst): uma constante declarada globalmente pode ser usada em
  qualquer contexto:

$$\dfrac{c : \sigma \;\text{declarada globalmente}}{C \vdash c : \sigma}
  \quad\text{(Cst)}$$

# Regras de Tipagem

- **Variável** (Var): uma variável é usável se estiver no contexto local:

$$\dfrac{(x : \sigma) \in C}{C \vdash x : \sigma}
  \quad\text{(Var)}$$

- Se $x$ aparece mais de uma vez em $C$, a ocorrência mais à direita prevalece
  (**sombreamento**).

# Regras de Tipagem

- **Aplicação** (App):

$$\dfrac{C \vdash t : \sigma \to \tau \qquad C \vdash u : \sigma}
        {C \vdash t\; u : \tau}
  \quad\text{(App)}$$

# Regras de Tipagem

- **Abstração** (Fun):

$$\dfrac{C,\, x : \sigma \vdash t : \tau}
        {C \vdash \mathbf{fun}\; x{:}\sigma \mapsto t \;:\; \sigma \to \tau}
  \quad\text{(Fun)}$$

- Para tipar o corpo $t$, estendemos o contexto com $x : \sigma$.

# Regras de Tipagem

- Resumo das quatro regras:

| Regra   | Forma                           |
| ------- | ------------------------------- |
| **Cst** | constante declarada globalmente |
| **Var** | variável no contexto local      |
| **App** | aplicação função-argumento      |
| **Fun** | introdução de função anônima    |

# Árvores de Derivação

# Árvores de Derivação

- Uma **árvore de derivação** demonstra formalmente que um termo é bem-tipado.

- Exemplo: mostrar que $\mathbf{fun}\; x{:}\mathbb{Z} \mapsto \mathsf{abs}\; x
  \;:\; \mathbb{Z} \to \mathbb{N}$

# Árvores de Derivação

$$
\dfrac{
  \dfrac{
    \dfrac{}{\mathsf{abs} : \mathbb{Z} \to \mathbb{N}}\ \text{(Cst)}
    \qquad
    \dfrac{(x : \mathbb{Z}) \in \{x : \mathbb{Z}\}}{x : \mathbb{Z} \in x{:}\mathbb{Z}}\ \text{(Var)}
  }{x{:}\mathbb{Z} \vdash \mathsf{abs}\; x : \mathbb{N}}\ \text{(App)}
}{
  \emptyset \vdash \mathbf{fun}\; x{:}\mathbb{Z} \mapsto \mathsf{abs}\; x
  \;:\; \mathbb{Z} \to \mathbb{N}
}\ \text{(Fun)}
$$

# Árvores de Derivação

- O processo de construção da árvore é **descendente**: decompomos o julgamento
  objetivo nas premissas das regras, recursivamente.

- Nos folhas encontramos sempre Cst ou Var.

# Habitação de Tipos

# Habitação de Tipos

- Dado um tipo $\sigma$, o **problema de habitação** pergunta:

> Existe algum termo $t$ tal que $\emptyset \vdash t : \sigma$?

# Habitação de Tipos

- Estratégia para encontrar um habitante de $\sigma$ (aplica-se recursivamente):

  1. Se $\sigma = \tau \to \upsilon$: introduza
     $\mathbf{fun}\; x{:}\tau \mapsto \underline{\quad}$ e tente habitar
     $\upsilon$ com $x$ disponível.

  2. Caso contrário: procure uma constante ou variável do tipo
     $\tau_1 \to \cdots \to \tau_n \to \sigma$ e aplique-a, habitando cada
     argumento recursivamente.

# Habitação de Tipos

- Exemplo: habitar o tipo

$$(\alpha \to \beta \to \gamma) \to ((\beta \to \alpha) \to \beta) \to \alpha \to \gamma$$

# Habitação de Tipos

- Passo 1 — introduzir três variáveis:

$$\mathbf{fun}\; f{:}(\alpha\to\beta\to\gamma)\; g{:((\beta\to\alpha)\to\beta)}\; a{:}\alpha
  \mapsto \underline{\quad}$$

- Meta restante: habitar $\gamma$ com $f : \alpha\to\beta\to\gamma$,
  $g : (\beta\to\alpha)\to\beta$, $a : \alpha$ disponíveis.

# Habitação de Tipos

- Passo 2 — aplicar $f$ (único caminho para $\gamma$):

$$f\; \underline{\quad}_\alpha\; \underline{\quad}_\beta$$

- Preencher $\alpha$: usar $a$ diretamente.
- Preencher $\beta$: aplicar $g$, que exige $\beta \to \alpha$, fornecida por
  $\mathbf{fun}\; b{:}\beta \mapsto a$.

# Habitação de Tipos

- Habitante encontrado:

$$\mathbf{fun}\; f\; g\; a \mapsto f\; a\; (g\;(\mathbf{fun}\; b \mapsto a))$$

# Habitação de Tipos

- **Princípio de desenvolvimento incremental**: escreva um programa
  sintaticamente correto desde o início, usando $\underline{\quad}$ para partes
  ainda desconhecidas, e preencha os buracos progressivamente.

- No Lean, `_` representa um buraco que o elaborador tenta inferir.

# Lean na prática

# Lean na prática

- Declarando tipos e constantes opacas:

```lean
opaque α : Type
opaque β : Type
opaque f : α → β
opaque a : α
```

# Lean na prática

- Verificando tipos com `#check`:

```lean
#check f a         -- β
#check fun x : α ↦ f x   -- α → β
```

# Lean na prática

- Exemplo com múltiplos argumentos e currying:

```lean
opaque g : α → α → β

#check g             -- α → α → β
#check g a           -- α → β
#check g a a         -- β
#check fun x y : α ↦ g x y   -- α → α → β
```

# Lean na prática

- `#check` é um **comando diagnóstico**: seu resultado é exibido durante a
  elaboração mas não faz parte da prova ou do programa final.

# Resumo

# Resumo

| Conceito           | Descrição                                           |
| ------------------ | --------------------------------------------------- |
| Tipo primitivo     | `Int`, `Nat`, `Bool`, ...                           |
| Tipo funcional     | $\sigma \to \tau$ (associa à direita)               |
| Constante          | símbolo global com tipo fixo                        |
| Variável           | ligada por `fun` ou livre no contexto               |
| Aplicação          | $t\; u$ — associa à esquerda                        |
| Abstração          | `fun x : σ ↦ t`                                     |
| Beta-redução       | $(\mathbf{fun}\; x \mapsto t)\; u \to t[x := u]$    |
| Habitação de tipos | encontrar $t$ tal que $\emptyset \vdash t : \sigma$ |

# Referências

# Referências

- PIERCE, Benjamin C. _Types and Programming Languages_. MIT Press, 2002. (Cap.
  9–11: cálculo lambda simplesmente tipado)

- DE MOURA, Leonardo et al. Lean 4: A Theorem Prover and Programming Language.
  In: _CADE-28_, 2021.

- SORENSEN, Morten; URZYCZYN, Pawel. _Lectures on the Curry-Howard Isomorphism_.
  Elsevier, 2006.
