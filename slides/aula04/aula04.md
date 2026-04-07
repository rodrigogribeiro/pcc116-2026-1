---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lambda cálculo não tipado
---

# Objetivos

# Objetivos

- Apresentar a sintaxe do lambda cálculo não tipado.

# Objetivos

- Apresentar a semântica _call-by-value_ do lambda cálculo não tipado.

# Objetivos

- Mostrar como representar booleanos, números naturais e funções sobre estes no
  lambda cálculo.

# Objetivos

- Apresentar a notação De Bruijn e descrever a substituição nessa representação.

# Objetivos

- Apresentar os pontos principais da implementação em Haskell.

# Introdução

# Introdução

- O **lambda cálculo** foi proposto por Alonzo Church na década de 1930 como um
  modelo formal de computação.

# Introdução

- É baseado em apenas três conceitos:
  - Variáveis
  - Abstração (definição de função)
  - Aplicação (chamada de função)

# Introdução

- Apesar de sua simplicidade extrema, o lambda cálculo é Turing-completo:
  qualquer função computável pode ser representada.

# Introdução

- O lambda cálculo serve como fundação teórica de linguagens funcionais como
  Haskell, ML, Scheme e outras.

# Introdução

- Além disso, é o ponto de partida para estudarmos sistemas de tipos, semântica
  de linguagens e teoria de tipos.

# Sintaxe

# Sintaxe

- A gramática do lambda cálculo não tipado é extremamente simples.

$$
t \;::=\; x \;\mid\; \lambda x.\, t \;\mid\; t\;t
$$

# Sintaxe

- $x$ — **variável**: um identificador qualquer.

# Sintaxe

- $\lambda x.\, t$ — **abstração**: define uma função com parâmetro $x$ e corpo
  $t$.

# Sintaxe

- $t_1\;t_2$ — **aplicação**: aplica a função $t_1$ ao argumento $t_2$.

# Sintaxe

- A aplicação é **associativa à esquerda**:

$$t_1\;t_2\;t_3 \;=\; (t_1\;t_2)\;t_3$$

# Sintaxe

- O corpo de uma abstração se estende o máximo possível à direita:

$$\lambda x.\;t_1\;t_2 \;=\; \lambda x.\;(t_1\;t_2)$$

# Sintaxe

- Abstrações múltiplas são abreviadas:

$$\lambda x\,y\,z.\;t \;=\; \lambda x.\,\lambda y.\,\lambda z.\,t$$

# Variáveis Livres e Ligadas

- Uma ocorrência de $x$ em $t$ é **ligada** se está sob o escopo de um
  $\lambda x$.

# Variáveis Livres e Ligadas

- Caso contrário, a ocorrência é **livre**.

# Variáveis Livres e Ligadas

- Exemplo: em $\lambda x.\;x\;y$
  - $x$ é **ligada**
  - $y$ é **livre**

# Variáveis Livres e Ligadas

- O conjunto de variáveis livres $\text{FV}(t)$ é definido por:

$$
\begin{array}{lcl}
\text{FV}(x) & = & \{x\} \\
\text{FV}(\lambda x.\,t) & = & \text{FV}(t) \setminus \{x\} \\
\text{FV}(t_1\;t_2) & = & \text{FV}(t_1) \cup \text{FV}(t_2) \\
\end{array}
$$

# Alpha-equivalência

- Dois termos são **alpha-equivalentes** ($=_\alpha$) se diferem apenas nos
  nomes de variáveis ligadas.

# Alpha-equivalência

- Exemplo:

$$\lambda x.\;x \;=_\alpha\; \lambda y.\;y \;=_\alpha\; \lambda z.\;z$$

# Alpha-equivalência

- No lambda cálculo, termos alpha-equivalentes são considerados **idênticos**.

# Semântica: Call-by-Value

# Semântica

- A semântica do lambda cálculo é dada por um sistema de **redução** que define
  como termos se simplificam.

# Semântica

- A regra fundamental é a **beta-redução**:

$$(\lambda x.\;t_1)\;t_2 \;\longrightarrow\; [x \mapsto t_2]\;t_1$$

# Semântica

- Leitura: a aplicação de $\lambda x.\;t_1$ ao argumento $t_2$ reduz ao corpo
  $t_1$ com $x$ substituído por $t_2$.

# Semântica

- Exemplo:

$$(\lambda x.\;x\;x)\;(\lambda y.\;y)
\;\longrightarrow\;
(\lambda y.\;y)\;(\lambda y.\;y)
\;\longrightarrow\;
\lambda y.\;y$$

# Call-by-Value

- Existem diversas **estratégias de avaliação** que determinam a ordem em que
  reduzimos sub-termos.

# Call-by-Value

- Na estratégia **call-by-value** (CBV):
  - O argumento é **completamente avaliado** antes de ser passado.
  - Não se reduz sob abstrações.

# Call-by-Value

- **Valores** na estratégia CBV são apenas as abstrações:

$$v \;::=\; \lambda x.\;t$$

# Call-by-Value

- Regras de redução CBV:

$$
\dfrac{t_1 \;\longrightarrow\; t_1'}{t_1\;t_2 \;\longrightarrow\; t_1'\;t_2}
\quad\text{(E-App1)}
$$

# Call-by-Value

$$
\dfrac{t_2 \;\longrightarrow\; t_2'}{v_1\;t_2 \;\longrightarrow\; v_1\;t_2'}
\quad\text{(E-App2)}
$$

# Call-by-Value

$$
(\lambda x.\;t_{12})\;v_2 \;\longrightarrow\; [x \mapsto v_2]\;t_{12}
\quad\text{(E-Beta)}
$$

# Call-by-Value

- Em E-App1: reduzimos a função antes do argumento.

- Em E-App2: a função já é um valor; reduzimos o argumento.

- Em E-Beta: ambos são valores; disparamos a beta-redução.

# Call-by-Value

$$
(\lambda x.\;x)\;((\lambda y.\;y)\;(\lambda z.\;z))
$$

# Call-by-Value

$$
\dfrac{
  (\lambda y.\;y)\;(\lambda z.\;z) \;\longrightarrow\; \lambda z.\;z
}{
  (\lambda x.\;x)\;((\lambda y.\;y)\;(\lambda z.\;z))
  \;\longrightarrow\;
  (\lambda x.\;x)\;(\lambda z.\;z)
}
\quad\text{(E-App2)}
$$

# Call-by-Value

$$
(\lambda x.\;x)\;(\lambda z.\;z)
\;\longrightarrow\;
\lambda z.\;z
\quad\text{(E-Beta)}
$$

# Forma Normal

- Um termo está em **forma normal** quando nenhuma regra de redução pode ser
  aplicada.

# Forma Normal

- Nem todo termo possui forma normal:

$$
(\lambda x.\;x\;x)\;(\lambda x.\;x\;x)
\;\longrightarrow\;
(\lambda x.\;x\;x)\;(\lambda x.\;x\;x)
\;\longrightarrow\;\cdots
$$

# Forma Normal

- Este é o chamado **combinador $\Omega$** — o termo mais simples que não
  termina.

# Encodings: Booleanos

# Booleanos

- No lambda cálculo, podemos **codificar** tipos de dados como funções.

# Booleanos

- Ideia: um booleano é uma função que escolhe entre dois valores.

$$
\begin{array}{lcl}
\mathbf{true}  & = & \lambda t.\,\lambda f.\;t \\
\mathbf{false} & = & \lambda t.\,\lambda f.\;f \\
\end{array}
$$

# Booleanos

- O condicional:

$$
\mathbf{if} \;=\; \lambda b.\,\lambda t.\,\lambda f.\;b\;t\;f
$$

# Booleanos

- Verificação de $\mathbf{if}\;\mathbf{true}\;M\;N \to M$:

$$
(\lambda b.\,\lambda t.\,\lambda f.\;b\;t\;f)\;\mathbf{true}\;M\;N
$$

$$
\longrightarrow^* \mathbf{true}\;M\;N
$$

$$
= (\lambda t.\,\lambda f.\;t)\;M\;N
\;\longrightarrow^*\; M
$$

# Booleanos

- Operações lógicas:

$$
\begin{array}{lcl}
\mathbf{and} & = & \lambda b_1.\,\lambda b_2.\;b_1\;b_2\;\mathbf{false}\\
\mathbf{or}  & = & \lambda b_1.\,\lambda b_2.\;b_1\;\mathbf{true}\;b_2 \\
\mathbf{not} & = & \lambda b.\;b\;\mathbf{false}\;\mathbf{true} \\
\end{array}
$$

# Booleanos

- Verificação de $\mathbf{not}\;\mathbf{true} \to \mathbf{false}$:

$$
(\lambda b.\;b\;\mathbf{false}\;\mathbf{true})\;\mathbf{true}
\;\longrightarrow\;
\mathbf{true}\;\mathbf{false}\;\mathbf{true}
$$

$$
= (\lambda t.\,\lambda f.\;t)\;\mathbf{false}\;\mathbf{true}
\;\longrightarrow^*\;
\mathbf{false}
$$

# Encodings: Números Naturais

# Números de Church

- Os **números de Church** codificam naturais como iteração de funções.

# Números de Church

$$
\begin{array}{lcl}
\mathbf{0} & = & \lambda f.\,\lambda x.\;x \\
\mathbf{1} & = & \lambda f.\,\lambda x.\;f\;x \\
\mathbf{2} & = & \lambda f.\,\lambda x.\;f\,(f\;x) \\
\mathbf{n} & = & \lambda f.\,\lambda x.\;\underbrace{f\,(f\,(\cdots(f}_{n}\;x)\cdots))\\
\end{array}
$$

# Números de Church

- Intuição: o numeral $\mathbf{n}$ representa a aplicação de $f$ exatamente $n$
  vezes ao argumento $x$.

# Números de Church

- Sucessor:

$$
\mathbf{succ} = \lambda n.\,\lambda f.\,\lambda x.\;f\,(n\;f\;x)
$$

# Números de Church

- Verificação de $\mathbf{succ}\;\mathbf{1} \to \mathbf{2}$:

$$
(\lambda n.\,\lambda f.\,\lambda x.\;f\,(n\;f\;x))\;\mathbf{1}
\;\longrightarrow\;
\lambda f.\,\lambda x.\;f\,(\mathbf{1}\;f\;x)
$$

$$
\longrightarrow^*\;
\lambda f.\,\lambda x.\;f\,(f\;x)
\;=\; \mathbf{2}
$$

# Números de Church

- Adição:

$$
\mathbf{plus} = \lambda m.\,\lambda n.\,\lambda f.\,\lambda x.\;m\;f\;(n\;f\;x)
$$

# Números de Church

- Intuição: aplicar $f$ $m$ vezes ao resultado de aplicar $f$ $n$ vezes a $x$.

# Números de Church

- Multiplicação:

$$
\mathbf{mult} = \lambda m.\,\lambda n.\,\lambda f.\;m\,(n\;f)
$$

# Números de Church

- Intuição: aplicar $(n\;f)$ — "aplicar $f$ $n$ vezes" — exatamente $m$ vezes.

# Números de Church

- Teste de zero:

$$
\mathbf{iszero} = \lambda n.\;n\;(\lambda x.\;\mathbf{false})\;\mathbf{true}
$$

# Números de Church

- Verificação de $\mathbf{iszero}\;\mathbf{0} \to \mathbf{true}$:

$$
(\lambda n.\;n\;(\lambda x.\;\mathbf{false})\;\mathbf{true})\;\mathbf{0}
\;\longrightarrow\;
\mathbf{0}\;(\lambda x.\;\mathbf{false})\;\mathbf{true}
$$

$$
= (\lambda f.\,\lambda x.\;x)\;(\lambda x.\;\mathbf{false})\;\mathbf{true}
\;\longrightarrow^*\;
\mathbf{true}
$$

# Notação De Bruijn

# Motivação

- Na notação com nomes, dois termos alpha-equivalentes são considerados iguais
  mas têm representações diferentes.

# Motivação

- Isso complica a implementação: verificar alpha-equivalência e realizar
  substituição livre-de-captura são operações delicadas.

# Motivação

- A **notação De Bruijn** (1972) elimina os nomes de variáveis, substituindo-os
  por índices numéricos.

# Notação De Bruijn

- O **índice De Bruijn** de uma variável é o número de lambdas que a separam de
  seu binder.

# Notação De Bruijn

- Exemplos:

$$
\begin{array}{lcl}
\lambda x.\;x & \longrightarrow & \lambda.\;0 \\
\lambda x.\,\lambda y.\;x & \longrightarrow & \lambda.\,\lambda.\;1 \\
\lambda x.\,\lambda y.\;y & \longrightarrow & \lambda.\,\lambda.\;0 \\
\lambda x.\,\lambda y.\;x\;y & \longrightarrow & \lambda.\,\lambda.\;1\;0 \\
\end{array}
$$

# Notação De Bruijn

- Termos alpha-equivalentes têm **a mesma** representação De Bruijn.

$$
\lambda x.\;x \;=_\alpha\; \lambda y.\;y \;=_\alpha\; \lambda z.\;z
\;\longrightarrow\; \lambda.\;0
$$

# Notação De Bruijn

- A gramática na notação De Bruijn:

$$
t \;::=\; n \;\mid\; \lambda.\,t \;\mid\; t\;t
\quad (n \in \mathbb{N})
$$

# Shift

- Ao realizar uma substituição, variáveis livres podem ter seus índices
  alterados — precisamos do operador de **shift**.

# Shift

- $\uparrow^d_c\,t$ incrementa em $d$ todos os índices livres de $t$ que são
  $\geq c$ (cutoff).

# Shift

$$
\uparrow^d_c\,k \;=\;
\begin{cases}
k     & \text{se } k < c \\
k + d & \text{se } k \geq c
\end{cases}
$$

$$
\uparrow^d_c(\lambda.\,t) \;=\; \lambda.\,\uparrow^d_{c+1} t
$$

$$
\uparrow^d_c(t_1\;t_2) \;=\; (\uparrow^d_c t_1)\;(\uparrow^d_c t_2)
$$

# Substituição

- $[j \mapsto s]\,t$ substitui o índice $j$ por $s$ em $t$.

$$
[j \mapsto s]\,k \;=\;
\begin{cases}
s & \text{se } k = j \\
k & \text{caso contrário}
\end{cases}
$$

$$
[j \mapsto s]\,(\lambda.\,t) \;=\;
\lambda.\,[j{+}1 \mapsto \uparrow^1_0 s]\,t
$$

$$
[j \mapsto s]\,(t_1\;t_2) \;=\;
([j \mapsto s]\,t_1)\;([j \mapsto s]\,t_2)
$$

# Beta-Redução

- Beta-redução na notação De Bruijn:

$$
(\lambda.\,t_1)\;t_2
\;\longrightarrow\;
\uparrow^{-1}_0\!\left([0 \mapsto \uparrow^1_0\,t_2]\;t_1\right)
$$

# Beta-Redução

- Por que $\uparrow^1_0\,t_2$?

  - Ao entrar sob o lambda de $t_1$, o argumento $t_2$ fica um nível mais fundo
    — seus índices livres devem ser incrementados.

# Beta-Redução

- Por que $\uparrow^{-1}_0$ no resultado?

  - Após a substituição, o lambda consumido desaparece — os índices livres que
    apontavam "além" do lambda devem ser decrementados.

# Exemplo

- Redução de $(\lambda.\;0)\;(\lambda.\;0)$:

$$
\uparrow^{-1}_0\!\left([0 \mapsto \uparrow^1_0(\lambda.\;0)]\;0\right)
$$

$$
= \uparrow^{-1}_0\!\left([0 \mapsto \lambda.\;0]\;0\right)
= \uparrow^{-1}_0\!(\lambda.\;0)
= \lambda.\;0
$$

# Named → De Bruijn

- A conversão usa um **contexto** $\Gamma$ — lista de nomes de variáveis, com o
  mais recente na frente.

$$
\begin{array}{lcl}
\text{conv}(\Gamma, x) & = & i \;\text{ onde } \Gamma[i] = x \\
\text{conv}(\Gamma, \lambda x.\,t) & = & \lambda.\;\text{conv}(x:\Gamma,\, t) \\
\text{conv}(\Gamma, t_1\;t_2) & = & \text{conv}(\Gamma,t_1)\;\text{conv}(\Gamma,t_2)\\
\end{array}
$$

# De Bruijn → Named

- A conversão inversa recupera nomes a partir do contexto, gerando nomes frescos
  para lambdas.

$$
\begin{array}{lcl}
\text{conv}^{-1}(\Gamma, k) & = & \Gamma[k] \\
\text{conv}^{-1}(\Gamma, \lambda.\,t) & = & \lambda x.\;\text{conv}^{-1}(x:\Gamma,\,t) \\
& & \text{onde } x \notin \Gamma\\
\text{conv}^{-1}(\Gamma, t_1\;t_2) & = &
  \text{conv}^{-1}(\Gamma,t_1)\;\text{conv}^{-1}(\Gamma,t_2) \\
\end{array}
$$

# Implementação em Haskell

# Tipos de Dados

- Representação com nomes (`Untyped.Syntax.Named`):

```haskell
data Term
  = Var String       -- variável
  | Lam String Term  -- λx. t
  | App Term Term    -- t1 t2
```

# Tipos de Dados

- Representação De Bruijn (`Untyped.Syntax.DeBruijn`):

```haskell
data Term
  = Var Int      -- índice
  | Lam Term     -- λ. t  (sem nome)
  | App Term Term
```

# Conversão Named → De Bruijn

```haskell
type Context = [String]

fromNamed :: Context -> N.Term -> Either String Term
fromNamed ctx (N.Var x) =
  case findIndex (== x) ctx of
    Just i  -> Right (Var i)
    Nothing -> Left ("Unbound variable: " ++ x)
fromNamed ctx (N.Lam x body) =
  Lam <$> fromNamed (x : ctx) body
fromNamed ctx (N.App t1 t2) =
  App <$> fromNamed ctx t1 <*> fromNamed ctx t2
```

# Conversão De Bruijn → Named

```haskell
toNamed :: Context -> Term -> N.Term
toNamed ctx (Var i)
  | i < length ctx = N.Var (ctx !! i)
  | otherwise      = N.Var ("_" ++ show i)
toNamed ctx (Lam body) =
  let name = freshName ctx
  in  N.Lam name (toNamed (name : ctx) body)
toNamed ctx (App t1 t2) =
  N.App (toNamed ctx t1) (toNamed ctx t2)
```

# Shift

```haskell
shift :: Int -> Int -> Term -> Term
shift d c (Var k)
  | k >= c    = Var (k + d)
  | otherwise = Var k
shift d c (Lam body)  = Lam (shift d (c + 1) body)
shift d c (App t1 t2) = App (shift d c t1)
                            (shift d c t2)
```

# Substituição

```haskell
subst :: Int -> Term -> Term -> Term
subst j s (Var k)
  | k == j    = s
  | otherwise = Var k
subst j s (Lam body)  =
  Lam (subst (j+1) (shift 1 0 s) body)
subst j s (App t1 t2) =
  App (subst j s t1) (subst j s t2)
```

# Beta-Redução

```haskell
betaReduce :: Term -> Term -> Term
betaReduce t1 t2 =
  shift (-1) 0 (subst 0 (shift 1 0 t2) t1)
```

# Avaliação

- O interpretador usa **normal-order** (leftmost-outermost): reduz o redex mais
  externo à esquerda, incluindo sob lambdas.

```haskell
step :: Term -> Maybe Term
step (App (Lam body) t2) =
  Just (betaReduce body t2)
step (App t1 t2) =
  case step t1 of
    Just t1' -> Just (App t1' t2)
    Nothing  -> App t1 <$> step t2
step (Lam body) = Lam <$> step body
step _          = Nothing
```

# Avaliação

```haskell
data EvalResult
  = NormalForm Term Int  -- forma normal + nº de passos
  | StepLimit  Term      -- limite atingido

eval :: Int -> Term -> EvalResult
eval maxSteps = go 0
  where
    go n t
      | n >= maxSteps = StepLimit t
      | otherwise =
          case step t of
            Nothing -> NormalForm t n
            Just t' -> go (n+1) t'
```

# Referências

# Referências

- PIERCE, Benjamin C. **Types and Programming Languages**. MIT Press, 2002.
  - Capítulos 5 (Untyped Lambda Calculus) e 6 (Nameless Representation).

# Referências

- DE BRUIJN, Nicolaas G. Lambda calculus notation with nameless dummies, a tool
  for automatic formula manipulation, with application to the Church-Rosser
  theorem. **Indagationes Mathematicae**, 34(5):381–392, 1972.

# Referências

- CHURCH, Alonzo. A formulation of the simple theory of types. **Journal of
  Symbolic Logic**, 5(2):56–68, 1940.
