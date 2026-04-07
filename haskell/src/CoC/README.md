# `coc` — REPL do Cálculo de Construções

Verificador de tipos interativo e assistente de provas por táticas para o
**Cálculo de Construções (CoC)**, o vértice superior do cubo de Barendregt. No
CoC, tipos e termos habitam a mesma linguagem, permitindo provas de proposições
com quantificação universal e existencial sobre tipos.

## Execução

A partir do diretório `haskell/`:

```bash
cabal run coc
```

O REPL inicia no modo de termos com um contexto pré-carregado de conectivos
lógicos codificados à la Church.

---

## Comandos — modo de termos

| Comando        | Descrição                                                   |
| -------------- | ----------------------------------------------------------- |
| `:def x := t`  | Define `x` como o termo `t` (adicionado ao contexto global) |
| `:check t`     | Infere e exibe o tipo de `t`                                |
| `:eval t`      | Normaliza `t` e exibe seu valor e tipo                      |
| `:whnf t`      | Reduz `t` à forma normal de cabeça fraca                    |
| `:ctx`         | Exibe o contexto global atual                               |
| `proof T`      | Entra no modo de prova por táticas para o tipo `T`          |
| `:help`        | Exibe a referência de comandos                              |
| `:quit` / `:q` | Sai do REPL                                                 |

Qualquer outra entrada é verificada quanto ao tipo e o resultado é exibido.

---

## Sintaxe de termos

| Construção            | Sintaxe                    |
| --------------------- | -------------------------- |
| Sort dos tipos        | `*`                        |
| Sort dos kinds        | `□` ou `Box`               |
| Variável              | `x`                        |
| Abstração lambda      | `\(x:A). t` ou `λ(x:A). t` |
| Múltiplos binders     | `\(x:A)(y:B). t`           |
| Produto dependente    | `Π(x:A). B` ou `∀(x:A). B` |
| Tipo função (anônimo) | `A -> B`                   |
| Aplicação             | `f a`                      |
| Anotação de tipo      | `(t : A)`                  |

---

## Termos pré-definidos no contexto inicial

As seguintes constantes codificadas à la Church estão disponíveis na
inicialização:

| Nome        | Tipo                      | Significado             |
| ----------- | ------------------------- | ----------------------- |
| `True`      | `*`                       | `⊤ = Πa:*. a→a`         |
| `False`     | `*`                       | `⊥ = Πa:*. a`           |
| `tt`        | `True`                    | Prova de `⊤`            |
| `exFalso`   | `False -> Πa:*. a`        | Ex falso quodlibet      |
| `and_intro` | `Πa b:*. a -> b -> a ∧ b` | Introdução da conjunção |
| `and_fst`   | `Πa b:*. a ∧ b -> a`      | Projeção esquerda       |
| `and_snd`   | `Πa b:*. a ∧ b -> b`      | Projeção direita        |
| `or_inl`    | `Πa b:*. a -> a ∨ b`      | Injeção esquerda        |
| `or_inr`    | `Πa b:*. b -> a ∨ b`      | Injeção direita         |

---

## Modo de prova por táticas

Entre no modo de prova com `proof T`. O prompt muda para `coc[n]>` mostrando o
número de objetivos restantes. Cada objetivo exibe o contexto local acima de uma
linha separadora e o tipo do objetivo abaixo.

| Tática        | Descrição                                                      |
| ------------- | -------------------------------------------------------------- |
| `intro x`     | Introduz o ligador `Π`/`→` mais externo como hipótese `x`      |
| `introType x` | Introduz um ligador `Π(x:*)` de tipo como variável de tipo `x` |
| `apply h`     | Aplica `h` ao objetivo; abre subobjetivos para cada argumento  |
| `exact t`     | Fecha o objetivo com o termo explícito `t`                     |
| `assumption`  | Fecha o objetivo encontrando uma hipótese correspondente       |
| `split`       | Prova `A ∧ B`: abre subobjetivos para `A` e `B`                |
| `left`        | Prova `A ∨ B` pelo ramo esquerdo                               |
| `right`       | Prova `A ∨ B` pelo ramo direito                                |
| `exists t`    | Prova `∃x:A.B` com testemunha `t`                              |
| `unfold nome` | Desdobra a definição de `nome` no objetivo atual               |
| `trivial`     | Fecha um objetivo `⊤`                                          |
| `absurd h`    | Fecha qualquer objetivo usando `h : ⊥`                         |
| `:qed`        | Finaliza a prova quando não há mais objetivos                  |
| `:abandon`    | Descarta a prova em andamento                                  |
| `:save <arq>` | Salva o script de táticas em um arquivo                        |

---

## Exemplos

### Verificação de tipos

```
coc> \(a:*)(x:a). x
λa. λx. x : Πa:*. a → a

coc> :def id := \(a:*)(x:a). x
id : Πa:*. a → a

coc> :eval id * (\(x:*). x)
  Value: λx. x
  Type:  * → *
```

### Prova por táticas — `P → P`

```
coc> proof \(P:*). P -> P
coc[1]> introType P
coc[1]> intro h
coc[1]> assumption
coc[0]> :qed
Proof complete!
  Term: λP. λh. h
  Type: Πa:*. a → a
```

### Prova por táticas — `∀A B. A ∧ B → A`

```
coc> proof ∀(a:*)∀(b:*). (∀(c:*).(a->b->c)->c) -> a
coc[1]> introType a
coc[1]> introType b
coc[1]> intro h
coc[1]> apply h
coc[2]> intro ha
coc[1]> intro hb
coc[1]> assumption
coc[0]> :qed
Proof complete!
```

---

## Codificações de Church utilizadas internamente

| Conectivo | Codificação                   |
| --------- | ----------------------------- |
| `⊤`       | `Πa:*. a → a`                 |
| `⊥`       | `Πa:*. a`                     |
| `A ∧ B`   | `Πc:*. (A → B → c) → c`       |
| `A ∨ B`   | `Πc:*. (A → c) → (B → c) → c` |
| `∃x:A. B` | `Πc:*. (Πx:A. B → c) → c`     |
| `¬A`      | `A → ⊥`                       |
