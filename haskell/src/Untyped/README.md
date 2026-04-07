# `untyped` — REPL do Cálculo Lambda Não Tipado

Interpretador interativo para o **cálculo lambda não tipado** com suporte às
representações de variáveis por nomes e índices de De Bruijn.

## Execução

A partir do diretório `haskell/`:

```bash
cabal run untyped
```

O REPL inicia no **modo baseado em nomes**. Troque a representação com
`:mode db` / `:mode named`.

---

## Comandos

| Comando        | Descrição                                     |
| -------------- | --------------------------------------------- |
| `:mode named`  | Alterna para entrada com variáveis nomeadas   |
| `:mode db`     | Alterna para entrada com índices de De Bruijn |
| `:help`        | Exibe a referência de comandos                |
| `:quit` / `:q` | Sai do REPL                                   |

Após cada termo inserido, o REPL exibe as formas nomeada e de De Bruijn e reduz
o termo à forma normal (até 1 000 000 passos).

---

## Sintaxe — modo nomeado

| Construção    | Sintaxe                         |
| ------------- | ------------------------------- |
| Variável      | `x`, `foo`, `x'`                |
| Abstração     | `\x. t` ou `λx. t`              |
| Multi-ligador | `\x y z. t`                     |
| Aplicação     | `t1 t2 t3` (associa à esquerda) |
| Agrupamento   | `(t)`                           |

## Sintaxe — modo De Bruijn

| Construção | Sintaxe                         |
| ---------- | ------------------------------- |
| Variável   | `0`, `1`, `2`, …                |
| Abstração  | `\. t` ou `λ. t`                |
| Aplicação  | `t1 t2 t3` (associa à esquerda) |

---

## Exemplos

```
named> \x. x
  Input (named):    λx. x
  Input (De Bruijn): λ. 0
  Normal form (0 steps):
    Named:    λx. x
    De Bruijn: λ. 0

named> (\x. x) (\y. y)
  Input (named):    (λx. x) (λy. y)
  Input (De Bruijn): (λ. 0) (λ. 0)
  Normal form (1 step):
    Named:    λy. y
    De Bruijn: λ. 0

named> \f x. f (f x)
  Input (named):    λf. λx. f (f x)
  Normal form (0 steps):
    Named:    λf. λx. f (f x)
```

Numerais de Church:

```
named> \f x. f x          -- 1
named> \f x. f (f x)      -- 2
named> \f x. f (f (f x))  -- 3
```

Combinador ômega (atinge o limite de passos):

```
named> (\x. x x) (\x. x x)
```
