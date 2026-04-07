# BCC244 / PCC116 — Lógica aplicada à computação

Este repositório contém o material desenvolvido até o momento para a disciplina.

---

## Configuração do ambiente de desenvolvimento Haskell

### Opção 1 — Nix flakes

Requer [Nix](https://nixos.org/download) com flakes habilitado.

```bash
# Enter the dev shell (GHC, Cabal, HLS, Pandoc, formatters, linters)
nix develop

# Build all executables
cd haskell
cabal build all

# Run a specific executable
cabal run untyped
cabal run typed
cabal run proof-search
cabal run coc
```

Para habilitar flakes permanentemente, adicione a linha abaixo em
`~/.config/nix/nix.conf`:

```
experimental-features = nix-command flakes
```

### Opção 2 — Docker Compose

Requer [Docker](https://docs.docker.com/get-docker/) e
[Docker Compose](https://docs.docker.com/compose/).

```bash
# Compila e inicializa o container 
docker compose up -d

# Abre o shell com as ferramentas de desenvolvimento Haskell 
docker compose exec haskell-dev bash

# No shell do container:
cd haskell
cabal build all
cabal run untyped
```

The project directory is mounted at `/workspace` inside the container, so edits
made on the host are immediately visible.

To stop the container:

```bash
docker compose down
```

---

## Slides usados em sala

Slides são escritos em Markdown e compilados para html usando a biblioteca
[reveal.js](https://revealjs.com/) usando a ferramenta Pandoc.

```bash
# Build all slide decks
make all

# Build a specific deck
make slides/aula01/aula01.html
```

A ferramenta pandoc está disponível tanto no Nix quando no Docker.
