# Dockerfile — Haskell development environment
# Mirrors the flake.nix devShell: GHC, Cabal, HLS, linters, formatters, Pandoc

FROM haskell:9.6-slim AS base

# ── System dependencies (pkg-config, zlib, zlib-dev) ────────────────────────
RUN apt-get update && apt-get install -y --no-install-recommends \
        pkg-config \
        zlib1g \
        zlib1g-dev \
        curl \
        git \
    && rm -rf /var/lib/apt/lists/*

# ── Pandoc ──────────────────────────────────────────────────────────────────
RUN cabal update \
    && apt-get update && apt-get install -y --no-install-recommends pandoc \
    && rm -rf /var/lib/apt/lists/*

# ── Haskell tooling via cabal ───────────────────────────────────────────────
# GHC and cabal-install are already provided by the base image.
# Install the remaining tools globally.
RUN cabal install --install-method=copy --installdir=/usr/local/bin \
        fourmolu \
        hlint \
        hoogle \
        ghcid \
        cabal-fmt

# ── Haskell Language Server ─────────────────────────────────────────────────
# Install GHCup, then use it to install the matching HLS version.
ENV GHCUP_INSTALL_BASE_PREFIX=/usr/local
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org \
    | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 \
      BOOTSTRAP_HASKELL_INSTALL_HLS=1 \
      BOOTSTRAP_HASKELL_MINIMAL=1 \
      sh \
    && ln -sf /root/.ghcup/bin/haskell-language-server-wrapper /usr/local/bin/haskell-language-server-wrapper

# ── Hoogle database (optional but handy) ───────────────────────────────────
RUN hoogle generate

# ── Runtime config ──────────────────────────────────────────────────────────
ENV LD_LIBRARY_PATH=/usr/lib/x86_64-linux-gnu

WORKDIR /workspace
CMD ["bash"]
