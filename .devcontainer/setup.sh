#!/bin/zsh
set -e

# Change ownership of bind mounts
sudo chown -Rv $(id -u):$(id -g) ~/.claude

# Copy shell configuration
cp .devcontainer/config/.zshrc ~/.zshrc
source ~/.zshrc
mkdir -p ~/.config
cp .devcontainer/config/starship.toml ~/.config/starship.toml

# Install elan (the Lean version manager) non-interactively.
# --no-modify-path: we put elan on PATH ourselves (below) instead of letting
# the installer edit shell profiles, keeping the copied ~/.zshrc predictable.
# Elan reads ./lean-toolchain and fetches the pinned Lean on demand; we
# pre-install it here so the editor is ready immediately on first open.
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain none
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.zshrc
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(cat lean-toolchain)"

# Install Claude Code CLI
curl -fsSL https://claude.ai/install.sh | bash

# Configure Claude Code
mkdir -p ~/.claude
cat > ~/.claude/settings.json <<'EOF'
{
  "permissions": {
    "defaultMode": "bypassPermissions"
  },
  "env": {
    "CLAUDE_CODE_DISABLE_FEEDBACK_SURVEY": "1",
    "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC": "1",
    "CLAUDE_CODE_DISABLE_OFFICIAL_MARKETPLACE_AUTOINSTALL": "1",
    "CLAUDE_CODE_ENABLE_TELEMETRY": "0",
    "DISABLE_ERROR_REPORTING": "1",
    "DISABLE_FEEDBACK_COMMAND": "1",
    "DISABLE_TELEMETRY": "1",
    "ENABLE_CLAUDEAI_MCP_SERVERS": "false"
  },
  "disableRemoteControl": true,
  "skipWebFetchPreflight": true
}
EOF
