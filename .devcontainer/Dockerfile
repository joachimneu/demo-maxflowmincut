FROM ubuntu:24.04

# No interactive prompts during apt installs (tzdata otherwise hangs the build)
ARG DEBIAN_FRONTEND=noninteractive

# Update, upgrade, and install development tools
RUN apt-get update
RUN apt-get dist-upgrade -y
RUN apt-get autoremove -y --purge
RUN apt-get install -y sudo openssh-client zsh git
RUN apt-get install -y curl wget file
RUN apt-get install -y build-essential git-delta nano ripgrep
RUN apt-get install -y python3-dev

# Use the non-root user provided by the base image (Claude Code refuses bypassPermissions as root)
RUN echo "ubuntu ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers.d/ubuntu
RUN usermod -s /usr/bin/zsh ubuntu

# Install starship
RUN curl -sS https://starship.rs/install.sh | sh -s -- --yes

USER ubuntu
