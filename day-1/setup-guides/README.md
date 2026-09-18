# Lean Setup <!-- omit in toc -->
## Table of Contents <!-- omit in toc -->
- [Basic Setup](#basic-setup)
- [Full Setup](#full-setup)
  - [Nix Package Manager](#nix-package-manager)
  - [Lean Blueprint](#lean-blueprint)
  - [Aeneas](#aeneas)

These guides were tested on **Ubuntu** and **Windows**, and are provided as is, with no guarantee that they work on every machine or version. Each guide links to the official documentation, which takes precedence if something does not match your system.

## Basic Setup
Installs Lean (via `elan`), VS Code with the Lean 4 extension, and a Lean project with Mathlib. This is enough for most of the examples in the summer school and is the required starting point.

* [Basic setup for Ubuntu](basic_setup_linux.md)
* [Basic setup for Windows](basic_setup_windows.md)
* On **macOS and other Linux distros**, follow the Ubuntu guide and adjust using the linked references where needed.

## Full Setup
Adds the Nix package manager, Lean Blueprint, and the Aeneas toolchain, so you can run the complete workflows (writing blueprints, verifying Rust code). It extends the basic setup rather than replacing it.

Complete the guides in this order:

1. [Basic setup](#basic-setup) — on Windows, first install **WSL with Ubuntu** ([WSL setup](wsl_setup.md)), then follow the Ubuntu guide inside WSL.
2. [Nix setup](nix_setup.md)
3. [Lean Blueprint](lean_blueprint_via_nix.md) and/or [Aeneas](aeneas_via_nix.md) — independent of each other, install either or both.

*Requires at least 16 GB of RAM.* The guides were tested on **Ubuntu** (native and under WSL); on **macOS and other Linux distros** they should work with minor adjustments, using the linked references.

---

### Nix Package Manager
Nix is a cross-platform package manager for Unix-like systems and a functional language to configure those systems
(see [https://nixos.org/](https://nixos.org/)).

**Guide:** [Nix Setup](nix_setup.md)

---

### Lean Blueprint
Lean Blueprint is a plasTeX plugin that allows you to write blueprints for Lean 4 projects
(see [https://github.com/PatrickMassot/leanblueprint](https://github.com/PatrickMassot/leanblueprint)).

**Guide:** [Lean Blueprint Setup](lean_blueprint_via_nix.md)

---

### Aeneas
Aeneas is a verification toolchain for Rust programs. It relies on a translation from Rust's MIR internal language to pure lambda calculus. It is intended to be used in combination with Charon, which compiles Rust programs to an intermediate representation called LLBC
(see [https://github.com/AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas)).

**Guide:** [Aeneas Setup](aeneas_via_nix.md)

---