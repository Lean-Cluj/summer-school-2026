# Lean Setup <!-- omit in toc -->
## Table of Contents <!-- omit in toc -->
- [Basic Setup](#basic-setup)
- [Full Setup](#full-setup)
  - [Nix Package Manager](#nix-package-manager)
  - [Lean Blueprint](#lean-blueprint)
  - [Aeneas](#aeneas)

## Basic Setup
For a light installation which allows you to work with all the examples in the summer school, here are some tested guides:

* [Basic setup for Ubuntu](basic_setup_linux.md)
* [Basic setup for Windows](basic_setup_windows.md)
* For **macOS and other Linux distros**, follow [Basic setup for Ubuntu](basic_setup_linux.md) and use the references to make any adjustments if needed.

## Full Setup
If you want to have control of the full workflows, you need to install Lean Blueprint and Aeneas. You can do this by following the official installation instructions or the guides below.

* The guides below were tested on **Ubuntu**, but should work fine on other distros.
* For **Windows** users, we suggest you install **WSL with Ubuntu** by following the steps here: [WSL setup](wsl_setup.md). Then, you can follow this guide for installing Lean Blueprint and Aeneas.
*This configuration requires an absolute minimum of 16 GB RAM.*

* For **macOS and other Linux distros**, follow the guides below and use the references to make any adjustments if needed.

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