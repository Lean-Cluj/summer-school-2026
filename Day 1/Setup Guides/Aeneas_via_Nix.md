# Setting up the Aeneas verification toolchain via Nix <!-- omit in toc -->

## Table of Contents <!-- omit in toc -->
- [Install Aeneas](#install-aeneas)
- [Using Aeneas](#using-aeneas)
  - [Create a Test Rust Project](#create-a-test-rust-project)
  - [Translate from Rust to Lean](#translate-from-rust-to-lean)
  - [Integrate the Generated Lean 4 Code](#integrate-the-generated-lean-4-code)
- [Uninstall Aeneas](#uninstall-aeneas)

## Install Aeneas
The official installation instructions can be found here: [https://github.com/AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas). Nix handles downloading and configuring Cargo, rustc, and Charon.

1. If you haven't done so already, follow: [Nix Installation](Nix_setup.md)
2. **Clone** the repository into your home folder:
    ```bash
    cd ~
    git clone https://github.com/AeneasVerif/aeneas.git
    cd aeneas
    ```

3. **Set up Dependencies via Nix**: Initialize the Nix development environment. This single command will download and compile the exact versions of Rust, OCaml, and other required packages:
    ```bash
    nix develop
    ```
    This first run will take quite a bit of time—potentially around 30 minutes, depending on your internet connection and hardware—as it fetches the entire Rust and OCaml toolchains into `/nix/store`.

4. **Verify**: Once `nix develop` finishes, your terminal prompt will change slightly. You are now inside an isolated Nix shell where `rustc`, `cargo`, and Aeneas are all available and correctly configured, without placing them on your default `PATH`. If you followed [Nix Setup](Nix_setup.md), you will see "(nix)" in front of your prompt. You can also check:
    ```bash
    which rustc
    which cargo
    ```
5. **Set Up Charon**: Aeneas requires a specific version of the Charon repository. This command automatically clones the exact, compatible version into a local subfolder.
    ```bash
    make setup-charon
    ```
6. **Build** the Aeneas project:
    ```bash
    make
    ```
7. **Add to PATH**: Run this command to make `charon` and `aeneas` available outside the Nix shell. Note: if you later run `nix-collect-garbage`, these paths may break and you will need to rebuild.
    ```bash
    echo 'export PATH="$HOME/aeneas/bin:$HOME/aeneas/charon/bin:$PATH"' >> ~/.bashrc
    source ~/.bashrc
    ```
8. **Verify** the installation:
    ```bash
    charon --help
    aeneas -version
    ```
## Using Aeneas
### Create a Test Rust Project


1. **Rust**: The Nix shell provided `rustc` and `cargo` for building Aeneas, but for your own Rust projects, you need a host-level Rust installation. Install it via [rustup](https://rustup.rs/) if you have not already, then set the default toolchain:
    ```bash
    rustup default stable
    ```
2. Initialize a **new Rust crate**:
    ```bash
    mkdir -p ~/workspace/rust
    cd ~/workspace/rust
    cargo new simple_math --lib
    ```
3. **Open** the newly created project:
    ```bash
    cd simple_math
    code src/lib.rs
    ```
4. **Replace** the default code with a simple function that we want to verify in Lean:
    ```rust
    pub fn double_number(x: u32) -> u32 {
        x + x
    }
    ```
5. **Save** the file.

### Translate from Rust to Lean

Aeneas cannot read raw Rust code directly. We first use `charon` to compile the Rust code into a simplified Intermediate Representation called LLBC (Low-Level Borrow Calculus).
1. Make sure you are inside your project directory:
    ```bash
    cd ~/workspace/rust/simple_math
    ```
2. **Run Charon** to generate the intermediate code for Aeneas:
    ```bash
    charon cargo --preset=aeneas
    ```
    This hooks into the Rust compiler and generates a file named `simple_math.llbc`, typically located right in your project folder.

3. **Run the Aeneas translator**, instructing it to use the Lean backend, and specify the destination folder so the code lands directly in your configured Lean project:
    ```bash
    aeneas -backend lean simple_math.llbc -dest ~/workspace/lean/my_project/
    ```
    If everything is configured correctly, Aeneas will output `SimpleMath.lean`.

### Integrate the Generated Lean 4 Code
To work with the generated `SimpleMath.lean`, we need to add it to a Lean project.
1. Navigate to your Lean project and open VS Code:
    ```bash
    cd ~/workspace/lean/my_project/MyProject
    code .
    ```
2. Open the configuration file `lakefile.toml` and add one of the following dependency blocks:

    **Option A (Local Path):**
    ```toml
    [[require]]
    name = "aeneas"
    path = "../../../aeneas/backends/lean"
    ```
    **Option B (Standalone GitHub - Best for sharing):**
    ```toml
    [[require]]
    name = "aeneas"
    git = "https://github.com/AeneasVerif/aeneas.git"
    subDir = "backends/lean"
    rev = "main" # (Or a specific commit hash)
    ```
3. **Align Toolchain Version:** Make sure that the `lean-toolchain` file in your newly created project declares the exact Lean version that Aeneas is using, so they can work together.
    Check the Aeneas version:
    ```bash
    cat ~/aeneas/backends/lean/lean-toolchain 
    ```
    **Modify** your `lean-toolchain` file in `my_project` to match that version perfectly (e.g., `leanprover/lean4:v4.31.0`).
    **Modify** your `lakefile.toml` such that the `[[require]] name = "mathlib"` block 
    * is at the **end of the file**, and
    * has the **same mathlib version as Aeneas**.

4. **DO NOT run** `lake update`; it may pull a newer Mathlib that requires a different Lean toolchain, breaking compatibility with Aeneas.
5. Download the precompiled mathlib binaries and build:
    ```bash
    lake exe cache get
    lake build
    ```
6. Open the result:
    ```bash
    code MyProject/SimpleMath.lean
    ```
    You will see your imperative Rust `double_number` function translated into a Lean definition using the `Result` monad. You can now start writing proofs about this code.

## Uninstall Aeneas
1. Since we compiled Aeneas in this folder, all the files are inside this folder.
    ```bash
    rm -rf ~/aeneas
    ```
2. Clean `~/.bashrc` by removing the line `export PATH="$HOME/aeneas/bin:$HOME/aeneas/charon/bin:$PATH"`:
    ```bash
    cd ~
    code .bashrc
    source ~/.bashrc
    ```
3. Clean the Nix Store:
    ```bash
    nix-collect-garbage
    ```