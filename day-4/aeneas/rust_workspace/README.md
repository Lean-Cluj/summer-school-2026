# Rust crates

The workspace contains seven library crates. Each crate consists of a file
`src/lib.rs` with one or two public Rust functions and their unit tests. Five
crates have a Lean file with specifications and proofs, listed in the order of
the session. The crates `enums` and `affine_cipher` have no Lean file.

| Crate | Rust source | Lean file |
| :--- | :--- | :--- |
| `add_ten` | [add ten](add_ten/src/lib.rs) | [`AddTen_verified.lean`](../lean_proofs/Proofs/AddTen_verified.lean) |
| `error_codes` | [error codes](error_codes/src/lib.rs) | [`ErrorCodes_verified.lean`](../lean_proofs/Proofs/ErrorCodes_verified.lean) |
| `mersenne31` | [Mersenne31 field arithmetic](mersenne31/src/lib.rs) | [`Mersenne31_verified.lean`](../lean_proofs/Proofs/Mersenne31_verified.lean) |
| `max_array` | [max in array](max_array/src/lib.rs) | [`MaxArray_verified.lean`](../lean_proofs/Proofs/MaxArray_verified.lean) |
| `xor_cipher` | [XOR cipher](xor_cipher/src/lib.rs) | [`XorCipher_verified.lean`](../lean_proofs/Proofs/XorCipher_verified.lean) |
| `enums` | [enums](enums/src/lib.rs) | — |
| `affine_cipher` | [affine cipher](affine_cipher/src/lib.rs) | — |

## Translating a crate to Lean

The steps below use the installation of Charon and Aeneas for this course,
which is built with the Nix package manager, installed as described in
[Nix Setup](../../../day-1/setup-guides/nix_setup.md). Charon can also be built
without Nix, with `rustup` and `make`, as described in its repository. The
steps use the crate `add_ten` as the example.

1. **Enter the Nix environment.** The Charon of this installation runs inside
   the Nix environment in which it was built. The environment provides the
   required libraries and the nightly Rust toolchain.
    ```bash
    nix develop ~/aeneas
    ```

2. **Run the unit tests.** Go to the Rust workspace and run the tests of all
   crates:
    ```bash
    cd "day-4/aeneas/rust_workspace/"
    cargo test --workspace --lib
    ```

3. **Translate the Rust code to LLBC with Charon.** Inside the Nix
   environment, Charon translates the code in `src/lib.rs` into LLBC
   (Low-Level Borrow Calculus). Run the command below in the folder of the
   crate, here `add_ten/`. Since the crate is part of a workspace, the output
   file `add_ten.llbc` is created in the workspace folder `rust_workspace/`.
    ```bash
    charon cargo --preset=aeneas
    ```

4. **Translate LLBC to Lean with Aeneas.** In the folder `rust_workspace/`,
   where the file `add_ten.llbc` was created, run Aeneas with the Lean backend.
   The option `-dest` sets the folder for the generated Lean file.
    ```bash
    aeneas -backend lean add_ten.llbc -dest ../lean_proofs/Proofs/
    ```
   The generated file `AddTen.lean` contains the definitions only. The file
   `AddTen_verified.lean` contains the same definitions, followed by the
   specifications and proofs.

5. **Open the Lean project in VS Code.** Open the folder `lean_proofs/`
   itself, with `code .`. The Lean 4 extension finds the Lake project of an
   open file by searching upwards from the file for a `lean-toolchain` file;
   opening the root of the project is the simplest way to make sure that it
   uses the toolchain and the dependencies of this project.
    ```bash
    cd ../lean_proofs/
    code .
    ```
