# Rust library crates examples

The selected examples are:
- [add ten](add_ten/src/lib.rs)
- [max in array](max_array/src/lib.rs)
- [enums](enums/src/lib.rs)
- [error codes](error_codes/src/lib.rs)
- [Mersenne31 field arithmetic](mersenne31/src/lib.rs)
- [affine cipher](affine_cipher/src/lib.rs)
- [XOR cipher](xor_cipher/src/lib.rs)

Make sure you have the Nix package manager installed as indicated in [Nix Setup](../../../day-1/setup-guides/nix_setup.md). The next steps guide you in running the provided examples.

1. **Enter the Nix environment:** You need to run Charon from inside the Nix environment where it was built, which provides access to the correct libraries and the required nightly Rust toolchain.
    ```bash
    nix develop ~/aeneas
    ```

2. **Navigate to the Rust project folder** and run the tests:
    ```bash
    cd "day-4/aeneas/rust_workspace/"
    cargo test --workspace --lib
    ```

3. **Use Charon to convert `.rs` to `.llbc`:** Once inside the Nix shell, convert the code in `src/lib.rs` to LLBC (Low-Level Borrow Calculus). Because this is part of a workspace, the output file `add_ten.llbc` is created in the parent folder, `rust_workspace`.
    ```bash
    charon cargo --preset=aeneas
    ```
    Note: if your run this in a libary create subfoler you will generate the `.llbc` file for that library crate (in the root folder).

4. **Use Aeneas to convert `.llbc` to `.lean`:** Move up one directory to where the `.llbc` file was created, and invoke Aeneas to translate it to Lean. Use the `-dest` flag to specify where the generated proofs should go. From `rust_workspace/` run
    ```bash
    aeneas -backend lean add_ten.llbc -dest ../lean_proofs/Proofs/
    ```

5. **Open in VS Code:** Navigate to the Lean workspace and open it. Opening the folder root (`code .`) is important because the Lean 4 extension requires the workspace root to initialize correctly and verify `AddTen.lean`.
    ```bash
    cd ../lean_proofs/
    code .
    ```
