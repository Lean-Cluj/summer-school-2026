# Example crates

Make sure you have the Nix package manager installed as indicated in [Nix Setup](../../Day%201/Setup%20Guides/Nix_setup.md). The next steps guide you in running the provided examples.

1. **Navigate to the Rust project folder** (adjust the path if needed):
    ```bash
    cd "Day 4/Aeneas examples/rust_workspace/add_ten/"
    ```

2. **Enter the Nix environment:** You need to run Charon from inside the Nix environment where it was built, which provides access to the correct libraries and the required nightly Rust toolchain.
    ```bash
    nix develop ~/aeneas
    ```

3. **Use Charon to convert `.rs` to `.llbc`:** Once inside the Nix shell, convert the code in `src/lib.rs` to LLBC (Low-Level Borrow Calculus). Because this is part of a workspace, the output file `add_ten.llbc` is created in the parent folder, `rust_workspace`.
    ```bash
    charon cargo --preset=aeneas
    ```

4. **Use Aeneas to convert `.llbc` to `.lean`:** Move up one directory to where the `.llbc` file was created, and invoke Aeneas to translate it to Lean. Use the `-dest` flag to specify where the generated proofs should go.
    ```bash
    cd ..
    aeneas -backend lean add_ten.llbc -dest ../lean_proofs/MyProofs/
    ```

5. **Open in VS Code:** Navigate to the Lean workspace and open it. Opening the folder root (`code .`) is important because the Lean 4 extension requires the workspace root to initialize correctly and verify `AddTen.lean`.
    ```bash
    cd ../lean_proofs/
    code .
    ```
