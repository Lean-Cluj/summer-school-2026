

1. Make sure you have The nix package manager installed as indicated in [Nix Setup](../../Day%201/Setup%20Guides/Nix_setup.md)

## Example crates
Navigate to inside one of the Rust Project folders

```bash
cd "Day 4/Aeneas: Bridging Rust to Lean/rust_workspace/add_ten/"
```
Convert the `lib/src.rs` file to 
```bash
charon cargo --preset=aeneas
```

## Create new Rust crate

---
2. Open the Nix shell
```bash
    nix develop
```

# !!! atentie .. flake-ul asta instaleaza Aeneas dar a fost deja instalat


1. run 
> nix develop
this gives error: experimental Nix feature 'nix-command' is disabled; add '--extra-experimental-features nix-command' to enable it
nix --extra-experimental-features "nix-command flakes" develop

2. test
> which charon
If it outputs a path starting with /nix/store/..., the environment is active and working perfectly.

3. charon cargo is designed to analyze an entire Rust project (a "crate"), not standalone .rs files.
> cargo init --lib

When you want to translate a new Rust file, navigate to your rust_crate directory within your Nix shell and run the two-step translation:
Extract to LLBC:
> charon cargo --preset=aeneas
Translate to Lean:
> aeneas -backend lean crate_name.llbc  
or
> aeneas -backend lean rust_crate.llbc -dest ../lean_proofs/MyProofs/
This outputs a .lean file containing the pure functional model of your Rust code. 

4. move files 
> mv RustCrate.lean ../lean_proofs/

4. Initialize the Lean Project
> lake init MyProofs math
> lake new MyProject math

5. make Aeneas aware of your Lean environment. In your lakefile.lean, add aeneas as a dependency. You can point this dependency directly to the backends/lean directory of the Aeneas GitHub repository.
5.1 Configure lakefile.toml, (add this BEFORE the 'require mathlib')

[[require]]
name = "aeneas"
git = "https://github.com/AeneasVerif/aeneas.git"
rev = "main"
subDir = "backends/lean"

5.2 Remove the Manual Mathlib Dependency

>
lake clean
lake update ----> when you update, lake will tell you if there is a mismatch between the project version of Mathlib and the version that Aeneas requires
lake exe cache get
lake build

6. For several examples use this setup: you should convert your rust_crate directory into a Cargo Workspace
my_verification_project/
├── lean_proofs/
└── rust_crate/
    ├── Cargo.toml        # The workspace manager
    ├── add_ten/
    │   ├── Cargo.toml    # Sub-crate config
    │   └── src/lib.rs    # Put the add_ten code here
    ├── enums/
    │   ├── Cargo.toml
    │   └── src/lib.rs    # Put the enum code here
    └── mut_borrows/
        ├── Cargo.toml
        └── src/lib.rs    # Put the mutable borrow code here 
        
Ini, TOML

[workspace]
members = [
    "add_ten",
    "enums",
    "mut_borrows"
]

cargo new --lib add_ten
cargo new --lib enums
cargo new --lib mut_borrows

OR
cargo init --lib add_ten
cargo init --lib enums
cargo init --lib mut_borrows

cd rust_crate/add_ten

charon cargo --preset=aeneas

aeneas -backend lean add_ten.llbc -dest ../lean_proofs/MyProofs/
aeneas -backend lean ../add_ten.llbc -dest ../../lean_proofs/MyProofs/


7. When running
nix --extra-experimental-features "nix-command flakes" develop
nix will try to reproduce / backup the entire project including all artefacts
to avoid copying all the files in a nix repository
you want to tell nix to track only certain files
nix can do this if you have a git project,
nix will track the files added to the project, so it will ignore the files mentioned in .gitignore

remove all git folders from lean_proofs and rust_workspace
make one git repository in the top directory
then
>
git add .
nix --extra-experimental-features "nix-command flakes" develop

