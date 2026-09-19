# Setting up the Lean Blueprint via Nix <!-- omit in toc -->

## Table of Contents <!-- omit in toc -->
- [Prerequisites](#prerequisites)
- [Install Lean Blueprint](#install-lean-blueprint)
- [Using Lean Blueprint](#using-lean-blueprint)
  - [Building the blueprint](#building-the-blueprint)
  - [Viewing the blueprint](#viewing-the-blueprint)
- [Uninstall Lean Blueprint](#uninstall-lean-blueprint)


## Prerequisites
The guide is for **Ubuntu** (possibly via WSL) and assumes the following:
1. [WSL setup](WSL_setup.md) (if you are on a Windows machine)
2. [Basic setup for Linux](basic_setup_linux.md)
3. [Nix setup](Nix_setup.md)

## Install Lean Blueprint
Lean Blueprint is installed per project. As an example, we will use `my_project`, created in a previous step.

1. **Navigate** to the root folder of the project
    ```bash
    cd ~/workspace/lean/my_project
    ```
2. **Create** the Flake Configuration: Make sure you are in the project root, then create a new file named exactly `flake.nix`:
    ```bash
    code flake.nix
    ``` 
    and paste the following code into it:
    ```nix
    {
      description = "Lean Blueprint Development Environment";

      inputs = {
        nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
      };

      outputs = { self, nixpkgs }:
        let
          # Support for Linux and macOS (Intel & Apple Silicon)
          supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
          forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
          pkgsFor = system: import nixpkgs { inherit system; };
        in
        {
          devShells = forAllSystems (system:
            let
              pkgs = pkgsFor system;
            in
            {
              default = pkgs.mkShell {
                packages = with pkgs; [
                  python3Packages.leanblueprint
                  graphviz
                  texliveFull  # ~4–5 GB download; see guide notes for smaller alternatives
                ];
                
                shellHook = ''
                  echo "📘 Welcome to the Lean Blueprint environment!"
                  echo "Run 'leanblueprint new' to initialize your blueprint."
                '';
              };
            }
          );
        };
    }
    ```
3. **Activate** the Nix Shell:
    ```bash
    git add -N flake.nix
    nix develop
    ```
    Nix Flakes enforce a strict reproducibility rule: they will completely ignore any file in the repository that is not tracked by Git.

    The first time you run this, it may take a minute or two to download the required packages. Once finished, you should see the welcome message letting you know the blueprint tools are ready.

4. **Commit** the project: The `leanblueprint` tool enforces strict version control hygiene. It checks your repository status and aborts if it detects any uncommitted work.
    ```bash
    git add .
    git commit -m "Initial commit"
    ```
5. **Initialize** the blueprint: 
    ```bash
    leanblueprint new
    ```
    This is an interactive script. It will ask you a few setup questions (like your project name and author details). Hit **Enter** to choose the defaults and **Y** for everything else. It handles all the boilerplate by creating a `blueprint/` folder containing the necessary `.tex` files.

## Using Lean Blueprint
Whenever you add new formalized theorems to your Lean code or update your LaTeX (`.tex`) files, you will need to regenerate the blueprint to see the changes.

### Building the blueprint
1. In `lakefile.toml`, move the `[[require]] name = "mathlib"` block to the end of the file. Lake processes dependencies in order; placing Mathlib last prevents it from overriding settings from other dependencies.
2. The blueprint needs to verify your Lean declarations, so your code must compile successfully.
    ```bash
    lake update
    lake exe cache get
    lake build
    ```

3. Build the web version of the blueprint:
    ```bash
    leanblueprint web
    ```
    Note that `leanblueprint` is only available inside the Nix shell. If you followed the [Nix Setup](nix_setup.md), you should see "(nix)" in front of your prompt. If you don't, activate the Nix shell again with `nix develop`.
4. Build the PDF version of the blueprint:
    ```bash
    leanblueprint pdf
    ```

### Viewing the blueprint
1. For the **web version**: Serve the site locally to view the graph:
    ```bash
    leanblueprint serve
    ```
    This will spin up a local server. Open your web browser and navigate to `http://localhost:8000` to explore your project's blueprint.

    To see the Dependency Graph, navigate to `http://localhost:8000/dep_graph_document.html`.

2. The **PDF version** is, by default, `blueprint/print/print.pdf`.

    If you are running **WSL**, you can open the folder containing `print.pdf` with the following commands:
    ```bash
    # exit nix shell
    exit
    # go to the pdf
    cd blueprint/print/
    # open the Windows file browser
    explorer.exe .
    ```

## Uninstall Lean Blueprint
Lean Blueprint is installed per project. So, the only system cleanup that you may want to do is to clean the Nix store:
  ```bash
  # move to project root folder if needed
  cd ~/workspace/lean/my_project
  # exit the Nix shell if it is active
  exit
  # remove the Nix flake configuration files
  rm flake.nix flake.lock
  # let nix remove all packages which are no longer used
  nix-collect-garbage
  ```
Then, all other files which you may want to remove are in the project folder, e.g., the subfolder `blueprint/`. 