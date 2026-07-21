# Basic Lean Setup for Linux <!-- omit in toc -->

## Table of Contents <!-- omit in toc -->
- [Prerequisites](#prerequisites)
- [Install Elan](#install-elan)
- [Create a new Lean project for math](#create-a-new-lean-project-for-math)
- [Install the Lean 4 Extension for VS Code](#install-the-lean-4-extension-for-vs-code)
- [Cleanup](#cleanup)

## Prerequisites
The setup steps are exemplified for **Ubuntu** with links for **other OSs**. 
1. **Update**: For Ubuntu, press `Ctrl + Alt + T` and run 
    ```bash
    sudo apt update && sudo apt upgrade
    ```
2. **Git**: For other OSs, see [https://git-scm.com/install/windows](https://git-scm.com/install/windows)
   ```bash
    sudo apt install git
    git config --global user.name "Your Full Name" 
    git config --global user.email "your.email@example.com"
    ```
3. **Curl**: Should already be available [https://curl.se](https://curl.se)
    ```bash
    sudo apt install curl
    ```
4. **VS Code**: **SKIP this step IF** you are in Windows using **WSL**. For other OSs, see [code.visualstudio.com/docs/setup/linux](https://code.visualstudio.com/docs/setup/linux)
    ```bash
    sudo snap install --classic code
    ```
    Recent versions of VS Code heavily promote Microsoft's AI tools on the initial welcome screen. It often prompts you to "Enable AI features" or sign up for GitHub Copilot. **You can completely ignore or dismiss this**; Lean 4 does not require AI tools to function.

## Install Elan
In the Lean ecosystem, `elan` is the official version manager for Lean toolchains. For the different OSs, the installation guide is [https://lean-lang.org/install/manual/](https://lean-lang.org/install/manual/).
1. For Ubuntu, press `Ctrl + Alt + T` and run 
    ```bash
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
    ```
    The script will pause and ask you to choose an installation option. Press Enter to select the default option (1).
2. **Refresh** your shell: This ensures your shell updates the PATH variable to include `~/.elan/env`.
   ```bash
    source ~/.elan/env
    ```
3. **Verify** the installation: 
    ```bash
    elan --version
    ```

## Create a new Lean project for math
The official documentation for creating Lean projects is [https://leanprover-community.github.io/install/project.html](https://leanprover-community.github.io/install/project.html).
1. Create a dedicated folder for your project and let lake handle the setup:
    ```bash
    mkdir -p ~/workspace/lean
    cd ~/workspace/lean
    lake new my_project math
    ```
    This will set up the project structure and download the `mathlib` source code. 
    
    The very first time you run this command, you may see a few "warning: could not canonicalize path" messages followed by a large download. This is completely normal! Elan is simply downloading the toolchain.
2. When creating a new project, it is a good habit to run:
    ```bash
    cd my_project
    lake update
    lake exe cache get
    lake build
    ```
    This will update your project's dependencies to their latest compatible versions and download the precompiled mathlib binaries for the project. In this case, since we ran `lake new my_project math`, it should report that no files need to be downloaded.
3. **Verify** the installation: continue with the next step.

## Install the Lean 4 Extension for VS Code
This extension is the most popular way of interacting with Lean. The official webpage for this extension is [https://marketplace.visualstudio.com/items?itemName=leanprover.lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

1. **IF** you reached this point from the **WSL** guide, return in order to connect VS Code to WSL: click [WSL Setup (Continue)](basic_setup_linux.md#basic-lean-setup).


2. **ELSE**, open the newly created project:
    ```Bash
    cd ~/workspace/lean/my_project
    code .
    ```
    In the lower left corner of VS Code, you may see a status bar button saying **Restricted Mode**. Click on it and select **Trust**.
3. Press `Ctrl + Shift + X` to open the Extensions marketplace and type `lean 4` in the search bar.
4. Click **Install** on the official extension (published by `leanprover`)
5. **Verify** the installation: click on `MyProject/Basic.lean` and the `Lean InfoView` should appear and show no errors. Press `Ctrl + Shift + Enter` to toggle the InfoView panel on or off.


## Cleanup
1. To completely remove Elan and its associated Lean toolchains, you can use Elan's built-in uninstallation command.
    ```bash
    elan self uninstall
    ```
    This should remove `~/.elan` (where the binaries and toolchains are stored). If the folder persists, remove it manually:
    ```
    rm -rf ~/.elan
    ```
2. Check `~/.bashrc` and delete any lines that contain `export PATH="$HOME/.elan/bin:$PATH"`.
3. Remove the user cache:
    ```
    rm -rf ~/.cache/mathlib
    ```
    You can also delete the `.lake` folders inside any of your local Lean projects to drop their compiled build artifacts.