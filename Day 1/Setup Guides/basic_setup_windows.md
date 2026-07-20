# Basic Lean Setup for Windows <!-- omit in toc -->

## Table of Contents <!-- omit in toc -->
- [Prerequisites](#prerequisites)
  - [Install Git](#install-git)
  - [Install VS Code](#install-vs-code)
- [Install Elan](#install-elan)
- [Create a new Lean project for math](#create-a-new-lean-project-for-math)
- [Install the Lean 4 Extension for VS Code](#install-the-lean-4-extension-for-vs-code)
- [Cleanup](#cleanup)

## Prerequisites
### Install Git
Lean requires Git to automatically download Mathlib and other project dependencies. 
1. Open **PowerShell**: Press `Win + R`, type `powershell`, and hit Enter.
2. **Run** the following command:
    ```powershell
    winget install -e --id Git.Git --source winget --accept-package-agreements --accept-source-agreements
    ```
3. **Restart** PowerShell: Windows did not load the new Git path variables into your active session. Close your current PowerShell window and open a new one.
4. **Verify** the installation: In the new PowerShell window, run the following command:
    ```powershell
    git --version
    ```
### Install VS Code
VS Code is probably the most popular IDE for Lean.
1. Open **PowerShell**: Press `Win + R`, type `powershell`, and hit Enter.
2. **(Option 1) Run** the following command:
    ```powershell
    winget install -e --id Microsoft.VisualStudioCode --source winget --accept-package-agreements --accept-source-agreements
    ```
    By default, the winget installation will not add the "Open with Code" option to your Windows right-click menu.
3. **(Option 2) Run** the following command, if you want the "Open with Code" feature:
    ```powershell
    winget install -e --id Microsoft.VisualStudioCode --override '/VERYSILENT /SP- /MERGETASKS="addcontextmenufiles,addcontextmenufolders,associatewithfiles,addtopath"' --source winget --accept-package-agreements --accept-source-agreements
    ```
4. **Restart** PowerShell: The installation automatically adds the `code` command to your system `PATH`, but your currently open shell will not recognize it yet. Close your current PowerShell window and open a new one.
5. **Verify** the installation: Run the following command to open the current folder in VS Code.
    ```powershell
    code .
    ```
    Recent versions of VS Code heavily promote Microsoft's AI tools on the initial welcome screen. It often prompts you to "Enable AI features" or sign up for GitHub Copilot. **You can completely ignore or dismiss this**; Lean 4 does not require AI tools to function. 

## Install Elan
In the Lean ecosystem, `elan` is the official version manager for Lean toolchains.
1. Open **PowerShell**: Press `Win + R`, type `powershell`, and hit Enter.
2. **Run** the following commands:
    ```powershell
    cd ~
    curl.exe -O --location https://elan.lean-lang.org/elan-init.ps1
    powershell -ExecutionPolicy Bypass -f elan-init.ps1
    del elan-init.ps1
    ```
    The script will pause and ask you to choose an installation option. Press Enter to select the default option (1).
3. **Restart** PowerShell: This ensures your shell recognizes the newly added `%USERPROFILE%\.elan\bin` directory in your `PATH`.
4. **Verify** the installation: In the new PowerShell window, run the following command:
    ```powershell
    elan --version
    ```

## Create a new Lean project for math
The official documentation for creating Lean projects is [https://leanprover-community.github.io/install/project.html](https://leanprover-community.github.io/install/project.html).
1. Open **PowerShell**: Press `Win + R`, type `powershell`, and hit Enter.
2. **Run** the following commands:
    ```powershell
    cd ~
    mkdir .\workspace\lean
    cd .\workspace\lean
    lake new first_project math
    ```
    This will set up the project structure and download the `mathlib` source code. 
    
    The very first time you run this command, you may see a few "warning: could not canonicalize path" messages followed by a large download. This is completely normal! Elan is simply downloading the toolchain.
3. **Run** the following command:
    ```powershell
    cd first_project
    lake update
    lake exe cache get
    ```
    This will update your project's dependencies to their latest compatible versions and download the precompiled mathlib binaries for the project. In this case, since we ran `lake new first_project math`, it should report that no files need to be downloaded.
4. **Verify** the installation: continue with the next step.



## Install the Lean 4 Extension for VS Code
This extension is the most popular way of interacting with Lean. The official webpage for this extension is [https://marketplace.visualstudio.com/items?itemName=leanprover.lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
1. Open **PowerShell**: Press `Win + R`, type `powershell`, and hit Enter.
2. **Run** the following commands to open the project:
    ```powershell
    cd ~\workspace\lean\first_project
    code .
    ```
3. Press `Ctrl + Shift + X` to open the Extensions marketplace and type `lean 4` in the search bar.
4. Click **Install** on the official extension (published by `leanprover`). 
5. If asked about trust, click **Trust Workspace & Install**.
6. **Verify** the installation: Click on `FirstProject/Basic.lean` and the `Lean InfoView` should appear and show no errors. Press `Ctrl + Shift + Enter` to toggle the InfoView panel on or off.


## Cleanup
1. To completely remove Elan and its associated Lean toolchains, you can use Elan's built-in uninstallation command.
    ```bash
    elan self uninstall
    ```
    This should remove `~\.elan` (where the binaries and toolchains are stored). If the folder persists, remove it manually:
    ```
    Remove-Item -Recurse -Force ~\.elan
    ```
2. Clean the Environment PATH:
    * Press the Windows key, type Environment Variables, and select Edit the system environment variables (or Edit environment variables for your account).
    * Click the Environment Variables... button at the bottom.
    * In the top User variables section, select the Path variable and click Edit.
    * Select the entry ending in `.elan\bin` and click Delete, then click OK.
3. Remove the user cache:
    ```
    Remove-Item -Recurse -Force ~\.cache\mathlib
    ```
    You can also delete the `.lake` folders inside any of your local Lean projects to drop their compiled build artifacts.