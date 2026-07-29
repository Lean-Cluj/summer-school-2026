# WSL Setup <!-- omit in toc -->
## Table of Contents <!-- omit in toc -->
- [Requirements](#requirements)
- [Install WSL (with Ubuntu)](#install-wsl-with-ubuntu)
- [Basic Lean Setup](#basic-lean-setup)
- [Connect VS Code to WSL](#connect-vs-code-to-wsl)
- [Cleanup](#cleanup)

## Requirements
* **Windows 10 or 11**
* **16 GB RAM** (absolute minimum)
* **VS Code** (see [Basic Setup](basic_setup_windows.md)). In fact, it is recommended to complete the basic Windows setup first.
* **Make sure Windows is up to date:** Installing WSL may require a system reboot. 
  1. Press `Win + I` to open **Settings**.
  2. Select **Windows Update** from the left sidebar.
  3. Click **Check for updates**.
  4. Install any available updates.
  5. Restart and repeat these steps until no more required updates are available.

## Install WSL (with Ubuntu)
1. Click the Windows Start menu and type `powershell`.
2. Right-click **Windows PowerShell** and select **Run as administrator**.
3. In the prompt, type the following command and press Enter: 
    ```powershell
    wsl --install -d Ubuntu
    ```
    Wait for the process to finish. This command enables the necessary Virtual Machine Platform, downloads the Linux kernel, and installs Ubuntu.
4. **Reboot**: If you are installing virtualization tools for the first time, you will be prompted to reboot the system in order to finalize the virtualization setup.
5. **If you rebooted**: Do steps 1, 2, and 3 again.
6. **Create your Unix user account:** The terminal will prompt you to create a Unix username and a password. The password characters will be completely invisible as you type—this is normal Linux behavior.
7. **Verify** the installation: Once you see the green command prompt (e.g., `username@hostname:~$`), verify everything is running correctly by checking the Linux release details:
    ```bash
    cat /etc/os-release
    ```
    You should see output confirming you are running Ubuntu.
8. **Test network access and update:** Run a quick package manager update to ensure your new Linux environment is securely connected to the internet and up to date:
    ```bash
    sudo apt update && sudo apt upgrade -y
    ```

## Basic Lean Setup
1. Open your WSL Ubuntu shell:
    * either by clicking the Windows Start menu, typing `ubuntu` and selecting the app, or
    * by pressing `Win + R`, typing `wt wsl ~`, and hitting Enter.
2. Follow the steps in [Basic setup for Linux](basic_setup_linux.md)

## Connect VS Code to WSL
Ensure that your VS Code Windows UI and your Linux file system are working together smoothly:
1. Open VS Code **on Windows**: Press `Win + R`, type `powershell`, and hit Enter. **Run** the following commands:
    ```powershell
    cd ~
    code .
    ```
2. Go to the Extensions tab (`Ctrl+Shift+X`) and search for **WSL** (published by Microsoft). **Install** it and **close** VS Code.
3. Go back to your Ubuntu terminal and type:
    ```bash
    cd ~/workspace/lean/my_project
    code . 
    ```
    This command will trigger VS Code to install its lightweight server backend inside WSL and then open the folder. Look at the very bottom-left corner of your VS Code window—it should display a blue status bar button saying **WSL: Ubuntu**. 
4. In the lower left corner of VS Code, you may also see a status bar button saying **Restricted Mode**. Click on it and select **Trust**.
5. Go to the Extensions tab (`Ctrl+Shift+X`) and search for **Lean 4** (published by leanprover).
   
   Because VS Code detects that you are in a remote session, the install button will specifically say **Install in WSL: Ubuntu**. Click that button. 
6. **Verify** the installation: Click on `MyProject/Basic.lean` and the `Lean InfoView` should appear and show no errors. Press `Ctrl + Shift + Enter` to toggle the InfoView panel on or off.

## Uninstall WSL
1. Click the Windows Start menu and type `powershell`.
2. Right-click **Windows PowerShell** and select **Run as administrator**.
3. Unregister and wipe the Ubuntu distribution: This step instantly and permanently deletes all files, packages, and configurations inside your Ubuntu environment.
    ```powershell
    wsl --unregister Ubuntu
    ```
4. Remove the Ubuntu Store application package: Even after unregistering the distro, Windows keeps the app launcher package.
    ```powershell
    Get-AppxPackage *Ubuntu* | Remove-AppxPackage
    ```
5. Uninstall the WSL framework: To strip the WSL core software and Linux kernel from Windows entirely, run:
    ```powershell
    wsl --uninstall
    ```
6. Disable the Windows optional features (optional, requires restart): If you want to ensure the underlying virtualization components are completely turned off in Windows, run:
    ```powershell
    Disable-WindowsOptionalFeature -Online -FeatureName Microsoft-Windows-Subsystem-Linux, VirtualMachinePlatform
    ```
7. Remove the global WSL configuration file: If you created a `.wslconfig` file to cap memory or CPU usage for the Lean environment, uninstalling WSL does not remove it. You may delete it with:
    ```powershell
    Remove-Item -Force ~\.wslconfig
    ```
8. Clean up residual AppData folders: `Remove-AppxPackage` often leaves behind residual log files and an empty directory structure in the hidden Windows AppData folder.
    * Open File Explorer (`Win + E`)
    * Click directly inside the address bar and paste `%localappdata%\Packages`
    * Delete the folder with a name starting with `CanonicalGroupLimited.Ubuntu`.