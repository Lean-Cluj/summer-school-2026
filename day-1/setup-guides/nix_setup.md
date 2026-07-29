# Setting up Nix Package Manager <!-- omit in toc -->

The multi-user installation is the standard for Linux environments. Official instructions can be found here: [https://nixos.org/download/](https://nixos.org/download/).

1. Run the official installation script:
    ```bash
    curl --proto '=https' --tlsv1.2 -L https://nixos.org/nix/install | sh -s -- --daemon --yes
    ```
    The `--yes` flag accepts the defaults automatically. The script will still require your `sudo` password.
2. **Refresh** your shell: This ensures your shell updates the PATH variable.
    ```bash
    source /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
    ```
3. **Verify** the installation:
    ```bash
    nix --version
    ```
4. **Create** the Nix configuration directory and **enable flakes**:
    ```bash
    mkdir -p ~/.config/nix
    echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
    ```
    Many modern Nix-based projects, including those in this guide, use Nix flakes. You need to explicitly enable this feature.
5. **Shell Prompt Indicator**: By default, your bash prompt does not change when you enter a Nix development shell. To display a `(nix)` prefix so you can tell at a glance, add this setting:
    ```bash
    echo 'bash-prompt-prefix = (nix)\040' >> ~/.config/nix/nix.conf
    ```

## Continue the Guide With
* [Lean Blueprint Installation](Lean_Blueprint_via_Nix.md)
* [Aeneas Installation](Aeneas_via_Nix.md)


## Uninstall Nix
1. To uninstall Nix, follow the official instructions: [https://nix.dev/manual/nix/latest/installation/uninstall](https://nix.dev/manual/nix/latest/installation/uninstall)

2. In addition, remove local user state and Nix configuration with:
    ```bash
    rm -rf ~/.config/nix ~/.nix-profile ~/.nix-defexpr ~/.nix-channels ~/.cache/nix ~/.local/state/nix 
    ```

3. During installation, Nix creates a backup of your system-wide Bash configuration file. (Note: This guide assumes you are using Ubuntu, where this file is `/etc/bash.bashrc`). If you only installed Nix for the summer school and want to completely remove it, you should restore this backup.

    First, check that the only differences between the two files are the lines added by Nix:
    ```bash
    diff -u /etc/bash.bashrc /etc/bash.bashrc.backup-before-nix
    ```
    (You should only see lines containing "nix" being removed).

    Once you confirm the changes are safe, restore the original configuration by overwriting the current file with the backup:
    ```bash
    sudo mv /etc/bash.bashrc.backup-before-nix /etc/bash.bashrc
    ```