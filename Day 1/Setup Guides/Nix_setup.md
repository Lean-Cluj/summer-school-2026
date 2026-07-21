# Setting up Nix Package Manager <!-- omit in toc -->

The multi-user installation is the standard for Linux environments. Official instructions can be found here [https://nixos.org/download/](https://nixos.org/download/).

1. Run the official installation script:
    ```bash
    curl --proto '=https' --tlsv1.2 -L https://nixos.org/nix/install | sh -s -- --daemon --yes
    ```
    The script may ask for your confirmation at a few steps and will require your `sudo` password.
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
    Aeneas and modern Lean/Rust environments heavily utilize Nix "flakes". You need to explicitly enable this feature.
5. **Highlight**: By default, the activation of the Nix shell is not highlighted. To have a visual indication, do this:
    ```bash
    cd ~
    echo 'bash-prompt-prefix = (nix)\040' >> ~/.config/nix/nix.conf
    ```

## Continue the guide with:
* [Lean Blueprint Installation](Lean_Blueprint_via_Nix.md)
* [Aeneas Installation](Aeneas_via_Nix.md)


## Cleanup
Because you installed Nix using the `--daemon` flag, it set itself up as a background system service, created isolated build users, and installed files at the system root.
1. Stop and disable the Nix daemon
    ```bash
    sudo systemctl stop nix-daemon.socket
    sudo systemctl stop nix-daemon.service
    sudo systemctl disable nix-daemon.socket
    sudo systemctl disable nix-daemon.service
    sudo systemctl daemon-reload
    ```
2. Delete the system directories
    ```bash
    sudo rm -rf /nix
    sudo rm -rf /etc/nix
    sudo rm -rf /etc/profile.d/nix.sh 
    sudo rm -rf /etc/profile.d/nix-daemon.sh
    ```
3. Clean your user configuration
    ```bash
    rm -rf ~/.config/nix 
    rm -rf ~/.nix-profile 
    rm -rf ~/.nix-defexpr 
    rm -rf ~/.nix-channels
    rm -rf ~/.cache/nix
    ```
4. Clean your shell environment
    ```bash
    code ~/.bashrc
    ```
    Find and delete the block added in step 5.
    ```
    # Add an indicator when inside a Nix shell
    if [ -n "$IN_NIX_SHELL" ]; then
      export PS1="(nix) $PS1"
    fi
    ```
    Save the file, close the editor, and refresh your shell:
    ```bash
    source ~/.bashrc
    ```