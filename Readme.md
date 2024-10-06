## Contribution Guide

This repository uses [Verible](https://github.com/chipsalliance/verible) as a linter and formatter to maintain code quality.

### Getting Started

To contribute, you will need to install Verible. The recommended approach is to install the pre-built binary:

1. Navigate to the directory where you want to install Verible:
   ```bash
   cd "$DIR_YOU_WANT_INSTALL_VERIBLE"
   ```

2. Download the pre-built binary:
   ```bash
   wget https://github.com/chipsalliance/verible/releases/download/v0.0-3824-g14eed6a0/verible-v0.0-3824-g14eed6a0-linux-static-x86_64.tar.gz
   ```

3. Extract the downloaded file:
   ```bash
   tar -zxvf verible-v0.0-3824-g14eed6a0-linux-static-x86_64.tar.gz
   ```

4. Add Verible to your `PATH` by updating your `~/.bashrc` file:
   ```bash
   export PATH=$DIR_YOU_WANT_INSTALL_VERIBLE/verible-v0.0-3824-g14eed6a0/bin:$PATH
   ```

### Setting up Pre-commit Hooks

This project also uses `pre-commit` to enforce code standards. Follow these steps to set it up:

1. Install `pre-commit` using pip:
   ```bash
   pip install pre-commit
   ```

2. Clone the repository and navigate to the project directory:
   ```bash
   git clone https://github.com/fennecJ/formal_RV12
   cd formal_RV12
   ```

3. Install the pre-commit hooks:
   ```bash
   pre-commit install
   ```

Now you're ready to contribute!