# Installation

- [Installing with a package manager](#installing-with-a-package-manager)
- [Installing from source](#installing-from-source)
- [Installing Chez Scheme on Apple Silicon](#installing-chez-scheme-on-apple-silicon)

## Installing with a package manager

You can install Idris 2 with any one of a number of package managers.

### Installing with [Pack](https://github.com/stefan-hoeck/idris2-pack)
Pack comes with an installation of Idris 2, so you just need to install Pack.
See [the installation instructions](https://github.com/stefan-hoeck/idris2-pack/blob/main/INSTALL.md)
on GitHub.
### Installing with [Homebrew](https://brew.sh/)
```sh
brew install idris2
```
### Installing with [Nix](https://nixos.org/features.html)
```sh
nix-env -i idris2
```
### Installing with [Nix Flakes](https://nixos.wiki/wiki/Flakes)
```sh
nix profile install github:idris-lang/Idris2
```

## Installing from source

The easiest way to install from source is via the existing generated Scheme
code. The requirements are:

- A Scheme compiler; either Chez Scheme (default), or Racket.
- `bash`, `GNU make`, `gcc` or `clang`, `sha256sum` and `GMP`.  On Linux, you probably already
  have these.  On macOS and major BSD flavours, you can install them using a
  package manager: for instance, on macOS, you can install with the
  `brew install coreutils gmp` and on OpenBSD, with the `pkg_add coreutils
  bash gmake gmp` command. You specifically need the dev GMP library, which
  means on some systems the package you need to install will be named
  something more like `libgmp3-dev`. macOS ships with `clang` whereas `gcc` is
  more common for other \*nix distributions.

On Windows, it has been reported that installing via `MSYS2` works
[MSYS2](https://www.msys2.org/). On Windows older than Windows 8, you may need
to set an environment variable `OLD_WIN=1` or modify it in `config.mk`.

On Raspberry Pi, you can bootstrap via Racket.

By default, code generation is via Chez Scheme. You can use Racket instead,
by setting the environment variable `IDRIS2_CG=racket` before running `make`.
If you install Chez Scheme from source files, building it locally,
make sure you run `./configure --threads` to build multithreading support in.

**NOTE**: On FreeBSD, OpenBSD and NetBSD you need to use `gmake` command instead
of `make` in the following steps.

**NOTE**: If you're running macOS on Apple Silicon (arm64) you will need to
install the Racket fork of chez scheme as described below.  If you install gmp
via homebrew, you will also need to `export CPATH=/opt/homebrew/include`.

### 1: Set installation target directory

- Change the `PREFIX` in `config.mk` to the absolute path of your chosen
installation destination. The default is to install in `$HOME/.idris2`

If you have an existing Idris 2, go to Step 3. Otherwise, read on...

Make sure that:

- `$PREFIX/bin` is in your `PATH`

Further, on Apple silicon Macs (M1/M2), you need to set the following environment
variables:

``` sh
export IDRIS2_LIBS=/opt/homebrew/lib
export CPATH=/opt/homebrew/include:/opt/homebrew/lib
```

### 2: Installing without an existing Idris 2

You can build from pre-built Chez Scheme source, as long as you have Chez Scheme
installed (or, alternatively, Racket). To do this, enter one of the following:

- `make bootstrap SCHEME=chez`
- `make bootstrap-racket`

`chez` is the executable name of the Chez Scheme compiler. You may need to
replace this with the executable for Chez Scheme on your system. This could be
`scheme`, `chezscheme` or `chezscheme9.5` or something else, depending on your
system and the Chez Scheme version.

This builds an Idris 2 compiler from scheme code output from a working Idris 2
compiler (which isn't necessarily up to date, but is up to date enough to
build the current repository). It then rebuilds using the result, and runs
the tests.

If all is well, to install, type:

- `make install`

If you are building with Racket, you'll need to run `IDRIS2_CG=racket make install`.

### 3: Installing with an existing Idris 2

If you have the latest *released* version of Idris 2
(0.6.0 at the time of writing) installed:

- `make all`
- `make install`

### 4: (Optional) Installing Idris 2 library documentation

After `make install`, type `make install-libdocs` to install Idris 2 library documentation.  After
that, the index file can be found here: ``idris2 --libdir`/docs/index.html`.``

### 5: (Optional) Self-hosting step

As a final step, you can rebuild from the newly installed Idris 2 to verify
that everything has worked correctly. Assuming that `idris2` is in your
`PATH`.

- `make clean` -- to make sure you're building everything with the new version
- `make all && make install` -- OR
`make all IDRIS2_BOOT='idris2 --codegen racket' && make install`
if using Racket.

### 6: Running tests

After `make all`, type `make test` to check everything works. This uses the
executable in `./build/exec`.

### 7: (Optional) Enabling incremental compilation

If you are working on Idris, incremental compilation means that rebuilds are
much faster, at the cost of runtime performance being slower. To enable
incremental compilation for the Chez backend, set the environment variable
`IDRIS2_INC_CGS=chez`, or set the `--inc chez` flag in `idris2.ipkg`.

### 8: (Optional) Installing the Idris 2 API

You'll only need this if you're developing support tools, such as an external
code generator. To do so, once everything is successfully installed, type:

- `make install-api`

The API will only work if you've completed the self-hosting step (step 5), since
the intermediate code versions need to be consistent throughout. Otherwise, you
will get an `Error in TTC: TTC data is in an older format` error.

### 9: (Optional) Shell Auto-completion

Idris2 supports tab auto-completion for Bash-like shells.

#### For Bash Users

From within bash, run the following command:

```sh
eval "$(idris2 --bash-completion-script idris2)"
```

You can also add it to your `.bashrc` file.

#### For ZSH Users

From within ZSH, run the following commands:

```sh
autoload -U +X compinit && compinit
autoload -U +X bashcompinit && bashcompinit
eval "$(idris2 --bash-completion-script idris2)"
```

You can also add them to your `.zshrc` file.

### 10: Building on Windows Without an Existing Idris 2

As of January 2024, an installation workflow for Window 10 and Windows 11 goes like this:
Download and install Chez Scheme; you can get it from here: `https://github.com/cisco/ChezScheme/releases/tag/v9.6.4)`. In the Windows Command Shell, create a
junction like this:

```sh
mklink /j C:\Chez "<Chez Scheme install_dir>"
```

(You may replace `C:\Chez` with any other path as long as it does not contain any spaces.) Since the name
of Chez Scheme's  installation directory contains a version, here is a small script to copy into a `.cmd`
file, say `mkLink2Chez.cmd`, to get you future-proof:

```sh
@rd C:\Chez
@for /f "tokens=1 delims=:" %%i in ('dir "%ProgramFiles%\Chez*" /B /O-D') do @mklink /j C:\Chez  "%ProgramFiles%\%%i"
```

Running this file will delete an existing junction and create a new one. If Chez Scheme is not installed
it does nothing but display a file not found message. In case there are multiple versions it will use the
latest one. If the junction does not exist, it will display an error. Whenever you install a newer version
of Chez Scheme, you should run this command again.

Add `C:\Chez\bin\ta6nt` to the system path on your machine. (This does not need to be updated for new
versions of Chez Scheme). Also, add the variable `SCHEME` with the value `scheme` to your
machine's system environment; it will be used by the build process.

Next, you download MSYS2 from `https://www.msys2.org/`. After successful installation to a location whose
path does not contain spaces, uncomment `MSYS2_PATH_TYPE=inherit` in the file `mingw64.ini` which can be
found in the installation directory of MSYS2. This will allow the mingw executable to use the Windows system
path. Then, add `<MSYS2_install_dir>\ucrt64\bin` to your machine's system path (important). To complete the
MSYS2 installation, start the Mingw64 shell, enter `pacman -Syuu` and repeat this step until it yields
something like "there is nothing to do". Finally, enter `pacman -S make mingw-w64-ucrt-x86_64-gcc` to
install the required tools.

After completion, you are ready to build Idris 2. In the Mingw64 shell, change to the directory where you
unpacked the Idris 2 sources to. Then enter `make bootstrap && make install` which should create and install
the executable under `/home/<username>/.idris2`. This virtual directory corresponds to
`<MSYS2_install_dir>\home\<username>\.idris2\`. When all is done, don't delete the source directory or move
it elsewhere since it may be referenced by the Idris 2 compiler. Adding `<idris2_install_dir>\bin\` to your
machine's system path will allow you to directly call the Idris 2 repl from the Windows Command Shell, since
the file `idris2.cmd` has been added at this location by the build process.

### Troubleshooting

If you get the message `variable make-thread-parameter is not bound` while
bootstrapping via Chez Scheme, or while running the tests when bootstrapping via
Racket, then your copy of Chez Scheme was built without thread support. Pass
`--threads` to `./configure` while building Chez Scheme to correct the issue.

## Running in text editor

### Run on emacs using nix flakes

If you are a [nix flakes](https://nixos.wiki/wiki/Flakes) user you can run
Idris 2 in emacs by running the following command:

```sh
nix run github:idris-lang/Idris2#emacs-with-idris idrisCode.idr
```

## Installing Chez Scheme on Apple Silicon

The official version of chez scheme does not yet support Apple Silicon. So, on
macOS with Apple Silicon (e.g. M1 and M2 macs), you will need to build and install
the Racket fork of chez scheme.

```sh
git clone git@github.com:racket/ChezScheme.git
cd ChezScheme
git submodule init
git submodule update
./configure --pb
make tarm64osx.bootquick
./configure --threads
make
sudo make install
```
