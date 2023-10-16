# Protocol Verification course assignments

These are the assignments for COMP SCI 839 (Protocol Verification), taught at
UW-Madison in Fall 2023 by [Tej Chajed](https://www.chajed.io/).

## Chapters

The exercises in each chapter are surrounded by `// FIXME` and `// END`; you're
not supposed to modify text outside these markers. When you're done we suggest
you change `FIXME` to `DONE`, but this isn't required.

- **Chapter 0**: Making sure your IDE is set up for Dafny (see installation
  instructions below).
- **Chapter 1**: Learn some fundamental Dafny syntax and concepts.

## Installation

These assignments will have you defining and verifying protocols in Dafny, a
verification-aware programming language.

We highly recommend using [VS Code](https://code.visualstudio.com/). Dafny is
an interactive tool, and the VS Code extension makes it easy to use it
interactively. If you're used to vim keybindings, the [vim
extension](https://marketplace.visualstudio.com/items?itemName=vscodevim.vim)
is quite good.

Install the [Dafny
extension](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode).
From within VS Code you can do this by clicking on the Extensions icon in the
left side bar and searching for `dafny-lang.ide-vscode`. If you're more
familiar with the command line, `code --install-extension
dafny-lang.ide-vscode` will also work.

You'll need to install .NET 6 and the ASP.NET Core Runtime to run Dafny (you
won't need to interact with these tools except for installing them). If you
don't have them, the Dafny extension will tell you. The simplest way to do this
is to install the SDK from
<https://dotnet.microsoft.com/en-us/download/dotnet/6.0>.

On macOS, you can instead use `brew install dotnet@6` and then in VS Code set
the option "Dafny: Dotnet Executable Path" to the output of `echo $(brew
--prefix dotnet@6)/bin/dotnet`.

## Learning Dafny

If you get stuck on something Dafny related, you might find what you need in a
[syntax tutorial](https://github.com/tchajed/dafny-syntax-tutorial) I wrote, or
you can check out the Dafny [getting started
guide](https://dafny.org/latest/OnlineTutorial/guide).

I recorded a [Dafny debugging
video](https://www.youtube.com/watch?v=3BkF-1B35y4) of the "toy consensus"
example ([code here](demos/ch04/toy_consensus.dfy)) that illustrates how to
come up with an inductive invariant and debug an inductiveness proof.
