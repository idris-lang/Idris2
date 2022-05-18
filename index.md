<style>
.IdrisData {
  color: darkred
}
.IdrisType {
  color: blue
}
.IdrisBound {
  color: black
}
.IdrisFunction {
  color: darkgreen
}
.IdrisKeyword {
  text-decoration: underline;
}
.IdrisComment {
  color: #b22222
}
.IdrisNamespace {
  font-style: italic;
  color: black
}
.IdrisPostulate {
  font-weight: bold;
  color: red
}
.IdrisModule {
  font-style: italic;
  color: black
}
.IdrisCode {
  display: block;
  background-color: whitesmoke;
}
</style>
Welcome to Idris2!
==================

<style>
body {
  width: 80%;
  max-width: 700px;
  margin: auto;
}
code {
  background-color: whitesmoke;
}
pre code {
  display: block;
}
</style>

[Idris](https://www.idris-lang.org/) is a programming language designed to encourage
_Type-Driven Development_.

### Getting started

Once you have [installed Idris2](https://idris2.readthedocs.io/en/latest/tutorial/starting.html#getting-started)
you can write a simple hello-world by opening a `Main.idr` file and writing:

<code class="IdrisCode">
<span class="IdrisKeyword">module</span>&nbsp;<span class="IdrisModule">Main</span><br />
<br />
<span class="IdrisComment">|||&nbsp;My&nbsp;first&nbsp;Idris2&nbsp;function</span><br />
<span class="IdrisFunction">main</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">IO</span>&nbsp;<span class="IdrisType">()</span><br />
<span class="IdrisFunction">main</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">putStrLn</span>&nbsp;<span class="IdrisData">&quot;Hello,&nbsp;and&nbsp;welcome&nbsp;to&nbsp;Idris2!&quot;</span><br />
</code>

You can run this example by using the `--exec ENTRYPOINT` option.
The command `idris2 --exec main Main.idr` will compile the module and immediately run `main`.

The line starting with a triple pipe (`|||`) attaches documentation to the identifier. You
can consult it by loading the file in the REPL (`idris2 Main.idr`) and querying the compiler
using the `:doc` command: `:doc main` will return:

    Main.main : IO ()
      My first Idris2 function
      Visibility: private

You should be able to use `:doc` on identifiers (e.g. `main`, `IO`, `()`, `putStrLn`, etc.) and
keywords (`module`, `:`, `=`, `private`, etc.) and hopefully get helpful information.

### Libraries shipped with the compiler

Here are links to the automatically generated documentation for the libraries shipped with the
**bleeding edge** version of the compiler. The documentation for the latest **released** version
is available on the [idris-lang.org](https://www.idris-lang.org/pages/documentation.html) site.

#### [Prelude](https://idris-lang.github.io/Idris2/prelude)

The `prelude` is always implicitly loaded unless you use the `--no-prelude` command-line option.
This is where the built-in types are bound, where the core data types (`List`, `Nat`, `Equal`, etc.)
and interfaces (`Eq`, `Show`, `Functor`, etc.) are defined.

#### [Base](https://idris-lang.github.io/Idris2/base)

`base` contains all the basics needed to write small programs. Its modules can be used by adding
an `import` statement to the top of your file.
In [`Data.List`](https://idris-lang.github.io/Idris2/base/docs/Data.List.html) for instance you
will find functions to `take` or `drop` values from a list, or `partition` it using a given predicate.
You can explore the content of a namespace like `Data.List` by using `:browse Data.List` in the REPL.
For more information about specific entries, you can then use `:doc`.

#### [Contrib](https://idris-lang.github.io/Idris2/contrib)

The `contrib` library contains a bit of everything. It will eventually be disbanded in favour of
third-party packages once we have a convenient package manager. To use modules defined in it, you
can pass the `-p contrib` option to `idris2`.

#### [Linear](https://idris-lang.github.io/Idris2/linear)

`linear` is the add-on to `base` you'll need for programs using linearity. Similarly to `contrib`,
you will need to pass `-p linear` to `idris2` to use modules defined in it.

#### [Papers](https://idris-lang.github.io/Idris2/papers)

`papers` is not installed by default.
It contains complex examples that are lifted from academic papers using dependent typeds
and demonstrates advanced language features.

