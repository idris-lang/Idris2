# Idris 2

[![Documentation Status](https://readthedocs.org/projects/idris2/badge/?version=latest)](https://idris2.readthedocs.io/en/latest/?badge=latest)
[![Build Status](https://github.com/idris-lang/Idris2/actions/workflows/ci-idris2-and-libs.yml/badge.svg?branch=main)](https://github.com/idris-lang/Idris2/actions/workflows/ci-idris2-and-libs.yml?query=branch%3Amain)

[Idris 2](https://idris-lang.org/) is a purely functional programming language
with first class types.

For installation instructions, see [INSTALL.md](INSTALL.md).

The [wiki](https://github.com/idris-lang/Idris2/wiki) lists a number of useful
resources, in particular

+ [What's changed since Idris 1](https://idris2.readthedocs.io/en/latest/updates/updates.html)
+ [Resources for learning Idris](https://github.com/idris-lang/Idris2/wiki/Resources),
  including [official talks](https://github.com/idris-lang/Idris2/wiki/Resources#official-talks)
  that showcase its capabilities
+ [Editor support](https://github.com/idris-lang/Idris2/wiki/Editor-Support)

## Installation and Packages

The most common way to install the latest version of Idris and its packages is through [`pack`][PACK] Idris' package manager. Working with the latest version of Idris is as easy as `pack switch latest`.
Follow instructions [on the `pack` repo][PACK] for how to install `pack`.

To use `pack` and idris, you will need an `.ipkg` file (Idris-package file) that describes your idris project. You can generate one with `idris2 --init`. Once setup with an `.ipkg` file, `pack` gives you access to the [_pack collection_][PACK_COL] of packages, a set of compatible libraries in the ecosystem. If your dependency is in the `depends` field of your `.ipkg` file, `pack` will automatically pull the dependency from you matching pack collection.

The wiki hosts a list of [curated packages by the community](https://github.com/idris-lang/Idris2/wiki/Third-party-Libraries).

## Things still missing

+ Cumulativity (currently `Type : Type`. Bear that in mind when you think
  you've proved something)
+ `rewrite` doesn't yet work on dependent types

## Contributions wanted

If you want to learn more about Idris, contributing to the compiler could be
one way to do so. The [contribution guidelines](CONTRIBUTING.md) outline
the process. Having read that, choose a [good first issue][1] or have a look at
the [contributions wanted][2] for something more involved. This [map][3] should
help you find your way around the source code. See [the wiki page][4]
for more details.

[1]: <https://github.com/idris-lang/Idris2/issues?q=is%3Aopen+is%3Aissue+label%3A%22good+first+issue%22>
[2]: <https://github.com/idris-lang/Idris2/wiki/What-Contributions-are-Needed>
[3]: <https://github.com/idris-lang/Idris2/wiki/Map-of-the-Source-Code>
[4]: <https://github.com/idris-lang/Idris2/wiki/Getting-Started-with-Compiler-Development>
[PACK]: https://github.com/stefan-hoeck/idris2-pack
[PACK_COL]: https://github.com/stefan-hoeck/idris2-pack-db