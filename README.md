# Idris 2

[![Documentation Status](https://readthedocs.org/projects/idris2/badge/?version=latest)](https://idris2.readthedocs.io/en/latest/?badge=latest)
[![Build Status](https://github.com/idris-lang/Idris2/actions/workflows/ci-idris2-and-libs.yml/badge.svg?branch=main)](https://github.com/idris-lang/Idris2/actions/workflows/ci-idris2-and-libs.yml?query=branch%3Amain)

[Idris 2](https://idris-lang.org/) is a purely functional programming language
with first class types.

For installation instructions, see [INSTALL.md](INSTALL.md).

The [wiki](https://github.com/idris-lang/Idris2/wiki) lists a number of useful resources, in particular

+ [What's changed since Idris 1](https://idris2.readthedocs.io/en/latest/updates/updates.html)
+ [Resources for learning Idris](https://github.com/idris-lang/Idris2/wiki/Resources), including [videos](https://github.com/idris-lang/Idris2/wiki/Resources#official-talks) that showcase its capabilities
+ [Editor support](https://github.com/idris-lang/Idris2/wiki/Editor-Support)

## Things still missing

+ Cumulativity (currently `Type : Type`. Bear that in mind when you think you've proved something)
+ `rewrite` doesn't yet work on dependent types

## Contributions wanted

If you want to learn more about Idris, contributing to the compiler could be one way to do so. The [contribution guidelines](CONTRIBUTING.md) outline the process. Having read that, choose a [good first issue][1] or have a look at the [contributions wanted][2] for something more involved. This [map][3] should help you find your way around the source code. See [the wiki page][4] for more details.

[1]: <https://github.com/idris-lang/Idris2/issues?q=is%3Aopen+is%3Aissue+label%3A%22good+first+issue%22>
[2]: <https://github.com/idris-lang/Idris2/wiki/What-Contributions-are-Needed>
[3]: <https://github.com/idris-lang/Idris2/wiki/Map-of-the-Source-Code>
[4]: <https://github.com/idris-lang/Idris2/wiki/Getting-Started-with-Compiler-Development>
