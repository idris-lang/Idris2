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
Follow instructions [on the `pack` repository][PACK] for how to install `pack`.

To use `pack` and idris, you will need an `.ipkg` file (Idris-package file) that describes your idris project.
You can generate one with `idris2 --init`. Once setup with an `.ipkg` file, `pack` gives you access to the [_pack collection_][PACK_COL] of packages, a set of compatible libraries in the ecosystem.
If your dependency is in the `depends` field of your `.ipkg` file, `pack` will automatically pull the dependency from you matching pack collection.
The wiki hosts a list of [curated packages by the community](https://github.com/idris-lang/Idris2/wiki/Third-party-Libraries).

Finally, `pack` also makes it easy to download, and keep updated version of, [idris2-lsp](https://github.com/idris-community/idris2-lsp), and other idris-related programs.

## Resources to Learn Idris 2

### Books
- [_Type-Driven Development with Idris_](https://www.manning.com/books/type-driven-development-with-idris), Edwin brady. This was written for Idris1. If you are using Idris2, you should make [these changes](https://idris2.readthedocs.io/en/latest/typedd/typedd.html)
### Tutorials
- [_Functional Programming in Idris 2_](https://github.com/idris-community/idris2-tutorial)
- [_A Tutorial on Elaborator Reflection in Idris 2_](https://github.com/stefan-hoeck/idris2-elab-util/blob/main/src/Doc/Index.md), accompanied by [library utilities](https://github.com/stefan-hoeck/idris2-elab-util)
- [_An attempt at explaining Decidable Equality_](https://teh6.eu/en/post/intro-to-decidable-equality/)
### Official talks
- [_What's New in Idris 2_](https://www.youtube.com/watch?v=nbClauMCeds), Edwin Brady, Berlin Functional Programming Group
- [Scheme Workshop Keynote](https://www.youtube.com/watch?v=h9YAOaBWuIk), Edwin Brady, ACM SIGPLAN
- [_Idris 2 - Type-driven Development of Idris_](https://www.youtube.com/watch?v=DRq2NgeFcO0), Edwin Brady, Curry On! 2019
- [_Idris 2: Type-driven development of Idris_](https://www.youtube.com/watch?v=mOtKD7ml0NU), Edwin Brady, Code Mesh LDN 18
- [_The implementation of Idris 2_](https://www.youtube.com/playlist?list=PLmYPUe8PWHKqBRJfwBr4qga7WIs7r60Ql), Edwin Brady, SPLV'20 and [accompanying code](https://github.com/edwinb/SPLV20)
### Community talks
- [_Domain Driven Design Made Dependently Typed_](https://www.youtube.com/watch?v=QBj-4K-l-sg), Andor Penzes, Aug '21
- [_Extending RefC - Making Idris 2 backends while avoiding most of the work_](https://www.youtube.com/watch?v=i-_U6US3bBk), Robert Wright, Sept '21
- [_Introduction to JVM backend for Idris 2_](https://www.youtube.com/watch?v=kSIUsBQS3EE), Marimuthu Madasamy, Oct '21
- [_Idris Data Science Infrastructure - Because sometimes we have to consider the real world_](https://www.youtube.com/watch?v=4jDlYJf9_34),  Robert Wright, Dec '21

## Documentation

- [Official documentation](https://idris2.readthedocs.io/en/latest/index.html)
- Standard library online API reference
  - [official, latest](https://idris-lang.github.io/Idris2/)
  - [community](https://idris2docs.sinyax.net/)
- [Community API reference for selected packages](https://idris2-quickdocs.surge.sh)

## Docker images

- Multi-arch, multi-distro Docker [images](https://github.com/joshuanianji/idris-2-docker) for Idris 2
- Official [images](https://github.com/stefan-hoeck/idris2-pack/pkgs/container/idris2-pack) for the Pack package manager
- [alexhumphreys/idris2-dockerfile](https://github.com/alexhumphreys/idris2-dockerfile)
- [mattpolzin/idris-docker](https://github.com/mattpolzin/idris-docker)
- [dgellow/idris-docker-image](https://github.com/dgellow/idris-docker-image)

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
