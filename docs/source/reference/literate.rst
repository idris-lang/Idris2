.. _ref-sect-literate:

**********************
Literate Programming
**********************

Idris2 supports several types of literate mode styles.

The unlit'n has been designed based such that we assume that we are parsing markdown-like languages
The unlit'n is performed by a Lexer that uses a provided literate style to recognise code blocks and code lines.
Anything else is ignored.

A literate style consists of:

+ a list of String encoded code block deliminators;
+ a list of line indicators; and
+ a list of valid file extensions.

Lexing is simple and greedy in that when consuming anything that is a code blocks we treat everything as code until we reach the closing deliminator.
This means that use of verbatim modes in a literate file will also be treated as active code.

In future we should add support for literate ``LaTeX`` files, and potentially other common document formats.
But more importantly, a more intelligent processing of literate documents using a pandoc like library in Idris such as: `Edda <https://github.com/jfdm/edda>` would also be welcome.

Bird Style Literate Files
=========================

Bird notation is a classic literate mode found in Haskell, (and Orwell) in which code lines begin with ``>``.
Other lines are treated as documentation.

We treat files with an extension of ``.lidr`` as bird style literate files.

Embedding in Markdown-like documents
====================================

While Bird Style literate mode is useful, it does not lend itself well
to more modern markdown-like notations such as Org-Mode and CommonMark.

Idris2 also provides support for recognising both 'visible' and 'invisible' code blocks and lines in both CommonMark and OrgMode documents.

OrgMode
*******

+ Org mode source blocks for idris are recognised as visible code blocks,
+ Comment blocks that begin with ``#+COMMENT: idris`` are treated as invisible code blocks.
+ Invisible code lines are denoted with ``#+IDRIS:``.

We treat files with an extension of ``.org`` as org-mode style literate files.

CommonMark
************

Only code blocks denoted by standard code blocks labelled as idris are recognised.

We treat files with an extension of ``.md`` and ``.markdown`` as org-mode style literate files.
