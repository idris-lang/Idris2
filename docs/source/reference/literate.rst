.. _ref-sect-literate:

**********************
Literate Programming
**********************

Idris2 supports several types of literate mode styles.

The unlit'n has been designed based such that we assume that we are parsing markdown-like languages
The unlit'n is performed by a Lexer that uses a provided literate style to recognise code blocks and code lines.
Anything else is ignored.
Idris2 also provides support for recognising both 'visible' and 'invisible' code blocks using 'native features' of each literate style.

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

We treat files with an extension of ``.lidr`` as bird style literate files.

Bird notation is a classic literate mode found in Haskell, (and Orwell) in which visible code lines begin with ``>`` and hidden lines with ``<``.
Other lines are treated as documentation.



.. note::
   We have diverged from ``lhs2tex`` in which ``<`` is traditionally used to display inactive code.
   Bird-style is presented as is, and we recommended use of the other styles for much more comprehensive literate mode.

Embedding in Markdown-like documents
====================================

While Bird Style literate mode is useful, it does not lend itself well
to more modern markdown-like notations such as Org-Mode and CommonMark.
Idris2 also provides support for recognising both 'visible' and 'invisible'
code blocks and lines in both CommonMark and OrgMode documents using native code blocks and lines..

The idea being is that:

1. **Visible** content will be kept in the pretty printer's output;
2. **Invisible** content will be removed; and
3. **Specifications** will be displayed *as is* and not touched by the compiler.

OrgMode
*******

We treat files with an extension of ``.org`` as org-style literate files.
Each of the following markup is recognised regardless of case:

+ Org mode source blocks for idris sans options are recognised as visible code blocks::

    #+begin_src idris
    data Nat = Z | S Nat
    #+end_src

+ Comment blocks that begin with ``#+BEGIN_COMMENT idris`` are treated as invisible code blocks::

    #+begin_comment idris
    data Nat = Z | S Nat
    #+end_comment

+ Visible code lines, and specifications, are not supported. Invisible code lines are denoted with ``#+IDRIS:``::

    #+IDRIS: data Nat = Z | S Nat

+ Specifications can be given using OrgModes plain source or example blocks::

    #+begin_src
    map : (f : a -> b)
       -> List a
       -> List b
    map f _ = Nil
    #+end_src

CommonMark
**********

We treat files with an extension of ``.md`` and ``.markdown`` as CommonMark style literate files.

+ CommonMark source blocks for idris sans options are recognised as visible code blocks::

    ```idris
    data Nat = Z | S Nat
    ```

    ~~~idris
    data Nat = Z | S Nat
    ~~~

+ Comment blocks of the form ``<!-- idris\n ... \n -->`` are treated as invisible code blocks::

    <!-- idris
    data Nat = Z | S Nat
    -->

+ Code lines are not supported.

+ Specifications can be given using CommonMark's pre-formatted blocks (indented by four spaces) or unlabelled code blocks.::

    Compare

    ```idris
    map : (f : a -> b)
       -> List a
       -> List b
    map f _ = Nil
    ```

    with

        map : (f : a -> b)
           -> List a
           -> List b
        map f _ = Nil

LaTeX
*****

We treat files with an extension of ``.tex`` and ``.ltx`` as LaTeX style literate files.

+ We treat environments named ``code`` as visible code blocks::

    \begin{code}
    data Nat = Z | S Nat
    \end{code}


+ We treat environments named ``hidden`` as invisible code blocks::

    \begin{hidden}
    data Nat = Z | S Nat
    \end{hidden}

+ Code lines are not supported.

+ Specifications can be given using user defined environments.

We do not provide definitions for these code blocks and ask the user to define them.
With one such example using ``fancyverbatim`` and ``comment`` packages as::

    \usepackage{fancyvrb}
    \DefineVerbatimEnvironment
      {code}{Verbatim}
      {}

    \usepackage{comment}

    \excludecomment{hidden}
