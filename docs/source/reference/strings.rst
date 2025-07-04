String literals in Idris
========================

To facilitate the use of string literals, idris provides three features
in addition to plain string literals: multiline strings, raw strings and interpolated
strings.

Plain string literals
---------------------

String literals behave the way you expect from other programming language. Use quotation marks
``"`` around the piece of text that you want to use as a string:

``"hello world"``

As explained in :doc:`overloadedlit`, string literals can be overloaded to return a type different than string.

Multiline string literals
--------------------------

In some cases you will have to display a large string literal that spans multiple lines. For this you
can use *multiline string literals*, they allow you to span a string across multiple vertical
lines, preserving the line returns and the indentation. Additionally they allow you to indent your
multiline string with the surrounding code, without breaking the intended format of the string.

To use multiline strings, start with a triple quote ``"""`` followed by a line return, then
enter your text and close it with another triple quote ``"""`` with whitespace on its left.
The indentation of the closing triple quote will determine how much whitespace should be cropped
from each line of the text.

.. note::

   Multiline strings use triple quotes to enable the automatic cropping of leading whitespace
   when the multiline block is indented.


.. code-block:: idris

    welcome : String
    welcome = """
        Welcome to Idris 2

        We hope you enjoy your stay
          This line will remain indented with 2 spaces
        This line has no intendation
        """

printing the variable `welcome` will result in the following text:

::

    Welcome to Idris 2

    We hope you enjoy your stay
      This line will remain indented with 2 spaces
    This line has no intendation

As you can see, each line has been stripped of its leading 4 space, that is because the closing
delimiter was indented with 4 spaces.

In order to use multiline string literals, remember the following:

- The starting delimited must be followed by a line return
- The ending delimiter's intendation level must not exceed the indentation of any line

Raw string literals
-------------------

It is not uncommon to write string literals that require some amount of escaping. For plain string
literals the characters ``\\`` and ``"`` must be escaped, for multiline strings the characters
``"""`` must be escaped. Raw string literals allow you to dynamically change the required
escaped
sequence in order to avoid having to escape those very common sets of characters. For this, use
``#"`` as starting delimiter and ``"#`` as closing delimiter. The number of ``#`` symbols can be
increased in order to accommodate for edge cases where ``"#`` would be a valid symbol.
In the following example we are able to match on ``\{`` by using half as many ``\\`` characters
as if we didn't use raw string literals:

.. code-block:: idris

    myRegex : Regex
    myRegex = parseRegex #"\\{"#

If you need to escape characters you still can by using a ``\\`` followed by the same number of
``#`` that you used for your string delimiters. In the following example we are using two
``#`` characters as our escape sequence and want to print a line return:

.. code-block::

    markdownExample : String
    markdownExample = ##"markdown titles look like this: \##n"# Title \##n body""##

This last example could be implemented by combining raw string literals with multiline strings:

.. code-block::

    markdownExample : String
    markdownExample = ##"""
        markdown titles look like this:
        "# Title
        body"
        """##

Interpolated strings
--------------------

Concatenating string literals with runtime values happens all the time, but sprinkling our code
with lots of ``"`` and ``++`` symbols sometimes hurts legibility which in turn can introduce bugs
that are hard to detect for human eyes. Interpolated strings allow to inline the execution of
programs that evaluate to strings with a string literals in order to avoid manually writing out
the concatenation of those expressions. To use interpolated strings, use ``\{`` to start an
interpolation slice in which you can write an idris expression. Close it with ``}``

.. code-block::

    print : Expr -> String
    print (Var name expr) = "let \{name} = \{print expr}"
    print (Lam arg body) = #"\\#{arg} => \#{print body}"#
    print (Decl fname fargs body) = """
        func \{fname}(\{commasep fargs}) {
            \{unlines (map print body)}
        }
        """
    print (Multi lns) = #"""
        """
        \#{unlines lns}
        """
        """#

As you can see in the second line, raw string literals and interpolated strings can be combined.
The starting and closing delimiters indicate how many ``#`` must be used as escape sequence in the
string, since interpolated strings require the first ``{`` to be escaped, an interpolated slice
in a raw string uses ``\#{`` as starting delimiter.

Additionally multiline strings can also be combined with string interpolation in the way you
expect, as shown with the ``Decl`` pattern. Finally all three features can be combined together in the
last branch of the example, where a multiline string has a custom escape sequence and includes an
interpolated slice.

Interpolation Interface
-----------------------

The Prelude exposes an ``Interpolation`` interface with one function ``interpolate``. This function
is used within every interpolation slice to convert an arbitrary expression into a string that can
be concatenated with the rest of the interpolated string.

To go into more details, when you write ``"hello \{username}"`` the compiler translates the expression
into ``concat [interpolate "hello ", interpolate username]`` so that the concatenation is fast and so that if
``username`` implement the ``Interpolation`` interface, you don't have to convert it to a string manually.

Here is an example where we reuse the ``Expr``
type but instead of implementing a ``print`` function we implement ``Interpolation``:

.. code-block::

  Interpolation Expr where
      interpolate (Var name expr) = "let \{name} = \{expr}"
      interpolate (Lam arg body) = #"\\#{arg} => \#{body}"#
      interpolate (Decl fname fargs body) = """
          func \{fname}(\{commasep fargs}) {
              \{unlines (map interpolate body)}
          }
          """
      interpolate (Multi lns) = #"""
          """
          \#{unlines lns}
          """
          """#

As you can see we avoid repeated calls to ``print`` since the slices are automatically applied to
``interpolate``.

We use ``Interpolation`` instead of ``Show`` for interpolation slices because the semantics of ``show``
are not necessarily the same as ``interpolate``. Typically the implementation of ``show`` for ``String``
adds double quotes around the text, but for ``interpolate`` what we want is to return the string as is.
In the previous example, ``"hello \{username}"``, if we were to use ``show`` we would end up with the string
``"hello "Susan""`` which displays an extra pair of double quotes. That is why the implementation of
``interpolate`` for ``String`` is the identity function: ``interpolate x = x``. This way the desugared
code looks like: ``concat [id "hello ", interpolate username]``.
