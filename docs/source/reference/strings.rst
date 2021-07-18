String literals in Idris
===============

Strings are ubiquitous in programming, they allow the programmer to ingest data, display it and communicate information in a format that's legible to humans.

To facilitate the use of string in daily programming, idris provides feature to make them easier to read and easier to understand. Those features are multi-line strings, raw strings and interpolated strings. Let us start with plain string literals.

Plain string literals
---------------------

String literals behave the way you expect from other programming language. Use quotation marks `"` around the piece of text that you want to use as a string:

``"hello world"``

As explained in :doc:`overloadedlit`, string literals can be overloaded to return a type different than string. 

Multi-line string literals
--------------------------

In some cases you will have to display a large string literal that span multiple lines. For this you can use _multi-line string literals_, they
allow you to span your string across multiple vertical lines, preserving the line returns and the indentation. Additionally they allow you to indent your multi-line string with the surrounding code, without breaking the intended format of the string. 

To use multi-line strings, start with a triple quote `"""` followed by a line return, then enter your text and close it with another triple quote `"""`. The indentation of the closing triple quote will determine how much whitespace should be cropped from each line of the text.

``
welcome : String
welcome = """
    Welcome to Idris 2
    
    We hope you enjoy your stay
      This line will remain indented with 2 spaces
    """
``

printing the variable `welcome` will result in the following text:

``
Welcome to Idris 2
    
We hope you enjoy your stay
  This line will remain indented with 2 spaces
``

As you can see, each line has been stripped of its leading 4 space, that is because the closing delimiter was indented with 4 spaces.

In order to use multi-line string literals, remember the following:

- The starting delimited must be followed by a line return
- The ending delimiter's intendation level must not exceed the indentation of any line

Raw string literals
-------------------

It is not uncommon to write string literals that require some amount of escaping. For plain string literals the characters `\` and `"` must be escaped, for multi-line strings the characters `"""` must be escaped as well. Raw string literals allow you to dynamically change the required escaped sequence in order to avoid having to escape those very common sets of characters. For this use `#"` as starting delimiter and `"#` as closing delimiter. The number of `#` symbols can be increased in order to accomodate for edge cases where `"#` would be a valid symbol. In the following example we are able to match on `\{` by using half as many `\` characters as if we didn't use raw string literals:

``
myRegex : Regex
myRegex = parseRegex #"\\{"#
``

If you need to escape characters you still can by using a `\` followed by the same number of `#` that you used for your string delimiters. In the following example we are using two `#` characters as our escape sequence and want to print a line return:

``
markdownExample : String
markdownExample = ##"markdown titles look like this: \##n"# Title \##n body""##
```

This last example could be implemented by combining raw string literals with multi-line strings:

``
markdownExample : String
markdownExample = ##"""
    markdown titles look like this:
    "# Title
    body"
    """##
``

Interpolated strings
--------------------

Concatenating string literals with runtime values happens all the time, but sprinking our code with lots of `"` and `++` symbols sometimes hurts legibility which in turn can introduce bugs that are hard to detect for human eyes. Interpolated strings allow to inline the execution of programs that evaluate to strings with a string literals in order to avoid manually writing out the concatenation of those expressions. To use interpolated strings, use `\{` to start an interpolation slice in which you can write an idris expression. Close it with `}`

``
print : Expr
print (Var name expr) = "let \{name} = \{print expr}"
print (Lam arg body) = #"\\#{arg} => \#{print body}"#
print (Decl fname fargs body) = """
    func \{fname}(\{commasep fargs}) {
        \{lines (map print body)}
    }
    """
print (Multi lns) = #"""
    """
    \#{lines lns}
    """
    """#
``

As you can see in the second line, raw string literals and interpolated strings can be combined. The starting and closing delimiters indicate how many `#` must be used as escape sequence in the string, since interpolated strings require the first `{` to be escaped, an interpolated slice in a raw string uses `\#{` as starting delimiter.
Additionally multi-line strings can also be combined with string interpolation in the way you expect, as shown with `Decl`. Finally all three features can be combined together in the last example.