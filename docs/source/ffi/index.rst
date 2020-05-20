**************************
Foreign Function Interface
**************************

.. note::

   The documentation for Idris has been published under the Creative
   Commons CC0 License. As such to the extent possible under law, *The
   Idris Community* has waived all copyright and related or neighboring
   rights to Documentation for Idris.

   More information concerning the CC0 can be found online at: http://creativecommons.org/publicdomain/zero/1.0/

Idris 2 is designed to support multiple code generators. The default target is
Chez Scheme, with Racket and Gambit code generators also supported. However, the
intention is, as with Idris 1, to support multiple targets on multiple platforms,
including e.g. JavaScript, JVM, .NET, and others yet to be invented.
This makes the design of a foreign function interface (FFI), which calls
functions in other languages, a little challenging, since ideally it will
support all possible targets!

To this end, the Idris 2 FFI aims to be flexible and adaptable, while still
supporting most common requirements without too much need for "glue" code in
the foreign language.

.. toctree::
   :maxdepth: 1

   ffi
   readline
