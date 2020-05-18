To build and install from Idris 2 in Idris 1:

* Change the `prefix` which is currently hard coded in `Idris.Main`
* `make all && make install`

Then, to build from the newly installed `idris2sh`

* make clean
* `make all IDRIS_BOOT=idris2sh && make install`

For amusement, try using `time` on the above. I get about 3m for installing
from `idris2`, and about 1m45 for installing from `idris2sh`.
