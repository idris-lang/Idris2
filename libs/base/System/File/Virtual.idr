module System.File.Virtual

import System.File.Support
import public System.File.Types

%default total

%foreign support "idris2_stdin"
         "node:lambda:x=>({fd:0, buffer: Buffer.alloc(0), name:'<stdin>', eof: false})"
prim__stdin : FilePtr

%foreign support "idris2_stdout"
         "node:lambda:x=>({fd:1, buffer: Buffer.alloc(0), name:'<stdout>', eof: false})"
prim__stdout : FilePtr

%foreign support "idris2_stderr"
         "node:lambda:x=>({fd:2, buffer: Buffer.alloc(0), name:'<stderr>', eof: false})"
prim__stderr : FilePtr

export
stdin : File
stdin = FHandle prim__stdin

export
stdout : File
stdout = FHandle prim__stdout

export
stderr : File
stderr = FHandle prim__stderr
