import fs from "node:fs";
import tty from "node:tty";
// usually its not ok to import support file from support file (./support/js/Lib1.js from ./support/js/Lib2.js)
// why?
// bc maybe You dont do `import Lib1` in `Lib2.idr` - so ./support/js/Lib1.js will be never copied
//
// but here - ok, since runtime.js is always copied
import { truncInt32 } from "../js/runtime.js";

export const prim__fileSize = (fp) => fs.fstatSync(fp.fd).size;

export const prim__fileIsTTY = (fp) => Number(tty.isatty(fp.fd));

export function prim__filetime(file_ptr) {
  const { fd } = file_ptr;
  const st = fs.fstatSync(fd);
  const ft = {
    atime_sec: truncInt32(Math.trunc(st.atimeMs / 1000)),
    atime_nsec: (st.atimeMs * 1000000) % 1000000000,
    mtime_sec: truncInt32(Math.trunc(st.mtimeMs / 1000)),
    mtime_nsec: (st.mtimeMs * 1000000) % 1000000000,
    ctime_sec: truncInt32(Math.trunc(st.ctimeMs / 1000)),
    ctime_nsec: (st.mtimeMs * 1000000) % 1000000000,
  };
  return ft;
}
